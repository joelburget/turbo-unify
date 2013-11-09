{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}

module Main where

import Control.Applicative ((<$>), (*>), (<*))
import Control.Arrow hiding ((|||))
import Control.Monad (void)
import Control.Monad.Error
import Control.Monad.State
import Data.Char (isLower, isUpper, isAlpha)
import Data.Functor.Identity
import Data.List (nub, foldl1')
import Data.Map.Lazy hiding (map)
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack)
import Data.Word (Word8)
import GHC.Generics
import Prelude hiding (lookup)
import System.Random
import Text.Parsec as P hiding (Empty)

import Data.Colour.SRGB
import Data.Tree (Tree)
import Diagrams.Prelude hiding (moveTo, stroke)
import Diagrams.Backend.GHCJS
import Diagrams.TwoD.Layout.Tree
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Marshal
import JavaScript.Canvas (Context, getContext, clearRect)
import JavaScript.JQuery (select)

-- Note this is left associative
tyExpr :: Parsec String () Ty
tyExpr = foldl1' TyApp <$> many1 (atomicTy <* spaces)

-- | Unsophisticated type representation. This ignores at least two
-- important things:
-- * name capture
-- * kinds
type Const = String
type Var = String

data Ty = TyVar Var
        | TyConst Const
        | TyApp Ty Ty
        deriving (Show, Generic)

tyToTree :: Ty -> BTree String
tyToTree (TyVar v) = BNode v Empty Empty
tyToTree (TyConst c) = BNode c Empty Empty
tyToTree (TyApp t1 t2) = BNode "@" (tyToTree t1) (tyToTree t2)

data Unifier = AppEq Unifier Unifier -- some application equals another
             | VarEq Ty Ty -- some var equals a constant
             | FailEq Ty Ty
             deriving Generic

unToTree :: Unifier -> BTree String
unToTree (AppEq u1 u2) = BNode "@" (unToTree u1) (unToTree u2)
unToTree (VarEq t1 t2) = BNode (pprint t1 ++ " = " ++ pprint t2) Empty Empty
unToTree (FailEq t1 t2) = BNode (pprint t1 ++ "=/=" ++ pprint t2) Empty Empty

instance ToJSRef Ty where toJSRef = toJSRef_generic id
instance ToJSRef Unifier where toJSRef = toJSRef_generic id

-- ty := atomicTy *
--
-- atomicTy := '(' ty ')'
--           | var
--           | const

parseExpr :: String -> Either ParseError Ty
parseExpr = runParser tyExpr () "expression"

atomicTy :: Parsec String () Ty
atomicTy =  parenTy <|> tyVar <|> tyConst where
    parenTy = char '(' *> tyExpr <* char ')'
    tyVar = TyVar <$> lowerIdentifier
    tyConst = TyConst <$> upperIdentifier

nameBegins :: (Char -> Bool) -> Parsec String () String
nameBegins test = do
    lookAhead $ P.try $ P.satisfy test
    many (satisfy isAlpha)

-- | A name beginning with a lower-case letter.
upperIdentifier :: Parsec String () String
upperIdentifier = nameBegins isUpper

-- | A name beginning with a lower-case letter.
lowerIdentifier :: Parsec String () String
lowerIdentifier = nameBegins isLower

class Pprint a where
    pprint :: a -> String

instance Pprint Ty where
    pprint (TyVar var) = var
    pprint (TyConst var) = var
    pprint (TyApp t1 t2) = pprint t1 ++ " " ++ pprint t2

instance (Pprint a, Pprint b) => Pprint (a, b) where
    pprint (a, b) = "(" ++ pprint a ++ ", " ++ pprint b ++ ")"

instance Pprint Unifier where
    pprint (AppEq t1 t2) = "(" ++ pprint t1 ++ ")" ++ " = " ++ "(" ++ pprint t2 ++ ")"
    pprint (VarEq t1 t2) = pprint t1 ++ " = " ++ pprint t2
    pprint (FailEq t1 t2) =
        "fail: couldn't unify " ++ pprint t1 ++ " and " ++ pprint t2

unify :: Ty -> Ty -> Unifier
unify t1@(TyVar _) t2 = VarEq t1 t2
unify t1 t2@(TyVar _) = VarEq t1 t2
unify t1@(TyConst nm1) t2@(TyConst nm2) = if nm1 == nm2
    then VarEq t1 t2
    else FailEq t1 t2
unify (TyApp t11 t12) (TyApp t21 t22) =
    AppEq (unify t11 t21) (unify t12 t22)
unify t1 t2 = FailEq t1 t2

mapBoth :: (a -> b) -> (a, a) -> (b, b)
mapBoth f (a, a') = (f a, f a')

sequenceBoth :: (Either e a, Either e b) -> Either e (a, b)
sequenceBoth (Right a, Right b) = Right (a, b)
sequenceBoth (Left e, _) = Left e
sequenceBoth (_, Left e) = Left e

testCases :: Either ParseError [(Ty, Ty)]
testCases = sequence $ fmap (sequenceBoth . mapBoth parseExpr)
    [ ("x", "y")
    , ("x", "Const")
    , ("Const x", "Const y")
    , ("Const x", "Const (Const Float)")
    , ("Const x y", "Either Int Float")
    , ("Either Int y", "Either Int Float")
    , ("Either Int y", "Either x Float")
    , ("Either Int y", "x")
    , ("Const Int", "a Int")
    , ("a b", "Either a (Const Float)")
    ]

printUnification :: (Ty, Ty) -> IO ()
printUnification tys = mapM_ putStrLn
    [ pprint tys
    , "=>"
    , pprint $ uncurry unify tys
    , ""
    ]

safeColors :: [Clr]
safeColors = [
      sRGB24read "#002A4A"
    , sRGB24read "#17607D"
    , sRGB24read "#FFF1CE"
    , sRGB24read "#FF9311"
    , sRGB24read "#E33200"
    ]

stripes :: Clr -> Clr -> Int -> Diag
stripes c1 c2 stripes = let width = (1 / fromIntegral stripes) in
    foldl1 (|||)
        $ map (\clr -> rect width 1 # fc clr # lc clr)
        $ take stripes
        $ cycle [c1, c2]

fills :: [Diag]
fills = ([\clr -> square 1 # fc clr # lc clr] <*> safeColors)
     <> ((\clr1 clr2 -> stripes clr1 clr2 10
                # translate (r2 (-0.4, 0))
                # rotateBy (3/8)
                # scale 1.5
                # clipBy (square 1))
            <$> safeColors <*> safeColors)

node :: Map String Diag -> String -> Diag
node backgrounds name =
    let bg = fromMaybe (square 1 # fc black) (lookup name backgrounds)
		   # scale 3
		   # clipBy (roundedRect 3 1.3 0.3)
    in (text name # font "Droid Sans Mono" # fc white # scale 0.8) <> bg

nameNodes :: BTree String -> TreeM StdGen ()
nameNodes Empty = return ()
nameNodes (BNode a t1 t2) = do
    colorName a
    nameNodes t1
    nameNodes t2

drawTree :: BTree String
         -> Context
         -> IO (Either String ((), StdGen, [Diag], Map String Diag))
drawTree tree ctx = do
    seed <- getStdGen
    runTreeT' seed $ do
        liftIO $ clearRect 0 0 220 220 ctx
        let d = uniqueXLayout 2 2 tree
            d' :: TreeM g (Tree (String, P2))
            d' = (TreeT . lift . liftEither . mToE "couldn't lay out diagram") d
        nameNodes tree :: TreeM StdGen ()
        names <- (\(_, _, a) -> a) <$> get
        tree' <- (pad 1.1 . lw 0.03 . centerXY . renderTree (node names) (~~))
            <$> d'
        liftIO $ renderDia' ctx tree'

renderDia' :: Context -> Diag -> IO ()
renderDia' c = renderDia Canvas (CanvasOptions (Dims 200 200) c)

type Clr = Colour Double
type Diag = Diagram Canvas R2

-- TODO:
-- * think of a set of primitives
newtype TreeT g m a = TreeT {
    unTreeT :: StateT (g, [Diag], Map String Diag) (ErrorT String m) a
    } deriving (Functor, Applicative, Monad)
deriving instance Monad m => MonadState (g, [Diagram Canvas R2], Map String Diag) (TreeT g m)
deriving instance Monad m => MonadError String (TreeT g m)
deriving instance MonadIO m => MonadIO (TreeT g m)
-- Monadic language for describing trees
type TreeM g a = TreeT g IO a
-- Restricted version
type RTreeM g a = TreeT g Identity a

type MonadTree g m = (RandomGen g, Monad m, MonadState (g, [Diagram Canvas R2], Map String (Diagram Canvas R2)) m, MonadError String m)

colorName :: MonadTree g m => String -> m ()
colorName str = do
    (rand, diags, nameColors) <- get
    case diags of
        [] -> throwError "Out of colors!"
        diag':diags' -> put (rand, diags', insert str diag' nameColors)

runTreeT' :: g
          -> TreeM g a
          -> IO (Either String (a, g, [Diagram Canvas R2], Map String Diag))
runTreeT' = runTreeT

runTreeT :: Functor m
         => g
         -> TreeT g m a
         -> m (Either String (a, g, [Diagram Canvas R2], Map String Diag))
runTreeT g m = (fmap.fmap) flatten
    $ runErrorT
    $ runStateT (unTreeT m) (g, fills, empty)

flatten :: (a, (b, c, d)) -> (a, b, c, d)
flatten (a, (b, c, d)) = (a, b, c, d)

right :: (b -> c) -> Either a b -> Either a c
right _ (Left a) = Left a
right f (Right b) = Right (f b)

liftEither :: Monad m => Either e a -> ErrorT e m a
liftEither = ErrorT . return

mToE :: String -> Maybe a -> Either String a
mToE str = maybe (Left str) Right

eToM :: Either String a -> Maybe a
eToM = either (const Nothing) Just

-- generate a color for each variable
nextColor :: RandomGen g => g -> (Clr, g)
nextColor gen = (sRGB24 r g b, newGen) where
    (_, newGen) = next gen
    r:g:b:_ = map fromIntegral (randomRs (0, 255) gen :: [Int])

pageInteraction :: JSRef () -> IO ()
pageInteraction ref = do
    expr1 <- fromJSString <$> getProp ("expr1" :: Text) ref
    expr2 <- fromJSString <$> getProp ("expr2" :: Text) ref

    case (parseExpr expr1, parseExpr expr2) of
        (Right ty1, Right ty2) -> do
            let getctx str = getContext =<< indexArray 0 . castRef =<< select str
                unified = unify ty1 ty2

            drawTree (tyToTree ty1)     =<< getctx "#leftCanvas"
            drawTree (tyToTree ty2)     =<< getctx "#rightCanvas"
            drawTree (unToTree unified) =<< getctx "#unifiedCanvas"

            u <- toJSRef unified
            setProp ("unified" :: JSString) u ref

        e -> print e

main :: IO ()
main = case testCases of
    Left err -> print err
    Right exprs -> mapM_ printUnification exprs
