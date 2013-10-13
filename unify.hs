{-# LANGUAGE OverloadedStrings, DeriveGeneric #-}

module Main where

import Control.Applicative ((<$>), (*>), (<*))
import Control.Monad (void)
import Data.Char (isLower, isUpper, isAlpha)
import Data.List (nub, foldl1')
import Data.Text (Text, pack)
import GHC.Generics
import Text.Parsec as P hiding (Empty)

import Diagrams.Prelude hiding (font, moveTo, stroke)
import Diagrams.Backend.GHCJS
import Diagrams.TwoD.Layout.Tree
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Marshal
import JavaScript.Canvas (Context, getContext, clearRect)
import JavaScript.JQuery (select)

-- Note this is left associative
tyExpr :: Parsec String () Ty
tyExpr = foldl1' TyApp <$> (many (atomicTy <* spaces))

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
testCases = sequence $ fmap sequenceBoth $ (fmap.mapBoth) parseExpr
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
    , pprint $ uncurry unify $ tys
    , ""
    ]

-- TODO figure out why single variables don't cause a render
pageInteraction :: JSRef () -> IO ()
pageInteraction ref = do
    expr1 <- fromJSString <$> getProp ("expr1" :: Text) ref
    expr2 <- fromJSString <$> getProp ("expr2" :: Text) ref

    case (parseExpr expr1, parseExpr expr2) of
        (Right ty1, Right ty2) -> do
            let getctx str = getContext =<< indexArray 0 . castRef =<< select str
            leftCtx <- getctx "#leftCanvas"
            rightCtx <- getctx "#rightCanvas"
            unifiedCtx <- getctx "#unifiedCanvas"

            let drawTree tree ctx = do
                clearRect 0 0 200 200 ctx
                let d = uniqueXLayout 2 2 tree
                    node name = text name <> roundedRect 3 1.3 0.3 # fc white
                    tree' = pad 1.1 . lw 0.03 . centerXY <$> renderTree node (~~) <$> d
                renderDia' ctx $ maybe (circle 1) id tree'

            drawTree (tyToTree ty1) leftCtx
            drawTree (tyToTree ty2) rightCtx
            drawTree (unToTree (unify ty1 ty2)) unifiedCtx

            u <- toJSRef $ unify ty1 ty2
            setProp ("unified"::JSString) u ref

        e -> print e

renderDia' :: Context -> Diagram Canvas R2 -> IO ()
renderDia' c = renderDia Canvas (CanvasOptions (Dims 200 200) c)

main :: IO ()
main = do
    case testCases of
        Left err -> print err
        Right exprs -> mapM_ printUnification exprs
