{-# LANGUAGE OverloadedStrings #-}

module Main where

-- import Control.Applicative (many, (<$>), (<|>), (*>), (<*))
import Control.Applicative ((<$>), (*>), (<*))
import Control.Monad (void)
import Data.Char (isLower, isUpper, isAlpha)
import Data.List (nub, foldl1')
import Data.Text (Text, pack)
import Text.Parsec as P

import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Marshal
import JavaScript.Canvas (Context, getContext, fillText, moveTo, lineTo, scale, translate, save, restore, stroke, strokeStyle, clearRect, beginPath, font)
import JavaScript.JQuery (select)

import Debug.Trace

-- Note this is left associative
tyExpr :: Parsec String () Ty
-- tyExpr = foldl1' TyApp <$> (many (atomicTy <* spaces))
tyExpr = do
    atomics <- many1 (atomicTy <* spaces)
    trace "tyExpr trace:" (return ())
    trace (show atomics) (return ())
    return $ foldl1' TyApp atomics

-- | Unsophisticated type representation. This ignores at least two
-- important things:
-- * name capture
-- * kinds
type Const = String
type Var = String

data Ty = TyVar Var
        | TyConst Const
        | TyApp Ty Ty
        deriving (Show, Eq)

data Unifier = AppEq Unifier Unifier -- some application equals another
             | VarEq Ty Ty -- some var equals a constant
             | FailEq Ty Ty

instance ToJSRef Ty where
    toJSRef (TyVar v) = do
        o <- newObj
        setProp ("type"::JSString) ("var"::JSString) o
        setProp ("name"::JSString) (toJSString v) o
        return o
    toJSRef (TyConst c) = do
        o <- newObj
        setProp ("type"::JSString) ("const"::JSString) o
        setProp ("name"::JSString) (toJSString c) o
        return o
    toJSRef (TyApp t1 t2) = do
        o <- newObj
        setProp ("type"::JSString) ("app"::JSString) o
        left <- toJSRef t1
        right <- toJSRef t2
        setProp ("left"::JSString) left o
        setProp ("right"::JSString) right o
        return o

instance ToJSRef Unifier where
    toJSRef (AppEq u1 u2) = do
        o <- newObj
        setProp ("type"::JSString) ("app"::JSString) o
        u1' <- toJSRef u1
        u2' <- toJSRef u2
        setProp ("left"::JSString) u1' o
        setProp ("right"::JSString) u2' o
        return o
    toJSRef (VarEq v1 v2) = do
        o <- newObj
        setProp ("type"::JSString) ("varEq"::JSString) o
        v1' <- toJSRef v1
        v2' <- toJSRef v2
        setProp ("left"::JSString) v1' o
        setProp ("right"::JSString) v2' o
        return o
    toJSRef (FailEq v1 v2) = do
        o <- newObj
        setProp ("type"::JSString) ("failEq"::JSString) o
        v1' <- toJSRef v1
        v2' <- toJSRef v2
        setProp ("left"::JSString) v1' o
        setProp ("right"::JSString) v2' o
        return o

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

mapBoth :: (a -> b) -> (a, a) -> (b, b)
mapBoth f (a, a') = (f a, f a')

sequenceBoth :: (Either e a, Either e b) -> Either e (a, b)
sequenceBoth (Right a, Right b) = Right (a, b)
sequenceBoth (Left e, _) = Left e
sequenceBoth (_, Left e) = Left e

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

fillText' :: String -> Double -> Double -> Context -> IO ()
fillText' str = fillText (pack str)

drawWith :: (Double -> Double -> Double -> Double -> a -> Context -> IO b) -> a -> Context -> IO b
drawWith f a ctx = do
    clearRect 0 0 220 220 ctx
    font "12px sans-serif" ctx
    strokeStyle 0 0 0 0 ctx

    f 10 10 210 210 a ctx

unHeight :: Unifier -> Double
unHeight (AppEq u1 u2) = 1 + (max (unHeight u1) (unHeight u2))
unHeight _ = 1

tyHeight :: Ty -> Double
tyHeight (TyApp t1 t2) = 1 + (max (tyHeight t1) (tyHeight t2))
tyHeight _ = 1

drawTy :: Double -> Double -> Double -> Double -> Ty -> Context -> IO (Double, Double)
drawTy x y w h (TyVar v) ctx = let (x', y') = (x + w/2, y+h/2) in fillText' v x' y' ctx >> return (x', y')
drawTy x y w h (TyConst c) ctx = let (x', y') = (x + w/2, y+h/2) in fillText' c x' y' ctx >> return (x', y')
--     @
--    / \
--   t1 t2
drawTy x y w h ty@(TyApp t1 t2) ctx = do
    let treeHeight = tyHeight ty
        vUnit = h/treeHeight
        appPos = (x + w/2, y+vUnit/2)
    -- split up the space:
    -- vertically: 1/treeHeight for '@', rest for t1 and t2
    -- horizonally: 1/2 for t1, 1/2 for t2

    fillText' "@" (fst appPos) (snd appPos) ctx

    -- t1
    t1End <- drawTy x (y+vUnit) (w/2) (h - vUnit) t1 ctx

    -- t2
    t2End <- drawTy (x + w/2) (y+vUnit) (w/2) (h - vUnit) t2 ctx

    -- lines
    beginPath ctx
    -- /
    moveTo (fst appPos) (snd appPos) ctx
    -- lineTo (x+hUnit/2) (y+1.5*vUnit) ctx
    lineTo (fst t1End) (snd t1End) ctx
    -- \
    moveTo (fst appPos) (snd appPos) ctx
    -- lineTo (x+3*hUnit/2) (y+1.5*vUnit) ctx
    lineTo (fst t2End) (snd t2End) ctx
    stroke ctx
    return appPos

drawUnifier :: Double -> Double -> Double -> Double -> Unifier -> Context -> IO (Double, Double)
drawUnifier x y w h un@(VarEq t1 t2) ctx = let (x', y') = (x + w/2, y+h/2) in fillText' (pprint t1 ++ " = " ++ pprint t2) x' y' ctx >> return (x', y')
drawUnifier x y w h un@(FailEq t1 t2)  ctx = let (x', y') = (x + w/2, y+h/2) in fillText' (pprint t1 ++ " =/= " ++ pprint t2) x' y' ctx >> return (x', y')
--     @
--    / \
--   t1 t2
drawUnifier x y w h un@(AppEq u1 u2) ctx = do
    let treeHeight = unHeight un
        vUnit = h/treeHeight
        appPos = (x + w/2, y+vUnit/2)
    -- split up the space:
    -- vertically: 1/treeHeight for '@', rest for t1 and t2
    -- horizonally: 1/2 for t1, 1/2 for t2

    fillText' "@" (fst appPos) (snd appPos) ctx

    -- t1
    t1End <- drawUnifier x (y+vUnit) (w/2) (h - vUnit) u1 ctx

    -- t2
    t2End <- drawUnifier (x + w/2) (y+vUnit) (w/2) (h - vUnit) u2 ctx

    -- lines
    beginPath ctx
    -- /
    moveTo (fst appPos) (snd appPos) ctx
    -- lineTo (x+hUnit/2) (y+1.5*vUnit) ctx
    lineTo (fst t1End) (snd t1End) ctx
    -- \
    moveTo (fst appPos) (snd appPos) ctx
    -- lineTo (x+3*hUnit/2) (y+1.5*vUnit) ctx
    lineTo (fst t2End) (snd t2End) ctx
    stroke ctx
    return appPos

pageInteraction :: JSRef () -> IO ()
pageInteraction ref = do
    expr1 <- fromJSString <$> getProp ("expr1" :: Text) ref
    expr2 <- fromJSString <$> getProp ("expr2" :: Text) ref

    case (parseExpr expr1, parseExpr expr2) of
        (Right ty1, Right ty2) -> do
            putStrLn expr1
            putStrLn expr2
            leftCtx <- getContext =<< indexArray 0 . castRef =<< select "#leftCanvas"
            rightCtx <- getContext =<< indexArray 0 . castRef =<< select "#rightCanvas"
            unifiedCtx <- getContext =<< indexArray 0 . castRef =<< select "#unifiedCanvas"

            void $ drawWith drawTy ty1 leftCtx
            void $ drawWith drawTy ty2 rightCtx

            void $ drawWith drawUnifier (unify ty1 ty2) unifiedCtx

            {-
            ty1' <- toJSRef ty1
            ty2' <- toJSRef ty2
            setProp ("parsed1"::JSString) ty1' ref
            setProp ("parsed2"::JSString) ty2' ref
            -}
            u <- toJSRef $ unify ty1 ty2
            setProp ("unified"::JSString) u ref

        e -> print e

main :: IO ()
main = case testCases of
    Left err -> print err
    Right exprs -> mapM_ printUnification exprs
