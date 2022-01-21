{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module LogicT where
-- import Control.Monad.State
-- import Data.List (intercalate)
import MCMC
import PreciseProb
import Algebra.Classes
import Prelude hiding (Ord(..),Num(..),(/),fromRational,(&&),(||),not)

type Prop = Expr Prob

type SR t = (Show t, Read t)
data Type t where
  Distribution :: Distribution t -> Type t
  Sigma :: (SR t,SR u) => Type t -> (Expr t -> Type u) -> Type (t,u)
  IsTrue :: Prop -> Type ()
  Image :: SR t => (Expr t -> Expr u) -> Type t -> Type u

density :: Type t -> t -> Prob
density (Sigma a f) (x,y) = density a x * density (f (Con (pure x))) y
density (IsTrue p) () = _ -- eval p


-- Possible next step: use a more general category than (->). But!
-- ExpectedValue won't be derivable anyway?
-- (Perhaps it'll work with samples?)




data Expr t where
  -- Proportion :: Type t -> (Expr t -> Type u) -> Expr R
  -- Measure :: Type t -> Expr R
  Bin :: (t -> u -> v) -> Expr t -> Expr u -> Expr v
  Con :: Probabilistic t -> Expr t
  -- Var :: String -> Expr t
  Pair :: Expr t -> Expr u -> Expr (t,u)
  -- Fun :: Expr x -> [Expr t] -> Expr u
  -- Proof :: Expr ()
  ExpectedValue :: (Show t, Read t) => Type t -> (Expr t -> Expr R) -> Expr R
  App :: Expr (t -> u) -> Expr t -> Expr u
  -- Lam :: (Expr t -> Expr u) -> Expr (t -> u)
  -- Truth, Falsity :: Prop

sample' :: Read t => Show t => Type t -> P (Probabilistic t)
sample' = \case
  IsTrue p -> do
    p' <- eval p
    pure <$> observe p'
  Sigma a f -> do
    x <- sample' a
    y <- sample' (f (Con x))
    return $ (,) <$> x <*> y
  Distribution d -> sample d
  Image f a -> do
    x <- sample' a
    (eval (f (Con x)))
  -- Distribution d -> Sample d Result

indicator :: Bool -> R
indicator True = 1
indicator False = 0

eval :: Expr t -> P (Probabilistic t)
eval = \case
  App t u -> do
    t' <- eval t
    u' <- eval u
    return (t' <*> u')
  Pair t u -> do
    x <- eval t
    y <- eval u
    return ((,) <$> x <*>  y)
  ExpectedValue a f -> do
    freqs <- subInference $ do
      x <- sample' a
      eval (f (Con x))
    return (expectedValue <$> freqs)
  Con t -> return t
  -- Bin f t u -> f (eval t) (eval u)
     -- (Var _) -> _
     -- ... -> _
  -- Truth -> True


-- proportion :: Type t -> (Expr t -> Type u) -> Expr R
-- proportion a b = Measure (Sigma a b) / Measure a

-- (~~>) :: Prop -> Prop -> Expr R
-- a ~~> b = proportion (IsTrue a) (\_ -> IsTrue b)

-- max :: Expr R -> Expr R -> Expr R
-- max x y = Fun (Con "Max") [x,y]

-- type Op = String

-- type R = String

-- type Gen = State Int

-- instance Fractional (Expr R) where
--   (/) = Bin "/"
--   fromRational x = Con $ show x'
--     where x' :: R
--           x' = fromRational x

-- instance Num (Expr R) where
--   (*) = Bin "*"
--   (+) = Bin "+"
--   (-) = Bin "-"
--   abs = Fun (Con "Abs") . return
--   signum = Fun (Con "signum") . return
--   fromInteger x = Con (show x)

-- bounds :: Distr -> (Expr R,Expr R)
-- bounds Interval = (0,1)
-- bounds (Beta _ _) = (0,1)

-- density :: Distr -> Expr R -> Expr R
-- density Interval _ = 1
-- density (Beta a b) x = Fun (Fun (Con "PDF") [Fun (Con "BetaDistribution") [a,b]]) [x]

-- newVar :: Gen (Expr R)
-- newVar = do
--   x <- get
--   put (x+1)
--   return (Var $ "x" ++ show x)

-- integral :: Type t -> (Expr t -> Gen R) -> Gen R
-- integral (Image f t) g = integral t (g . f)
-- integral (IsTrue p) f = do
--   p' <- eExpr p
--   f' <- f Proof
--   return (p' ++ "*" ++ f')
-- integral (Distribution d) f = do
--   x@(Var v) <- newVar
--   body <- (f x)
--   d' <- eExpr (density d x)
--   let (lo,hi) = bounds d
--   lo' <- eExpr lo
--   hi' <- eExpr hi
--   return $ parens $ ("Integrate [" ++ body ++ "*" ++ d' ++ ", {" ++ v ++ "," ++ lo' ++ "," ++ hi' ++ "}]")
-- integral (Sigma a f) g = integral a $ \x -> integral (f x) $ \y -> g (Pair x y)

-- eType :: Type t -> Expr R
-- eType (Distribution _) = 1
-- eType (Image _ t) = eType t
-- eType (IsTrue p) = Indicator p
-- eType (Sigma a f) = Integral a (eType . f)

parens :: [Char] -> [Char]
parens x = "(" ++ x ++ ")"

brackets :: [Char] -> [Char]
brackets x = "[" ++ x ++ "]"


type Support a = [a] -- actually a (disjoint) list of intervals.



-- integralAvg :: Type a -> (Expr a -> Gen R) -> Gen R
-- integralAvg t f | finite (support t) = sum (map f elements) / length elements
--   where elements = _
--                 | otherwise = ... usual

-- eExpr :: Expr t -> Gen R
-- -- eExpr (Proportion a f) = integralAverage a (eExpr . Measure . f)
-- eExpr Truth = return "True"
-- eExpr Falsity = return "False"
-- eExpr (Measure t) = eExpr (eType t)
-- eExpr (Indicator t) = (\x -> "Boole[" ++ x ++ "]") <$> eExpr t
-- eExpr (Pair x y) = eExpr (Bin "," x y)
-- eExpr Proof = return "<>"
-- eExpr (Fun f xs) = do
--  f' <- eExpr f
--  xs' <- mapM eExpr xs
--  return $ f' ++ brackets (intercalate "," xs')
-- eExpr (Integral t f) = integral t (eExpr . f)
-- eExpr (Bin op x y) = do
--   x' <- eExpr x
--   y' <- eExpr y
--   return $ parens $ x' ++ op ++ y'
-- eExpr (Var x) = return x
-- eExpr (Con x) = return x
-- -- eExpr (Pair x y) = eExpr x ++ "," ++ eExpr y

-- proj1 :: Expr (t,u) -> Expr t
-- proj1 (Pair x _) = x

-- proj2 :: Expr (t,u) -> Expr u
-- proj2 (Pair _ x) = x

-- app :: Expr (a -> b) -> Expr a -> Expr b
-- app (Lam f) a = f a

-- test
--   = Sigma (Distribution $ Beta 2 8) $ \x ->
--     Sigma (Distribution Interval) $ \y ->
--     IsTrue (x <= y)


-- toMathematica :: Type t -> String
-- toMathematica = fst . flip runState 0. eExpr . eType

-- >>> toMathematica test
-- "(Integrate [(Integrate [Boole[(x0<=x1)]*1, {x1,0,1}])*PDF[BetaDistribution[2,8]][x0], {x0,0,1}])"


