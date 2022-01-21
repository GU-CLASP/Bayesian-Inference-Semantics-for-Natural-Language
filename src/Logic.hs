module Logic where

import Control.Monad.State
import Data.List (intercalate)

data Distr = Interval

data Type = Distribution Distr 
          | Sigma Type (Expr -> Type)
          | IsTrue Prop

data Prop = Truth | Falsity | Forall Type (Expr -> Prop) | Expr :>=: Expr
data Expr = Measure Type
          | Bin Op Expr Expr
          | Con String
          | Var String
          | Pair Expr Expr
          | Fun String [Expr]
          | Proof
          | Integral Type (Expr -> Expr)


(-->) :: Prop -> Prop -> Prop
a --> b = Forall (IsTrue a) (\_ -> b)

proportion :: Type -> (Expr -> Type) -> Expr
proportion a b = Measure (Sigma a b) / Measure a

(~~>) :: Prop -> Prop -> Expr
a ~~> b = proportion (IsTrue a) (\_ -> IsTrue b)

type Op = String

type R = String

type Gen = State Int

instance Fractional Expr where
  (/) = Bin "/"
  fromRational = Con . show
  
instance Num Expr where
  (*) = Bin "*"
  (+) = Bin "+"
  (-) = Bin "-"
  abs = Fun "abs" . return
  signum = Fun "signum" . return
  fromInteger x = Con (show x)

density :: Distr -> Expr -> Expr
density Interval = Fun "interval" . return

newVar :: Gen Expr
newVar = do
  x <- get
  put (x+1)
  return (Var $ "x" ++ show x)

integral :: Type -> (Expr -> Gen R) -> Gen R
integral (IsTrue p) f = do
  p' <- eExpr (eProp p)
  f' <- f Proof
  return (p' ++ "*" ++ f')
integral (Distribution d) f = do
  x@(Var v) <- newVar
  body <- (f x)
  d' <- eExpr (density d x)
  return $ parens $ ("Integrate " ++ body ++ "*" ++ d' ++ v)
integral (Sigma a f) g = integral a $ \x -> integral (f x) $ \y -> g (Pair x y)

eType :: Type -> Expr
eType (Distribution _) = 1
eType (IsTrue p) = eProp p
eType (Sigma a f) = Integral a (eType . f)

parens :: [Char] -> [Char]
parens x = "(" ++ x ++ ")"

eProp :: Prop -> Expr
eProp Truth = 1
eProp Falsity = 0
eProp (Forall a f) = eProp (Measure (Sigma a (IsTrue . f)) :>=: Measure a)
eProp (e1 :>=: e2) = Bin ">=" e1 e2

eExpr :: Expr -> Gen R
eExpr (Measure t) = eExpr (eType t)
eExpr (Pair x y) = eExpr (Bin "," x y)
eExpr Proof = return "<>"
eExpr (Fun f xs) = do
 xs' <- mapM eExpr xs
 return $ f ++ parens (intercalate "," xs')
eExpr (Integral t f) = integral t (eExpr . f)
eExpr (Bin op x y) = do
  x' <- eExpr x
  y' <- eExpr y
  return $ parens $ x' ++ op ++ y'
eExpr (Var x) = return x
eExpr (Con x) = return x
-- eExpr (Pair x y) = eExpr x ++ "," ++ eExpr y

proj1 (Pair x _) = x
proj2 (Pair _ x) = x



{-
integral y ∈ [0,1] (x < y)
  = integral y ∈ [0,x] (x < y) + integral y ∈ [x,1] (x < y)
  = integral y ∈ [0,x] 0       + integral y ∈ [x,1] 1
  = 0                          + (1-x)


integral x∈[0,1] (1-x)
  = (1-x^2/2) [0,1]
  = 1/2
-}

