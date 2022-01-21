{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
module Common where

import Numeric
import Prelude hiding (and,or,Ord(..))
import Control.Monad.RWS
import System.Process
import System.Exit
import Data.List (intercalate)
import qualified Data.Vector.Unboxed as V
import Statistics.Sample.KernelDensity
import Text.Read (readMaybe)

--------------------------------------------
-- Basic code-gen infrastructure

type a ⊸ b = a -> b
data Expr t where
  Expr :: String -> Expr t -- constant expression
  Lam :: (Expr a -> Expr t) -> Expr (a -> t) -- lambda
  App :: Expr (a -> t) -> Expr a -> Expr t -- application
  BinOp :: (String -> String -> String) -> Expr a -> Expr b -> Expr c
  UnOp :: (String -> String) -> Expr a -> Expr b
  If :: Prop -> Expr a -> Expr a -> Expr a
  -- Let :: P (Expr a) -> (Expr a ⊸ Expr b) -> Expr b
  Thunk :: P (Expr t) -> Expr t

instance Show (Expr t) where
  show _ = "<<EXPR>>"

class Representable a where
  constant :: a -> Expr a

instance Representable Bool where
  constant True = Expr "true"
  constant False = Expr "false"

instance Representable Float where
  constant = Expr . show

instance Fractional (Expr Float) where
  fromRational x = constant (fromRat x)
  (/) = BinOp (infixOp "/")

instance Num (Expr Float) where
  abs = UnOp (\x -> "Math.abs(" ++ x ++ ")")
  (-) = BinOp (infixOp "-")
  (+) = BinOp (infixOp "+")
  fromInteger x = constant (fromInteger x)
  (*) = BinOp (infixOp "*")

instance Floating (Expr Float) where
  sqrt = UnOp (\x -> "Math.sqrt(" ++ x ++ ")")
  exp = UnOp (\x -> "Math.exp(" ++ x ++ ")")
  log = UnOp (\x -> "Math.log(" ++ x ++ ")")

render :: Expr a -> P String
render = \case
  UnOp op x -> do
    x' <- render x
    return (op x')
  BinOp op x y -> do
    x' <- render x
    y' <- render y
    return (op x' y')
  Expr x -> return x
  App (Lam f) x -> render (f x)
  Lam f -> do
    x <- newVar
    body <- render (f (Expr x))
    return ("function( " ++ x ++ ") { return " ++ body ++ "; }")
  Thunk f -> do
    (x,body) <- censor (\_ -> []) $ listen f
    x' <- render x
    return ("function() {\n" ++ unlines body ++ " return " ++ x' ++ ";\n }")
  App x y -> do
    x' <- render x
    y' <- render y
    return ("(" ++ x' ++ ")(" ++ y' ++ ")")
  If cond x y -> do
    c' <- render cond
    x' <- render x
    y' <- render y
    return ("(" ++ c'  ++ "?" ++ x' ++ ":" ++ y' ++ ")")
  -- Let e f -> do
  --   x <- newVar
  --   e' <- render =<< e -- works only if f uses its argument at most once.
  --   fx <- render (f (Expr x))
  --   return ("var " ++ x ++ " = "++ e' ++";\n" ++ fx)

infixl #
(#) :: Expr (a -> b) -> Expr a -> Expr b
(#) = App

parens :: [Char] -> [Char]
parens x = "("++ x ++")"
infixOp :: [Char] -> [Char] -> [Char] -> [Char]
infixOp op x y = parens x ++ op ++ parens y
binFunc :: [Char] -> [Char] -> [Char] -> [Char]
binFunc f x y = f ++ "("++ x ++ "," ++ y ++")"

unFunc ::  [Char] -> [Char] -> [Char]
unFunc f x = f ++ "("++ x ++ ")"

newtype P a = P (RWS () [String] State a) deriving (Functor,Applicative,Monad,MonadState State, MonadWriter [String])

data State = State {nextVar :: Int}

logtrace :: String -> Expr a -> P ()
logtrace msg x = do
  x' <- render x
  emit ("console.log(" ++ show "LOG: " ++ "+" ++ show msg ++ "+ \" \" +" ++ x' ++ ");")

compileModel :: String -> P (Expr a) -> String
compileModel mainFunc m = unlines (z ++ [x])
  where (x,_,z) = runRWS p () (State {nextVar = 0})
        (P p) = render (UnOp (unFunc mainFunc) (Thunk m))


-- | Allocate a new variable
newVar :: P String
newVar = do
  n <- gets nextVar
  modify $ \State{..} -> State {nextVar = n+1, ..}
  return ("v" ++ show n)

emit :: String -> P ()
emit x = tell [x]

--------------------------------
-- Running models

class KnownTyp a where
  isContinuous :: Bool

instance KnownTyp Float where
  isContinuous = True

instance KnownTyp Bool where
  isContinuous = False

parseValues :: [String] -> IO [Double]
parseValues [] = return []
parseValues (v:vs) = case readMaybe v of
  Nothing -> putStrLn v >> parseValues vs
  Just x -> (x:) <$> parseValues vs

run :: forall a. KnownTyp a => P (Expr a) -> IO ()
run model = do
  putStrLn "Creating model..."
  rts <- readFile "../Frontend/RTS.wppl"
  let m = compileModel mainName model
      funname = "modelFunction"
      mainName = if isContinuous @a then "mainContinuous" else "mainDiscrete"
      fname = funname ++ ".wppl"
  writeFile fname (intercalate "\n\n" [rts,m])
  putStrLn "Running webppl..."
  (code,output,errors) <- readProcessWithExitCode "webppl" [fname] ""
  case code of
    ExitFailure _ -> do
      putStrLn "Webppl failed with errors:"
      putStrLn output
      putStrLn errors
    ExitSuccess -> do
      putStrLn "Success!"
      case isContinuous @a of
        True -> do
            values <- parseValues (lines output)
            plot funname values
        False -> putStrLn output

plot :: String -> [Double] -> IO ()
plot prefix xs = do
  let (xs',ys') = kde 64 (V.fromList xs)
      fname = prefix ++ ".svg"
  let ls = 
        ["set terminal svg size 350,262 fname 'Verdana' enhanced background rgb 'white'",
         "set output '" ++ fname ++ "'",
         "set key off", -- no legend
          "$data << EOD"] ++
        [show x ++ " " ++ show y | (x,y) <- zip (V.toList xs') (V.toList ys')] ++
        ["EOD", "plot '$data' with lines"] -- filledcurve
  putStrLn "Plotting results..."
  (code,output,errors) <- readProcessWithExitCode "gnuplot" ["-p"] (unlines ls)
  case code of
    ExitFailure _ -> do
      putStrLn "Gnuplot failed with input:"
      putStrLn (unlines ls)
      putStrLn "errors:"
      putStrLn output
      putStrLn errors
    ExitSuccess ->
      putStrLn ("Plot output to " ++ fname)
  return ()

---------------
-- Props

type Prop = Expr Bool

eAnd :: Prop -> Prop -> Prop
eAnd = BinOp (infixOp "&&")

eIff :: Prop -> Prop -> Prop
eIff = BinOp (infixOp "==")

eOr :: Prop -> Prop -> Prop
eOr = BinOp (infixOp "||")

eNot :: Prop -> Prop
eNot = UnOp (\x -> "(!(" ++ x ++ "))")

greaterThan :: Expr Float -> Expr Float -> Prop
greaterThan = BinOp (infixOp ">")

greaterEqualThan :: Expr Float -> Expr Float -> Prop
greaterEqualThan = BinOp (infixOp ">=")


-----------------------
-- Operators

(>) :: Expr Float -> Expr Float -> Prop
(>) = greaterThan

(<) :: Expr Float -> Expr Float -> Prop
(<) = flip (>)

(>=) :: Expr Float -> Expr Float -> Prop
(>=) = greaterEqualThan

(<=) :: Expr Float -> Expr Float -> Prop
(<=) = flip (Common.>=)

instance Lattice (Expr Bool) where
  (/\) = eAnd
  (\/) = eOr
  isBottom x = eIff x (constant False)

-----------------------
-- Intervals, Boxes, Area


class Lattice a where
  (/\) :: a -> a -> a
  (\/) :: a -> a -> a
  isBottom :: a -> Expr Bool
  (⊆) :: a -> a -> Expr Bool

instance Lattice (Expr Float) where
  x /\ y = If (x < y) x y
  x \/ y = If (y > x) y x
  isBottom = error "no bottom float"

data Interval = Ivl (Expr Float) (Expr Float)

(∈) :: Expr Float -> Interval -> Prop
x ∈ ivl = Ivl x x ⊆ ivl


type Box = [Interval]

instance Lattice Interval where
  (Ivl l1 h1) /\ (Ivl l2 h2) = Ivl (l1 \/ l2) (h1 /\ h2)
  (Ivl l1 h1) \/ (Ivl l2 h2) = Ivl (l1 /\ l2) (h1 \/ h2)
  isBottom (Ivl l h) = l > h
  Ivl l1 h1 ⊆ Ivl l2 h2 = (l2 <= l1) /\ (h1 <= h2)

instance Lattice a => Lattice [a] where
  (/\) = zipWith (/\)
  (\/) = zipWith (\/)
  isBottom xs = foldr1 (/\) (map isBottom xs)
  (⊆) b1 b2 = (foldr (/\) (constant True) (zipWith (⊆) b1 b2))

data Pair a = Pair a a deriving (Functor,Foldable)
instance Applicative Pair where
  pure x = Pair x x
  Pair f1 f2 <*> Pair x1 x2 = Pair (f1 x1) (f2 x2)

-- | Disjoint union of boxes, represented as a k-d-tree.
data Volume = Tip Bool | Split Int (Expr Float) (Pair Volume)

type BoxedVolume = (Box,Volume)

complement :: Volume -> Volume
complement (Tip x) = Tip (not x)
complement (Split d x lr) = Split d x (complement <$> lr)

volume :: Box -> Volume -> Expr Float
volume _ (Tip False) = 0
volume b (Tip True) = product [0 \/ (h - l) | Ivl l h <- b]
volume b (Split d x cs) = sum (volume <$> subBoxes b d x <*> cs)

subIntervals :: Interval -> Expr Float -> Pair Interval
subIntervals (Ivl lo hi) mid = Pair (Ivl lo mid) (Ivl mid hi)

subBoxes :: Box -> Int -> Expr Float -> Pair Box
subBoxes [] _ _ = pure []
subBoxes (i:is) 0 cs = (:) <$> subIntervals i cs <*> pure is
subBoxes (i:is) n cs = (i:) <$> subBoxes is (n-1) cs

-- instance Lattice Volume where


-------------------
-- Vecs
type Vec = [Expr Float]

numberOfDimensions :: Int
numberOfDimensions = 2

cosineDistance :: Vec -> Vec -> Expr Float
cosineDistance x y = dotProd x y / (norm x * norm y)

norm2 :: Vec -> Expr Float
norm2 x = dotProd x x

norm :: Vec -> Expr Float
norm = sqrt . norm2

normalize :: Vec -> Vec
normalize xs = ((/ norm xs) <$> xs)

newVector :: Monad m => m a -> m [a]
newVector distr = sequence (replicate numberOfDimensions distr)

dotProd :: Vec -> Vec -> Expr Float
dotProd x y = sum (zipWith (*) x y)


--------------------
-- Random vars

sampleGaussian :: Expr Float -> Expr Float -> P (Expr Float)
sampleGaussian mu sigma = sample (gaussian mu sigma)

sampleUniform :: Expr Float -> Expr Float -> P (Expr Float)
sampleUniform lo hi = sample (uniform (Ivl lo hi))


data Distrib a

unsafeSample :: Expr (Distrib a) -> Expr a
unsafeSample d = Expr "sample" # d

sample :: Expr (Distrib a) -> P (Expr a)
sample d = do
  v <- newVar
  e <- render (unsafeSample d)
  emit ("var " ++ v ++ " = " ++ e ++";" )
  return (Expr v)

bernouilli :: Expr Float -> Expr (Distrib Bool)
bernouilli = UnOp (\x -> "Bernoulli({p:" ++ x ++ "})")

beta :: Expr Float -> Expr Float -> Expr (Distrib Float)
beta = BinOp (\a b -> "Beta({a:" ++ a ++ ",b:" ++ b++ "})")

uniform :: Interval ->  Expr (Distrib Float)
uniform (Ivl lo hi) = BinOp (\a b -> "Uniform({a:" ++ a ++ ",b:" ++ b++ "})") lo hi

gaussian ::  Expr Float ->Expr Float ->  Expr (Distrib Float)
gaussian = BinOp (\a b -> "Gaussian({mu:" ++ a ++ ",sigma:" ++ b++ "})")

--------------------
-- Bayesian operators


observe :: Prop -> P ()
observe = hyp

hyp :: Prop -> P ()
hyp x = do
  x' <- render x
  emit ("hyp(" ++ x' ++ ");")

squared :: Num a => a -> a
squared x = x*x

observeEqual :: Expr Float -> Expr Float -> P ()
observeEqual x y = do
  f <- render (negate (squared (x-y)))
  emit ("factor(" ++ f ++ ");")

expectedPortion :: P Prop -> Expr Float
expectedPortion = UnOp (unFunc "expectedPortion") . Thunk

---------------------------
-- 
