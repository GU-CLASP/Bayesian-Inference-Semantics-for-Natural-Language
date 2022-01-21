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
module Lib where

import Common
import Prelude hiding (and,or,(>))
import Control.Monad.RWS
import System.Process
import System.Exit
import qualified Data.Vector.Unboxed as V
import Statistics.Sample.KernelDensity

and :: Prop -> Prop -> Prop
and = BinOp (infixOp "&&")

(∧) :: Prop -> Prop -> Prop
(∧) = and

iff :: Prop -> Prop -> Prop
iff = BinOp (infixOp "==")

or :: Prop -> Prop -> Prop
or = BinOp (infixOp "||")

not' :: Prop -> Prop
not' = UnOp (\x -> "(!(" ++ x ++ "))")


(-->) :: Prop -> Prop -> Prop
p --> q = not' p `or` q

-----------------------------------
-- Types

type Ind = Vec
type Mat = [Vec]
-- type Vec = Expr Vector
type Pred = Ind -> Prop
type Measure = Ind -> Expr Float
type Adj = Vec
type AP = Measure
type CN = Ind -> Prop
type VP = Ind -> Prop
type NP = VP -> Prop
type Quant = CN -> NP

----------------------------------------------------
-- Compositional semantics


squared :: Num a => a -> a
squared x = x*x

-- | Sample new individual
newInd :: P Ind
newInd = newIndSuch []

-- | Sample new individual which satisfies some additional predicates
newIndSuch :: [Pred] -> P Ind
newIndSuch hs = do
  x <- newVector (sampleGaussian 0 1)
  forM_ hs $ \h -> hyp (h x)
  return x

newNormedVector :: P Vec
newNormedVector = do
  xs <- newVector (sampleGaussian 0 1)
  return ((/ norm xs) <$> xs)

newMatrix = newVector (newVector (sampleGaussian 0 1))
newMatrix :: P Mat

satisfyAll :: [Ind] -> [Pred] -> P ()
satisfyAll xs ps = forM_ xs $ \x -> forM ps $ \p -> hyp (p x)

vecMatProd :: Vec -> Mat -> Vec
vecMatProd v = map (dotProd v)

type Scalar = (Vec,Expr Float)

newScalarA :: P Scalar
newScalarA = do
  bias <- sampleGaussian 0 1
  v <- newNormedVector
  return (v,bias)


newClass :: P Mat
newClass = newMatrix

forClass :: Mat -> Adj -> AP
forClass cl adj x = dotProd (vecMatProd adj cl) x

-- -- Alternative for scalar adjectives. We take the measure to be greater than that of a "random" element of the class.
-- forClassScalar :: Mat -> Adj -> AP
-- forClassScalar cl a x = Let (newIndSuch [isClass cl]) (\y -> adjAP a x - adjAP a y)

isClass :: Mat -> Pred
isClass clas x = dotProd (head clas) x > 0


adjAP :: Adj -> AP
adjAP = dotProd

gaussian :: Expr Float -> Expr Float -> Expr Float
gaussian mean stdDev = BinOp (binFunc "gaussian") mean stdDev

vague :: Float -> Measure -> Measure
vague vagueness m x = m x + gaussian 0 (Expr (show vagueness))

newMeasure :: P Measure
newMeasure = do
  (v,bias) <- newScalarA
  return (\x -> bias + dotProd v x)

positive :: Expr Float -> Prop
positive x = greaterThan x 0

newPred :: P (Ind -> Prop)
newPred = do
  m <- newMeasure
  return (\x -> positive (m x))

-- TODO: there is a choice here.

-- this is an "intuitionistic" probably (it does not exclude the strong implication)
probablyInt :: Expr Float -> Prop -> Prop
probablyInt v x = sample (bernouilli v) --> x

-- this is a "definite" probably (it excludes the strong implication)
probablyDef ::  Expr Float -> Prop -> Prop
probablyDef v x = If (sample (bernouilli v)) x (not' x)

--  "a --> b"
-- and "if a then b else (not b)"
-- are not the same!


genQProb :: Expr Float -> Quant
genQProb prob cn vp = expectedPortion p > prob
  where p = do x <- newInd
               observe (cn x)
               return (vp x)

many :: Quant
many = genQProb 0.6

most :: Quant
most = genQProb 0.7

few :: Quant
few cn vp = genQProb 0.8 cn (not' . vp)

some :: Quant
some = genQProb 0.1

every :: Quant
every = genQProb 0.99

is :: Measure -> Pred
is m x =  (m x) > 0

more :: Measure -> Ind -> Ind -> Prop
more m x y = (m x) > (m y)

-- equal :: Expr Float -> Expr Float -> Prop
-- equal x y = 0.1 > (abs (x - y))


equal :: Expr Float -> Expr Float -> Prop
equal x y = 0.1 > (abs (x - y))


disjoint :: Pred -> Pred -> Pred
disjoint p q x = not' (p x) `or` not' (q x)


subsective :: Adj -> Mat -> Pred
subsective a cl x = isClass cl x `and` is (forClass cl a) x

-- An alternative semantics for subsective scalars.

anything :: Pred
anything _ = Expr "true"

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
  

