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
module CommonMCMC where

import MCMC
import Space (numberOfDimensions)
import System.Process
import System.Exit
import qualified Data.Vector.Unboxed as V
import Statistics.Sample.KernelDensity
import Control.Applicative
import Data.Map as M (lookup)
import Data.Maybe (maybe)
import Logits
import Algebra.Classes (zero)
import Boolean
import Prelude hiding (not)
import PreciseProb
--------------------------------------------
-- Basic code-gen infrastructure

type Expr = Probabilistic



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

type Prop = Expr Truth


-------------------
-- Vecs
type Vec = [Expr R]

cosineDistance :: Vec -> Vec -> Expr R
cosineDistance x y = dotProd x y / (norm x * norm y)

norm2 :: Vec -> Expr R
norm2 x = dotProd x x

norm :: Vec -> Expr R
norm = sqrt . norm2

normalize :: Vec -> Vec
normalize xs = (/ norm xs) <$> xs

newVector :: Monad m => m (Probabilistic a) -> m [Probabilistic a]
newVector distr = sequence (replicate numberOfDimensions distr)

dotProd :: Vec -> Vec -> Expr R
dotProd x y = sum (zipWith (*) x y)


--------------------
-- Random vars

sampleGaussian :: Expr R -> Expr R -> P (Expr R)
sampleGaussian mu sigma = sample (Gaussian mu sigma)

sampleUniform :: Expr R -> Expr R -> P (Expr R)
sampleUniform lo hi = sample (Uniform lo hi)


--------------------
-- Bayesian operators


observeEqual :: Expr R -> Expr R -> P ()
observeEqual x y = factor (ExpNeg <$> (square (x-y)))

expectedPortion :: P Prop -> Probabilistic Prob
expectedPortion p = trueProb <$> magicMcmc 100 p
