{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RebindableSyntax #-}
module BoxMeasure where

import Space hiding (R)
import MCMC hiding (factor)
import CommonMCMC hiding (Prop)
import Control.Applicative
import Prelude hiding (Num(..),(/),fromRational,(&&),(||),not,recip)
import Prelude (abs)
-- import qualified Data.Map.Strict as M
import Algebra.Classes



{- |

applicability formula:
applicability(x) = 1 - ∣(x-center) ⊙ slopes∣
 with a 1-norm

maximal at center.
-}

-- applicability :: Measure -> Ind -> Expr R
applicability :: Measure -> [Expr R] -> Expr R
applicability Measure{..} x = 1 - maximum (zipWith (*) (abs <$> (zipWith (-) x mCenter)) mSlopes)



{- | Box where predicate applies:
∣(x-center) ⊙ slopes∣ = 1
if x[i]-center[i] > 0,  x-center  = 1/slopes[i]
But never outside the unit box 
-}
measureBounds :: Measure -> Probabilistic Box
measureBounds Measure {..} = (/\ unitBox) <$>
  (Box <$> sequenceA [Ivl <$> (c-delta) <*> (c+delta) | (c,s) <- zip mCenter mSlopes, let delta = 1/s])
  -- [Ivl (c-delta) (c+delta) | (c,s) <- zip mCenter mSlopes, let delta = 1/s]

data Measure =
  Measure {mCenter :: Vec
          ,mSlopes :: Vec -- all slopes > 0
          }

newMeasure :: P Measure
newMeasure = do
  center <- newVector (sample (Uniform 0 1))
  widths <- newVector (sample (Beta 2 8))
  let slopes = (recip . (0.01 +)) <$> widths
  return (Measure center slopes)





