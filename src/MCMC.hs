{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- This module follows the WebPPL tutorial (without the bugs, hopefully)
-- This could be an alternative implementation: http://mlg.eng.cam.ac.uk/pub/pdf/SciGhaGor15.pdf
module MCMC (P,R,sample,Probabilistic,Distribution(..),
              mcmc,mcmc',magicMcmc,
              expectedValue,expectedTruthValue,quantile,
              if_,observe,subInference,factor,
              trueProb,showHistogram,Categorical,Truth,
              MC(..)) where

import qualified Statistics.Distribution as S
import Statistics.Distribution.Normal
import Statistics.Distribution.Beta
import Statistics.Distribution.Uniform
import Control.Applicative
import Control.Monad (ap)
-- import Control.Monad.ST
import Data.Type.Equality
import qualified Data.Map.Strict as M
import System.Random.MWC (GenIO,withSystemRandom,asGenST,uniformR,createSystemRandom)
import System.Random.MWC.Distributions (bernoulli)
import System.IO.Unsafe
import Boolean
import Algebra.Classes
import Prelude hiding (Num(..),(/),not,recip,sum)
import qualified Prelude
import Logits
import Data.List (find,sort)
import PreciseProb
import Control.Monad.Fail

type R = Double
type Truth = Prob

-- | Beta distribution with mean (μ) and sample size (ν)
betaμν :: Probabilistic R -> Probabilistic R -> Distribution R
betaμν μ ν = Beta (μ*ν) ((1-μ)*ν)

-- | Beta distribution with mode (ω) and concentration (κ).  (High concentration means not high variance)
betaωκ :: Probabilistic R -> Probabilistic R -> Distribution R
betaωκ ω κ = Beta (ω*(κ-2)+1) ((1-ω)*(κ-2)+1)

data Distribution a where
  Bernoulli :: !(Probabilistic R) -> Distribution Truth
  Uniform :: !(Probabilistic R) -> !(Probabilistic R) -> Distribution R
  Gaussian :: !(Probabilistic R) -> !(Probabilistic R) -> Distribution R
  Beta :: !(Probabilistic R) -> !(Probabilistic R) -> Distribution R

deriving instance (Show (Distribution a))

-- | Test that two distributions are equal. If they are, return a
-- proof that their underlying types are equal too.
eqDistributions :: Distribution a -> Distribution b -> Maybe (a :~: b)
eqDistributions (Bernoulli p) (Bernoulli q) | p == q = Just Refl
eqDistributions (Uniform l1 h1) (Uniform l2 h2) | l1 == l2, h1 == h2 = Just Refl
eqDistributions (Beta a1 b1) (Beta a2 b2) | a1 == a2, b1 == b2 = Just Refl
eqDistributions (Gaussian a1 b1) (Gaussian a2 b2) | a1 == a2, b1 == b2 = Just Refl
eqDistributions _ _ = Nothing


-- | This is an abstract type, so that we know it can be observed only
-- via the Choice/Infer combinator.  This means that we can trace the
-- dependencies on Probabilistic values explicitly; and thus we can
-- reuse bigger parts of traces.
newtype Probabilistic a = Prob {fromProb :: a}
  deriving (Functor,Additive,Multiplicative,Group,AbelianAdditive,Ring,Show,Eq,Ord,Prelude.Num,Division,Field,Fractional,Floating)
instance Ring a => Module (Probabilistic a) (Probabilistic a) where
  Prob a *^ Prob b = Prob (a * b)
instance Applicative Probabilistic where
  pure = Prob
  Prob f <*> Prob a = Prob (f a)

-- | The type of program processes.
data MC r where
  -- | A value was sampled.
  Sample :: (Show a, Read a) => !(Distribution a) -> (Probabilistic a -> MC r) -> MC r
  -- | Modulate the probability of the trace by a factor (given in log space).
  Factor :: !(Probabilistic Logit) -> MC r -> MC r
  -- | Observe a probabilistic (boolean) variable.
  Choice :: !(Probabilistic Truth) -> (Truth -> MC r) -> MC r
  -- could be generalised to any Typeable a, Eq a type.
  -- | Return a result (and quit)
  Result :: !(Probabilistic r) -> MC r
  -- | Make an inner inferece
  Infer  :: (Show a, Ord a) => P (Probabilistic a) -> (Categorical a -> MC r) -> MC r
  -- | Fail (sample rejected)
  Fail   :: MC r

-- | The type of probabilistic programs (as a continuation monad)
newtype P a = P {fromP :: forall r. (a -> MC r) -> MC r} deriving Functor

instance Applicative P where
  pure = return
  (<*>) = ap

instance Monad P where
  return x = P (\k -> k x)
  P p >>= f = P $ \k -> p $ \x -> fromP (f x) k

instance MonadFail P where
  fail _ = P $ \_ -> Fail

factor :: Probabilistic Logit -> P ()
factor p = P $ \k -> Factor p (k ())

sample :: (Show a, Read a) => Distribution a -> P (Probabilistic a)
sample d = P $ \k -> Sample d k

if_ :: Probabilistic Truth -> (Truth -> P a) -> P a
if_ c b = P $ \k -> Choice c $ \c' -> fromP (b c') k

observe :: Probabilistic Truth -> P ()
observe c = P $ \k -> Factor (indicator <$> c) (k ())

subInference :: (Show a,Ord a) => P (Probabilistic a) -> P (Probabilistic (Categorical a))
subInference p = P $ \k -> Infer p (k . pure)

instance Show r => Show (MC r) where
  show (Sample d _) = "S" ++ show d
  show (Factor (Prob f) k) = "F" ++show f ++ show k
  show (Choice (Prob c) k) = "C" ++ show c ++ show (k c)
  show (Result r) = "R" ++ show r
  show (Infer _ _) = "I"
  show Fail = "F"

-- | Trace entry.
data Entry r where
  Sampled :: Show d => Distribution d -> d -> Entry r
  -- | This is used to force resampling (for taking a random step).
  ForceSample :: Entry r
  Chose   :: !Truth -> Entry r
  Factored :: !Logit -> Entry r
  -- | this must be re-executed every time, because dependencies can be hidden in the sub-inferrence.
  Inferred :: Entry r
  Stop :: !(Maybe r) -> Entry r

deriving instance Show r => Show (Entry r)

-- | Traces. (A state in the Markov Chain)
type Trace r = [(Entry r -- trace entry
                ,MC r -- mc state coming BEFORE the above entry
                )]


forceFirstSample :: [Entry r] -> [Entry r]
forceFirstSample [] = []
forceFirstSample (Sampled _ _:es) = ForceSample:es
forceFirstSample (t:es) = t:forceFirstSample es

-- | Actually sample from a distribution
doSample :: GenIO -> Distribution a -> IO a
doSample gen = \case
  Bernoulli (Prob p) -> fromBool <$> bernoulli p gen
  Gaussian (Prob mu) (Prob sigma) -> S.genContinuous (normalDistr mu sigma) gen
  Uniform (Prob lo) (Prob hi) -> S.genContinuous (uniformDistr lo hi) gen
  Beta (Prob a) (Prob b) -> S.genContinuous (betaDistr a b) gen

-- | Evaluate one process step.
{-# INLINE evalStep #-}
evalStep :: GenIO -> MC r -> IO (Entry r,MC r)
evalStep gen mc = case mc of
  Infer p k -> do
    h <- mcmc' 100 gen p
    return (Inferred,k h)
  Sample d k -> do
    r <- doSample gen d
    return (Sampled d r, k (Prob r))
  Factor (Prob p) k -> return $ if p == zero
    then (Stop Nothing,Fail)
    else (Factored p, k)
  Choice (Prob c) k -> return (Chose c, k c)
  Result (Prob x) -> return (Stop (Just x),Fail)
  Fail -> return (Stop Nothing,Fail)

-- | Re-run a process by repeating what happened before
{-# INLINE revalStep #-}
revalStep :: MC r -> Entry r -> Maybe (Entry r,MC r)
revalStep (Sample d k) e@(Sampled d0 r0) = case eqDistributions d d0 of
  Just Refl -> Just (e,k (Prob r0)) -- reuse sample
  Nothing -> Nothing -- error, stop here
revalStep (Choice (Prob c) k) e@(Chose c0) | (c0 == c) = Just (e,k c)
revalStep (Factor (Prob f) k) _ = Just (Factored f, k) -- the factor MAY be different because we have forced one resampling.
-- For Inferred: we have no way of comparing the programs!
revalStep _ _ = Nothing

toMC :: P (Probabilistic r) -> MC r
toMC (P k) = k (\x -> Result x)

-- | Generate a trace. (Many tries)
firstTrace :: GenIO -> MC r -> Trace r -> IO (Trace r)
firstTrace gen mc t0 = do
  (e',mc') <- evalStep gen mc
  case e' of
    Stop r -> return ((Stop r,mc):t0)
    _  -> firstTrace gen mc' ((e',mc):t0)

-- | Generate a new trace (one step in the markov chain)
reTrace :: GenIO -> MC r -> [Entry r] -> Trace r -> IO (Trace r)
reTrace gen mc [] t0 = firstTrace gen mc t0
reTrace gen mc (ForceSample:es) t0 = do
  evalled <- evalStep gen mc
  case evalled of
    (e',mc') -> reTrace gen mc' es ((e',mc):t0)
reTrace gen mc (e:es) t0 = do
  case revalStep mc e of
    Nothing -> firstTrace gen mc t0
    Just (e',mc') -> reTrace gen mc' es ((e',mc):t0)

-- | Generate a candidate trace (force a random sample)
candidateTrace :: GenIO -> Trace r -> IO (MC r,Trace r, [Entry r])
candidateTrace gen t = do
  n <- uniformR (0,length t - 1) gen
  let (after,(e,mc):before) = splitAt n t
  return (mc,before,forceFirstSample (e:reverse (map fst after)))

entriesScore :: [Entry r] -> Logit
entriesScore t = foldl (*) one [p | Factored p <- t]

traceScore :: [(Entry r, b)] -> Logit
traceScore = entriesScore . map fst

mhAcceptProb :: Trace r -> Trace r -> Logit
mhAcceptProb trace oldTrace = min one (traceScore trace / traceScore oldTrace)

traceResult :: Trace r -> Maybe r
traceResult ((Stop x,_):_) = x
traceResult _ = error "panic: traceResult"

type History r = M.Map r Logit

-- | With the additional normalized property (sum of keys = 1)
type Categorical r = M.Map r Logit


findTraces :: Ord r => Show r => GenIO -> Int -> MC r -> IO (History r)
findTraces gen n mc = do
  x <- firstTrace gen mc []
  debug "Frst" mc
  case traceResult x of
    Nothing -> findTraces gen n mc
    Just r -> twoFindMoreTraces gen (n-1) (M.singleton r (traceScore x)) x

debug :: Show a => [Char] -> a -> IO ()
-- debug msg@"Acxp" x = putStrLn (msg ++ ": " ++ show x)
-- debug msg x = putStrLn (msg ++ ": " ++ show x)
debug _ _ = return ()

twoFindMoreTraces :: Ord r => Show r => GenIO -> Int -> History r -> Trace r -> IO (History r)
twoFindMoreTraces _ 0 history _ = return history
twoFindMoreTraces gen n !history tr = do
  debug "Found trace" (map fst tr)
  (mc,t0,es) <- candidateTrace gen tr
  debug "Kept" mc
  debug "Rest" es
  tr' <- reTrace gen mc es t0
  let p = mhAcceptProb tr' tr
  choice <- bernoulli (fromLogit p) gen
  debug "Acxp" (show (traceScore tr',traceScore tr,p,choice))
  case (traceResult tr',choice) of
    (Just r,True) -> twoFindMoreTraces gen (n-1) (M.insertWith (+) r (traceScore tr') history) tr'
    _ -> twoFindMoreTraces gen n history tr

magicMcmc :: (Show a,Ord a) => Int -> P (Probabilistic a) -> Probabilistic (Categorical a)
magicMcmc n p = Prob (unsafePerformIO (mcmc n p))

-- trueProb :: Categorical Truth -> Prob
-- trueProb r = logitToProb $ M.findWithDefault zero True r

trueProb :: Categorical Truth -> Prob
trueProb r = logitToProb $ sum [t | (x,t) <- M.assocs r, x > (toProb 0.5)]

expectedTruthValue :: Categorical Truth -> Prob
expectedTruthValue c = logitToProb $ sum $ [ w * indicator x | (x,w) <- M.assocs c]
-- attn! do no use expectedValue here to avoid numerical errors.

expectedValue :: Categorical R -> R
expectedValue c = sum [fromLogit w * x | (x,w) <- M.assocs c]

quantile :: forall a. Logit -> Categorical a -> a
quantile θ m = case find ((>= θ) . snd) as of
  Just (a,_) -> a
  Nothing -> error "quantile: not found"
  where as :: [(a,Logit)]
        as = scanl (\(_,x) (a,x') -> (a,x + x')) (error "quantile:panic",zero) (M.assocs m)

mcmc :: (Show a,Ord a) => Int -> P (Probabilistic a) -> IO (Categorical a)
mcmc n p = do
  gen <- createSystemRandom
  mcmc' n gen p

mcmc' :: (Show a,Ord a) => Int -> GenIO -> P (Probabilistic a) -> IO (Categorical a)
mcmc' n gen p = MCMC.normalize <$> findTraces gen n (toMC p)

showHistogram :: Int -> R -> R -> History R -> String
showHistogram n lo hi history = unlines [show (lo + fromIntegral i*delta, p) | (i,p) <- M.toList histogram]
  where getBin :: R -> Int
        getBin x = floor (fromIntegral n * (x-lo) / (hi-lo))
        delta = (hi-lo)  / fromIntegral n
        histogram = M.fromListWith (+) [(getBin x,p) | (x,p) <- M.toList history]

normalize :: (Foldable f, Division b, Additive b, Functor f) => f b -> f b
normalize hs = (/ sum hs) <$> hs





instance Boolean a => Boolean (Probabilistic a) where
  indicator (Prob x) = indicator x
  (∧) = liftA2 (∧)
  (∨) = liftA2 (∨)
  not = fmap (not)
  (<->) =  liftA2 (<->)
  fromBool = pure . fromBool

-- (⊗) :: (t3 -> t2) -> (t1 -> t) -> (t3, t1) -> (t2, t)
-- (f ⊗ g) (x,y) = (f x, g y)
-- squared x = x*x

-- exampleFactor :: P (Probabilistic R)
-- exampleFactor = do
--   x <- sample (Gaussian 0 1)
--   -- factor (squared (x-3))
--   return x

