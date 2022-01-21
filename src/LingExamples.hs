{-# LANGUAGE FlexibleContexts #-}
import Control.Monad
import MCMC
import Algebra.Classes
import Prelude hiding (Num(..),(/),sum)

isPositive :: Additive x => Ord x => Probabilistic x -> Probabilistic Bool
isPositive = ((> zero) <$>) 

numberOfDimensions :: Int
numberOfDimensions = 2

newVector :: Monad m => m a -> m [a]
newVector distr = sequence (replicate numberOfDimensions distr)

norm2 x = dotProd x x

norm = sqrt . norm2

normalize' xs = ((/ norm xs) <$> xs)

dotProd x y = sum (zipWith (*) x y)

newNormedVector :: P Vec
newNormedVector = do
  xs <- newVector (sample (Gaussian 0 1))
  return (normalize' xs)




type Vec = [Probabilistic R]
type Ind = Vec
type Pred = Vec -> Probabilistic Bool
type Grade = Vec -> Probabilistic R

is :: Grade -> Vec -> Probabilistic Bool
is g x = isPositive (g x)

-- | Subsected graded adj.
is' :: Grade -> Pred -> Vec -> Probabilistic Bool
is' g cn x = isPositive (g x - (expectedValue <$> avg))
  where distr = magicMcmc 100 $ do
          y <- individual
          observe (cn y)
          return (g y)

more :: Grade -> Vec -> Vec -> Probabilistic Bool
more g x y = isPositive (g x - g y)

predicate :: P Pred
predicate = do
  g <- grade
  return (is g)

grade :: P Grade
grade = do
  v <- newNormedVector
  b <- sample (Gaussian 0 1)
  return (\x -> (b + dotProd x v))

op :: Grade -> Grade
op g = negate <$> g

individual :: P Vec
individual = do
  newVector (sample (Gaussian 0 1))








































atLeast :: Probabilistic Double -> Pred -> Pred -> Probabilistic Bool
atLeast theta cn vp = (>) <$> (expectedTruthValue 100 test) <*> theta
  where test = do
          x <- individual
          observe (cn x)
          return (vp x)

most :: Pred -> Pred -> Probabilistic Bool
most = atLeast 0.8

exampleSocrates :: P (Probabilistic Bool)
exampleSocrates = do
  man <- predicate
  mortal <- predicate
  observe (most man mortal)
  socrates <- individual
  observe (man socrates)
  return (mortal socrates)

-- >>> mcmc 1000 exampleSocrates >>= print
-- fromList [(False,4.99999999999999e-2),(True,0.9500000000000004)]




















exampleTall :: P (Probabilistic Bool)
exampleTall = do
  tall <- grade
  john <- individual
  mary <- individual
  observe (more tall john mary)
  return (is tall john)
-- >>> mcmc 1000 exampleTall >>= print
-- fromList [(False,0.3109999999999997),(True,0.6890000000000003)]


















