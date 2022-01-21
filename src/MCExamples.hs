{-# LANGUAGE LambdaCase #-}

module MCExamples where

import MCMC
import Boolean
import Prelude hiding (not)

exampleBalls :: P (Probabilistic Bool)
exampleBalls = do
  p <- sample (Uniform 0 1)
  -- p <- sample (Beta 0.5 0.5)
  let ball = sample (Bernoulli p)
      redBall = do
        b <- ball
        observe b
      blueBall = do
        b <- ball
        observe (not b)
  redBall
  redBall
  redBall
  blueBall
  ball5 <- ball
  return (ball5)
-- >>> print =<< mcmc 100000 exampleBalls
-- fromList [(False,0.32594999999997626),(True,0.6740500000000244)]

percent :: Probabilistic R
percent = 0.01

drugTest :: Probabilistic Bool -> P (Probabilistic Bool)
drugTest isUser = if_ isUser $ \case
  True -> sample (Bernoulli (99 * percent))
  False -> sample (Bernoulli (1 * percent))

exampleDrug :: P (Probabilistic Bool)
exampleDrug = do
  isUser <- sample (Bernoulli (0.5 * percent))
  testedPositive <- drugTest isUser
  observe testedPositive
  return isUser
-- >>> print =<< mcmc 100000 exampleDrug
-- fromList [(False,0.6362700000000127),(True,0.363729999999987)]









sloubi' :: P (Probabilistic R)
sloubi' = do
  alice <- player
  bob <- player
  charles <- player
  david <- player
  win' alice bob
  win' bob charles
  win' bob david
  return alice
-- >>> print =<< mcmc 100000 sloubi
-- fromList [(False,1.4069999999999411e-2),(True,0.9859300000000005)]


main :: IO ()
main = do
  putStrLn "running..."
  r <- mcmc 100000 sloubi'
  putStrLn $ showHistogram 10 0 2000 r

-- >>> main
-- running...
-- (200.0,6.000000000000006e-5)
-- (400.0,2.130000000000002e-3)
-- (600.0,1.423000000000002e-2)
-- (800.0,5.1729999999999936e-2)
-- (1000.0,0.11803999999999987)
-- (1200.0,0.18653000000000067)
-- (1400.0,0.23285000000000025)
-- (1600.0,0.17554000000000036)
-- (1800.0,0.12282999999999974)
-- (2000.0,5.921000000000007e-2)
-- (2200.0,2.3080000000000055e-2)
-- (2400.0,1.0430000000000019e-2)
-- (2600.0,2.569999999999998e-3)
-- (2800.0,7.700000000000007e-4)
