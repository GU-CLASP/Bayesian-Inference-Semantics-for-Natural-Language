{-# LANGUAGE FlexibleContexts #-}
import Control.Monad
import Prelude hiding (Num(..),(/))
import Lib3
import MCMC(P)

test :: P S
test = do
  large <- newMeasure
  elephant <- newPred
  Lib3.observe (cltoS True (s1 (QNP most elephant) (bare (is large))))
  mouse <- newPred
  Lib3.observe (cltoS True (s1 (QNP few mouse) (bare (is large))))
  dumbo <- newIndSuch elephant
  mickey <- newIndSuch mouse
  Lib3.observe (cltoS False (s1 (PN dumbo) (bare (isFor large elephant))))
  return (cltoS True (s1 (PN dumbo) (bare (moreVP large (PN mickey)) )))

-- >>> run' 1000 test >>= print
-- 0.9960000000000002
