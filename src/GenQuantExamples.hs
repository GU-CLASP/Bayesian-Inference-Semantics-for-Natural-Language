
import Lib3
import Common (P,Expr)
import Control.Monad
import Prelude hiding (or,and)
import MCMC hiding (observe,P)
import qualified MCMC
import Space (volume')

heightObservation1 = do
  mary' <- newInd
  let mary = PN mary'
  tall <- newMeasure
  centimeter <- newUnit
  observe $ cltoS pos (s1 mary (bare (measure (digitsToCard (addDigit n1_Dig (addDigit n6_Dig (oneDigit n0_Dig)))) centimeter tall)))
  observe $ cltoS pos (s1 mary (bare (testVP tall))) -- try deactivating this
  -- return $ applicability tall mary'
  return $ computeMeasure centimeter tall mary'
  
tst = runHist' 10 0 100 heightObservation1

-- >>> tst
-- (150.0,0.41411282400329225)
-- (160.0,0.585887175996703)
-- (170.0,1.3767218722621314e-48)


ex0 = run $ do
  a <- newPred
  x <- newInd
  return (cltoS True (S1 (PN x) (bare a)))

-- >>> ex0
-- fromList [(False,0.8629),(True,0.1371)]

{-

ex0c = do
  a <- newPred
  x <- newInd
  observe (cltoS True (S1 (qNP aFew person) a))
  return (cltoS True (S1 (PN x) a))

-- >>> run ex0c
-- fromList [(False,0.6723),(True,0.3277)]

ex0da = do
  a <- newPred
  return (cltoS True (S1 (qNP most person) a))

-- >>> run ex0da
-- fromList [(False,1.0)]

ex0da' = do
  a@(SimplePred box) <- newPred
  observe (cltoS True (S1 (qNP most person) a))
  return (volume' <$> box) 

-}


-- >>> runHist ex0da'
-- (0.9,0.8126000000000002)
-- (1.0,0.1874)

ex12 = do
  a@(SimplePred abox) <- newPred
  b@(SimplePred bbox) <- newPred
  c@(SimplePred cbox) <- newPred
  x <- newInd
  observe (cltoS True (S1 (PN x) (bare a)))
  observe (cltoS True (S1 (qNP every a) (bare b)))
  observe (cltoS True (S1 (qNP few b) (bare c)))
  return (cltoS True (S1 (PN x) (bare c)))
  -- return (volume' <$> cbox)


problem1 = do
  violinist <- newPred
  musician <- newPred
  readMusic <- newPred
  john <- PN <$> newInd
  observe $ cltoS pos (s1 (qNP every violinist) (bare (isA musician)))
  observe $ cltoS pos (s1 (qNP genericPl musician) (modify few readMusic))
  -- observe $ (cltoS pos (s1 john (bare (isA violinist))))
  -- return $ (cltoS pos (s1 john (bare readMusic)))
  
  return $ if_ (cltoS pos (s1 john (bare (isA violinist)))) (cltoS pos (s1 john (bare readMusic)))

-- >>> run problem1

{-
ex0d = do
  a <- newPred
  observe (cltoS True (S1 (qNP most person) a))
  x <- newInd
  return (cltoS True (S1 (PN x) a))

-- >>> run ex0d
-- fromList [(False,4.76e-2),(True,0.9524)]


ex0b = do
  a <- newPred
  b <- newPred
  observe (cltoS True (S1 (qNP aFew a) b))
  x <- newInd
  observe (cltoS True (S1 (PN x) a))
  return  (cltoS True (S1 (PN x) b))

-- >>> run ex0b
-- fromList [(False,0.5407),(True,0.4593)]


ex1 = do
  car <- newPred
  red <- newPred

  observe (cltoS True (S1 (qNP most car) red))
  return (cltoS True (S1 (qNP aFew car) red))



-- >>> run ex1
-- fromList [(True,1.0)]

ex2 = do
  car <- newPred
  red <- newPred

  observe (cltoS True (S1 (qNP every car) red))
  return (cltoS True (S1 (qNP most car) red))


-- >>> run ex2
-- fromList [(True,1.0)]


ex3 = do
  car <- newPred
  red <- newPred

  observe (cltoS True (S1 (qNP aFew car) red))
  return (cltoS True (S1 (qNP every car) red))

-- >>> run ex3
-- fromList [(False,0.9131),(True,8.69e-2)]

ex3b = do
  car <- newPred
  red <- newPred

  observe (cltoS True (S1 (qNP aFew car) red))
  return (cltoS True (S1 (qNP most car) red))

-- >>> run ex3b
-- fromList [(False,0.8782),(True,0.1218)]

ex4 = do
  a <- newPred
  b <- newPred
  c <- newPred
  observe (cltoS True (S1 (qNP every a) b))
  observe (cltoS True (S1 (qNP every b) c))
  return  (cltoS True (S1 (qNP every a) c))

-- >>> run ex4
-- fromList [(True,1.0)]




ex4a = do
  animal <- newPred
  bird <- newPred
  fly <- newPred

  observe (cltoS True (S1 (qNP most bird) fly))
  observe  (cltoS True (S1 (qNP few animal) bird))

  x <- newInd
  observe (cltoS True (S1 (PN x) animal))
  return (cltoS True (S1 (PN x) fly))

-- >>> run ex4a
-- fromList [(False,0.7259),(True,0.2741)]

{-

ex4d :: P (Expr Bool)
ex4d = do
  animal <- newPred
  bird <- newPred
  fly <- newPred

  observe (most animal (\x -> not' (fly x)))
  observe (most bird fly)
  observe (most animal (not' . bird))
  observe (every bird animal)

  x <- newIndSuch [bird]
  return (fly x)

-- Marginal:
--     true : 0.9
--     false : 0.1


ex4e :: P (Expr Bool)
ex4e = do
  animal <- newPred
  bird <- newPred
  fly <- newPred

  observe (most animal (\x -> not' (fly x)))
  observe (most bird fly)
  observe (most animal (not' . bird))
  observe (every bird animal)

  x <- newIndSuch [animal]
  return (fly x)


-- Marginal:
--     false : 0.807
--     true : 0.193

ex4f :: P (Expr Bool)
ex4f = do
  animal <- newPred
  bird <- newPred
  fly <- newPred

  observe (most animal (\x -> not' (fly x)))
  observe (most bird fly)
  observe (every bird animal)

  x <- newIndSuch [animal]
  return (bird x)


-- Marginal:
-- false : 0.743
-- true : 0.257

ex4g :: P (Expr Bool)
ex4g = do
  animal <- newPred
  bird <- newPred
  fly <- newPred

  observe (most animal (not' . fly))
  observe (most bird fly)
  observe (every bird animal)
  return (most animal (not' . bird))


-}
-}
