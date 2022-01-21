import Lib

-- This new interpretation of 'every' measures the angle between the vectors and compares the biases.
everyCos :: Scalar -> Scalar -> Prop
everyCos x y = (Lib.and ((cosineDistance (fst x) (fst y)) Lib.> 0.99) (snd y Lib.> snd x))

-- One premiss.
-- All men are mortal. ->
-- All men are mortal.

-- Test a: using old interpretation of 'every' throughout for comparison.
cosineTest1a :: P (Expr Bool)
cosineTest1a = do 

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  
  observe (every man mortal)
  return (every man mortal)

-- >>> run cosineTest1a
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     true : 0.74
--     false : 0.26


-- Test b: using new interpretation of 'every' throughout.

cosineTest1b :: P (Expr Bool)
cosineTest1b = do 

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  
  observe (everyCos manScalar mortalScalar)
  return (everyCos manScalar mortalScalar)

-- >>> run cosineTest1b
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     true : 1

-- Test c: mixed - new interpretation in premisses, old in conclusion.

cosineTest1c :: P (Expr Bool)
cosineTest1c = do 

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  
  observe (everyCos manScalar mortalScalar)
  return (every man mortal)

-- >>> run cosineTest1c
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     true : 0.983
--     false : 0.017

-- Test d: mixed - old in premisses, new in conclusion.

cosineTest1d :: P (Expr Bool)
cosineTest1d = do 

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  
  observe (every man mortal)
  return (everyCos manScalar mortalScalar)

-- >>> run cosineTest1d
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     false : 0.847
--     true : 0.153


-- Two premisses.

-- All men are mortal.
-- All greeks are men. ->
-- All greeks are mortal.


cosineTest2a :: P (Expr Bool)
cosineTest2a = do 

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  greekScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let greekMeasure = \x -> snd greekScalar + dotProd (fst greekScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  let greek = \x -> positive (greekMeasure x)
  
  observe (every man mortal)
  observe (every greek man)
  return (every greek mortal)
  
-- >>> run cosineTest2a
-- Creating model...
-- Running webppl...
-- Success!
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Marginal:
--     true : 0.812
--     false : 0.188



cosineTest2b :: P (Expr Bool)
cosineTest2b = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  greekScalar <- newScalarA
  
  observe(everyCos manScalar mortalScalar)

  observe(everyCos greekScalar manScalar)

  return (everyCos greekScalar mortalScalar)

-- >>> run cosineTest2b
-- Creating model...
-- Running webppl...
-- Success!
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Marginal:
--     true : 0.842
--     false : 0.158


cosineTest2c :: P (Expr Bool)
cosineTest2c = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  greekScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let greekMeasure = \x -> snd greekScalar + dotProd (fst greekScalar) x
  
-- as predicates (corresponding to "newPred")
  let mortal = \x -> positive (mortalMeasure x)
  let greek = \x -> positive (greekMeasure x)


  observe(everyCos manScalar mortalScalar)

  observe(everyCos greekScalar manScalar)

  return (every greek mortal)

-- >>> run cosineTest2c
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     true : 1


cosineTest2d :: P (Expr Bool)
cosineTest2d = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  greekScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let greekMeasure = \x -> snd greekScalar + dotProd (fst greekScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  let greek = \x -> positive (greekMeasure x)

  observe(every man mortal)

  observe(every greek man)

  return (everyCos greekScalar mortalScalar)

-- >>> run cosineTest2d
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     false : 0.931
--     true : 0.069




-- Three premisses.
-- All mammals are mortal.
-- All men are mammals.
-- All greeks are men.
-- All greeks are mortal.

cosineTest3a :: P (Expr Bool)
cosineTest3a = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  greekScalar <- newScalarA
  mammalScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let greekMeasure = \x -> snd greekScalar + dotProd (fst greekScalar) x
  let mammalMeasure = \x -> snd mammalScalar + dotProd (fst mammalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  let greek = \x -> positive (greekMeasure x)
  let mammal = \x -> positive (mammalMeasure x)

  observe(every mammal mortal)
  observe(every man mammal)
  observe(every greek man)
  return(every greek mortal)

-- >>> run cosineTest3a
-- Creating model...
-- Running webppl...
-- Success!
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Marginal:
--     true : 0.705
--     false : 0.295

cosineTest3b :: P (Expr Bool)
cosineTest3b = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  greekScalar <- newScalarA
  mammalScalar <- newScalarA
  
  observe(everyCos mammalScalar mortalScalar)
  observe(everyCos manScalar mammalScalar)
  observe(everyCos greekScalar manScalar)
  return(everyCos greekScalar mortalScalar)

-- >>> run cosineTest3b
-- Creating model...
-- Running webppl...
-- Success!
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Initialization warning [2/4]: Trace not initialized after 10000 attempts.
-- Initialization warning [3/4]: Trace not initialized after 100000 attempts.
-- Marginal:
--     true : 0.619
--     false : 0.381

cosineTest3c :: P (Expr Bool)
cosineTest3c = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  greekScalar <- newScalarA
  mammalScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let greekMeasure = \x -> snd greekScalar + dotProd (fst greekScalar) x
  
-- as predicates (corresponding to "newPred")
  let mortal = \x -> positive (mortalMeasure x)
  let greek = \x -> positive (greekMeasure x)

  observe(everyCos mammalScalar mortalScalar)
  observe(everyCos manScalar mammalScalar)
  observe(everyCos greekScalar manScalar)
  return(every greek mortal)

-- >>> run cosineTest3c
-- Creating model...
-- Running webppl...
-- Success!
-- Initialization warning [1/4]: Trace not initialized after 1000 attempts.
-- Initialization warning [2/4]: Trace not initialized after 10000 attempts.
-- Marginal:
--     true : 1

cosineTest3d :: P (Expr Bool)
cosineTest3d = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  greekScalar <- newScalarA
  mammalScalar <- newScalarA
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let greekMeasure = \x -> snd greekScalar + dotProd (fst greekScalar) x
  let mammalMeasure = \x -> snd mammalScalar + dotProd (fst mammalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  let greek = \x -> positive (greekMeasure x)
  let mammal = \x -> positive (mammalMeasure x)

  observe(every mammal mortal)
  observe(every man mammal)
  observe(every greek man)
  return(everyCos greekScalar mortalScalar)

-- >>> run cosineTest3d
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     false : 0.941
--     true : 0.059


cosineTest4a :: P (Expr Bool)
cosineTest4a = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  mammalScalar <- newScalarA

  john <- newInd
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let mammalMeasure = \x -> snd mammalScalar + dotProd (fst mammalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  let mammal = \x -> positive (mammalMeasure x)

  observe(mortal john)
  observe(every man mammal)
  return(Lib.and (mortal john) (every man mammal))

-- >>> run cosineTest4a
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     true : 0.834
--     false : 0.166

cosineTest4b :: P (Expr Bool)
cosineTest4b = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  mammalScalar <- newScalarA

  john <- newInd
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let mammalMeasure = \x -> snd mammalScalar + dotProd (fst mammalScalar) x
  
-- as predicates (corresponding to "newPred")
  let mortal = \x -> positive (mortalMeasure x)

  observe(mortal john)
  observe(everyCos manScalar mammalScalar)
  return(Lib.and (mortal john) (everyCos manScalar mammalScalar))

-- >>> run cosineTest4b
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     true : 1

cosineTest4c :: P (Expr Bool)
cosineTest4c = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  mammalScalar <- newScalarA

  john <- newInd
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let mammalMeasure = \x -> snd mammalScalar + dotProd (fst mammalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  let mammal = \x -> positive (mammalMeasure x)

  observe(mortal john)
  observe(everyCos manScalar mammalScalar)
  return(Lib.and (mortal john) (every man mammal))

-- >>> run cosineTest4c
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     true : 0.996
--     false : 0.004


cosineTest5c :: P (Expr Bool)
cosineTest5c = do

-- "bare" scalars
  manScalar <- newScalarA     --(Vector, Bias)
  mortalScalar <- newScalarA
  mammalScalar <- newScalarA

  john <- newInd
  
-- as measures (corresponding to "newMeasure")
  let manMeasure = \x -> snd manScalar + dotProd (fst manScalar) x
  let mortalMeasure = \x -> snd mortalScalar + dotProd (fst mortalScalar) x
  let mammalMeasure = \x -> snd mammalScalar + dotProd (fst mammalScalar) x
  
-- as predicates (corresponding to "newPred")
  let man = \x -> positive (manMeasure x)
  let mortal = \x -> positive (mortalMeasure x)
  let mammal = \x -> positive (mammalMeasure x)

  observe(Lib.and (mortal john) (everyCos manScalar mammalScalar))
--  return(mortal john)
  return (every man mammal)

-- >>> run cosineTest5c
-- Creating model...
-- Running webppl...
-- Success!
-- Marginal:
--     true : 0.998
--     false : 0.002

main = run cosineTest1a
