{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RebindableSyntax #-}

module Montague where

import Space hiding (R)
import MCMC hiding (factor)
import CommonMCMC hiding (Prop)
import qualified CommonMCMC as Com
import Control.Applicative
import Prelude hiding (Num(..),(/),fromRational,(&&),(||),not,recip)
import Boolean
-- import qualified Data.Map.Strict as M
import Logits (toLogit)
import PreciseProb
import Algebra.Classes
import qualified BoxMeasure as Box

data ModelKind = BoxModel | GaussianPlanes

modelKind :: ModelKind
modelKind = BoxModel

data Prop = (Expr R) :=: (Expr R)
          | (Expr R) :/=: (Expr R)
          | forall a. Ord a => (Expr a) :>: (Expr a)
          -- | If (Expr Bool) Prop Prop
          | Or Prop Prop
          | And Prop Prop
          | Con (Expr Bool)
          -- deriving Show

positive :: Expr R -> Prop
positive x = x :>: 0

instance Boolean Prop where
  (∧) = And
  (∨) = Or
  not = not'

not' :: Prop -> Prop
not' (Con x) = Con (not x)
not' (x :=: y) = (x :/=: y)
not' (x :/=: y) = (x :=: y)
not' (x :>: y) = (y :>: x)
not' (x `And` y) = not' x `Or` not' y
not' (x `Or` y) = not' x `And` not' y


eval :: Prop -> Expr Truth
eval (Con x) = fromBool <$> x
eval (x :>: y) = fromBool <$> liftA2 (>) x y
eval (x :=: y) = liftA2 approxEq x y -- bad if categorical truth
eval (Or x y) = eval x ∨ eval y
eval (And x y) = eval x ∧ eval y
-- eval (If c x y) = cond <$> c <*> (eval x) <*> (eval y)
eval _x = error ("no eval for some expr")

observe :: S -> P ()
observe (S p) = observeP p

observeP :: Prop -> P ()
observeP (And x y) = observeP x >> observeP y
observeP (x :=: y) = Com.observeEqual x y
observeP p = MCMC.observe (eval p)

data S where
  S :: Prop -> S
  YouS :: Quant -> Pred -> S

fromS :: S -> Prop
fromS (S x) = x

data Scoping = Narrow | Wide

type Plane = (Expr R,Vec)

data Pred = BoxPred (Probabilistic Volume)
          | EvalledPred ShallowPred
          | PlanePred (Plane)
          | Universe Bool

type Ind = Vec
type CN = Pred
type VP = Pred
type Card = Int
type RS = Pred
type RCl = VP
type RP = ()

type ShallowPred = Ind -> Prop

genImply :: Expr Prob -> Prop -> Prop -> Prop
genImply prob premiss conclusion = expectedPortion p :>: prob
  where p = do observeP premiss
               return (eval (conclusion))

genQProb :: Expr Prob -> Pred -> VP -> Prop
genQProb prob (BoxPred cn) (BoxPred vp) = (areaRatio <$> cn <*> vp) :>: prob
genQProb prob cn vp = expectedPortion p :>: prob
  where p = do x <- newInd
               observeP (evalPred cn x)
               return (eval (evalPred vp x))
areaRatio :: Volume -> Volume -> Prob
areaRatio cn vp = toProb (volume' (cn /\ vp) / volume' cn)

evalPred :: Pred -> ShallowPred
evalPred (EvalledPred p) = p
evalPred (BoxPred box) = \x -> Con (liftA2 (∈) (sequenceA x) box)
evalPred (PlanePred (bias,a)) = \x -> dotProd x a :>: bias
evalPred (Universe pol) = \_ -> Con (fromBool pol)


-- | Predicate inclusion
universalOptimized :: Pred -> Pred -> Prop
universalOptimized _ (Universe True) = Con (fromBool True)
universalOptimized (Universe False) _ = Con (fromBool True)
universalOptimized (BoxPred b1) (BoxPred b2) = Con (liftA2 (⊆) b1 b2)
universalOptimized (PlanePred (thx,x)) (PlanePred (thy,y)) = ((cosineDistance x y) :>: 0.99) ∧ (thx :>: thy)
universalOptimized x y = genQProb (toProb <$> 0.99) x y

isAbove :: Plane -> ShallowPred
isAbove (bias,a) x = dotProd a x  :>: bias


newInd :: P Ind
newInd = case modelKind of
  BoxModel -> newVector (sampleUniform 0 1)
  GaussianPlanes -> newVector (sampleGaussian 0 1)

newIndSuch :: CN -> P Ind
newIndSuch cn = do
  x <- newInd
  Montague.observe (S $ evalPred cn x)
  return x



negGenQProb :: Expr Prob -> Pred -> VP -> Prop
negGenQProb prob cn vp = genQProb prob cn (non vp)

newNormedVector :: P Vec
newNormedVector = do
  xs <- newVector (sampleGaussian 0 1)
  return ((/ norm xs) <$> xs)

newMeasure :: P Measure
newMeasure = case modelKind of
  BoxModel -> BoxMeasure <$> Box.newMeasure
  GaussianPlanes -> do
      bias <- sampleGaussian 0 1
      v <- newNormedVector
      return $ PlaneMeasure (bias,v)

newPred :: P CN
newPred = do
  m0 <- newMeasure
  case m0 of
    BoxMeasure m -> return (BoxPred (boxToVolume <$> (Box.measureBounds m)))
    PlaneMeasure p -> return $ PlanePred p

data Operator = Equal | More | Less

data NP where
  Percents :: Card -> CN -> NP
  QNP :: Quant -> CN -> NP
  PN :: Ind -> NP
  You :: NP

genericYou :: NP
genericYou = You


composePol :: Bool -> VP -> VP
composePol True = id
composePol False = non


type Quant = (Float,Pred -> VP -> Prop, Scoping, Float)
type AVP = (Quant,VP)
type Pol = Bool
type Di = Int
type Digits = [Int]

type ModalAdv = Quant


modify :: ModalAdv -> VP -> AVP
modify = (,)

bare ::             VP -> AVP
bare = ((-2,universalOptimized,Wide,0.6),)

-- probablyInt :: Expr R -> Prop -> Prop
-- probablyInt v x = Con (unsafeSample (Com.bernouilli v)) --> x

-- probablyDef ::  Expr R -> Prop -> Prop
-- probablyDef v x = If (unsafeSample (Com.bernouilli v)) x (not' x)

simpleModalAdv :: (Pred -> VP -> Prop) -> ModalAdv
simpleModalAdv q = (1,q,Narrow,0.6)

definitely :: ModalAdv
definitely = simpleModalAdv universalOptimized

generally :: ModalAdv
generally = simpleModalAdv (genQProb $ toProb <$> 0.8)

always :: ModalAdv
always = simpleModalAdv universalOptimized

rarely :: ModalAdv
rarely = simpleModalAdv (negGenQProb $ toProb <$> 0.90)

usually :: ModalAdv
usually = simpleModalAdv (genQProb $ toProb <$> 0.8)

probably :: ModalAdv
probably = simpleModalAdv (genQProb $ toProb <$> 0.75)

often :: ModalAdv
often = simpleModalAdv (genQProb $ toProb <$> 0.7)

frequently :: ModalAdv
frequently = simpleModalAdv (genQProb $ toProb <$> 0.8)

also :: ModalAdv
also = (-2,universalOptimized,Wide,0.6)


regularly :: ModalAdv
regularly = simpleModalAdv (genQProb $ toProb <$> 0.7)

-- regularly :: ModalAdv
-- regularly = simpleModalAdv (probablyInt 0.7)

-- never :: ModalAdv
-- never vp  = non vp

-- occasionally :: ModalAdv
-- occasionally vp = EvalledPred $ \pol x ->
--     probablyInt 0.2 (evalPred vp pol x)
--   ∧ probablyInt 0.2 (evalPred vp (Prelude.not pol) x)
-- -- With a factor closer to 0.5, this would be more accurate. However it is sloooow.


isA :: CN -> VP            -- Example: to be a violinist
isA = id

data Cl where
  S1  :: NP -> AVP -> Cl                -- Example: John reads music

s1 :: NP -> AVP -> Cl
s1 = S1

-- If  : S -> S -> S;            -- Example: If John generally reads music, then Mary is a violinist
-- But : S -> S -> S;



interpQuantifier :: Bool -> NP -> VP -> Prop
interpQuantifier pol q0 vp = case q0 of
  Percents n cn -> genQProb (toProb <$> (fromIntegral n / 100)) cn (composePol pol vp)
  PN x  -> topPol pol (evalPred vp x)
  QNP (_,q,Wide,_) cn    -> topPol pol (q cn vp)
  QNP (_,q,Narrow,_) cn  -> q cn (composePol pol vp)

topPol :: Pol -> Prop -> Prop
topPol b = if b then id else not'

chooseQ :: NP -> Quant -> NP
chooseQ (QNP (a1@(prior1,_q1,_s1,_θ1)) cn) a2@(prior2,_q2,_s2,_θ2) = case compare prior1 prior2 of
  GT -> QNP a1 cn
  EQ -> error "can't decide what to do (1)"
  LT -> QNP a2 cn
chooseQ np (x,_q,_s,_) = if x <= 0 then np else error "can't decide what to do (2)"

cltoS :: Pol -> Cl -> S
cltoS pol (S1 You (q,vp)) = YouS q (composePol pol vp)
cltoS pol (S1 q (q',vp)) = S (interpQuantifier pol (chooseQ q q') vp)


neg :: Pol
neg = False

pos :: Pol
pos = True

tHAT :: RP
tHAT = ()

makeRCL :: RP -> VP -> RCl;
makeRCL _ = id

makepolarRS :: Pol -> RCl -> RS;
makepolarRS True = id
makepolarRS False = non

instance Lattice Pred where
  Universe True /\ p = p
  Universe False /\ _ = Universe False
  p /\ Universe True  = p
  _ /\ Universe False = Universe False
  (BoxPred b1) /\ (BoxPred b2) = BoxPred (liftA2 (/\) b1  b2)
  cn /\ rs = EvalledPred $ \ x -> (evalPred cn x ∧ evalPred rs x)

relativiseCN :: CN -> RS -> CN
relativiseCN = (/\)

-- All,Most,Few,Every,GenericPl, Many, the, a : Quant;
every :: Quant
every = (1,universalOptimized,Wide,0.99)

all :: Quant
all = (0.75,universalOptimized,Narrow,0.99)

genericPl :: Quant
genericPl = (0,genQProb $ toProb <$> 0.90,Narrow,0.9)
  -- according to Guy Emerson, this should be interpreted as NOT a
  -- boolean truth value, but as a probabilistic one, with "Generic
  -- x:CN. V(x)" interpreted as P(V(x) | CN). The various
  -- interpretations of the generic arise due to pragmatics ("Rational
  -- Speech Act"). (Perhaps we can get a similar behaviour if we let θ
  -- be priorized with a Beta(1/2, 1/2)).

many :: Quant
many = (1,genQProb $ toProb <$> 0.75,Narrow,0.4)

most :: Quant
most = (2,genQProb $ toProb <$> 0.9,Narrow,0.9)

few :: Quant
few = (1,negGenQProb $ toProb <$> 0.8,Wide,error "few: quantile: ???")

aFew :: Quant
aFew = (1,genQProb $ toProb <$> 0.2,Narrow,0.2)


percentOf :: Card -> CN -> NP
percentOf = Percents
-- Exactly, AtLeast, MoreThan : Card -> Quant;


non :: CN -> CN
non (EvalledPred vp) = EvalledPred $ \x -> not' (vp x)
non (BoxPred vol) = BoxPred (complement <$> vol)
non (PlanePred (b,a)) = PlanePred (negate b,negate <$> a)
non (Universe p) = Universe (not p)


-- Qual : A -> CN -> CN;                  -- Example: short musician

qNP :: Quant -> CN -> NP
qNP = QNP

-- if_ :: S -> S -> S
-- if_ (S x) (S y) = S (x --> y)
-- if_ (YouS (-2,_,_,_) vp1) (YouS q2 vp2) = S (interpQuantifier True (QNP q2 vp1) vp2)
-- -- TODO: figure out semantics for the remaining case. The issue is
-- -- that the adverb is in a *negative* position, and so it is not clear
-- -- how to deal with it.

-- infixr -->
-- (-->) :: S -> S -> S
-- (S x) --> (S y) = S (x Com.--> y)

but :: S -> S -> S
but = (∧)

if_ :: S -> S -> S
if_ (S x) (S y) = S (x --> y)
if_ (YouS (-2,_,_,_) vp1) (YouS q2 vp2) = S (interpQuantifier True (QNP q2 vp1) vp2)
-- TODO: figure out semantics for the remaining case. The issue is
-- that the adverb is in a *negative* position, and so it is not clear
-- how to deal with it.

and :: S -> S -> S
and = (∧)

parens :: S -> S
parens = id

instance Boolean S where
  not (S x) = S (not x)
  (S x) ∧ (S y) = S (x ∧ y)
  (S x) ∨ (S y) = S (x ∨ y)

less :: Operator
less = Less

more :: Operator
more = More

equal :: Operator
equal = Equal

moreVP :: A -> NP -> VP
moreVP a = comparVP More a

more' :: Measure -> Ind -> Ind -> Prop
more' m x y = applicability m x :>: applicability m y

applicability :: Measure -> Ind -> Expr R
applicability (BoxMeasure b) = Box.applicability b
applicability (PlaneMeasure (b,a)) = \x -> dotProd a x - b

compareOptimized :: Operator -> Measure -> NP -> VP
compareOptimized op m (Percents θ cn) = compareToScore op m (quantile (toLogit ((fromIntegral θ) / 100)) <$> distr)
  where distr = magicMcmc 100 (do y <- newIndSuch cn; return (applicability m y))
compareOptimized op m (PN x) = compareToScore op m (applicability m x)
compareOptimized op m (QNP (_,_,_,θ) cn) = compareToScore op m (quantile (toLogit (realToFrac θ)) <$> distr)
  where distr = magicMcmc 100 (do y <- newIndSuch cn; return (applicability m y))

-- | example: isFor tall elephant  --> is tall for an elephant
isFor :: Measure -> CN -> VP
isFor m baseClass = moreThanScore m (expectedValue <$> avgClass)
  where avgClass = magicMcmc 100 (do x <- newIndSuch baseClass; return (applicability m x))

compareToScore :: Operator -> Measure -> Probabilistic R -> Pred
compareToScore More = moreThanScore
compareToScore Less = lessThanScore

-- | Predicate: more than the given score $k$. 
moreThanScore :: Measure -> Probabilistic R -> Pred
moreThanScore (PlaneMeasure (b,a)) k = PlanePred (k+b, a)
moreThanScore (BoxMeasure (Box.Measure {..})) k = BoxPred $ boxToVolume <$> Box.measureBounds Box.Measure{mSlopes = scale <$> mSlopes,.. } -- k < 1
  where scale slope = (\k' s' -> (s'::R) / (1 - k')) <$> k <*> slope
-- moreThanScore 

lessThanScore :: Measure -> Probabilistic R -> Pred
lessThanScore m k = non (moreThanScore m k)

-- applicability m x > k
-- 1 - maximum (zipWith (*) (abs <$> (zipWith (-) x mCenter)) mSlopes) > k
-- maximum (zipWith (*) (abs <$> (zipWith (-) x mCenter)) mSlopes) < 1-k
-- (maximum (zipWith (*) (abs <$> (zipWith (-) x mCenter)) mSlopes)) / (1-k) < 1
-- (maximum (zipWith (*) (abs <$> (zipWith (-) x mCenter)) (mSlopes / (1-k)))) < 1
-- 1 - (maximum (zipWith (*) (abs <$> (zipWith (-) x mCenter)) (mSlopes / (1-k)))) > 0


is :: A -> Pred
is (BoxMeasure m) = BoxPred . fmap boxToVolume . Box.measureBounds $ m
is (PlaneMeasure p) = PlanePred p


equal' :: Measure -> Ind -> Ind -> Prop
equal' m x y = applicability m x :=: applicability m y

comparVP :: Operator -> A -> NP -> VP
comparVP Equal a q  = EvalledPred $ \x -> interpQuantifier True q  $ EvalledPred $ \y ->
  equal' a x y
  -- case (op) of
  -- -- (More) -> more' a x y
  -- -- (Less) -> more' a y x
comparVP op a x = compareOptimized op a x


qual :: A -> CN -> CN
qual a cn = is a /\ cn

testVP :: A -> VP
testVP = is

parseFailure :: S
parseFailure = S (Con $ pure False)

run' :: Int -> P S -> IO Prob
run' iterations p = do
  r <- mcmc iterations (eval <$> fromS <$> p)
  return (trueProb r)

run :: P S -> IO Prob
run = run' 10000

runHist :: P (Probabilistic R) -> IO ()
runHist p = (showHistogram 10 0 1 <$> mcmc 100000 p) >>= putStrLn

runHist' :: Int -> R -> R -> P (Probabilistic R) -> IO ()
runHist' bin lo hi p = (showHistogram bin lo hi <$> mcmc 100000 p) >>= putStrLn


universe :: Pred
universe = case modelKind of
  BoxModel -> BoxPred $ pure $ boxToVolume $ Box $ replicate numberOfDimensions $ Ivl 0 1
  GaussianPlanes -> Universe True

person :: CN
person = universe


mkCanPlayChoords :: P (Operator -> Card -> VP)
mkCanPlayChoords = do
  choordAbility <- newMeasure -- FIXME what to do with bounds?
  factor <- sampleGaussian 100 50
  bias <- sampleGaussian 0 1
  let ability x = factor * (applicability choordAbility x) + bias
  return $ \op n -> EvalledPred $ \x ->
    case (op) of
      (Equal) -> ability x :=: pure (fromIntegral n)
      (Less) ->  pure (fromIntegral n) :>: ability x 
      (More) ->  ability x :>: pure (fromIntegral n)

n0_Dig :: Di
n0_Dig = 0
n1_Dig :: Di
n1_Dig = 1
n2_Dig :: Di
n2_Dig = 2
n3_Dig :: Di
n3_Dig = 3
n4_Dig :: Di
n4_Dig = 4
n5_Dig :: Di
n5_Dig = 5
n6_Dig :: Di
n6_Dig = 6
n7_Dig :: Di
n7_Dig = 7
n8_Dig :: Di
n8_Dig = 8
n9_Dig :: Di
n9_Dig = 9

addDigit :: Di -> Digits -> Digits;
addDigit = (:)

oneDigit :: Di -> Digits;
oneDigit = (:[])

digitsToCard :: Digits -> Card;
digitsToCard = foldl (\x y -> 10 * x + y) 0

-- >>> digitsToCard [1,4,5]
-- 145

type Unit = (Expr R, Expr R, Expr R)

newUnit :: P Unit
newUnit = do
  alpha <- sampleUniform 1 10
  beta <- sampleUniform 0.1 100
  gamma <- sampleUniform (-10) 10
  return (alpha,beta,gamma)
-- These biases worked somewhat better for example 38

data Measure = BoxMeasure Box.Measure  | PlaneMeasure Plane
type A = Measure

measure :: Card -> Unit -> A -> VP
measure n u a  = EvalledPred $ \x -> computeMeasure u a x  :=:  (fromIntegral n)

computeMeasure :: Unit -> A -> Ind -> Probabilistic R
computeMeasure (alpha,beta,gamma) a  = \x -> beta * (alpha ** (applicability a x) + gamma)

like :: a
like = error "like: TODO"
-- regularly = error "regularly: TODO"
