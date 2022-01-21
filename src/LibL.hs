{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
module LibL where

import LogicT
import Control.Applicative
import Prelude hiding (Ord(..),Real)
import Prelude (compare)
import qualified Prelude

type Real = Expr Float
type V x = (x,x)
type Vec = (Float,Float)
type Ind = Expr Vec

vector :: Type t -> Type (t,t)
vector t = t × t

pair :: Type t -> Type (t,t)
pair t = t × t


(<*!>) :: Expr (V (a -> b)) -> Expr (V a) -> Expr (V b)
f <*!> a = Pair (proj1 f `app` (proj1 a)) (proj2 f `app` (proj2 a))

pureVec :: Expr a -> Expr (V a)
pureVec x = Pair x x

zipVecWith :: (Expr t -> Expr u -> Expr v) -> Expr (V t) -> Expr (V u) -> Expr (V v)
zipVecWith f v1 v2 = pureVec (Lam $ \x -> Lam $ \y -> f x y) <*!> v1 <*!> v2

zipVec :: Expr (V t) -> Expr (V u) -> Expr (V (t,u))
zipVec = zipVecWith Pair

(<$!>) :: (Expr t -> Expr u) -> Expr (V t) -> Expr (V u)
f <$!> xs = pureVec (Lam f) <*!> xs

vecMax :: Expr Vec -> Expr Float
vecMax v = max (proj1 v) (proj2 v)

individual :: Type Vec
individual = vector (uniform 0 1)

predicate :: Type (Vec -> Bool)
predicate = (Lam . is) `Image` measure

type Measure = Expr (Vec,Vec)
type Box = Expr (Vec,Vec)

applicability :: Measure -> Ind -> Real
applicability m x = 1 - vecMax (zipVecWith (*) (abs <$!> (zipVecWith (-) x (proj1 m))) (proj2 m))


-- measureBounds :: Measure -> Box
-- measureBounds m = (/\ unitBox) <$>
--   (Box <$> sequenceA [Ivl <$> (c-delta) <*> (c+delta) | (c,s) <- zipVec (proj1 m) (proj2 m), let delta = 1/s])
--   -- [Ivl (c-delta) (c+delta) | (c,s) <- zip mCenter mSlopes, let delta = 1/s]

-- data Measure =
--   Measure {mCenter :: Vec
--           ,mSlopes :: Vec -- all slopes > 0
--           }

measure :: Type (Vec,Vec)
measure = vector (uniform 0 1) × vector ((recip . (0.01 +)) `Image` beta 2 8)

data Scoping = Narrow | Wide

type Pred = Ind -> Prop
type CN = Pred
type VP = Pred
type A = Measure
type Card = Int
type RS = Pred
type RCl = VP
type RP = ()

data S where
  S :: Prop -> S
  YouS :: Quant -> Pred -> S
fromS :: S -> Prop
fromS (S x) = x

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


is :: Measure -> Ind -> Prop
is m x = applicability m x > 0

negGenQProb :: Expr Float -> Pred -> VP -> Prop
negGenQProb prob cn vp = genQProb prob cn (non vp)

genQProb :: Expr Float -> Pred -> Pred -> Expr Bool
genQProb p cn vp = p <= proportion (Sigma individual (IsTrue . cn)) (\x -> IsTrue (vp (proj1 x)))

universalOptimized :: Pred -> Pred -> Expr Bool
universalOptimized = genQProb 0.99

type Quant = (Float,Pred -> VP -> Prop, Scoping)
type AVP = (Quant,VP)
type Pol = Bool
type Di = Int
type Digits = [Int]

type ModalAdv = Quant

modify :: ModalAdv -> VP -> AVP
modify = (,)

bare ::             VP -> AVP
bare = ((-2,universalOptimized,Wide),)

-- probablyInt :: Expr R -> Prop -> Prop
-- probablyInt v x = Con (unsafeSample (Com.bernouilli v)) --> x

-- probablyDef ::  Expr R -> Prop -> Prop
-- probablyDef v x = If (unsafeSample (Com.bernouilli v)) x (not' x)

simpleModalAdv :: Num a => b -> (a, b, Scoping)
simpleModalAdv q = (1,q,Narrow)

definitely :: ModalAdv
definitely = simpleModalAdv universalOptimized

generally :: ModalAdv
generally = simpleModalAdv (genQProb 0.8)

always :: ModalAdv
always = simpleModalAdv universalOptimized

rarely :: ModalAdv
rarely = simpleModalAdv (negGenQProb 0.90)

usually :: ModalAdv
usually = simpleModalAdv (genQProb 0.8)

probably :: ModalAdv
probably = simpleModalAdv (genQProb 0.75)

often :: ModalAdv
often = simpleModalAdv (genQProb 0.7)

frequently :: ModalAdv
frequently = simpleModalAdv (genQProb 0.8)

also :: ModalAdv
also = (-2,universalOptimized,Wide)


regularly :: ModalAdv
regularly = simpleModalAdv (genQProb 0.7)

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
  Percents n cn -> genQProb (fromIntegral n / 100) cn (composePol pol vp)
  PN x  -> topPol pol (vp x)
  QNP (_,q,Wide) cn    -> topPol pol (q cn vp)
  QNP (_,q,Narrow) cn  -> q cn (composePol pol vp)

topPol :: Pol -> Prop -> Prop
topPol b = if b then id else not'

chooseQ :: NP -> (Float, Pred -> VP -> Prop, Scoping) -> NP
chooseQ (QNP (a1@(prior1,q1,s1)) cn) a2@(prior2,q2,s2) = case compare prior1 prior2 of
  GT -> QNP a1 cn
  EQ -> error "can't decide what to do (1)"
  LT -> QNP a2 cn
chooseQ np (prior2,q,s) = if prior2 Prelude.<= 0 then np else error "can't decide what to do (2)"

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

relativiseCN :: CN -> RS -> CN
relativiseCN = (/\)

-- All,Most,Few,Every,GenericPl, Many, the, a : Quant;
every :: Quant
every = (1,universalOptimized,Wide)

all :: Quant
all = (0.75,universalOptimized,Narrow)

genericPl :: Quant
genericPl = (0,genQProb 0.90,Narrow)

many :: Quant
many = (1,genQProb 0.75,Narrow)

most :: Quant
most = (1,genQProb 0.9,Narrow)

few :: Quant
few = (1,negGenQProb 0.8,Wide)

aFew :: Quant
aFew = (1,genQProb 0.2,Narrow)


percentOf :: Card -> CN -> NP
percentOf = Percents
-- Exactly, AtLeast, MoreThan : Card -> Quant;


non :: CN -> CN
non vp = not' . vp


-- Qual : A -> CN -> CN;                  -- Example: short musician

qNP :: Quant -> CN -> NP
qNP = QNP

if_ :: S -> S -> S
if_ (S x) (S y) = S (x --> y)
if_ (YouS (-2,_,_) vp1) (YouS q2 vp2) = S (interpQuantifier True (QNP q2 vp1) vp2)
-- TODO: figure out semantics for the remaining case

-- infixr -->
-- (-->) :: S -> S -> S
-- (S x) --> (S y) = S (x Com.--> y)

but :: S -> S -> S
but (S x) (S y) = S (x ∧ y)

and :: S -> S -> S
and (S x) (S y) = S (x ∧ y)

parens :: S -> S
parens = id

not :: S -> S
not (S x) = S (not' x)

less :: Operator
less = Less

more :: Operator
more = More

equal :: Operator
equal = Equal

moreVP :: A -> NP -> VP
moreVP a = comparVP More a

more' :: Measure -> Ind -> Ind -> Prop
more' m x y = applicability m x > applicability m y


comparVP :: Operator -> A -> NP -> VP
comparVP op a q  = \x -> interpQuantifier True q  $ \y -> case (op) of
  (More) -> more' a x y
  (Less) -> more' a y x
  (Equal) -> error "what is equal?"


qual :: A -> CN -> CN
qual a cn = is a /\ cn

(/\) :: (t -> Prop) -> (t -> Prop) -> t -> Prop
(p /\ q) x = p x ∧ q x

testVP :: A -> VP
testVP = is

parseFailure :: S
parseFailure = S (error "PARSE FAILURE")

universe :: Pred
universe _ = Truth

person :: CN
person = universe


-- mkCanPlayChoords :: P (Operator -> Card -> VP)
-- mkCanPlayChoords = do
--   choordAbility <- newMeasure -- FIXME what to do with bounds?
--   factor <- sampleGaussian 100 50
--   bias <- sampleGaussian 0 1
--   let ability x = factor * (applicability choordAbility x) + bias
--   return $ \op n -> EvalledPred $ \x ->
--     case (op) of
--       (Equal) -> ability x :=: pure (fromIntegral n)
--       (Less) ->  pure (fromIntegral n) :>: ability x 
--       (More) ->  ability x :>: pure (fromIntegral n)

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

-- newUnit :: P Unit
-- newUnit = do
--   alpha <- sampleUniform 1 10
--   beta <- sampleUniform 0.1 100
--   gamma <- sampleUniform (-10) 10
--   return (alpha,beta,gamma)
-- -- These biases worked somewhat better for example 38

-- measure :: Card -> Unit -> A -> VP
-- measure n u a  = EvalledPred $ \x -> computeMeasure u a x  :=:  (fromIntegral n)

-- computeMeasure :: Unit -> A -> Ind -> Probabilistic R
-- computeMeasure (alpha,beta,gamma) a  = \x -> beta * (alpha ** (applicability a x) + gamma)

like = error "like: TODO"
-- regularly = error "regularly: TODO"


