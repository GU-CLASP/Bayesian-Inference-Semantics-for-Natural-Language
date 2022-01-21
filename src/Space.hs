{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
module Space where

import Test.QuickCheck
-- import Test.QuickCheck.All
-- import Control.Applicative

type R = Double

class Lattice a where
  (/\) :: a -> a -> a
  (\/) :: a -> a -> a
  isBottom :: a -> Bool
  (⊆) :: a -> a -> Bool

data Pair a = Pair a a deriving (Functor,Foldable,Eq,Show)

data Interval = Ivl R R deriving (Eq,Show)

instance Arbitrary Interval where
  arbitrary = Ivl <$> choose (0,1) <*> choose (0,1)

newtype Box = Box [Interval] deriving (Eq,Show,Lattice)
data Volume = Tip Bool | Split Int (R) (Pair Volume) deriving (Eq,Show)

(∈) :: [R] -> Volume -> Bool
_ ∈ Tip b = b
xs ∈ Split dim mid (Pair l r) = (xs ∈) $ if xs!!dim <= mid then l else r

numberOfDimensions :: Int
numberOfDimensions = 2
unitInterval :: Interval
unitInterval = Ivl 0 1
unitBox :: Box
unitBox = Box (replicate numberOfDimensions unitInterval)

instance Lattice Bool where
  (/\) = (&&)
  (\/) = (||)
  isBottom x = x == False
  False ⊆ _ = True
  _ ⊆ False = False
  True ⊆ True = True

instance Lattice Interval where
  (Ivl l1 h1) /\ (Ivl l2 h2) = Ivl (max l1 l2) (min h1 h2)
  (Ivl l1 h1) \/ (Ivl l2 h2) = Ivl (min l1 l2) (max h1 h2)
  isBottom (Ivl l h) = l > h
  Ivl l1 h1 ⊆ Ivl l2 h2 = (l2 <= l1) /\ (h1 <= h2)

instance Lattice a => Lattice [a] where
  (/\) = zipWith (/\)
  (\/) = zipWith (\/)
  isBottom xs = foldr1 (/\) (map isBottom xs)
  (⊆) b1 b2 = (foldr (/\) True (zipWith (⊆) b1 b2))


instance Applicative Pair where
  pure x = Pair x x
  Pair f1 f2 <*> Pair x1 x2 = Pair (f1 x1) (f2 x2)

type BoxedVolume = (Box,Volume)

-- | 
-- >>> apps [(+1),(*2)] (3::Int)
-- 7

apps :: [(a -> a)] -> a -> a
apps fs x = foldr ($) x fs
infixr `apps`

boxToVolume :: Box -> Volume
boxToVolume (Box is)
  | any isBottom is = Tip False
  | otherwise
  = [\r -> Split d hi (Pair r (Tip False)) | (d,Ivl _ hi) <- zip [0..] is ] `apps`
    [\r -> Split d lo (Pair (Tip False) r) | (d,Ivl lo _) <- zip [0..] is ] `apps` (Tip True)

-- | complement
complement :: Volume -> Volume
complement (Tip x) = Tip (not x)
complement (Split d x lr) = Split d x (complement <$> lr)

boxVolume :: Box -> R
boxVolume (Box b) = product [max 0 (h - l) | Ivl l h <- b]

-- | n-volume of a volume
volume :: Box -> Volume -> R
volume _ (Tip False) = 0
volume b (Tip True) = boxVolume b
volume b (Split d x cs) = sum (volume <$> subBoxes b d x <*> cs)

-- | Divide an interval at a
subIntervals :: Interval -> R -> Pair Interval
subIntervals (Ivl lo hi) mid = Pair (Ivl lo mid) (Ivl mid hi)

(+:) :: Interval -> Box -> Box
i +: (Box is) = Box (i:is)

-- | Divide a box along a plane
subBoxes :: Box -> Int -> R -> Pair Box
subBoxes (Box []) _ _ = pure (Box [])
subBoxes (Box (i:is)) 0 cs = (+:) <$> subIntervals i cs <*> pure (Box is)
subBoxes (Box (i:is)) n cs = (i +:) <$> subBoxes (Box is) (n-1) cs

data Side = LessThan | MoreThan deriving Eq

compat :: Ordering -> Side -> Bool
compat EQ _ = True
compat GT MoreThan = True
compat LT LessThan = True
compat _ _ = False

compar :: Ord a => a -> a -> Side
compar x y = if x < y then LessThan else MoreThan

pairTuple :: Pair t -> (t, t)
pairTuple (Pair x y) = (x,y)

-- | restrict a volume to a side of a base plane at dimension d and position x.
restrict :: Side -> R -> Int -> Volume -> Volume
restrict _ _ _ (Tip b) = Tip b
restrict s x d (Split d' x' lr)
  | d == d', compat (compare x x') s = restrict s x d $ (case s of LessThan -> fst; MoreThan -> snd) $ (pairTuple lr)
  | otherwise = split d' x' (restrict s x d <$> lr)

intersection :: Volume -> Volume -> Volume
intersection (Tip True) v = v
intersection (Tip False) _ = Tip False
intersection (Split d x lr) v = Split d x
  (intersection <$> (restrict <$> (Pair LessThan MoreThan) <*> pure x <*> pure d <*> pure v) <*> lr)

-- | optimized combination of volumes
split :: Int -> R -> Pair Volume -> Volume
split _ _ (Pair (Tip b) (Tip b')) | b == b' = Tip b
split d x lr = Split d x lr

union :: Volume -> Volume -> Volume
union v1 v2 = complement (complement v1 `intersection` complement v2)

instance Lattice Volume where
  (/\) = intersection
  (\/) = union
  isBottom = \case
    Split _ _ lr -> all isBottom lr 
    Tip x -> not x
  Tip False ⊆ _ = True
  _ ⊆ Tip True = True
  Tip True ⊆ Tip False = False
  Tip True ⊆ Split _ _ lr = all (Tip True ⊆) lr
  Split _ _ lr ⊆ Tip False = all (⊆ Tip False) lr
  Split d x lr ⊆ v = and ((⊆) <$> lr <*> (restrict <$> (Pair LessThan MoreThan) <*> pure x <*> pure d <*> pure v))


volume' :: Volume -> R
volume' = volume unitBox

(≃) :: (Fractional a, Ord a) => a -> a -> Bool
x ≃ y = abs (x-y) < 0.005
infix 2 ≃

eqV :: Volume -> Volume -> Bool
eqV v1 v2 = volume' v1 ≃ volume' v2

instance Arbitrary Box where
  arbitrary = Box <$> vector numberOfDimensions

instance Arbitrary Volume where
  arbitrary = oneof [boxToVolume <$> arbitrary, complement . boxToVolume <$> arbitrary]

prop_maxbox :: Box -> Bool
prop_maxbox v = boxVolume v <= 1

prop_maxvol :: Volume -> Bool
prop_maxvol v = volume' v <= 1

prop_notnot :: Volume -> Bool
prop_notnot v = complement (complement v) == v

prop_compl_v :: Volume -> Bool
prop_compl_v v = volume' v + volume' (complement v) ≃ 1

prop_vol_box :: Box -> Bool
prop_vol_box b = boxVolume b == volume' (boxToVolume b)

prop_intersect_idem_v :: Volume -> Bool
prop_intersect_idem_v v = eqV v (intersection v v)


prop_intersect_idem :: Volume -> Bool
prop_intersect_idem v = v == (intersection v v)

prop_intersect_mono :: Volume -> Volume -> Bool
prop_intersect_mono v1 v2 = volume' v1 >= volume' (intersection v1 v2)

prop_intersect_commut_v :: Volume -> Volume -> Bool
prop_intersect_commut_v v1 v2 = eqV (intersection v1 v2) (intersection v2 v1)

prop_intersect_assoc_v :: Volume -> Volume -> Volume -> Bool
prop_intersect_assoc_v v1 v2 v3 = eqV ((v1 /\ v2) /\ v3) (v1 /\ (v2 /\ v3))

prop_intersect_sub :: Volume -> Volume -> Bool
prop_intersect_sub v1 v2 = (v1 /\ v2) ⊆ v1

prop_union_sub :: Volume -> Volume -> Bool
prop_union_sub v1 v2 = v1 ⊆ (v1 \/ v2)

prop_vol_sub :: Volume -> Volume -> Property
prop_vol_sub v1 v2 = (v1 ⊆ v2) ==> (volume' v1 <= volume' v2)


return []
runTests :: IO Bool
runTests = $quickCheckAll


