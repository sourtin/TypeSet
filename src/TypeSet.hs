{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}

module TypeSet where
import Data.Proxy (Proxy(Proxy))
import Numeric.Natural (Natural)
import Data.Foldable (foldl')
import Data.List (foldl1')
import Control.Monad (liftM2)
import qualified Data.Bits as B
import qualified Data.Word as W
import qualified Data.Set as S

import TypeSet.Theory
import TypeSet.Algorithm (popBits, whichBits)
import TypeSet.Cardinality (Cardinal(..))

foldl10' :: (a -> a -> a) -> a -> [a] -> a
foldl10' f x0 [] = x0
foldl10' f _ xs = foldl1' f xs

(\\) :: TypeSubset s a => s -> s -> s
(\\) = difference

class (Eq a, Eq s, Countable a) => TypeSubset s a | s -> a where
  empty :: s
  universe :: s
  powerset :: Finite a => [s]
  complement :: s -> s
  singleton :: a -> s
  fromList :: [a] -> s
  toList :: s -> [a]
  member :: a -> s -> Bool
  size :: s -> Cardinal
  size' :: s -> Natural
  null :: s -> Bool
  full :: s -> Bool
  isSubsetOf, isProperSubsetOf, disjoint :: s -> s -> Bool
  union, intersection, difference, symmetricDifference :: s -> s -> s
  unions, intersections :: [s] -> s
  filter :: (a -> Bool) -> s -> s
  build :: (a -> Bool) -> s

  empty = fromList []
  universe = fromList enumerate
  powerset = map build enumerate
  complement = fromList . flip Prelude.filter enumerate . (not .) . flip member
  singleton = fromList . pure
  fromList = unions . map singleton
  toList = flip Prelude.filter enumerate . flip member
  member x = elem x . toList
  size = CardFin . size'
  size' = fromIntegral . length . toList
  null = (== empty)
  full = (== universe)
  isSubsetOf a b = b == union a b
  isProperSubsetOf a b = a /= b && isSubsetOf a b
  disjoint a b = TypeSet.null (union a b)
  union a b = fromList (toList a ++ toList b)
  intersection a b = complement (complement a `union` complement b)
  difference a b = a `intersection` complement b
  symmetricDifference a b = (a `difference` b) `union` (b `difference` a)
  unions = foldl10' union empty
  intersections = foldl10' intersection universe
  filter = intersection . build
  build = fromList . flip Prelude.filter enumerate

  {-# MINIMAL (toList | member), (fromList | singleton, union) #-}

instance (Finite u, Eq v) => Eq (u -> v) where
  f == g = and $ zipWith (==) (map f enumerate) (map g enumerate)

instance (Eq u, Finite u) => TypeSubset (u -> Bool) u where
  empty = const False
  universe = const True
  powerset = enumerate
  complement = (not .)
  singleton = (==)
  fromList = flip elem
  toList = flip Prelude.filter enumerate
  null = flip all enumerate . (not .)
  full = flip all enumerate
  member = flip ($)
  union = liftM2 (||)
  intersection = liftM2 (&&)
  difference f g x = f x && not (g x)
  symmetricDifference = liftM2 B.xor
  unions fs x = any ($ x) fs
  intersections fs x = all ($ x) fs
  filter = intersection
  build = id

type BitSet a = BitSet' (BitSetMin a) a
newtype BitSet' b a = BitSet {getBitSet :: b}
  deriving (Show, Eq, Ord)
bsmap :: (b -> b) -> (BitSet' b a -> BitSet' b a)
bsmap f (BitSet s) = BitSet (f s)
bslift :: (b -> b -> b) -> (BitSet' b a -> BitSet' b a -> BitSet' b a)
bslift f (BitSet s) (BitSet t) = BitSet (f s t)

instance (Eq a, Countable a, Num b, Enum b, B.Bits b, BitSettable a b) => TypeSubset (BitSet' b a) a where
  empty = BitSet B.zeroBits
  universe = complement empty
  powerset = case cardinality (Proxy :: Proxy a) of
    CardFin p -> map BitSet [0..fromIntegral 2^p-1]
  complement = bsmap $ case cardinality (Proxy :: Proxy a) of
    CardFin p -> flip (foldl' B.complementBit) [0..fromIntegral p-1]
    CardInf 0 -> B.complement
  singleton = BitSet . B.setBit B.zeroBits . fromIntegral . toNatural
  fromList = BitSet . foldl' B.setBit B.zeroBits . map (fromIntegral . toNatural)
  toList = map (fromNatural' . fromIntegral) . whichBits . getBitSet
  member = (. getBitSet) . flip B.testBit . fromIntegral . toNatural
  size (BitSet s) = case B.popCount s of
    n | n < 0 -> CardInf 0
      | otherwise -> CardFin (fromIntegral n)
  size' = fromIntegral . B.popCount . getBitSet
  union = bslift (B..|.)
  intersection = bslift (B..&.)
  difference = bslift $ \s -> foldl' B.clearBit s . whichBits
  symmetricDifference = bslift B.xor
  filter p = bsmap $ \s -> foldl' B.clearBit s . Prelude.filter (not . p . fromNatural' . fromIntegral) $ whichBits s
  build = BitSet . foldl' B.setBit B.zeroBits . map fst . Prelude.filter snd . zip [0..] . flip map enumerate

instance (Eq a, Ord a, Countable a) => TypeSubset (S.Set a) a where
  empty = S.empty
  singleton = S.singleton
  fromList = S.fromList
  toList = S.toList
  member = S.member
  size' = fromIntegral . S.size
  null = (==0) . S.size
  full = (== cardinality (Proxy :: Proxy a)) . size
  isSubsetOf = S.isSubsetOf
  isProperSubsetOf = S.isProperSubsetOf
  disjoint = S.disjoint
  union = S.union
  intersection = S.intersection
  difference = S.difference
  unions = S.unions
  filter = S.filter