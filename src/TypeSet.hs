{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}

module TypeSet where
import Numeric.Natural (Natural)
import Data.Foldable (foldl')
import Control.Monad (liftM2)

import TypeSet.Theory (Countable(enumerate), Finite, BitSettable)
import TypeSet.Algorithm (popBits)
import TypeSet.Cardinality (Cardinal(..))

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
  isSubsetOf, isProperSubsetOf, disjoint :: s -> s -> Bool
  union, difference, symmetricDifference, intersection :: s -> s -> s
  unions, intersections :: [s] -> s
  filter :: (a -> Bool) -> s -> s
  build :: (a -> Bool) -> s

  universe = fromList enumerate
  empty = fromList []
  powerset = map build enumerate
  complement = difference universe
  singleton = fromList . pure
  fromList = unions . map singleton
  member x = elem x . toList
  size = CardFin . size'
  size' = fromIntegral . length . toList
  null = (== CardFin 0) . size
  isSubsetOf a b = b == union a b
  isProperSubsetOf a b = a /= b && isSubsetOf a b
  disjoint a b = TypeSet.null (union a b)
  union a b = fromList (toList a ++ toList b)
  difference a b = a `intersection` complement b
  symmetricDifference a b = (a `difference` b) `union` (b `difference` a)
  intersection a b = complement (complement a `union` complement b)
  unions = foldl' union empty
  intersections = complement . unions . map complement
  filter p = fromList . Prelude.filter p . toList
  build = flip TypeSet.filter universe

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
  member = flip ($)
  union = liftM2 (||)
  intersection = liftM2 (&&)
  difference f g x = f x && not (g x)
  unions fs x = any ($ x) fs
  intersections fs x = all ($ x) fs
  filter = intersection
  build = id



foo :: BitSettable a 8 => a -> Bool
foo _ = True