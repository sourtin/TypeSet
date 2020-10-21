# TypeSet

The purpose of `TypeSet` is to abstract the `Set` data type from its representation, so that `Data.Set` can be readily swapped out for a more efficient or more appropriate implementation when required. For example, if the underlying type is small then a bitset offers a far more efficient and speedy representation. 

## Data.TypeSet

### TypeSubset

```haskell
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

(\\) :: TypeSubset s a => s -> s -> s
(\\) = difference
```

#### Instances:
- ```haskell
(Eq u, Finite u) =>
TypeSubset (u -> Bool) u
```
- ```haskell
(Eq a, Countable a, Num b, Enum b, B.Bits b, BitSettable a b) =>
TypeSubset (BitSet' b a) a
```
- ```haskell
(Eq a, Ord a, Countable a) =>
TypeSubset (Set a) a
```

The convenience type `BitSet a` is provided which picks the smallest bitset type (i.e. `Word8`, `Word16`, `Word32`, `Word64` or `Integer`) to represent subsets of the type `a`.