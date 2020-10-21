# TypeSet

The purpose of `TypeSet` is to abstract the `Set` data type from its representation, so that `Data.Set` can be readily swapped out for a more efficient or more appropriate implementation when required. For example, if the underlying type is small then a bitset offers a far more efficient and speedy representation. 

- [Data.Fin](#datafin): `Fin`
- [Data.TypeSet](#datatypeset): `TypeSubset(..)`
- [Data.TypeSet.Theory](#datatypesettheory): `TypeSet(..)`, `Countable(..)`, `Finite`
- [Data.TypeSet.Cardinality](#datatypesetcardinality): `Cardinal(..)`, `Cardinal'(..)`
- [Data.TypeSet.Algorithm](#datatypesetalgorithm): ...
- [Instances](#instances-1): ...

## Data.Fin

Defines the opaque `Fin` data type. Manipulation can be achieved through its `Countable` instance.

```haskell
data Fin (n :: Nat)
```

## Data.TypeSet

### TypeSubset

`TypeSubset s a` is a typeclass which indicates that data of type `s` can represent any subset of values of type `a`. For example, the instance for `Set` is `TypeSubset (Set a) a`. It generalises many of the functions from `Data.Set`, and adds a couple more of its own.

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

  {-# MINIMAL (toList | member), (fromList | singleton, union) #-}

(\\) :: TypeSubset s a => s -> s -> s
(\\) = difference
```

#### Instances:
- Indicator functions

    ```haskell
    (Eq u, Finite u) =>
    TypeSubset (u -> Bool) u
    ```

- Bitsets (any type `b` that has a `Bits` instance and which has a type instance for `BitWidth b` [suitably defined](#bitsets))

    ```haskell
    (Eq a, Countable a, Num b, Enum b, Bits b, BitSettable a b) =>
    TypeSubset (BitSet' b a) a
    ```

    The convenience type `BitSet a` is provided which (statically) picks the smallest bitset type (out of `Word8`, `Word16`, `Word32`, `Word64` and `Integer`) to represent subsets of the type `a`.
- Regular `Data.Set` sets

    ```haskell
    (Eq a, Ord a, Countable a) =>
    TypeSubset (Set a) a
    ```

### BitSets

By default, the types `()`, `Bool`, `Char`, `Natural`, `Integer`, `Int8`, `Int16`, `Int32`, `Int64`, `Word8`, `Word16`, `Word32`, and `Word64` can be used as the underlying bitset `b` in `BitSet' b a`. Other than some standard typeclasses, the main required instances are [`Countable`](#countable) and `Bits`. In addition, you should give a type instance for `BitWidth b`. E.g. if the bitfield has 24 bits, then you should do

```haskell
type instance BitWidth MyBitField24 = CardFin' 24
```

If the bitfield is unbounded in size, e.g. `Natural`, then you can instead do

```haskell
type instance BitWidth MyBitField24 = CardInf' 0
```

to indicate it has the cardinality of countable infinity, <img alt="\aleph_0=\beth_0" src="https://render.githubusercontent.com/render/math?math=\aleph_0=\beth_0">.

## Data.TypeSet.Theory

Contains some mathematical theory for behind-the-scenes plumbing of `TypeSubset`. Specifically, it defines what a `TypeSet` is so that we can take a subset of it, and also defines the subclasses `Countable` and `Finite` for the 'special' case of types of countable- and finite- cardinality respectively.

As a corollary of these, it also defines the following type families:

```haskell
BitWidth a :: Cardinal'
BitSettable a b :: Constraint
BitSetMin a :: *
```

- `BitWidth a`, for types that can be interpreted as a bitfield, gives the maximum number of independent bits it can store as a cardinality. E.g. `BitWidth Char = CardFin' 20` because, although a `Char` takes up at least 21 bits, it cannot store a full 2^21 distinct values.
- `BitSettable a b` tests whether subsets of type `a` can be represented by a bitfield of type `b`.
- `BitSetMin a` gives the smallest bitset type (out of `Word8`, `Word16`, `Word32`, `Word64` and `Integer`) to represent subsets of the type `a`.

### TypeSet

```haskell
class TypeSet a where
  type Cardinality a :: Cardinal'
  cardinality :: Proxy a -> Cardinal
```

`TypeSet` provides both type-level and value-level access to the cardinality of a type. If a type has a cardinality then it can be represented as a set. In principle, category theory allows us to generate collections too large to be a set, but in practice the set of objects we can construct in haskell are countable. Nevertheless, we do give the cardinality of `Natural -> Bool` as <img alt="\beth_1=\mathfrak{c}" src="https://render.githubusercontent.com/render/math?math=\beth_1=\mathfrak{c}">, the cardinality of the continuum, and `((Natural -> Bool) -> Bool) -> Bool` as <img alt="\beth_3" src="https://render.githubusercontent.com/render/math?math=\beth_3">.

### Countable

To meaningfully talk about discrete subsets, we need to know which `TypeSet`s are countable and have a way to form bijections or enumerate them.

```haskell
class TypeSet a => Countable a where
  toNatural :: a -> Natural
  fromNatural :: Natural -> Maybe a
  fromNatural' :: Natural -> a
  enumerate :: [a]

  {-# MINIMAL toNatural, fromNatural #-}
```

### Finite

We would also like to distinguish `TypeSet`s that are not only countable, but finite. This typeclass has no members, it simply serves as a constraint.

```haskell
class Countable a => Finite a
```

## Data.TypeSet.Cardinality

This contains the definitions of Cardinals, as well as type families for cardinal arithmetic. It also contains a type family `ShowCardinality (a :: Cardinal') :: ErrorMessage` for convenience.

### Cardinal, Cardinal'

```haskell
data Cardinal = CardFin Natural
              | CardInf { bethIndex :: Natural }

data Cardinal' = CardFin' Nat
               | CardInf' Nat
```

We use the first datatype for value-level cardinals, and the second datatype for type-level cardinals via `DataKinds` lifting. Unfortunately we cannot (?) use a single definition here because GHC's canonical data-level naturals and type-level naturals are distinct.

### Cardinal arithmetic

```haskell
CardAdd (a :: Cardinal') (b :: Cardinal') :: Cardinal'
CardMul (a :: Cardinal') (b :: Cardinal') :: Cardinal'
CardExp (a :: Cardinal') (b :: Cardinal') :: Cardinal'
CardList (a :: Cardinal') :: Cardinal'
CmpCard (a :: Cardinal') (b :: Cardinal') :: Ordering
Injectable (a :: Cardinal') (b :: Cardinal') (msg :: ErrorMessage)
```

`CardAdd`, `CardMul`, and `CardExp` compute cardinal addition, multiplication and exponentiation respectively. `CardList` computes the cardinality of lists of `a`, or equivalently corresponds to the Kleene star operation. `CmpCard` can be used to compare cardinals, returning `LT`, `EQ` or `GT`. `Injectable` is a constraint that asserts `a <= b` and thus that there exists an injection of type `a -> b`, or else it raises a type error with the given message.

## Data.TypeSet.Algorithm

Some miscellaneous helper functions, primarily used for instances of `Countable`

```haskell
-- map non-negative to even, negative to odd
bijIntNat :: Integer -> Natural
bijNatInt :: Natural -> Integer

-- map between integral and positional representation
-- first argument is base
digits :: Integral a => a -> a -> [a]
digitsReverse :: Integral a => a -> a -> [a]
fromDigits :: Integral a => a -> [a] -> a
fromDigitsReverse :: Integral a => a -> [a] -> a

-- which bits are set, least significant first
popBits :: Bits b => b -> [Bool]
whichBits :: Bits b => b -> [Int]

-- is the type b unbounded?
bitsIsInfinite :: Bits b => b -> Bool

bitsIsNegative' :: Bits b => b -> Bool
bitsToNatural :: Bits b => b -> Natural
bitsFromNatural :: Bits b => Natural -> b
bitsToInteger' :: Bits b => b -> Integer
bitsFromInteger' :: Bits b => Integer -> b

-- canonical cantor pairing functions
cantorPair :: Natural -> Natural -> Natural
cantorUnpair :: Natural -> (Natural, Natural)
-- recursively apply cantor pairing to list and
-- return (length, flattened), & vice versa
cantorZip' :: [Natural] -> (Natural, Natural)
cantorUnzip' :: Natural -> Natural -> [Natural]
-- cantor fold in the length, too
cantorZip :: [Natural] -> Natural
cantorUnzip :: Natural -> [Natural]

-- borrowed from haskell wiki (for use in cantorUnpair)
(^!) :: Num a => a -> Int -> a
squareRoot :: Integer -> Integer
```

## Instances

```haskell
type BitWidth Bool
type BitWidth Char
type BitWidth Int8
type BitWidth Int16
type BitWidth Int32
type BitWidth Int64
type BitWidth Integer
type BitWidth Natural
type BitWidth Word8
type BitWidth Word16
type BitWidth Word32
type BitWidth Word64
type BitWidth ()
```

```haskell
instance TypeSet Bool
instance TypeSet Char
instance TypeSet Int8
instance TypeSet Int16
instance TypeSet Int32
instance TypeSet Int64
instance TypeSet Integer
instance TypeSet Natural
instance TypeSet Word8
instance TypeSet Word16
instance TypeSet Word32
instance TypeSet Word64
instance TypeSet ()
instance TypeSet Void
instance TypeSet a => TypeSet ([a] :: Type)
instance KnownNat n => TypeSet (Fin n :: Type)
instance (TypeSet a, TypeSet b) => TypeSet (a -> b :: Type)
instance (TypeSet a, TypeSet b) => TypeSet (Either a b :: Type)
instance (TypeSet a, TypeSet b) => TypeSet ((a, b) :: Type)
instance (TypeSet a, TypeSet b, TypeSet c) => TypeSet ((a, b, c) :: Type)
instance (TypeSet a, TypeSet b, TypeSet c, TypeSet d) => TypeSet ((a, b, c, d) :: Type)
instance (TypeSet a, TypeSet b, TypeSet c, TypeSet d, TypeSet e) => TypeSet ((a, b, c, d, e) :: Type)
```

```haskell
instance Countable Bool
instance Countable Char
instance Countable Int8
instance Countable Int16
instance Countable Int32
instance Countable Int64
instance Countable Integer
instance Countable Natural
instance Countable Word8
instance Countable Word16
instance Countable Word32
instance Countable Word64
instance Countable ()
instance Countable Void
instance Countable a => Countable [a]
instance KnownNat n => Countable (Fin n)
instance (Finite a, Countable b) => Countable (a -> b)
instance (Countable a, Countable b) => Countable (Either a b)
instance (Countable a, Countable b) => Countable (a, b)
instance (Countable a, Countable b, Countable c) => Countable (a, b, c)
instance (Countable a, Countable b, Countable c, Countable d) => Countable (a, b, c, d)
instance (Countable a, Countable b, Countable c, Countable d, Countable e) => Countable (a, b, c, d, e)
```

```haskell
instance Finite Bool
instance Finite Char
instance Finite Int8
instance Finite Int16
instance Finite Int32
instance Finite Int64
instance Finite Word8
instance Finite Word16
instance Finite Word32
instance Finite Word64
instance Finite ()
instance Finite Void
instance KnownNat n => Finite (Fin n)
instance (Finite a, Finite b) => Finite (a -> b)
instance (Finite a, Finite b) => Finite (Either a b)
instance (Finite a, Finite b) => Finite (a, b)
instance (Finite a, Finite b, Finite c) => Finite (a, b, c)
instance (Finite a, Finite b, Finite c, Finite d) => Finite (a, b, c, d)
instance (Finite a, Finite b, Finite c, Finite d, Finite e) => Finite (a, b, c, d, e)
```

```haskell
instance (Eq a, Ord a, Countable a) => TypeSubset (Set a) a
instance (Eq u, Finite u) => TypeSubset (u -> Bool) u
instance (Eq a, Countable a, Num b, Enum b, Bits b, BitSettable a b) => TypeSubset (BitSet' b a) a
```