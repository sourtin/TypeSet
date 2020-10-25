{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Fin (Fin) where

import GHC.TypeNats (Nat, KnownNat, natVal)
import Data.Proxy (Proxy(..))
import Data.Kind (Type)
import Data.Ix (Ix(..))
import Numeric.Natural

import Data.TypeSet.Cardinality (Cardinal'(..), Cardinal(..))
import Data.TypeSet.Theory (TypeSet(..), Countable(..), Finite)

-- A 'true' Fin type can be made with GADTs, but it is
-- inefficient as it uses a Peano inductive definition;
-- Instead, we make the constructor private and require
-- the use of the Countable instance to create a value
-- or read its underlying number
data Fin (n :: Nat) = MkFin { getFin :: Natural }
  deriving (Eq,Ord)

instance forall n. KnownNat n => TypeSet (Fin n) where
  type Cardinality (Fin n) = CardFin' n
  cardinality Proxy = CardFin $ natVal (Proxy :: Proxy n)

instance forall n. KnownNat n => Countable (Fin n) where
  toNatural = getFin
  fromNatural m | m < natVal p = Just (MkFin m)
                | otherwise    = Nothing
                where p = Proxy :: Proxy n
  enumerate = map MkFin [0..natVal (Proxy :: Proxy n) - 1]

instance forall n. KnownNat n => Finite (Fin n)

instance forall n. KnownNat n => Bounded (Fin n) where
  minBound = MkFin 0
  maxBound = MkFin $ natVal (Proxy :: Proxy n) - 1

instance forall n. KnownNat n => Enum (Fin n) where
  fromEnum = fromIntegral . getFin
  toEnum m | 0 <= m && m' < natVal p = MkFin m'
    where p = Proxy :: Proxy n
          m' = toEnum m

instance forall n. KnownNat n => Num (Fin n) where
  abs = id
  signum 0 = 0
  signum _ = 1
  negate 0 = 0
  MkFin a + MkFin b = fromIntegral (a + b)
  MkFin a * MkFin b = fromIntegral (a * b)
  fromInteger m | 0 <= m && m' < natVal p = MkFin m'
    where p = Proxy :: Proxy n
          m' = fromInteger m

instance forall n. KnownNat n => Show (Fin n) where
  show (MkFin m) = show m ++ "_" ++ show (natVal p)
    where p = Proxy :: Proxy n

instance forall n. KnownNat n => Ix (Fin n) where
  range (MkFin m, MkFin n) = map MkFin $ range (m,n)
  index (MkFin m, MkFin n) (MkFin l) = index (m,n) l
  inRange (MkFin m, MkFin n) (MkFin l) = inRange (m,n) l
  rangeSize (MkFin m, MkFin n) = rangeSize (m,n)