module Data.TypeMap.Internal
( TotalArray(..)
) where

import Numeric.Natural (Natural)
import qualified Data.Array as A

newtype TotalArray k v = MkTotalArray { getTotalArray :: A.Array Natural v }