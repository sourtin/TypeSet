module Data.TypeMap.Internal where

import Numeric.Natural (Natural)
import qualified Data.Array as A
import qualified Data.Array.ST as AS
import qualified Data.Map.Strict as MS

newtype TotalArray k v = MkTotalArray { getTotalArray :: A.Array Natural v }
newtype TotalArrayST s k v = MkTotalArrayST { getTotalArrayST :: AS.STArray s Natural v }
newtype TotalMap k v = MkTotalMap { getTotalMap :: MS.Map k v }