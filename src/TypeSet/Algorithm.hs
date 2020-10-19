module TypeSet.Algorithm where
import Numeric.Natural (Natural)
import Data.Bits (Bits)
import qualified Data.Bits as B
import Data.Foldable (foldl')


digitsReverse :: Integral a => a -> a -> [a]
digitsReverse p = go
  where go 0 = []
        go n = let (n',d) = divMod n p in d : go n'

digits :: Integral a => a -> a -> [a]
digits p = flip go []
  where go 0 = id
        go n = let (n',d) = divMod n p in go n' . (d :)

fromDigitsReverse :: Integral a => a -> [a] -> a
fromDigitsReverse p [] = 0
fromDigitsReverse p (x:xs) = x + p*fromDigitsReverse p xs

popBits :: Bits b => b -> [Bool]
popBits = go 0
  where go i x | x == B.zeroBits = []
               | otherwise = B.testBit x i : go (i+1) (B.clearBit x i)

bitsIsInfinite :: Bits b => b -> Bool
bitsIsInfinite x = B.popCount x < 0 || B.popCount (B.complement x) < 0

bitsIsNegative' :: Bits b => b -> Bool
bitsIsNegative' = (<0) . B.popCount

{- snippet: haskell wiki -}
(^!) :: Num a => a -> Int -> a
(^!) x n = x^n

squareRoot :: Integer -> Integer
squareRoot 0 = 0
squareRoot 1 = 1
squareRoot n =
   let twopows = iterate (^!2) 2
       (lowerRoot, lowerN) =
          last $ takeWhile ((n>=) . snd) $ zip (1:twopows) twopows
       newtonStep x = div (x + div n x) 2
       iters = iterate newtonStep (squareRoot (div n lowerN) * lowerRoot)
       isRoot r  =  r^!2 <= n && n < (r+1)^!2
  in  head $ dropWhile (not . isRoot) iters
{- end snippet; -}

cantorPair :: Natural -> Natural -> Natural
cantorPair x y = ((x + y) * (x + y + 1)) `div` 2 + y

cantorZip' :: [Natural] -> (Natural, Natural)
cantorZip' [x] = (0, x)
cantorZip' (x:xs) = let (n, z) = cantorZip' xs in (n+1, cantorPair x z)

cantorZip :: [Natural] -> Natural
cantorZip [] = 0
cantorZip xs = succ . uncurry cantorPair $ cantorZip' xs

cantorUnpair :: Natural -> (Natural, Natural)
cantorUnpair z = let xy1 = fromInteger . squareRoot . toInteger $ 2*z
                     t1 = xy1 * (xy1+1) `div` 2
                     t2 = xy1 * (xy1-1) `div` 2
                     y1 = z - t1
                     y2 = z - t2
                 in if z >= t1 then (xy1-y1,y1) else (xy1-1-y2,y2)

cantorUnzip' :: Natural -> Natural -> [Natural]
cantorUnzip' 0 x = [x]
cantorUnzip' n z = let (x, z') = cantorUnpair z in x : cantorUnzip' (n-1) z'

cantorUnzip :: Natural -> [Natural]
cantorUnzip 0 = []
cantorUnzip n = uncurry cantorUnzip' . cantorUnpair $ pred n
