{-# LANGUAGE LambdaCase #-}

module TypeSet.Algorithm where
import Numeric.Natural (Natural)
import Data.Bits (Bits)
import qualified Data.Bits as B
import Data.Foldable (foldl')

bijIntNat :: Integer -> Natural
bijIntNat x | x >= 0 = 2 * fromInteger x
            | x < 0  = 2 * fromInteger (-x) - 1

bijNatInt :: Natural -> Integer
bijNatInt x = case divMod (toInteger x) 2 of
                   (x, 0) -> x
                   (x, 1) -> -1-x

digits :: Integral a => a -> a -> [a]
digits p = flip go []
  where go 0 = id
        go n = let (n',d) = divMod n p in go n' . (d :)

digitsReverse :: Integral a => a -> a -> [a]
digitsReverse p = go
  where go 0 = []
        go n = let (n',d) = divMod n p in d : go n'

fromDigits :: Integral a => a -> [a] -> a
fromDigits p = go 0
  where go acc []     = acc
        go acc (x:xs) = go (acc*p + x) xs

fromDigitsReverse :: Integral a => a -> [a] -> a
fromDigitsReverse p = go 0 1
  where go acc _   []     = acc
        go acc mul (x:xs) = go (acc + x*mul) (p*mul) xs

popBits :: Bits b => b -> [Bool]
popBits = go 0
  where go i x | x == B.zeroBits = []
               | otherwise = B.testBit x i : go (i+1) (B.clearBit x i)

bitsIsInfinite :: Bits b => b -> Bool
bitsIsInfinite x = B.popCount x < 0 || B.popCount (B.complement x) < 0

bitsIsNegative' :: Bits b => b -> Bool
bitsIsNegative' = (<0) . B.popCount

bitsToNatural :: Bits b => b -> Natural
bitsToNatural x | bitsIsInfinite x = bijIntNat $ bitsToInteger' x
                | otherwise        = fromDigitsReverse 2 . map (\case {False->0; True->1}) $ popBits x

bitsFromNatural :: Bits b => Natural -> b
bitsFromNatural x = let ifInf = bitsFromInteger' $ bijNatInt x
                        ifFin = bitsFromInteger' $ fromIntegral x
                    in if bitsIsInfinite ifInf then ifInf else ifFin

bitsToInteger' :: Bits b => b -> Integer
bitsToInteger' x | bitsIsNegative' x = -1 - bitsToInteger' (B.complement x)
                 | otherwise         = fromIntegral $ bitsToNatural x

bitsFromInteger' :: Bits b => Integer -> b
bitsFromInteger' x | x < 0 = B.complement (bitsFromInteger' (-1 - x))
                   | otherwise = foldl' B.setBit B.zeroBits . map fst
                                     . Prelude.filter ((==1) . snd) . zip [0..]
                                     $ digitsReverse 2 x


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