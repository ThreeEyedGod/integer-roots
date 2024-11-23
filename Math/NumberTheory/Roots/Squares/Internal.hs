-- |
-- Module:      Math.NumberTheory.Roots.Squares.Internal
-- Copyright:   (c) 2011 Daniel Fischer, 2016-2020 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Internal functions dealing with square roots. End-users should not import this module.

{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE CPP              #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE CApiFFI #-} -- addition
{-# LANGUAGE UnboxedTuples #-} -- addition

module Math.NumberTheory.Roots.Squares.Internal
  ( karatsubaSqrt
  , isqrtA
  ) where

-- *********** BEGIN NEW IMPORTS   
import Control.Parallel (par, pseq)
import GHC.Prim (fmaddDouble#, (/##), (+##))
import Data.Maybe (fromMaybe)
import Data.Bits (Bits (xor))
import GHC.Integer (decodeDoubleInteger, encodeDoubleInteger)
import Math.NumberTheory.Logarithms (integerLog10', integerLogBase', integerLog2')
import Numeric.Floating.IEEE (isNormal)
import GHC.Num.Integer
    ( integerDecodeDouble#, integerShiftL#, integerFromInt,integerFromWordList,
      integerFromInt#,
      integerShiftR#,
      integerLog2#,
      integerQuotRem, integerToInt, integerLogBase, integerEncodeDouble, integerLogBase#)
import GHC.Float (divideDouble, isDoubleDenormalized, integerToDouble#)
import Data.FastDigits (digits, digitsUnsigned, undigits)
import qualified Data.Vector as VE (cons, ifoldl', empty, singleton, Vector)
import Data.Int (Int64)
import Foreign.C.Types ( CLong(..) )
import qualified Numeric.Floating.IEEE as NFI (nextDown, nextUp)
import Data.Word (Word32)
import GHC.Exts ((<##), (*##), Double(..), Double#)
-- *********** END NEW IMPORTS 

import Data.Bits (finiteBitSize, unsafeShiftL, unsafeShiftR, (.&.), (.|.))

import GHC.Exts (Int(..), Int#, isTrue#, int2Double#, sqrtDouble#, double2Int#, (<#))
#ifdef MIN_VERSION_integer_gmp
import GHC.Exts (uncheckedIShiftRA#, (*#), (-#))
import GHC.Integer.GMP.Internals (Integer(..), shiftLInteger, shiftRInteger, sizeofBigNat#)
import GHC.Integer.Logarithms (integerLog2#)
#define IS S#
#define IP Jp#
#define bigNatSize sizeofBigNat
#else
import GHC.Exts (uncheckedShiftRL#, word2Int#, minusWord#, timesWord#)
import GHC.Num.BigNat (bigNatSize#)
import GHC.Num.Integer (Integer(..), integerLog2#, integerShiftR#, integerShiftL#)
#endif

-- Find approximation to square root in 'Integer', then
-- find the integer square root by the integer variant
-- of Heron's method. Takes only a handful of steps
-- unless the input is really large.
{-# SPECIALISE isqrtA :: Integer -> Integer #-}
isqrtA :: Integral a => a -> a
isqrtA 0 = 0
isqrtA n = isqrtB n -- heron n (fromInteger . appSqrt . fromIntegral $ n) -- replace with isqrtB n 

-- Heron's method for integers. First make one step to ensure
-- the value we're working on is @>= r@, then we have
-- @k == r@ iff @k <= step k@.
{-# SPECIALISE heron :: Integer -> Integer -> Integer #-}
heron :: Integral a => a -> a -> a
heron n a = go (step a)
      where
        step k = (k + n `quot` k) `quot` 2
        go k
            | m < k     = go m
            | otherwise = k
              where
                m = step k

-- Find a fairly good approximation to the square root.
-- At most one off for small Integers, about 48 bits should be correct
-- for large Integers.
appSqrt :: Integer -> Integer
appSqrt (IS i#) = IS (double2Int# (sqrtDouble# (int2Double# i#)))
appSqrt n@(IP bn#)
    | isTrue# ((bigNatSize# bn#) <# thresh#) =
          floor (sqrt $ fromInteger n :: Double)
    | otherwise = case integerLog2# n of
#ifdef MIN_VERSION_integer_gmp
                    l# -> case uncheckedIShiftRA# l# 1# -# 47# of
                            h# -> case shiftRInteger n (2# *# h#) of
                                    m -> case floor (sqrt $ fromInteger m :: Double) of
                                            r -> shiftLInteger r h#
#else
                    l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
                            h# -> case integerShiftR# n (2## `timesWord#` h#) of
                                    m -> case floor (sqrt $ fromInteger m :: Double) of
                                            r -> integerShiftL# r h#
#endif
    where
        -- threshold for shifting vs. direct fromInteger
        -- we shift when we expect more than 256 bits
        thresh# :: Int#
        thresh# = if finiteBitSize (0 :: Word) == 64 then 5# else 9#
-- There's already a check for negative in integerSquareRoot,
-- but integerSquareRoot' is exported directly too.
appSqrt _ = error "integerSquareRoot': negative argument"


-- Integer square root with remainder, using the Karatsuba Square Root
-- algorithm from
-- Paul Zimmermann. Karatsuba Square Root. [Research Report] RR-3805, 1999,
-- pp.8. <inria-00072854>

karatsubaSqrt :: Integer -> (Integer, Integer)
karatsubaSqrt 0 = (0, 0)
karatsubaSqrt n
    | lgN < 2300 =
        let s = isqrtA n in (s, n - s * s)
    | otherwise =
        if lgN .&. 2 /= 0 then
            karatsubaStep k (karatsubaSplit k n)
        else
            -- before we split n into 4 part we must ensure that the first part
            -- is at least 2^k/4, since this doesn't happen here we scale n by
            -- multiplying it by 4
            let n' = n `unsafeShiftL` 2
                (s, r) = karatsubaStep k (karatsubaSplit k n')
                r' | s .&. 1 == 0 = r
                   | otherwise = r + double s - 1
            in  (s `unsafeShiftR` 1, r' `unsafeShiftR` 2)
  where
    k = lgN `unsafeShiftR` 2 + 1
#ifdef MIN_VERSION_integer_gmp
    lgN = I# (integerLog2# n)
#else
    lgN = I# (word2Int# (integerLog2# n))
#endif

karatsubaStep :: Int -> (Integer, Integer, Integer, Integer) -> (Integer, Integer)
karatsubaStep k (a3, a2, a1, a0)
    | r >= 0 = (s, r)
    | otherwise = (s - 1, r + double s - 1)
  where
    r = cat u a0 - q * q
    s = s' `unsafeShiftL` k + q
    (q, u) = cat r' a1 `quotRem` double s'
    (s', r') = karatsubaSqrt (cat a3 a2)
    cat x y = x `unsafeShiftL` k .|. y
    {-# INLINE cat #-}

karatsubaSplit :: Int -> Integer -> (Integer, Integer, Integer, Integer)
karatsubaSplit k n0 = (a3, a2, a1, a0)
  where
    a3 = n3
    n3 = n2 `unsafeShiftR` k
    a2 = n2 .&. m
    n2 = n1 `unsafeShiftR` k
    a1 = n1 .&. m
    n1 = n0 `unsafeShiftR` k
    a0 = n0 .&. m
    m = 1 `unsafeShiftL` k - 1

double :: Integer -> Integer
double x = x `unsafeShiftL` 1
{-# INLINE double #-}

-- BEGIN isqrtB ****************************************************************
-- BEGIN isqrtB ****************************************************************

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
-- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic
{-# SPECIALIZE isqrtB :: Integer -> Integer #-}
isqrtB :: (Integral a) => a -> a
isqrtB 0 = 0
isqrtB n = fromInteger . ni_ . fi_ . dgts_ . fromIntegral $ n

dgts_ :: Integer -> [Word32]
dgts_ n | n < 0 = error "dgts_: Invalid negative argument"
dgts_ 0 = [0]
dgts_ n = mkIW32_ n

-- | First Iteration
fi_ :: [Word32] -> ([Word32], Int, VE.Vector Word32, Integer)
fi_ [0] = ([], 0, VE.empty, 0) -- safety
fi_ [] = error "fi_: Invalid Argument null list "
fi_ dxs = (w32Lst, l', yCurrArr, remInteger)
  where
    l = length dxs
    ((w32Lst, dxs'), l') = let (head_, last_@[x]) = splitAt (l - 1) dxs in if even l then (splitAt (l - 2) dxs, l-2) else ((head_, [x, 0 :: Word32]), l-1)
    vInteger = intgrFromRvsrdLst dxs'
    searchFrom = if vInteger >= radixW32Squared then radixW32Squared else 0 -- heuristic
    y1_ = largestNSqLTE searchFrom vInteger
    y1 = if y1_ == radixW32 then pred radixW32 else y1_ -- overflow trap 
    yCurrArr = VE.singleton (fromIntegral y1)
    remInteger_ = vInteger - y1 * y1 
    remInteger = if remInteger_ == radixW32 then pred radixW32 else remInteger_ 

-- | Next Iterations till array empties out 
ni_ :: ([Word32], Int, VE.Vector Word32, Integer) -> Integer
ni_ (w32Lst, l, yCurrArr, iRem)
  | null w32Lst = vectorToInteger yCurrArr 
  | otherwise = ni_ (residuali32Lst, l-2, yCurrArrUpdated, remFinal)
  where
    position = pred $ l `quot` 2 -- last pair is psition "0"
    (residuali32Lst, nxtTwoDgts) = splitAt (l - 2) w32Lst
    tAInteger = (iRem * secndPlaceRadix) + intgrFromRvsrdLst nxtTwoDgts
    -- tAInteger = let  x1 = iRem * secndPlaceRadix 
    --                  x2 = intgrFromRvsrdLst nxtTwoDgts
    --   in x1 `par` x2 `pseq` x1 + x2 
    tBInteger' = vectorToInteger yCurrArr
    tCInteger' = radixW32 * tBInteger' -- sqrtF previous digits being scaled right here
    yTilde = nxtDgt_ (tAInteger, tCInteger')
    (yTildeFinal, remFinal) = computeRem_ (tAInteger, tBInteger', tCInteger') (yTilde, position)
    yCurrArrUpdated = VE.cons (fromIntegral yTildeFinal) yCurrArr

-- | Next Digit. In our model a 32 bit digit.    
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgt_ :: (Integer, Integer) -> Integer 
nxtDgt_ (tA, tC) 
    | tA == 0 = 0 
    | itsOKtoUsePlainDoubleCalc = floor (nextUp $ D# (nextUp# tA# /## nextDown# (sqrtDouble# (nextDown# rad#) +## nextDown# tC#))) 
    | otherwise = nxtDgtFX_ (tAFX, tCFX) 
 where 
    rad# = fmaddDouble# tC# tC# tA#
    !(D# maxDouble#) = maxDouble
    itsOKtoUsePlainDoubleCalc = isTrue# (rad# <## (fudgeFactor## *## maxDouble#)) where fudgeFactor## = 1.00## -- for safety it has to land within maxDouble (1.7*10^308) i.e. tC ^ 2 + tA <= maxSafeInteger
    tAFX = normalizeFX $ integer2FloatingX tA   
    tCFX = normalizeFX $ integer2FloatingX tC
    tA# = integerToDouble# tA
    tC# = integerToDouble# tC

-- | Use FLoatingX Arithmetic to throw up the next digit 
nxtDgtFX_ :: (FloatingX, FloatingX) -> Integer 
nxtDgtFX_ (tAFX, tCFX) =  iyTildeOut where
      !iyTildeOut = min iyTilde (pred radixW32) -- overflow trap   
      !iyTilde = floorX (nextUpFX iyTildeFX) 
      !iyTildeFX =  nextUpFX (numFX !/ denFX) 
      !numFX = nextUpFX tAFX 
      !denFX =  nextDownFX (sqrtDFX !+ yShiftedFX) 
      !sqrtDFX = nextDownFX (sqrtFX radFX) 
      !radFX =  nextDownFX (yShiftedSqrFX !+ tAFX) 
      !yShiftedSqrFX = nextDownFX (yShiftedFX !* yShiftedFX) 
      !yShiftedFX = tCFX -- scaled value of previous digit -- OK

-- | compute the remainder. It may be that the "digit" may need to be reworked 
-- that happens in handleRems_      
computeRem_ :: (Integer, Integer, Integer) -> (Integer, Int) -> (Integer, Integer)
computeRem_ (tA, tB, tC) (yTilde, pos) = result
  where
    rTrial = calcRemainder tA tC yTilde 
    result@(yTildeFinal, remFinal) = handleRems_ (pos, yTilde, rTrial, tA, tB, tC)

-- | if the remainder is negative it's a clear sign to decrement the candidate digit
-- if it's positive but far larger in length of the current accumulated root, then also it signals a need for current digit rework 
-- if it's positive and far larger in size then also the current digit rework 
handleRems_ :: (Int, Integer, Integer, Integer, Integer, Integer) -> (Integer, Integer)
handleRems_ (pos, yi, ri, tA, tB, tC)
  | ri == 0 = (yi, ri)
  | (ri > 0) && noExcessLength = (yi, ri) -- all ok just continue no need for any other check if pos =0 then this check is not useful
  | (ri < 0) && (yi > 0) = (nextDownDgt0, calcRemainder tA tC nextDownDgt0) -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | (ri > 0) && (pos > 0) && excessLengthBy3 = (yi, adjustedRemainder3) -- handleRems (pos, yCurrListReversed, yi, adjustedRemainder3, tA, tB)
  | (ri > 0) && firstRemainderBoundCheckFail = (nextUpDgt1, calcRemainder tA tC nextUpDgt1)
  | (ri > 0) && secondRemainderBoundCheckFail = (nextUpDgt2, calcRemainder tA tC nextUpDgt2)
  | otherwise = (yi, ri)
  where
    b = radixW32
    riCurrSqrtRatio = ri `quot` currSqrt
    noExcessLength = riCurrSqrtRatio < 2 -- quick escape all good
    {-  excessLengthBy3 = lenCurrRemainder >= lenCurrSqrt + 3
        lenCurrRemainder = 1 + integerLogBase' b ri
        lenCurrSqrt = 1 + integerLogBase' b yi
     -}
    excessLengthBy3 = integerLogBase' b (ri `div` yi) >= 3
    firstRemainderBoundCheckFail = not (isValidRemainder1 ri currSqrt pos)
    secondRemainderBoundCheckFail = not (isValidRemainder2 ri currSqrt pos)
    currSqrt = tB * radixW32 + yi 
    modulus3 = radixW32Cubed -- b^3
    adjustedRemainder3 = ri `mod` modulus3
    nextDownDgt0 = findNextDigitDown (tA, tB, tC) (yi, ri) pos yi 0 isValidRemainder0
    nextUpDgt1 = findNextDigitUp (tA, tB, tC) (yi, ri) pos yi (radixW32 - 1) isValidRemainder1
    nextUpDgt2 = findNextDigitUp (tA, tB, tC) (yi, ri) pos yi (radixW32 - 1) isValidRemainder2

-- Helper function to calculate remainder bounds
calcMaxAllowed :: Integer -> Int -> Integer
calcMaxAllowed currentSqrt pos = 2 * currentSqrt * (radixW32 ^ pos) + radixW32 ^ (2 * pos)

altBoundAllowed :: Integer -> Int -> Integer 
altBoundAllowed currentroot pos = 2 * currentroot * radixW32^(pos+1) --radixW32^(pos+1) -- remainder < 2 ^ (p + 32)   r < 2 aB ^ (p + 1)

isValidRemainder0 :: Integer -> Integer -> Int -> Bool 
isValidRemainder0 rem0 _ _ = rem0 >= 0 

isValidRemainder1 :: Integer -> Integer -> Int -> Bool 
isValidRemainder1 rem1 currentroot pos = rem1 < calcMaxAllowed currentroot pos

isValidRemainder2 :: Integer -> Integer -> Int -> Bool
isValidRemainder2 rem2 currentroot pos = rem2 < altBoundAllowed currentroot pos

-- Calculate remainder accompanying a 'digit'
calcRemainder :: Integer -> Integer -> Integer -> Integer
calcRemainder tA tC dgt = tA - ((2 * tC * dgt) + dgt ^ (2 :: Int))

findNextDigitUp :: (Integer, Integer, Integer) -> (Integer, Integer) -> Int -> Integer -> Integer -> (Integer -> Integer -> Int -> Bool) -> Integer 
findNextDigitUp (tA, tB, tC) (yi,ri) pos curr high checkFn
      | curr >= ceilNxtDgtUp  = ceilNxtDgtUp
      | curr > high = error "findNextDigitUp : no valid digit found (curr>high)"
      | curr == high = if checkFn curr yUpdated pos then curr - 1 else error "findNextDigitUp : no valid digit found (curr=high)"
      | otherwise = 
          let mid = (curr + high) `div` 2 
              testRem = calcRemainder tA tC mid 
              testRoot = tC + mid 
          in if checkFn testRem testRoot pos then 
              let validLower = tryRange curr (mid-1)
              in fromMaybe mid validLower 
             else
                findNextDigitUp (tA, tB, tC) (yi, ri) pos (mid+1) high checkFn
    where 
            ceilNxtDgtUp = radixW32 -1 
            yUpdated = tC + curr
            tryRange lowr highr 
              | lowr > highr = Nothing
              | otherwise = 
                  let mid = (lowr + highr) `div` 2
                      testRm = calcRemainder tA tC mid
                      testRt = tC + mid
                  in if checkFn testRm testRt pos 
                    then Just mid
                    else tryRange (mid+1) highr


findNextDigitDown :: (Integer, Integer, Integer) -> (Integer, Integer) -> Int -> Integer -> Integer -> (Integer -> Integer -> Int -> Bool) -> Integer
findNextDigitDown (tA, tB, tC) (yi, ri) pos curr low checkFn
  | curr < low = error "findNextDigitDown : no valid digit found (curr<low) "
  | curr == low = if checkFn curr yUpdated pos then curr else error "findNextDigitDown : no valid digit found (curr=low) "
  | curr == yi = if checkFn (yi-1) yUpdated pos then yi-1 else findNextDigitDown (tA, tB, tC) (yi, ri) pos (yi - 2) low checkFn
  | otherwise =
      let mid = (low + curr ) `div` 2
          testRem = calcRemainder tA tC mid
          testRoot = tC + mid 
       in if checkFn testRem testRoot pos
            then
              let validHigher = tryRange (mid + 1) curr
               in fromMaybe mid validHigher
            else
              findNextDigitDown (tA, tB, tC) (yi, ri) pos (mid - 1) low checkFn
  where
    yUpdated = tC + curr 
    tryRange lowr highr
      | lowr > highr = Nothing
      | otherwise =
          let mid = (lowr + highr) `div` 2
              testRm = calcRemainder tA tC mid
              testRt = tC + mid 
           in if checkFn testRm testRt pos
                then Just mid
                else tryRange lowr (mid - 1) 

-- | helper functions

mkIW32 :: Integer -> [Word32]
mkIW32 0 = [0]
mkIW32 i = int2wrd32 $ reverse' (digits (fromIntegral radixW32) i)

mkIW32' :: Integer -> [Word32]
mkIW32' 0 = [0]
mkIW32' i = wrd2wrd32 $ reverse'' (digitsUnsigned b n)
  where
    b = fromIntegral radixW32 :: Word
    n = fromInteger i

{-# INLINE [2] mkIW32_ #-}
-- spit out the list as-is from digitsUnsigned which comes in reversed format. 
mkIW32_ :: Integer -> [Word32]
mkIW32_ 0 = [0] -- safety 
mkIW32_ i = wrd2wrd32 (digitsUnsigned b n)
  where
    b = fromIntegral radixW32 :: Word
    n = fromInteger i

int2wrd32 :: [Int] -> [Word32]
int2wrd32 xs = fromIntegral <$> xs

wrd2wrd32 :: [Word] -> [Word32]
wrd2wrd32 xs = fromIntegral <$> xs

mkW32I :: [Word32] -> Integer
mkW32I xs = undigits radixW32 (reverse' xs)

-- https :// blog . poisson . chat / posts / 2019 - 09 - 13 - reverse . html

reverse' :: [a] -> [a]
reverse' xs = revApp xs []

-- revApp xs ys = reverse xs ++ ys
revApp :: [a] -> [a] -> [a]
revApp [] acc = acc
revApp (x : xs) acc = revApp xs (x : acc)

type DList a = [a] -> [a]

empty :: DList a
empty = id

singleton :: a -> DList a
singleton y = (y :)

(++.) :: DList a -> DList a -> DList a
(++.) = (.)

toList :: DList a -> [a]
toList ys = ys []
-- reverse, where the result is a difference list
reversed :: [a] -> DList a
reversed [] = empty
reversed (x : xs) = reversed xs ++. singleton x

reverse'' :: [a] -> [a]
reverse'' = toList . reversed
    
data FloatingX = FloatingX {signif :: Double, expnnt :: Int64} deriving (Eq,Show) 

{-# INLINE [2] vectorToInteger #-}
-- Function to convert a vector of Word32 values to an Integer with base 2^32 (radixw32)
vectorToInteger :: VE.Vector Word32 -> Integer
vectorToInteger = VE.ifoldl' (\acc i w -> acc + fromIntegral w * radixW32 ^ i) 0 

{-# INLINE [2] floorX #-}
floorX :: FloatingX -> Integer
floorX (FloatingX s e) = case compose (s, e) of
  Just d -> floor d 
  _ -> tl
  where
    tl = fromIntegral $ toLong s (fromIntegral e)
        
zero :: FloatingX
zero = FloatingX 0.0 (minBound :: Int64)
minValue :: FloatingX
minValue = FloatingX 1.0 0

{-# INLINE [2] (!+) #-}
(!+) :: FloatingX -> FloatingX -> FloatingX
(!+) x y = x `add` y 
{-# INLINE [2] (!*) #-}
(!*) :: FloatingX -> FloatingX -> FloatingX
(!*) x y = x `mul` y
{-# INLINE [2] (!/) #-}
(!/) :: FloatingX -> FloatingX -> FloatingX
(!/) x y = x `divide` y

add :: FloatingX -> FloatingX -> FloatingX
add (FloatingX 0.0 _) x = x
add x (FloatingX 0.0 _) = x
add a@(FloatingX signifA expA) b@(FloatingX signifB expB)
  | expA > expB = combine a b
  | expA < expB = combine b a
  | otherwise = FloatingX (signifA + signifB) expA
  where
    combine big@(FloatingX signifBig expBig) little@(FloatingX signifLittle expLittle) =
      let scale = expLittle - expBig
          scaledLittle = signifLittle * 2 ^^ scale
          resSignif = signifBig + scaledLittle
       in if resSignif >= 2.0
            then FloatingX (resSignif / 2.0) (expBig + 1)
            else FloatingX resSignif expBig

mul :: FloatingX -> FloatingX -> FloatingX
mul (FloatingX 0.0 _) _ = zero
mul _ (FloatingX 0.0 _) = zero
mul (FloatingX signifA expA) (FloatingX signifB expB) =
  let resExp = expA + expB
      resSignif = signifA * signifB
   in if resSignif >= 2.0
        then FloatingX (resSignif / 2.0) (resExp + 1)
        else FloatingX resSignif resExp

divide :: FloatingX -> FloatingX -> FloatingX
divide (FloatingX s1 e1) (FloatingX s2 e2)
    | s1 == 0.0 = zero
    | s2 == 0.0 = error "divide: error divide by zero " 
    | otherwise = 
        let resExp = e1 - e2
            resSignif = s1 / s2
            (finalSignif, finalExp) = if resSignif < 1.0
                                      then (resSignif * 2.0, resExp - 1)
                                      else (resSignif, resExp)
        in if (e1 `xor` e2) .&. (e1 `xor` resExp) < 0 || (resSignif < 1.0 && resExp == (minBound :: Int64))
           then zero
           else FloatingX finalSignif finalExp

sqrtFX :: FloatingX -> FloatingX
sqrtFX (FloatingX s e)  = FloatingX sX eX where 
    (sX, eX) = sqrtSplitDbl (s, e)

sqrtDX :: Double -> Double
sqrtDX d 
    | d ==0 = 0 
    | isNaN d = 0 
    | isInfinite d = maxDouble
    | d == 1 = 1 
    | otherwise = sqrt d -- actual call to "the floating point square root" {sqrt_fsqrt, sqrt, sqrtC, sqrtLibBF or other }
    
sqrtSplitDbl :: (Double,Int64) -> (Double, Int64) 
sqrtSplitDbl (d, e) 
  | d == 0 = (0,0) 
  | d == 1 = (1,0)
  | even e = (s, fromIntegral $ integerShiftR# (integerFromInt $ fromIntegral e) 1##) -- even 
  | otherwise = (sqrtOf2 * s, fromIntegral $ integerShiftR# (integerFromInt $ fromIntegral e-1) 1##) -- odd 
 where 
    s = sqrtDX d 

foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h sqrt_fsqrt" sqrt_fsqrt :: Double -> Double
foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h sqrtC" sqrtC :: Double -> Double
foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h toLong" toLong :: Double -> CLong -> CLong

compose :: (Double, Int64) -> Maybe Double
compose (d@(D# d#), e) 
    | isNaN d = Nothing --error "Input is NaN"
    | isInfinite d = Nothing -- error "Input is Infinity"
    | ex < 0 = Just $ fromIntegral m `divideDouble` (2^(-ex)) -- this is necessary 
    | otherwise = 
        let result# = encodeDoubleInteger m ex# 
            !(I# ex#) = ex
            result = D# result#
           in if isInfinite result || isNaN result then Nothing else Just result 
    where 
        !(# m, n# #) = decodeDoubleInteger d# 
        ex = I# n# + fromIntegral e 
        
-- | The list is "reversed" i.e. the digits are LSB --> MSB         
integerFrom2ElemW32List :: [Word32] -> Integer
integerFrom2ElemW32List [] = error "integerFrom2ElemW32List : Empty list"
integerFrom2ElemW32List [_] = error "integerFrom2ElemW32List : function needs 2 elems in List"
integerFrom2ElemW32List [0, 0] = 0
integerFrom2ElemW32List [l2, l1] = fromIntegral l2 * radixW32 + fromIntegral l1
integerFrom2ElemW32List _ = error "integerFrom2ElemW32List : Invalid list with more than 2 elems"

{-# INLINE [2] intgrFromRvsrdLst #-}
-- | Integer from a "reversed" list of Word32 digits
intgrFromRvsrdLst :: [Word32] -> Integer 
intgrFromRvsrdLst [x,y] = integerFrom2ElemW32List [y,x]
intgrFromRvsrdLst e = integerFrom2ElemW32List e 

radixW32 :: Integer
radixW32 = 2 ^ finiteBitSize (0 :: Word32)

secndPlaceRadix :: Integer
secndPlaceRadix = radixW32 * radixW32
radixW32Squared :: Integer
radixW32Squared = secndPlaceRadix
radixW32Cubed :: Integer
radixW32Cubed = secndPlaceRadix * radixW32

{-# INLINE [1] double2FloatingX #-}
double2FloatingX :: Double -> FloatingX
double2FloatingX d = let (s, e) = split d in FloatingX s e

-- The maximum integral value that can be unambiguously represented as a
-- Double. Equal to 9,007,199,254,740,991.
{-# INLINE integer2FloatingX #-}
integer2FloatingX :: Integer -> FloatingX
integer2FloatingX i
  | i == 0 = zero
  | i < 0 = error "integer2FloatingX : invalid negative argument"
  -- | i <= maxSafeInteger =  double2FloatingX (fromIntegral i) 
  | itsOKtoUsePlainDoubleCalc =  double2FloatingX (fromIntegral i) 
  | otherwise =  FloatingX s (fromIntegral e_)
  where
    !(D# maxDouble#) = maxDouble
    !(D# iDouble#) = fromIntegral i 
    itsOKtoUsePlainDoubleCalc = isTrue# (iDouble# <## (fudgeFactor## *## maxDouble#)) where fudgeFactor## = 1.00## -- for safety it has to land within maxDouble (1.7*10^308) i.e. tC ^ 2 + tA <= maxSafeInteger
    (i_, e_) = cI2D2 i -- so that i_ is below integral maxDouble
    s = fromIntegral i_

cI2D2 :: Integer -> (Integer, Int)
cI2D2 i | i < 0 = error "CI2D2: invalid negative argument"
cI2D2 0 = (0, 0)
cI2D2 i | i <= maxSafeInteger = (i, 0) 
cI2D2 i = go i 0
  where
    go n e
      | n <= maxUnsafeInteger = (n, e)
      | otherwise = go (n `unsafeShiftR` shiftAmount) (e + shiftAmount)
      where
        exPlus = integerLog10' n - 308 `quot` 10 -- would be dynamic (100-10)
        shiftAmount = max 1 exPlus

largestNSqLTE :: Integer -> Integer -> Integer
largestNSqLTE bot n = bbin bot (n + 1)
  where
    bbin a b
      | a + 1 == b = a
      | otherwise =
          if m * m > n
            then bbin a m
            else bbin m b
      where
        m = (a + b) `div` 2

{-# INLINE [2] split #-}
split :: Double -> (Double, Int64)
split d  = (fromIntegral s, fromIntegral $ I# expInt#) where 
  !(D# d#) = d
  !(# s, expInt# #) = decodeDoubleInteger d# 

{-# INLINE [1] normalize #-}
normalize :: Double -> Double 
normalize x
  | isNormal x = x 
  | x == 0 || isNegativeZero x = minDouble 
  | isInfinite x || isNaN x = error "normalize: Infinite or NaN "
  | isDoubleDenormalized x == 1 = x 
  | isIEEE x  = x 
  | otherwise =
      let !(# m, e# #) = integerDecodeDouble# x#
          n = floatRadix x
          (mantissa, expo) =  normalizeIter (abs (fromIntegral m)) (fromIntegral (I# e#)) n
       in 
            case compose (mantissa, expo) of 
                Just result -> result -- normalized 
                _          -> x  -- return as-is
  where
    !(D# x#) = x 
    normalizeIter = go
      where 
        go m' e' n' 
          | m' >= fromIntegral n' = go (m' / fromIntegral n') (e' + 1) n'
          | m' < 1 = go (m' * fromIntegral n') (e' - 1) n'
          | otherwise = (m', e')

{-# INLINE normalizeFX #-}
normalizeFX :: FloatingX -> FloatingX
normalizeFX (FloatingX d ex) = FloatingX s (ex + e)
  where
    nd = normalize d
    (s, e) = split nd

sqrtOf2 :: Double
sqrtOf2 = 1.4142135623730950488016887242097

maxDouble :: Double
maxDouble = 1.7976931348623157e308

minDouble :: Double
minDouble = 4.9406564584124654e-324 -- Minimum positive normalized value for Double as per IEEE 754

maxSafeInteger :: Integer
maxSafeInteger = 9007199254740991 -- 2^53 -1 this is the max integer that can be represented without losing precision

-- This is approximately 1.8 x 10^308 representable as Double but will lose precision
maxUnsafeInteger :: Integer
maxUnsafeInteger = 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368

-- https://stackoverflow.com/questions/1848700/biggest-integer-that-can-be-stored-in-a-double

{-# INLINE [2] nextUp #-}
nextUp :: Double -> Double
nextUp = NFI.nextUp

{-# INLINE [2] nextDown #-}
nextDown :: Double -> Double
nextDown = NFI.nextDown

{-# INLINE [2] nextUp# #-}
nextUp# :: Double# -> Double#
nextUp# dIn# = dOut# where !(D# dOut#) = NFI.nextUp d where d = D# dIn#

{-# INLINE [2] nextDown# #-}
nextDown# :: Double# -> Double#
nextDown# dIn# = dOut# where !(D# dOut#) = NFI.nextDown d where d = D# dIn#

{-# INLINE [2] nextUpFX #-}
nextUpFX :: FloatingX -> FloatingX
nextUpFX (FloatingX s e)
  | s == 0.0 = minValue
  | otherwise = if interimS >= 2.0 then FloatingX (interimS / 2) (e + 1) else FloatingX interimS e
  where
    interimS = nextUp s

{-# INLINE [2] nextDownFX #-}
nextDownFX :: FloatingX -> FloatingX
nextDownFX x@(FloatingX s e)
  | s == 0.0 || x == minValue = zero
  | otherwise = if interimS < 1.0 then FloatingX (interimS * 2) (e - 1) else FloatingX interimS e
  where
    interimS = nextDown s

-- End isqrtB ****************************************************************
-- End isqrtB ****************************************************************

