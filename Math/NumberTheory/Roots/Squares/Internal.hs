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
-- import Control.Monad.ST (runST)
-- import Data.Number.MPFR (RoundMode)
-- import qualified Data.Number.MPFR as M
-- import Data.Number.MPFR.Instances.Up ()
-- import qualified Data.Number.MPFR.Mutable as MM
import Debug.Trace 
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
import qualified Data.Vector.Unboxed as VU (Vector,(//), slice, unsafeSlice,length, replicate, unsafeHead, cons, snoc, unsnoc, uncons, empty, ifoldl', singleton, fromList, null, length, splitAt, head, toList, force)
import Data.Int (Int64)
import Foreign.C.Types ( CLong(..) )
import qualified Numeric.Floating.IEEE as NFI (nextDown, nextUp)
import Data.Word (Word32, Word64)
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
import qualified Data.Monoid as VU
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
isqrtB n = fromInteger . ni__ . fi__ . dgts__ . fromIntegral $ n

dgts__ :: Integer -> VU.Vector Word32
dgts__ n | n < 0 = error "dgts_: Invalid negative argument"
dgts__ 0 = VU.singleton 0 
dgts__ n = mkIW32__ n

-- | First Iteration
fi__ :: VU.Vector Word32 -> Itr
fi__ vec 
  | VU.length vec == 1 && VU.unsafeHead vec == 0 = Itr VU.empty 0 VU.empty 0
  | VU.null vec = error "fi_: Invalid Argument null vector "
  | otherwise = Itr w32Vec l' yCurrArr remInteger
    where
      !((w32Vec, dxsVec'), l') =
        let !l = VU.length vec 
            !(headVec1, lastVec1) = VU.splitAt (l - 1) vec
            !(headVec2, lastVec2) = VU.splitAt (l - 2) vec
        in if even l then ((VU.force headVec2,VU.force lastVec2), l - 2) else ((VU.force headVec1, VU.force $ VU.snoc lastVec1 0), l - 1)
      !vInteger = intgrFromRvsrd2ElemVec dxsVec'
      !y1 =
        let !searchFrom = if vInteger >= radixW32Squared then radixW32Squared else 0 -- heuristic
        in hndlOvflwW32 (largestNSqLTE searchFrom vInteger)-- overflow trap
      --yCurrArr = VU.singleton (fromIntegral y1)
      !yCurrArr = initSqRootVec l' y1 
      !remInteger =  hndlOvflwW32 $ vInteger - y1 * y1

-- | handle overflow 
{-# INLINE hndlOvflwW32 #-}
{-# SPECIALIZE hndlOvflwW32 :: Int64 -> Int64 #-}
hndlOvflwW32 :: Integral a => a -> a 
hndlOvflwW32 i = if i == maxW32 then pred maxW32 else i where maxW32 = fromIntegral radixW32

{-# INLINE initSqRootVec #-}
initSqRootVec :: Int -> Integer -> VU.Vector Word32        
initSqRootVec l' lsb = let 
          !rootLength  = (l' + 2) `quot` 2 
          !rootVec = VU.replicate rootLength 0
        in rootVec VU.// [(rootLength - 1, fromIntegral lsb)]

{-# INLINE updtSqRootVec #-}      
updtSqRootVec :: Int -> Int64 -> VU.Vector Word32 -> VU.Vector Word32
updtSqRootVec position yTildeFinal yCurrArr = yCurrArr VU.// [(position, fromIntegral yTildeFinal)]

-- | Iteration loop data 
data Itr = Itr {vecW32_ :: VU.Vector Word32, l_ :: Int, yCurrArr_ :: VU.Vector Word32, iRem_ :: Integer} deriving (Eq, Show)

-- | Next Iterations till array empties out
ni__ :: Itr -> Integer
ni__ loopVals
  | VU.null w32Vec = vectorToInteger yCurrArr
  | otherwise =
      let 
          !position = pred $ l `quot` 2 -- last pair is position "0"
          !(residuali32Vec, nxtTwoDgtsVec) = VU.splitAt (l - 2) w32Vec
          !tAInteger = (iRem * secndPlaceRadix) + intgrFromRvsrd2ElemVec (VU.force nxtTwoDgtsVec)
          yCurrWorkingCopy  = VU.force (VU.unsafeSlice (position+1) (VU.length yCurrArr - (position+1)) yCurrArr) 
          !tBInteger' = vectorToInteger yCurrWorkingCopy
          -- !tBInteger' = vectorToInteger yCurrArr
          !tCInteger' = radixW32 * tBInteger' -- sqrtF previous digits being scaled right here
          !inArgs = IterArgs tAInteger tBInteger' tCInteger'
          yTilde_ = nxtDgt_ inArgs
          IterRes yTildeFinal remFinal = computeRem_ inArgs yTilde_ position
          --yCurrArrUpdated = VU.cons (fromIntegral yTildeFinal) yCurrArr
          !yCurrArrUpdated = updtSqRootVec position yTildeFinal yCurrArr
       in ni__ $ Itr (VU.force residuali32Vec) (l-2) yCurrArrUpdated remFinal
  where 
          !l = l_ loopVals 
          !iRem = iRem_ loopVals 
          !w32Vec = vecW32_ loopVals 
          !yCurrArr = yCurrArr_ loopVals

-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm 
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgt_ :: IterArgs -> Int64 
nxtDgt_ inArgs
    | tA_ == 0 = 0 
    | itsOKtoUsePlainDoubleCalc = floor (nextUp $ D# (nextUp# tA# /## nextDown# (sqrtDouble# (nextDown# rad#) +## nextDown# tC#))) 
    | otherwise = let  
          !tAFX = normalizeFX $ integer2FloatingX tA_
          !tCFX = normalizeFX $ integer2FloatingX tC_
          !radFX = tCFX !* tCFX !+ tAFX
        in
          hndlOvflwW32 (floorX (nextUpFX (nextUpFX tAFX !/ nextDownFX (sqrtFX (nextDownFX radFX) !+ nextDownFX tCFX))))
 where 
    !tA_ = tA inArgs 
    !tC_ = tC inArgs
    !tA# = integerToDouble# tA_
    !tC# = integerToDouble# tC_
    !rad# = fmaddDouble# tC# tC# tA#
    !(D# maxDouble#) = maxDouble
    itsOKtoUsePlainDoubleCalc = isTrue# (rad# <## (fudgeFactor## *## maxDouble#)) where fudgeFactor## = 1.00## -- for safety it has to land within maxDouble (1.7*10^308) i.e. tC ^ 2 + tA <= maxSafeInteger

-- | compute the remainder. It may be that the "digit" may need to be reworked
-- that happens in handleRems_
computeRem_ :: IterArgs -> Int64 -> Int -> IterRes
computeRem_ inArgs yTilde_ pos =
  let !rTrial = calcRemainder inArgs yTilde_
   in handleRems_ pos inArgs (IterRes yTilde_ rTrial)

-- | if the remainder is negative it's a clear sign to decrement the candidate digit
-- if it's positive but far larger in length of the current accumulated root, then also it signals a need for current digit rework 
-- if it's positive and far larger in size then also the current digit rework 
handleRems_ :: Int -> IterArgs -> IterRes -> IterRes
handleRems_ pos inArgs inVals
  | ri_ == 0 = inVals
  | (ri_ > 0) && noExcessLength = inVals -- all ok just continue no need for any other check if pos =0 then this check is not useful
  | (ri_ < 0) && (yi > 0) = IterRes nextDownDgt0 $ calcRemainder inArgs nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | (ri_ > 0) && (pos > 0) && excessLengthBy3 = IterRes yi adjustedRemainder3 -- handleRems (pos, yCurrListReversed, yi, adjustedRemainder3, tA, tB)
  | (ri_ > 0) && firstRemainderBoundCheckFail = IterRes nextUpDgt1 $ calcRemainder inArgs nextUpDgt1
  | (ri_ > 0) && secondRemainderBoundCheckFail = IterRes nextUpDgt2 $ calcRemainder inArgs nextUpDgt2
  | otherwise = inVals
  where
    b = radixW32
    riCurrSqrtRatio = ri_ `quot` currSqrt
    noExcessLength = riCurrSqrtRatio < 2 -- quick escape all good
    {-  excessLengthBy3 = lenCurrRemainder >= lenCurrSqrt + 3
        lenCurrRemainder = 1 + integerLogBase' b ri
        lenCurrSqrt = 1 + integerLogBase' b yi
     -}
    excessLengthBy3 = integerLogBase' b (ri_`div` fromIntegral yi) >= 3
    firstRemainderBoundCheckFail = not (isValidRemainder1 ri_ currSqrt pos)
    secondRemainderBoundCheckFail = not (isValidRemainder2 ri_ currSqrt pos)
    !currSqrt = tC inArgs + fromIntegral yi
    modulus3 = radixW32Cubed -- b^3
    adjustedRemainder3 = ri_ `mod` modulus3
    !yi = yTilde inVals 
    !ri_ = ri inVals
    nextDownDgt0 = findNextDigitDown inArgs inVals pos yi 0 isValidRemainder0
    nextUpDgt1 = findNextDigitUp inArgs inVals pos yi (fromIntegral radixW32 - 1) isValidRemainder1
    nextUpDgt2 = findNextDigitUp inArgs inVals pos yi (fromIntegral radixW32 - 1) isValidRemainder2

data IterArgs = IterArgs {tA :: Integer, tB :: Integer, tC :: Integer} deriving (Eq,Show)
data IterRes = IterRes {yTilde :: Int64, ri :: Integer} deriving (Eq, Show) 

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
calcRemainder :: IterArgs -> Int64 -> Integer
calcRemainder tArgs dgt = tA tArgs - ((2 * tC tArgs * iDgt) + iDgt ^ (2 :: Int)) where iDgt = fromIntegral dgt

findNextDigitUp :: IterArgs -> IterRes -> Int -> Int64 -> Int64 -> (Integer -> Integer -> Int -> Bool) -> Int64 
findNextDigitUp inArgs inRes pos curr high checkFn
      | curr >= ceilNxtDgtUp  = ceilNxtDgtUp
      | curr > high = error "findNextDigitUp : no valid digit found (curr>high)"
      | curr == high = if checkFn (fromIntegral curr) yUpdated pos then curr - 1 else error "findNextDigitUp : no valid digit found (curr=high)"
      | otherwise = 
          let !mid = (curr + high) `div` 2 
              !testRem = calcRemainder inArgs mid 
              !testRoot = tC inArgs + fromIntegral mid
          in if checkFn testRem testRoot pos then 
              let validLower = tryRange Higher inArgs pos (fromIntegral curr) (fromIntegral mid-1) checkFn 
              in  fromMaybe (fromIntegral mid) (fromIntegral <$> validLower) 
             else
                findNextDigitUp inArgs inRes pos (mid+1) high checkFn
    where 
            !ceilNxtDgtUp = fromIntegral (pred radixW32) 
            !yUpdated = tC inArgs + fromIntegral curr

findNextDigitDown :: IterArgs -> IterRes -> Int -> Int64 -> Int64 -> (Integer -> Integer -> Int -> Bool) -> Int64
findNextDigitDown tArgs inRes pos curr low checkFn
  | curr < low = error "findNextDigitDown : no valid digit found (curr<low) "
  | curr == low = if checkFn (fromIntegral curr) yUpdated pos then curr else error "findNextDigitDown : no valid digit found (curr=low) "
  | curr == yi = if checkFn (fromIntegral yi-1) yUpdated pos then yi-1 else findNextDigitDown tArgs inRes pos (yi - 2) low checkFn
  | otherwise =
      let !mid = (low + curr ) `div` 2
          !testRem = calcRemainder tArgs mid
          !testRoot = tC tArgs + fromIntegral mid 
       in if checkFn testRem testRoot pos
            then
              let !validHigher = tryRange Lower tArgs pos (fromIntegral mid+1) (fromIntegral curr) checkFn 
               in fromMaybe mid validHigher 
            else
              findNextDigitDown tArgs inRes pos (mid - 1) low checkFn
  where
    !yUpdated = tC tArgs + fromIntegral curr 
    !yi = yTilde inRes 

data RangeSearch =  Lower | Higher deriving Eq 
tryRange :: RangeSearch -> IterArgs -> Int -> Integer -> Integer -> (Integer -> Integer -> Int -> Bool )  -> Maybe Int64     
tryRange rS tArgs pos lowr highr checkFn 
      | lowr > highr = Nothing
      | otherwise =
          let !mid = (lowr + highr) `div` 2
              !testRm = calcRemainder tArgs $ fromIntegral mid
              !testRt = tC tArgs + mid 
           in if checkFn testRm testRt pos
                then Just (fromIntegral mid) 
                else if rS == Lower then tryRange Lower tArgs pos lowr (mid - 1) checkFn else tryRange Higher tArgs pos (mid + 1) highr checkFn

-- | helper functions


{-# INLINE mkIW32__ #-}
-- spit out the unboxed Vector as-is from digitsUnsigned which comes in reversed format.
mkIW32__ :: Integer -> VU.Vector Word32
mkIW32__ 0 = VU.singleton 0 -- safety
mkIW32__ i = let
    !b = fromIntegral radixW32 :: Word
    !n = fromInteger i  
   in VU.fromList $ wrd2wrd32 (digitsUnsigned b n)

{-# INLINE wrd2wrd32 #-}
wrd2wrd32 :: [Word] -> [Word32]
wrd2wrd32 xs = fromIntegral <$> xs
    

{-# INLINE vectorToInteger #-}
-- Function to convert a vector of Word32 values to an Integer with base 2^32 (radixw32)
vectorToInteger :: VU.Vector Word32 -> Integer
vectorToInteger = VU.ifoldl' (\acc i w -> acc + fromIntegral w * radixW32 ^ i) 0 

{-# INLINE largestNSqLTE #-}
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
{-# INLINE intgrFromRvsrd2ElemVec #-}

-- | Integer from a "reversed" list of Word32 digits
intgrFromRvsrd2ElemVec :: VU.Vector Word32 -> Integer
intgrFromRvsrd2ElemVec v2ElemW32s =
  let (l1, l2) = case (VU.uncons v2ElemW32s, VU.unsnoc v2ElemW32s) of
        (Nothing, _) -> error "intgrFromRvsrd2ElemVec : Empty Vector"
        (_, Nothing) -> error "intgrFromRvsrd2ElemVec : Empty Vector"
        (Just u, Just v) -> (fst u, snd v)
   in fromIntegral l2 * radixW32 + fromIntegral l1

radixW32 :: Integer
radixW32 = 2 ^ finiteBitSize (0 :: Word32)

secndPlaceRadix :: Integer
secndPlaceRadix = radixW32 * radixW32

radixW32Squared :: Integer
radixW32Squared = secndPlaceRadix

radixW32Cubed :: Integer
radixW32Cubed = secndPlaceRadix * radixW32

-- | Custom double and its arithmetic        
data FloatingX = FloatingX {signif :: !Double, expnnt :: !Int64} deriving (Eq, Show) -- ! for strict data type

{-# INLINE floorX #-}
{-# SPECIALIZE floorX :: FloatingX -> Integer #-}
floorX :: Integral a => FloatingX -> a
floorX (FloatingX s e) = case fx2Double (FloatingX s e) of
  Just d -> floor d
  _ -> fromIntegral $ toLong s (fromIntegral e)

zero :: FloatingX
zero = FloatingX 0.0 (minBound :: Int64)
minValue :: FloatingX
minValue = FloatingX 1.0 0

{-# INLINE (!+) #-}
(!+) :: FloatingX -> FloatingX -> FloatingX
(!+) x y = x `add` y

{-# INLINE (!*) #-}
(!*) :: FloatingX -> FloatingX -> FloatingX
(!*) x y = x `mul` y

{-# INLINE (!/) #-}
(!/) :: FloatingX -> FloatingX -> FloatingX
(!/) x y = x `divide` y

{-# INLINE add #-}
add :: FloatingX -> FloatingX -> FloatingX
add (FloatingX 0.0 _) x = x
add x (FloatingX 0.0 _) = x
add a@(FloatingX signifA expA) b@(FloatingX signifB expB)
  | expA > expB = combine a b
  | expA < expB = combine b a
  | otherwise = FloatingX (signifA + signifB) expA
  where
    combine big@(FloatingX signifBig expBig) little@(FloatingX signifLittle expLittle) =
      let !scale = expLittle - expBig
          !scaledLittle = signifLittle * 2 ^^ scale
          !resSignif = signifBig + scaledLittle
       in if resSignif >= 2.0
            then FloatingX (resSignif / 2.0) (expBig + 1)
            else FloatingX resSignif expBig

{-# INLINE mul #-}
mul :: FloatingX -> FloatingX -> FloatingX
mul (FloatingX 0.0 _) _ = zero
mul _ (FloatingX 0.0 _) = zero
mul (FloatingX 1.0 0) b = b
mul a (FloatingX 1.0 0) = a
mul (FloatingX signifA expA) (FloatingX signifB expB) =
  let !resExp = expA + expB
      !resSignif = signifA * signifB
   in if resSignif >= 2.0
        then FloatingX (resSignif / 2.0) (resExp + 1)
        else FloatingX resSignif resExp

{-# INLINE divide #-}
divide :: FloatingX -> FloatingX -> FloatingX
divide n@(FloatingX s1 e1) d@(FloatingX s2 e2)
    | d == FloatingX 1.0 0 = n 
    | s1 == 0.0 = zero
    | s2 == 0.0 = error "divide: error divide by zero " 
    | otherwise = 
        let !resExp = e1 - e2
            !resSignif = s1 / s2
            !(finalSignif, finalExp) = if resSignif < 1.0
                                      then (resSignif * 2.0, resExp - 1)
                                      else (resSignif, resExp)
        -- in if (e1 `xor` e2) .&. (e1 `xor` resExp) < 0 || (resSignif < 1.0 && resExp == (minBound :: Integer))
        in if (e1 `xor` e2) .&. (e1 `xor` resExp) < 0 || (resSignif < 1.0 && resExp <= 0 )
           then zero
           else FloatingX finalSignif finalExp

{-# INLINE sqrtFX #-}
sqrtFX :: FloatingX -> FloatingX
sqrtFX (FloatingX s e)  = FloatingX sX eX where 
    !(sX, eX) = sqrtSplitDbl (FloatingX s e) 

sqrtSplitDbl :: FloatingX -> (Double, Int64) 
sqrtSplitDbl (FloatingX d e) 
  | d == 0 = (0,0) 
  | d == 1 = (1,0)
  | even e = (s,fromIntegral $ integerShiftR# (integerFromInt $ fromIntegral e) 1##) -- even 
  | otherwise = (sqrtOf2 * s, fromIntegral $ integerShiftR# (integerFromInt $ fromIntegral e-1) 1##) -- odd 
 where 
    !s = sqrtDX d 
{-# INLINEABLE sqrtSplitDbl #-}

sqrtDX :: Double -> Double
sqrtDX d
  | d == 0 = 0
  | isNaN d = 0
  | isInfinite d = maxDouble
  | d == 1 = 1
  | otherwise = sqrtC d -- actual call to "the floating point square root" {sqrt_fsqrt, sqrt, sqrtC, sqrtLibBF, sqrthpmfr or other }

-- sqrtDoublehmpfr :: Double -> Double
-- sqrtDoublehmpfr d = M.toDouble M.Near $ M.sqrt M.Near 1000 (M.fromDouble M.Near 1000 d)

foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h sqrt_fsqrt" sqrt_fsqrt :: Double -> Double
foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h sqrtC" sqrtC :: Double -> Double
foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h toLong" toLong :: Double -> CLong -> CLong

fx2Double :: FloatingX -> Maybe Double
fx2Double (FloatingX d@(D# d#) e)
    | isNaN d = Nothing --error "Input is NaN"
    | isInfinite d = Nothing -- error "Input is Infinity"
    | ex < 0 = Just $ fromIntegral m `divideDouble` (2^(-ex)) -- this is necessary 
    | otherwise = 
        let result# = encodeDoubleInteger m ex# 
            !(I# ex#) = ex
            !result = D# result#
           in if isInfinite result || isNaN result then Nothing else Just result 
    where 
        !(# m, n# #) = decodeDoubleInteger d# 
        !ex = I# n# + fromIntegral e 
{-# INLINEABLE fx2Double #-}

{-# INLINE double2FloatingX #-}
double2FloatingX :: Double -> FloatingX
double2FloatingX d = let 
   !(s, e) = split d 
  in FloatingX s e

-- The maximum integral value that can be unambiguously represented as a
-- Double. Equal to 9,007,199,254,740,991.
{-# INLINE integer2FloatingX #-}
integer2FloatingX :: Integer -> FloatingX
integer2FloatingX i
  | i == 0 = zero
  | i < 0 = error "integer2FloatingX : invalid negative argument"
  | itsOKtoUsePlainDoubleCalc =  double2FloatingX (fromIntegral i) 
  | otherwise =  let 
      !(i_, e_) = cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble
      !s = fromIntegral i_
    in FloatingX s (fromIntegral e_)
  where
    !(D# maxDouble#) = maxDouble
    !(D# iDouble#) = fromIntegral i 
    itsOKtoUsePlainDoubleCalc = isTrue# (iDouble# <## (fudgeFactor## *## maxDouble#)) where fudgeFactor## = 1.00## -- for safety it has to land within maxDouble (1.7*10^308) i.e. tC ^ 2 + tA <= maxSafeInteger

{-# INLINE cI2D2 #-}
cI2D2 :: Integer -> (Integer, Int)
cI2D2  = cI2D2'
    where 
      cI2D2' 0 = (0, 0)
      cI2D2' i | i <= maxSafeInteger = (i, 0)
      cI2D2' i = go 0 i
          where
            go e n
              | n <= maxUnsafeInteger = (n, e)
              | otherwise = go (e + shiftAmount) (n `unsafeShiftR` shiftAmount) 
              where
                exPlus = integerLog10' n - 308 `quot` 100 -- would be dynamic (100-10)
                shiftAmount = max 1 exPlus


{-# INLINE split #-}
split :: Double -> (Double, Int64)
split d  = (fromIntegral s, fromIntegral $ I# expInt#) where 
  !(D# d#) = d
  !(# s, expInt# #) = decodeDoubleInteger d# 

 -- | Normalising functions for doubles and our custom double  
{-# INLINE normalize #-}
normalize :: Double -> Double 
normalize x
  | isNormal x = x 
  | x == 0 || isNegativeZero x = minDouble 
  | isInfinite x || isNaN x = error "normalize: Infinite or NaN "
  | isDoubleDenormalized x == 1 = x 
  | isIEEE x  = x 
  | otherwise =
      let !(# m, e# #) = integerDecodeDouble# x#
          !n = floatRadix x
          !(mantissa, expo) =  normalizeIter (abs (fromIntegral m)) (fromIntegral (I# e#)) n
       in 
            case fx2Double (FloatingX mantissa expo) of 
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

-- | Some Constants 
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

-- | Floating Point rounding/nextup funxctions 
{-# INLINE nextUp #-}
nextUp :: Double -> Double
nextUp = NFI.nextUp

{-# INLINE nextDown #-}
nextDown :: Double -> Double
nextDown = NFI.nextDown

{-# INLINE nextUp# #-}
nextUp# :: Double# -> Double#
nextUp# dIn# = let 
    !d = D# dIn#
    !(D# dOut#) = NFI.nextUp d
  in dOut# 

{-# INLINE nextDown# #-}
nextDown# :: Double# -> Double#
nextDown# dIn# = let 
        !d = D# dIn#
        !(D# dOut#) = NFI.nextDown d 
    in dOut# 

{-# INLINE nextUpFX #-}
nextUpFX :: FloatingX -> FloatingX
nextUpFX (FloatingX s e)
  | s == 0.0 = minValue
  | otherwise = let 
     !interimS = nextUp s
    in
      if interimS >= 2.0 then FloatingX (interimS / 2) (e + 1) else FloatingX interimS e

{-# INLINE nextDownFX #-}
nextDownFX :: FloatingX -> FloatingX
nextDownFX x@(FloatingX s e)
  | s == 0.0 || x == minValue = zero
  | otherwise = let 
      !interimS = nextDown s
     in 
        if interimS < 1.0 then FloatingX (interimS * 2) (e - 1) else FloatingX interimS e

-- End isqrtB ****************************************************************
-- End isqrtB ****************************************************************

