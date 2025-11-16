{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE UnboxedTuples #-}

-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump=simpl or ddump-asm dumps else not
-- removed -fexpose-all-unfoldings may not necessarily help improve max performance. See https://well-typed.com/blog/2024/04/choreographing-specialization-pt1/
-- {-# OPTIONS_GHC -O2 -threaded -optl-m64  -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr  -fstrictness -funbox-small-strict-fields -fmax-worker-args=32 -optc-O3 -optc-ffast-math #-}

-- |
-- Module:      Math.NumberTheory.Roots.Squares.Internal
-- Copyright:   (c) 2011 Daniel Fischer, 2016-2020 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Internal functions dealing with square roots. End-users should not import this module.
-- {-# OPTIONS -ddump-simpl -ddump-to-file #-}
module Math.NumberTheory.Utils.ArthMtic_
  ( 
    powBigNat#,
    _evenInt64#,
    _oddInt64#,
    _even,
    _odd,
    nextDown#,
    nextUp#,
    updateDouble#,
    split,
    split#,
    fromInt64,
    sqrtOf2,
    double,
    radixW32,
    hndlOvflwW32,
    hndlOvflwW32##,
    hndlOvflwI32##,
    secndPlaceW32Radix,
    word64FromRvsrd2ElemList#,
    largestNSqLTEEven##,
    largestNSqLTEOdd##,
    maxDouble,
    maxSafeInteger,
    maxUnsafeInteger,
    pred,
    lenRadixW32,
    cI2D2_,
    convNToDblExp,
    bnToFxGtWord,
    bnToFxGtWord#,
    word64From2ElemList#,
    radixW32Squared,
    bnConst#
  )
where

-- \*********** BEGIN NEW IMPORTS

import Data.Bits (complement, finiteBitSize, shiftR, unsafeShiftL, unsafeShiftR, (.&.), (.|.))
import Data.Bits.Floating (nextDown, nextUp)
import Data.List (unfoldr)
import Data.Maybe (fromMaybe)
import Data.Word (Word32)
import GHC.Num.BigNat (BigNat (..), bigNatOne#, bigNatZero#, bigNatShiftL#)
import GHC.Exts
  ( Double (..),
    Double#,
    leWord#,
    Int (..),
    Int#,
    Int64#,
    Word (..),
    Word#,
    Word64#,
    and#,
    build,
    eqInt64#,
    eqWord#,
    eqWord64#,
    fmaddDouble#,
    geInt64#,
    gtInt64#,
    int2Double#,
    int2Word#,
    int64ToInt#,
    int64ToWord64#,
    intToInt64#,
    isTrue#,
    leInt64#,
    minusWord#,
    neWord#,
    not#,
    or#,
    plusInt64#,
    plusWord#,
    plusWord64#,
    quotInt64#,
    quotRemWord#,
    remInt64#,
    sqrtDouble#,
    subInt64#,
    subWord64#,
    timesInt64#,
    timesWord#,
    timesWord64#,
    uncheckedShiftL#,
    uncheckedShiftRL#,
    word2Double#,
    word2Int#,
    word32ToWord#,
    word64ToInt64#,
    wordToWord64#,
    (*##),
    (**##),
    (+#),
    (+##),
    (-#),
    (/##),
    (/=#),
    (<#),
    (<##),
    (==##),
    (>=#),
    (>=##),
  )
import GHC.Float (floorDouble)
import GHC.Int (Int32, Int64 (I64#))
import GHC.Integer (decodeDoubleInteger, encodeDoubleInteger, shiftRInteger)
import GHC.Integer.Logarithms (wordLog2#)
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatEncodeDouble#, bigNatIndex#, bigNatIsZero, bigNatLeWord#, bigNatLog2, bigNatLog2#, bigNatShiftR, bigNatShiftR#, bigNatSize#)
import GHC.Num.Integer (integerLog2#, integerLogBase#, integerLogBaseWord)
import GHC.Word (Word32 (..), Word64 (..))
import Math.NumberTheory.Utils.ShortCircuit_ (firstTrueOf)
import Numeric.Natural (Natural)
import Prelude hiding (pred)

-- *********** END NEW IMPORTS

-- | HELPER functions

-- powBigNat# :: Int# -> BigNat#
-- Compute radixW32 ^ p as a BigNat# by shifting 1 << (32 * p)
-- Requires `bigNatShiftL#` and GHC.Prim primops like (*#), (<=#), isTrue# in scope.
powBigNat# :: Word# -> BigNat#
powBigNat# p#
  | isTrue# (p# `leWord#` 0##) = bnConst# 1
  | otherwise           = bigNatShiftL# (bnConst# 1) (p# `timesWord#` 32##)
{-# INLINE powBigNat# #-}

bnConst# :: Int -> BigNat#
bnConst# i = case i of 
      0 -> bigNatZero# (# #)
      1 -> bigNatOne# (# #)
{-# INLINE bnConst# #-}

-- | Word64# from a "reversed" List of at least 1 and at most 2 Word32 digits
word64FromRvsrd2ElemList# :: [Word32] -> Word64#
word64FromRvsrd2ElemList# [] = error "word64FromRvsrd2ElemList# : null list"
word64FromRvsrd2ElemList# [llsb] = word64FromRvsrdTuple# (llsb, 0) 4294967296#Word64
word64FromRvsrd2ElemList# [llsb, lmsb] = word64FromRvsrdTuple# (llsb, lmsb) 4294967296#Word64
word64FromRvsrd2ElemList# (_ : _ : _) = error "word64FromRvsrd2ElemList# : more than 2 elems list"
{-# INLINE word64FromRvsrd2ElemList# #-}

-- | Word64# from a "normal" List of at least 1 and at most 2 Word32 digits
word64From2ElemList# :: [Word32] -> Word64#
word64From2ElemList# [] = error "word64From2ElemList# : null list"
word64From2ElemList# [llsb] = word64FromRvsrdTuple# (llsb, 0) 4294967296#Word64
word64From2ElemList# [lmsb,llsb] = word64FromRvsrdTuple# (llsb, lmsb) 4294967296#Word64
word64From2ElemList# (_ : _ : _) = error "word64From2ElemList# : more than 2 elems list"
{-# INLINE word64From2ElemList# #-}

-- | Spit out the Word32 List from digits which comes in normal format. MSB...LSB
mkIW32Lst_ :: Integer -> Word -> [Word32]
mkIW32Lst_ 0 _ = [0] -- safety
mkIW32Lst_ i b = wrd2wrd32 (iToWrdListBase_ i b) -- using the normal format digits function



--- END helpers
--- BEGIN Core numeric helper functions
--- ***********************************

{-# INLINE [0] integralFromRvsrdTuple #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Integer -> Integer #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Word64 -> Word64 #-}

-- | Integer from a "reversed" tuple of Word32 digits
-- Base 4.21 shipped with ghc 9.12.1 had a toInteger improvement : https://github.com/haskell/core-libraries-committee/issues/259
integralFromRvsrdTuple :: (Integral a) => (Word32, Word32) -> a -> a
integralFromRvsrdTuple (0, 0) 0 = 0
integralFromRvsrdTuple (0, lMSB) base = fromIntegral lMSB * base
integralFromRvsrdTuple (lLSB, 0) _ = fromIntegral lLSB
integralFromRvsrdTuple (lLSB, lMSB) base = fromIntegral lMSB * base + fromIntegral lLSB


{-# INLINE [0] integralFromTuple #-}
{-# SPECIALIZE integralFromTuple :: (Word32, Word32) -> Integer -> Integer #-}
{-# SPECIALIZE integralFromTuple :: (Word32, Word32) -> Word64 -> Word64 #-}
integralFromTuple :: (Integral a) => (Word32, Word32) -> a -> a
integralFromTuple (lMSB, lLSB) = integralFromRvsrdTuple (lLSB, lMSB)


-- | Integer from a "reversed" tuple of Word32 digits
-- Base 4.21 shipped with ghc 9.12.1 had a toInteger improvement : https://github.com/haskell/core-libraries-committee/issues/259
intgrFromRvsrdTuple :: (Word32, Word32) -> Integer -> Integer
intgrFromRvsrdTuple (0, 0) 0 = 0
intgrFromRvsrdTuple (0, lMSB) base = toInteger lMSB * base
intgrFromRvsrdTuple (lLSB, 0) _ = toInteger lLSB
intgrFromRvsrdTuple (lLSB, lMSB) base = toInteger lMSB * base + toInteger lLSB

{-# INLINE word64FromRvsrdTuple #-}

-- | Word64 from a "reversed" tuple of Word32 digits
word64FromRvsrdTuple :: (Word32, Word32) -> Word64 -> Word64
word64FromRvsrdTuple (0, 0) 0 = 0
word64FromRvsrdTuple (0, lMSB) base = fromIntegral lMSB * base
word64FromRvsrdTuple (lLSB, 0) _ = fromIntegral lLSB
word64FromRvsrdTuple (lLSB, lMSB) base = fromIntegral lMSB * base + fromIntegral lLSB

{-# INLINE word64FromRvsrdTuple# #-}

-- | Word64# from a "reversed" tuple of Word32 digits
word64FromRvsrdTuple# :: (Word32, Word32) -> Word64# -> Word64#
word64FromRvsrdTuple# (0, 0) _ = 0#Word64
word64FromRvsrdTuple# (0, W32# lMSB#) base# = wordToWord64# (word32ToWord# lMSB#) `timesWord64#` base#
word64FromRvsrdTuple# (W32# lLSB#, 0) _ = wordToWord64# (word32ToWord# lLSB#)
word64FromRvsrdTuple# (W32# lLSB#, W32# lMSB#) base# = (wordToWord64# (word32ToWord# lMSB#) `timesWord64#` base#) `plusWord64#` wordToWord64# (word32ToWord# lLSB#)

{-# INLINE doubleFromRvsrdTuple #-}

-- | double from a "reversed" tuple of Word32 digits
doubleFromRvsrdTuple :: (Word32, Word32) -> Integer -> Double
doubleFromRvsrdTuple (l1, l2) base = fromIntegral l2 * fromIntegral base + fromIntegral l1

{-# INLINE largestNSqLTEOdd #-}
largestNSqLTEOdd :: Word64 -> Word64
largestNSqLTEOdd i = floorDouble (sqrt (fromIntegral i) :: Double)

{-# INLINE largestNSqLTEEven #-}
largestNSqLTEEven :: Word64 -> Word64
largestNSqLTEEven i = let d_ = nextUp (fromIntegral i :: Double) in floorDouble (nextUp (sqrt d_))

{-# INLINE largestNSqLTEOdd## #-}
largestNSqLTEOdd## :: Word64# -> Word64#
largestNSqLTEOdd## w# = case floorDouble (sqrt (fromIntegral (W64# w#)) :: Double) of (W64# r#) -> r#

{-# INLINE largestNSqLTEEven## #-}
largestNSqLTEEven## :: Word64# -> Word64#
largestNSqLTEEven## w# =
  let !d_ = nextUp (fromIntegral (W64# w#) :: Double)
      !(W64# r#) = floorDouble (nextUp (sqrt d_))
   in r#

-- | handle overflow
{-# INLINE [0] hndlOvflwW32 #-} -- does delaying inlining to phase 0 make a significant difference?
{-# SPECIALIZE hndlOvflwW32 :: Integer -> Integer #-}
{-# SPECIALIZE hndlOvflwW32 :: Word64 -> Word64 #-}
hndlOvflwW32 :: (Integral a) => a -> a
hndlOvflwW32 i = if i == maxW32 then pred maxW32 else i where maxW32 = radixW32

{-# INLINE hndlOvflwW32## #-}
hndlOvflwW32## :: Word64# -> Word64#
hndlOvflwW32## w64# = if isTrue# (w64# `eqWord64#` maxW32#) then predmaxW32# else w64#
  where
    !(W64# maxW32#) = radixW32
    !(W64# predmaxW32#) = predRadixW32

{-# INLINE hndlOvflwI32## #-}
hndlOvflwI32## :: Int64# -> Int64#
hndlOvflwI32## i64# = if isTrue# (i64# `eqInt64#` maxW32#) then predmaxW32# else i64#
  where
    !(I64# maxW32#) = radixW32
    !(I64# predmaxW32#) = predRadixW32

{-# INLINE radixW32Length #-} -- this works
radixW32Length :: Integer -> Word
radixW32Length n
  | n == 0 = 1
  | otherwise = integerLogBaseWord radixW32 n + 1

{-# INLINE wrd2wrd32 #-}
wrd2wrd32 :: [Word] -> [Word32]
wrd2wrd32 xs = fromIntegral <$> xs


{-# INLINE iToWrdListBase_ #-}
iToWrdListBase_ :: Integer -> Word -> [Word]
iToWrdListBase_ 0 _ = [0]
-- iToWrdListBase_ i b = digits b (fromIntegral i) -- digits come in normal format MSB --> LSB //FIXME big bug here. 
-- iToWrdListBase_ i b = reverse $ digitsUnsigned b (fromIntegral i) -- digits come in normal format MSB --> LSB //FIXME reverse defeats the purpose no longer lazy. Evaluated !
iToWrdListBase_ i b = digitsInOrder (fromIntegral i) b -- digits come in normal format MSB --> LSB //FIXME reverse defeats the purpose no longer lazy. Evaluated !

-- | this is not lazy and will definitely be fully eagerly evaluated !!!
digitsInOrder :: (Integral a) => a -> Word -> [Word]
digitsInOrder _ base | base <= 1 = error "Base must be greater than 1"
digitsInOrder n base = map fromInteger $ go (toInteger n) (highestPower (toInteger n) (toInteger base))
  where
    -- Compute the highest power of base less than or equal to n
    highestPower :: Integer -> Integer -> Int
    highestPower x b
      | x < b     = 0
      | otherwise = 1 + highestPower (x `div` b) b

    -- Extract digits from most significant to least significant
    go :: Integer -> Int -> [Integer]
    go x p
      | p < 0     = []
      | otherwise =
          let b = toInteger base
              power = b ^ p
              digit = x `div` power
          in digit : go (x - digit * power) (p - 1)

{-# INLINE intgrFrom3DigitsBase32 #-}

-- | Integer from a 3rd place plus a "reversed" tuple of 2 Word32 digits on base
intgrFrom3DigitsBase32 :: Integer -> (Word32, Word32) -> Integer
intgrFrom3DigitsBase32 i (l1, l2) = (i * secndPlaceW32Radix) + intgrFromRvsrdTuple (l1, l2) radixW32

-- | custom even and odd to handle what we need
_even, _odd :: (Integral a) => a -> (Bool, a)
_even n = let !(q, r) = n `quotRem` 2 in (r == 0, q)
_odd = _even
{-# INLINE _even #-}
{-# INLINE _odd #-}

_evenInt64#, _oddInt64# :: Int64# -> (# Bool, Int64# #)
_evenInt64# n# = (# isTrue# (remInt64# n# 2#Int64 `eqInt64#` 0#Int64), n# `quotInt64#` 2#Int64 #)
_oddInt64# = _evenInt64#
{-# INLINE _evenInt64# #-}
{-# INLINE _oddInt64# #-}

sqrtDX :: Double -> Double
sqrtDX d
  | d == 0 = 0
  | isNaN d = 0
  | isInfinite d = maxDouble
  | d == 1 = 1
  | otherwise = sqrt d -- actual call to "the floating point square root" {sqrt_fsqrt, sqrt, sqrtC, sqrtLibBF, sqrthpmfr or other }
{-# INLINE sqrtDX #-}

unsafesqrtDX :: Double -> Double
unsafesqrtDX !d = sqrt d -- actual call to "the floating point square root" {sqrt_fsqrt, sqrt, sqrtC, sqrtLibBF, sqrthpmfr or other }
{-# INLINE unsafesqrtDX #-}

toInt64 :: Int64# -> Int64
toInt64 = I64#
{-# INLINE toInt64 #-}

fromInt64 :: Int64 -> Int64#
fromInt64 (I64# x#) = x#
{-# INLINE fromInt64 #-}

{-# INLINE updateDouble# #-}
updateDouble# :: Double# -> Int# -> Double#
updateDouble# d# ex# = case decodeDoubleInteger d# of (# m, n# #) -> encodeDoubleInteger m (n# +# ex#)

{-# INLINE split #-}
split :: Double -> (Double, Int64)
split (D# d#) = case split# d# of (# s#, ex# #) -> (D# s#, I64# ex#) -- let !(# s#, ex# #) = split# d# in (D# s#, I64# ex#)

{-# INLINE split# #-}
split# :: Double# -> (# Double#, Int64# #)
split# d# =
  let !(# s, expInt# #) = decodeDoubleInteger d#
      !(D# s#) = fromIntegral s
      !ex# = intToInt64# expInt#
   in (# s#, ex# #)

-- | Some Constants
{-# INLINE radixW32 #-}
{-# SPECIALIZE radixW32 :: Word #-}
{-# SPECIALIZE radixW32 :: Natural #-}
{-# SPECIALIZE radixW32 :: Integer #-}
{-# SPECIALIZE radixW32 :: Word64 #-}
{-# SPECIALIZE radixW32 :: Int64 #-}
radixW32 :: (Integral a) => a
radixW32 = 4294967296 -- 2 ^ finiteBitSize (0 :: Word32)

{-# INLINE predRadixW32 #-}
{-# SPECIALIZE predRadixW32 :: Word #-}
{-# SPECIALIZE predRadixW32 :: Natural #-}
{-# SPECIALIZE predRadixW32 :: Integer #-}
{-# SPECIALIZE predRadixW32 :: Word64 #-}
{-# SPECIALIZE predRadixW32 :: Int64 #-}
predRadixW32 :: (Integral a) => a
predRadixW32 = 4294967295 -- 2 ^ finiteBitSize (0 :: Word32) -1

{-# SPECIALIZE secndPlaceW32Radix :: Word #-}
{-# SPECIALIZE secndPlaceW32Radix :: Natural #-}
{-# SPECIALIZE secndPlaceW32Radix :: Integer #-}
{-# SPECIALIZE secndPlaceW32Radix :: Word64 #-}
{-# SPECIALIZE secndPlaceW32Radix :: Int64 #-}
secndPlaceW32Radix :: Integral a => a
secndPlaceW32Radix = 18446744073709551616 -- radixW32 * radixW32
{-# INLINE secndPlaceW32Radix #-}

{-# SPECIALIZE radixW32Squared :: Word #-}
{-# SPECIALIZE radixW32Squared :: Natural #-}
{-# SPECIALIZE radixW32Squared :: Integer #-}
{-# SPECIALIZE radixW32Squared :: Word64 #-}
{-# SPECIALIZE radixW32Squared :: Int64 #-}
radixW32Squared :: (Integral a) => a 
radixW32Squared = 18446744073709551616 -- secndPlaceRadix

radixW32Cubed :: Integer
radixW32Cubed = 79228162514264337593543950336 -- secndPlaceRadix * radixW32

sqrtOf2 :: Double
sqrtOf2 = 1.4142135623730950488016887242097
{-# INLINE sqrtOf2 #-}

maxDouble :: Double
maxDouble = 1.7976931348623157e308

minDouble :: Double
minDouble = 4.9406564584124654e-324 -- Minimum positive normalized value for Double as per IEEE 754

doublePrecisionBinary :: Int
doublePrecisionBinary = 53

doublePrecisionDecimal :: Int
doublePrecisionDecimal = 308

doublePrecisionRadix32 :: Int
doublePrecisionRadix32 = 32

maxSafeInteger :: Integer
maxSafeInteger = 9007199254740991 -- 2^53 -1 this is the max integer that can be represented without losing precision

-- This is approximately 1.8 x 10^308 representable as Double but will lose precision
maxUnsafeInteger :: Integer
maxUnsafeInteger = 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368

-- https://stackoverflow.com/questions/1848700/biggest-integer-that-can-be-stored-in-a-double

-- | Floating Point nextUp/nextDown funxctions
{-# INLINE nextUp# #-}
nextUp# :: Double# -> Double#
nextUp# dIn# = case nextUp (D# dIn#) of (D# dOut#) -> dOut# -- let !(D# dOut#) = nextUp (D# dIn#) in dOut#

{-# INLINE nextDown# #-}
nextDown# :: Double# -> Double#
nextDown# dIn# = case nextDown (D# dIn#) of (D# dOut#) -> dOut# -- let !(D# dOut#) = nextDown (D# dIn#) in dOut#

double :: Integer -> Integer
double x = x `unsafeShiftL` 1
{-# INLINE double #-}

{-# SPECIALIZE lenRadixW32 :: Integer -> Int #-}
{-# SPECIALIZE lenRadixW32 :: Word64 -> Int #-}
{-# SPECIALIZE lenRadixW32 :: Natural -> Int #-}
lenRadixW32 :: (Integral a) => a -> Int
lenRadixW32 n = I# (word2Int# (integerLogBase# radixW32 (fromIntegral n))) + 1
{-# INLINEABLE lenRadixW32 #-}

-- foldr' :: (a -> b -> b) -> b -> [a] -> b
-- foldr' f z xs = go xs
--   where
--     go [] = z
--     go (x : xs) = f x $! go xs
-- {-# INLINEABLE foldr' #-}


-- | because pred is Enum. this version blow is marginally faster
{-# SPECIALIZE pred :: Integer -> Integer #-}
{-# SPECIALIZE pred :: Word64 -> Word64 #-}
{-# SPECIALIZE pred :: Int -> Int #-}
{-# SPECIALIZE pred :: Int64 -> Int64 #-}
pred :: (Integral a) => a -> a
pred x = x + (-1)
{-# INLINE pred #-}

-- //FIXME floor seems to trigger off missing specialization and also properFractionDouble.

-- The maximum integral value that can be unambiguously represented as a
-- Double. Equal to 9,007,199,254,740,991 = maxsafeinteger
{-# INLINE cI2D2_ #-}
cI2D2_ :: BigNat# -> (# Double#, Int64# #)
cI2D2_ bn#
  | isTrue# (bigNatLeWord# bn# 0x1fffffffffffff##) = let d# = word2Double# (bigNatIndex# bn# 0#) in (# d#, 0#Int64 #)
  -- \| isTrue# (bnsz# <# thresh#) = (# bigNatEncodeDouble# bn# 0#, 0#Int64 #)
  | otherwise = bnToFxGtWord# bn#

-- where
--   bnsz# = bigNatSize# bn#
--   thresh# :: Int#
--   !thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14# -- aligned to the other similar usage and it workd

{-# INLINE convNToDblExp #-}
convNToDblExp :: Integer -> (# Double#, Int64# #)
convNToDblExp n
  | n <= maxUnsafeInteger = let !(D# d#) = fromIntegral n in (# d#, 0#Int64 #) -- don't use maxsafeInteger
  | otherwise = case integerLog2# n of
      l# -> case l# `minusWord#` 94## of
        rawSh# ->
          let !shift# = rawSh# `and#` not# 1##
           in case shiftRInteger n (word2Int# shift#) of
                mbn -> case fromIntegral mbn of (D# dmbn#) -> (# dmbn#, intToInt64# (word2Int# shift#) #)

{-# INLINE bnToFxGtWord# #-}
bnToFxGtWord# :: BigNat# -> (# Double#, Int64# #)
bnToFxGtWord# bn# = case bigNatLog2# bn# of
  --  | otherwise = case _bigNatLog2# bn# bnsz# of
  l# -> case l# `minusWord#` 94## of -- //FIXME is shift# calc needed. workd without it.
    rawSh# ->
      let !shift# = rawSh# `and#` not# 1##
       in case bigNatShiftR# bn# shift# of
            -- l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
            --   h# -> let !shift# = (2## `timesWord#` h#) in case bigNatShiftR# bn# shift# of
            mbn# -> (# bigNatEncodeDouble# mbn# 0#, intToInt64# (word2Int# shift#) #)

{-# INLINE bnToFxGtWord #-}
bnToFxGtWord :: BigNat -> (Double, Int64)
bnToFxGtWord bn@(BN# bn#) = case bigNatLog2 bn# of
  --  | otherwise = case _bigNatLog2# bn# bnsz# of
  l -> case l - 94 of -- //FIXME is shift# calc needed. workd without it.
    rawSh ->
      let !shift = rawSh .&. complement 1
       in case bigNatShiftR bn# shift of
            -- l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
            --   h# -> let !shift# = (2## `timesWord#` h#) in case bigNatShiftR# bn# shift# of
            mbn# -> (D# $ bigNatEncodeDouble# mbn# 0#, fromIntegral shift)

{-# INLINE cI2D2_FAST #-}
cI2D2_FAST :: BigNat# -> (# Double#, Int64# #)
cI2D2_FAST bn# =
  case bigNatSize# bn# of
    -- Single‐Word shortcut, exact up to 2^53–1
    1#
      | isTrue# (bigNatLeWord# bn# 0x1fffffffffffff##) ->
          let w# = bigNatIndex# bn# 0#
           in (# word2Double# w#, 0#Int64 #)
    -- General path: only touch two Words
    sz# ->
      -- 1) Bit-length l = (sz-1)*64 + log2(topWord)
      let hi# = sz# -# 1#
          topW# = bigNatIndex# bn# (word2Int# (int2Word# hi#))
          l# = int2Word# (wordLog2# topW#) `plusWord#` (int2Word# hi# `uncheckedShiftL#` 6#)

          -- 2) How many bits to drop to get a 53-bit mantissa
          rawSh# = l# `minusWord#` 52##

          -- 3) Split that into whole-Word and intra-Word shifts
          !(# wSh#, bSh# #) = rawSh# `quotRemWord#` 64##

          -- 4) Pick the two relevant Words
          idx1# = word2Int# (int2Word# hi# `minusWord#` wSh#)
          idx2# = idx1# -# 1#
          w1# = bigNatIndex# bn# idx1#
          w2# = if isTrue# (idx2# >=# 0#) then bigNatIndex# bn# idx2# else 0##

          -- 5) Assemble a 64-bit “payload” containing the top ~66 bits
          payload# =
            (w1# `uncheckedShiftL#` word2Int# (64## `minusWord#` bSh#))
              `or#` (w2# `uncheckedShiftRL#` word2Int# bSh#)

          -- 6) Peel off 53 mantissa bits (and keep the low 11 for rounding)
          mantRaw# = payload# `uncheckedShiftRL#` 11# -- 64-53 = 11

          -- 7) Half-even rounding using the next bit + sticky
          !(# mant53#, expInc# #) = roundHalfEven mantRaw# payload#

          -- 8) Build the final exponent + mantissa bitpattern
          rawExp# = rawSh# `plusWord#` expInc#
          finalExp# = rawExp# `plusWord#` 1023##
          bits# = (finalExp# `uncheckedShiftL#` 52#) `or#` mant53#
       in (# word2Double# bits#, intToInt64# (word2Int# rawSh#) #)

-- | Half-even rounding of a candidate 53-bit mantissa.
{-# INLINEABLE roundHalfEven #-}
roundHalfEven :: Word# -> Word# -> (# Word#, Word# #)
roundHalfEven m# payload# =
  let roundBit# = payload# `and#` (1## `uncheckedShiftL#` 10#) -- the 11th low bit
      sticky# =
        (payload# `and#` ((1## `uncheckedShiftL#` 10#) `minusWord#` 1##))
          `neWord#` 0##
      mAndOne# = m# `and#` 1##
      mAndOneInt# = word2Int# mAndOne#
      linkUp# = isTrue# (roundBit# `neWord#` 0##) && (isTrue# (sticky#) || isTrue# (mAndOneInt# /=# 0#))
      m'# = if linkUp# then m# `plusWord#` 1## else m#
   in if isTrue# (m'# `eqWord#` (1## `uncheckedShiftL#` 53#))
        then (# 0##, 1## #) -- carry into exponent
        else (# m'# `and#` (1## `uncheckedShiftL#` 52# `minusWord#` 1##), 0## #)

-- | Base 2 logarithm a bit faster
_bigNatLog2# :: BigNat# -> Int# -> Word#
_bigNatLog2# a s -- s = bigNatSize# a
  | bigNatIsZero a = 0##
  | otherwise =
      -- let i = int2Word# (bigNatSize# a) `minusWord#` 1##
      let i = int2Word# s `minusWord#` 1##
       in int2Word# (wordLog2# (bigNatIndex# a (word2Int# i))) `plusWord#` (i `uncheckedShiftL#` 6#) -- WORD_SIZE_BITS_SHIFT#)
{-# INLINE _bigNatLog2# #-}

-- https://stackoverflow.com/questions/1848700/biggest-integer-that-can-be-stored-in-a-double


