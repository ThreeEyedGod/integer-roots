{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnboxedTuples #-}

-- {-# OPTIONS -ddump-simpl -ddump-to-file -ddump-stg #-}

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
  ( _evenInt64#,
    _oddInt64#,
    upLiftDouble#,
    split,
    split#,
    fromInt64,
    sqrtOf2,
    double,
    radixW32,
    secndPlaceW32Radix,
    largestNSqLTE##,
    maxDouble,
    maxSafeInteger,
    maxUnsafeInteger,
    bnToFxGtWord#,
    word64FromRvsrdTuple#,
    word64FromWordRvsrdTuple##,
    quot32,
    bigNatSizeInBase4294967296#,
    bigNatToWordList_,
    isqrtInt',
    isqrtWord,
  )
where

-- \*********** BEGIN NEW IMPORTS

import Data.Bits (finiteBitSize, unsafeShiftL)
import GHC.Exts
  ( Double (..),
    Double#,
    Int (..),
    Int#,
    Int64#,
    Word (..),
    Word#,
    Word64#,
    and#,
    decodeDouble_Int64#,
    eqInt64#,
    eqWord#,
    int2Word#,
    int64ToInt#,
    int64ToWord64#,
    intToInt64#,
    isTrue#,
    minusWord#,
    neWord#,
    not#,
    or#,
    plusWord#,
    plusWord64#,
    quotInt64#,
    quotRemWord#,
    remInt64#,
    shiftL#,
    timesWord64#,
    uncheckedIShiftL#,
    uncheckedShiftL#,
    uncheckedShiftRL#,
    word2Double#,
    word2Int#,
    word32ToWord#,
    wordToWord64#,
    (+#),
    (-#),
    (/=#),
    (<#),
    (>=#),
  )
import GHC.Float.RealFracMethods (floorDoubleInt)
import GHC.Int (Int64 (I64#))
import GHC.Num.BigNat (BigNat#, bigNatEncodeDouble#, bigNatFromWord64#, bigNatIndex, bigNatIsZero, bigNatLog2#, bigNatShiftR#)
-- import GHC.Num.Primitives (intEncodeDouble#)
import GHC.Word (Word32 (..), Word64 (..))
import Numeric.Natural (Natural)
import Numeric.QuoteQuot (quoteQuot)

-- // Fixed floor missing specialization leading to not inlining of properFractionDouble
-- floorDoubleInteger only gets you to Integer , not Word. Hence if Floor to Integer and then to Word solves the not-inlining issue.

-- *********** END NEW IMPORTS

-- | HELPER functions

--- BEGIN Core numeric helper functions
--- ***********************************

isqrtInt' :: Int -> Int
isqrtInt' n
  | n < r * r = r - 1
  | otherwise = r
  where
    !r = (truncate :: Double -> Int) . sqrt $ fromIntegral n
{-# INLINEABLE isqrtInt' #-}

isqrtWord :: Word -> Word
isqrtWord x
  | x < (r * r)
      -- Double interprets values near maxBound as 2^64, we don't have that problem for 32 bits
      || finiteBitSize (0 :: Word) == 64 && r == 4294967296 =
      r - 1
  | otherwise = r
  where
    !r = (fromIntegral :: Int -> Word) . (truncate :: Double -> Int) . sqrt $ fromIntegral x
{-# INLINEABLE isqrtWord #-}

-- Equivalent to (`quot` 32).
quot32 :: Word -> Word
quot32 = $$(quoteQuot 32)
{-# INLINEABLE quot32 #-}

bigNatSizeInBase4294967296# :: BigNat# -> Word#
bigNatSizeInBase4294967296# a
  | bigNatIsZero a =
      0##
  | otherwise =
      bigNatLogBaseWord4294967296# a `plusWord#` 1##
{-# INLINEABLE bigNatSizeInBase4294967296# #-}

-- | Logarithm for an 2^32 base
bigNatLogBaseWord4294967296# :: BigNat# -> Word#
bigNatLogBaseWord4294967296# bn# = let (W# w#) = quot32 (W# (bigNatLog2# bn#)) in w# -- bigNatLog2# bn# `quotWord#` 32##
{-# INLINEABLE bigNatLogBaseWord4294967296# #-}

-- | Convert a BigNat into a list of non-zero Words (most-significant first) w/size supplied
bigNatToWordList_ :: BigNat# -> Int# -> [Word]
bigNatToWordList_ bn = go
  where
    go 0# = []
    go n = bigNatIndex bn (n -# 1#) : go (n -# 1#)
{-# INLINEABLE bigNatToWordList_ #-}

{-# DUMMY integralFromRvsrdTuple #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Integer -> Integer #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Word64 -> Word64 #-}

-- | Integer from a "reversed" tuple of Word32 digits
-- Base 4.21 shipped with ghc 9.12.1 had a toInteger improvement : https://github.com/haskell/core-libraries-committee/issues/259
integralFromRvsrdTuple :: (Integral a) => (Word32, Word32) -> a -> a
integralFromRvsrdTuple (0, 0) 0 = 0
integralFromRvsrdTuple (0, lMSB) base = fromIntegral lMSB * base
integralFromRvsrdTuple (lLSB, 0) _ = fromIntegral lLSB
integralFromRvsrdTuple (lLSB, lMSB) base = fromIntegral lMSB * base + fromIntegral lLSB

{-# DUMMY integralFromTuple #-}
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

{-# DUMMY word64FromRvsrdTuple# #-}

-- | Word64# from a "reversed" tuple of Word32 digits
word64FromRvsrdTuple# :: (Word32, Word32) -> Word64# -> Word64#
word64FromRvsrdTuple# (0, 0) _ = 0#Word64
word64FromRvsrdTuple# (0, W32# lMSB#) base# = wordToWord64# (word32ToWord# lMSB#) `timesWord64#` base#
word64FromRvsrdTuple# (W32# lLSB#, 0) _ = wordToWord64# (word32ToWord# lLSB#)
word64FromRvsrdTuple# (W32# lLSB#, W32# lMSB#) base# = (wordToWord64# (word32ToWord# lMSB#) `timesWord64#` base#) `plusWord64#` wordToWord64# (word32ToWord# lLSB#)

{-# DUMMY word64FromWordRvsrdTuple## #-}

-- | Word64# from a "reversed" tuple of Word32 digits
word64FromWordRvsrdTuple## :: (# Word#, Word# #) -> Word64#
word64FromWordRvsrdTuple## (# 0##, 0## #) = 0#Word64
word64FromWordRvsrdTuple## (# 0##, lMSB# #) = wordToWord64# (lMSB# `uncheckedShiftL#` 32#) -- lMSB# `timesWord64#` 4294967296#Word64
word64FromWordRvsrdTuple## (# lLSB#, 0## #) = wordToWord64# lLSB#
word64FromWordRvsrdTuple## (# lLSB#, lMSB# #) = word64FromWordRvsrdTuple## (# 0##, lMSB# #) `plusWord64#` wordToWord64# lLSB#

{-# DUMMY largestNSqLTE## #-}
largestNSqLTE## :: Word64# -> Word64#
largestNSqLTE## w# = case floorDoubleInt (sqrt (fromIntegral (W64# w#)) :: Double) of (I# iI#) -> wordToWord64# $ int2Word# iI#

_evenInt64#, _oddInt64# :: Int64# -> (# Bool, Int64# #)
_evenInt64# n# = (# isTrue# (remInt64# n# 2#Int64 `eqInt64#` 0#Int64), n# `quotInt64#` 2#Int64 #)
_oddInt64# = _evenInt64#

{-# INLINABLE_1 _evenInt64# #-}
{-# INLINABLE_1 _oddInt64# #-}

fromInt64 :: Int64 -> Int64#
fromInt64 (I64# x#) = x#

{-# DUMMY fromInt64 #-}

{-# INLINEABLE upLiftDouble# #-}
upLiftDouble# :: Double# -> Int# -> Double#
upLiftDouble# d# ex# = case decodeDouble_Int64# d# of (# !m, !n# #) -> bigNatEncodeDouble# (bigNatFromWord64# (int64ToWord64# m)) (n# +# ex#) -- intEncodeDouble# (int64ToInt# m) (n# +# ex#)

{-# DUMMY split #-}
split :: Double -> (Double, Int64)
split (D# d#) = case split# d# of (# s#, ex# #) -> (D# s#, I64# ex#) -- let !(# s#, ex# #) = split# d# in (D# s#, I64# ex#)

{-# DUMMY split# #-}
split# :: Double# -> (# Double#, Int64# #)
split# d# =
  let !(# s64, expInt# #) = decodeDouble_Int64# d#
      !(D# s#) = fromIntegral (I64# s64)
      !ex# = intToInt64# expInt#
   in (# s#, ex# #)

-- | Some Constants

{-# DUMMY radixW32 #-}
{-# SPECIALIZE radixW32 :: Word #-}
{-# SPECIALIZE radixW32 :: Natural #-}
{-# SPECIALIZE radixW32 :: Integer #-}
{-# SPECIALIZE radixW32 :: Word64 #-}
{-# SPECIALIZE radixW32 :: Int64 #-}
radixW32 :: (Integral a) => a
radixW32 = 4294967296 -- 2 ^ finiteBitSize (0 :: Word32)

{-# SPECIALIZE secndPlaceW32Radix :: Natural #-}
{-# SPECIALIZE secndPlaceW32Radix :: Integer #-}
secndPlaceW32Radix :: (Integral a) => a
secndPlaceW32Radix = 18446744073709551616 -- radixW32 * radixW32
{-# DUMMY secndPlaceW32Radix #-}

sqrtOf2 :: Double
sqrtOf2 = 1.4142135623730950488016887242097

{-# DUMMY sqrtOf2 #-}

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

double :: Integer -> Integer
double x = x `unsafeShiftL` 1

{-# DUMMY double #-}

{-# INLINEABLE bnToFxGtWord# #-}
bnToFxGtWord# :: BigNat# -> Word# -> (# Double#, Int64# #)
bnToFxGtWord# !bn# !lgn# =
  case lgn# `minusWord#` 94## of -- //FIXME is shift# calc needed. workd without it.
    !rawSh# ->
      let !shift# = rawSh# `and#` not# 1##
       in case bigNatShiftR# bn# shift# of
            -- l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
            --   h# -> let !shift# = (2## `timesWord#` h#) in case bigNatShiftR# bn# shift# of
            !mbn# -> (# bigNatEncodeDouble# mbn# 0#, intToInt64# (word2Int# shift#) #)
