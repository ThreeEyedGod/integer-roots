{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

{-# OPTIONS -ddump-simpl -ddump-to-file -ddump-stg #-}

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
    word64FromRvsrd2ElemList#,
    largestNSqLTE##,
    maxDouble,
    maxSafeInteger,
    maxUnsafeInteger,
    cI2D2_,
    bnToFxGtWord#,
    word64From2ElemList#,
    bnConst##,
    word64FromRvsrdTuple#,
    word64FromWordRvsrdTuple##,
  )
where

-- \*********** BEGIN NEW IMPORTS

import Data.Bits (complement, unsafeShiftL, (.&.))
import GHC.Exts
  ( Double (..),
    Double#,
    Int#,
    Int64#,
    Word#,
    Word64#,
    and#,
    decodeDouble_Int64#,
    eqInt64#,
    eqWord#,
    int2Word#,
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
    timesWord64#,
    uncheckedShiftL#,
    uncheckedShiftRL#,
    word2Double#,
    word2Int#,
    word32ToWord#,
    wordToWord64#,
    (+#),
    (-#),
    (/=#),
    (>=#), int64ToInt#,
  )
import GHC.Float.RealFracMethods (floorDoubleInteger)
import GHC.Int (Int64 (I64#))
import GHC.Integer (shiftRInteger)
import GHC.Integer.Logarithms (wordLog2#)
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatEncodeDouble#, bigNatIndex#, bigNatLeWord#, bigNatLog2, bigNatOne#, bigNatShiftR, bigNatShiftR#, bigNatSize#, bigNatZero#, bigNatToWordMaybe#)
import GHC.Num.Integer (integerLog2#)
import GHC.Word (Word32 (..), Word64 (..))
import Numeric.Natural (Natural)
import Prelude hiding (pred)
import GHC.Num.Primitives (intEncodeDouble#)

-- // Fixed floor missing specialization leading to not inlining of properFractionDouble
-- floorDoubleInteger only gets you to Integer , not Word. Hence if Floor to Integer and then to Word solves the not-inlining issue.

-- *********** END NEW IMPORTS

-- | HELPER functions
bnConst## :: Int# -> BigNat#
bnConst## i# = case i# of
  0# -> bigNatZero# (# #)
  1# -> bigNatOne# (# #)
  _ -> error "bnConst# : unsupported constant"
{-# INLINE bnConst## #-}

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
word64From2ElemList# [lmsb, llsb] = word64FromRvsrdTuple# (llsb, lmsb) 4294967296#Word64
word64From2ElemList# (_ : _ : _) = error "word64From2ElemList# : more than 2 elems list"
{-# INLINE word64From2ElemList# #-}

--- END helpers
--- BEGIN Core numeric helper functions
--- ***********************************

{-# INLINE integralFromRvsrdTuple #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Integer -> Integer #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Word64 -> Word64 #-}

-- | Integer from a "reversed" tuple of Word32 digits
-- Base 4.21 shipped with ghc 9.12.1 had a toInteger improvement : https://github.com/haskell/core-libraries-committee/issues/259
integralFromRvsrdTuple :: (Integral a) => (Word32, Word32) -> a -> a
integralFromRvsrdTuple (0, 0) 0 = 0
integralFromRvsrdTuple (0, lMSB) base = fromIntegral lMSB * base
integralFromRvsrdTuple (lLSB, 0) _ = fromIntegral lLSB
integralFromRvsrdTuple (lLSB, lMSB) base = fromIntegral lMSB * base + fromIntegral lLSB

{-# INLINE integralFromTuple #-}
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

{-# INLINE word64FromWordRvsrdTuple## #-}

-- | Word64# from a "reversed" tuple of Word32 digits
word64FromWordRvsrdTuple## :: (# Word#, Word# #) -> Word64# -> Word64#
word64FromWordRvsrdTuple## (# 0##, 0## #) _ = 0#Word64
word64FromWordRvsrdTuple## (# 0##, lMSB# #) base# = wordToWord64# lMSB# `timesWord64#` base#
word64FromWordRvsrdTuple## (# lLSB#, 0## #) _ = wordToWord64# lLSB#
word64FromWordRvsrdTuple## (# lLSB#, lMSB# #) base# = (wordToWord64# lMSB# `timesWord64#` base#) `plusWord64#` wordToWord64# lLSB#

{-# INLINE largestNSqLTE## #-}
largestNSqLTE## :: Word64# -> Word64#
largestNSqLTE## w# = case floorDoubleInteger (sqrt (fromIntegral (W64# w#)) :: Double) of iI -> case fromInteger iI of (W64# r#) -> r#

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

fromInt64 :: Int64 -> Int64#
fromInt64 (I64# x#) = x#
{-# INLINE fromInt64 #-}

{-# INLINE upLiftDouble# #-}
upLiftDouble# :: Double# -> Int# -> Double#
upLiftDouble# d# ex# = case decodeDouble_Int64# d# of (# !m, !n# #) -> intEncodeDouble# (int64ToInt# m) (n# +# ex#) 

{-# INLINE split #-}
split :: Double -> (Double, Int64)
split (D# d#) = case split# d# of (# s#, ex# #) -> (D# s#, I64# ex#) -- let !(# s#, ex# #) = split# d# in (D# s#, I64# ex#)

{-# INLINE split# #-}
split# :: Double# -> (# Double#, Int64# #)
split# d# =
  let !(# s64, expInt# #) = decodeDouble_Int64# d#
      !(D# s#) = fromIntegral (I64# s64)
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

{-# SPECIALIZE secndPlaceW32Radix :: Word #-}
{-# SPECIALIZE secndPlaceW32Radix :: Natural #-}
{-# SPECIALIZE secndPlaceW32Radix :: Integer #-}
{-# SPECIALIZE secndPlaceW32Radix :: Word64 #-}
{-# SPECIALIZE secndPlaceW32Radix :: Int64 #-}
secndPlaceW32Radix :: (Integral a) => a
secndPlaceW32Radix = 18446744073709551616 -- radixW32 * radixW32
{-# INLINE secndPlaceW32Radix #-}

sqrtOf2 :: Double
sqrtOf2 = 1.4142135623730950488016887242097
{-# INLINE sqrtOf2 #-}

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
{-# INLINE double #-}

-- The maximum integral value that can be unambiguously represented as a
-- Double. Equal to 9,007,199,254,740,991 = maxsafeinteger
{-# INLINE cI2D2_ #-}
cI2D2_ :: BigNat# -> Word# -> (# Double#, Int64# #)
cI2D2_ bn# lgn# = case bigNatToWordMaybe# bn# of
  (# | w# #) -> (# word2Double# w#, 0#Int64 #)
  _ -> bnToFxGtWord# bn# lgn#
  -- where
  -- | isTrue# (bigNatLeWord# bn# 0x1fffffffffffff##) = let d# = word2Double# (bigNatIndex# bn# 0#) in (# d#, 0#Int64 #) -- //FIXME CHECK THIS LOGIC
  -- -- \| isTrue# (bnsz# <# thresh#) = (# bigNatEncodeDouble# bn# 0#, 0#Int64 #)
  -- | otherwise = bnToFxGtWord# bn# lgn#

-- where
--   bnsz# = bigNatSize# bn#
--   thresh# :: Int#
--   !thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14# -- aligned to the other similar usage and it workd

{-# INLINE bnToFxGtWord# #-}
bnToFxGtWord# :: BigNat# -> Word# -> (# Double#, Int64# #)
bnToFxGtWord# bn# lgn# =
  case lgn# `minusWord#` 94## of -- //FIXME is shift# calc needed. workd without it.
    !rawSh# ->
      let !shift# = rawSh# `and#` not# 1##
       in case bigNatShiftR# bn# shift# of
            -- l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
            --   h# -> let !shift# = (2## `timesWord#` h#) in case bigNatShiftR# bn# shift# of
            !mbn# -> (# bigNatEncodeDouble# mbn# 0#, intToInt64# (word2Int# shift#) #)

-- https://stackoverflow.com/questions/1848700/biggest-integer-that-can-be-stored-in-a-double

