{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnboxedTuples #-}
-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump=simpl or ddump-asm dumps else not
{-# OPTIONS_GHC -O2 -threaded -optl-m64  -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fstrictness -funbox-small-strict-fields -funfolding-use-threshold=16 -fmax-worker-args=32 -optc-O3 -optc-ffast-math #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- |
-- Module:      Math.NumberTheory.Roots.Squares.Internal
-- Copyright:   (c) 2011 Daniel Fischer, 2016-2020 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Internal functions dealing with square roots. End-users should not import this module.
-- {-# OPTIONS -ddump-simpl -ddump-to-file #-}
module Math.NumberTheory.Utils.FloatingX_ where
-- \*********** BEGIN NEW IMPORTS

import Data.Bits (complement, finiteBitSize, shiftR, unsafeShiftL, unsafeShiftR, (.&.), (.|.))
import Data.Bits.Floating (nextDown, nextUp)
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
    ltInt64#,
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
import GHC.Float (properFractionDouble, divideDouble, int2Double, integerToDouble#, minusDouble, plusDouble, powerDouble, timesDouble)
import GHC.Int (Int64 (I64#))
import GHC.Integer (decodeDoubleInteger, encodeDoubleInteger, shiftRInteger)
import GHC.Integer.Logarithms (wordLog2#)
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatEncodeDouble#, bigNatIndex#, bigNatIsZero, bigNatLeWord#, bigNatLog2, bigNatLog2#, bigNatShiftR, bigNatShiftR#, bigNatSize#)
import GHC.Num.Integer (integerLog2#)
import GHC.Word (Word64 (..))
import Math.NumberTheory.Utils.ArthMtic_ (fromInt64, maxDouble, maxUnsafeInteger, nextDown#, nextUp#, split, split#, sqrtOf2, updateDouble#, _evenInt64#)

-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

-- | Custom Double Type and its arithmetic
data FloatingX = FloatingX !Double !Int64 deriving (Eq) -- ! for strict data type

-- | Custom double "unboxed" and its arithmetic
data FloatingX# = FloatingX# {signif# :: {-# UNPACK #-} !Double#, expnnt# :: {-# UNPACK #-} !Int64#} deriving (Eq) -- ! for strict data type

{-# INLINE zeroFx# #-}
zeroFx# :: FloatingX#
zeroFx# = let !(I64# mb#) = minBound :: Int64 in FloatingX# 0.0## mb#

{-# INLINE zeroFx #-}
zeroFx :: FloatingX
zeroFx = let !mb = minBound :: Int64 in FloatingX 0.00 mb

{-# INLINE oneFx# #-}
oneFx# :: FloatingX#
oneFx# = FloatingX# 1.0## 0#Int64

{-# INLINE minValueFx #-}
minValueFx :: FloatingX
minValueFx = FloatingX 1.0 0

{-# INLINE minValueFx# #-}
minValueFx# :: FloatingX#
minValueFx# = FloatingX# 1.0## 0#Int64

{-# NOINLINE [0] (!+) #-}
(!+) :: FloatingX -> FloatingX -> FloatingX
(!+) x y = x `addFx` y

{-# NOINLINE [0] (!*) #-}
(!*) :: FloatingX -> FloatingX -> FloatingX
(!*) x y = x `mulFx` y

{-# NOINLINE [0] (!/) #-}
(!/) :: FloatingX -> FloatingX -> FloatingX
(!/) x y = x `unsafeDivFx` y ---- note this is the unsafest version of divide

{-# NOINLINE [0] (!**+) #-}
(!**+) :: FloatingX -> FloatingX -> FloatingX
(!**+) x y = x `fsqraddFloatingX` y

{-# INLINE addFx #-}
addFx :: FloatingX -> FloatingX -> FloatingX
addFx a@(FloatingX sA expA) b@(FloatingX sB expB)
  -- \| a == zero# = b
  -- \| b == zero# = a
  | expA == expB = FloatingX (sA + sB) expA
  | expA > expB = combine a b
  | otherwise = combine b a
  where
    -- \| otherwise = FloatingX# (sA# +## sB#) expA# -- FloatingX (signifA + signifB) expA

    combine big@(FloatingX sBig expBig) little@(FloatingX sLittle expLittle) =
      let !scale = expLittle - expBig
          !scaleD@(D# scaleD#) = fromIntegral scale
          !scaledLittle = sLittle `timesDouble` (powerDouble 2.00 scaleD)
          !resSignif = sBig + scaledLittle
       in FloatingX resSignif expBig

{-# INLINE mulFx #-}
mulFx :: FloatingX -> FloatingX -> FloatingX
mulFx a@(FloatingX sA expA) b@(FloatingX sB expB) =
  let !resExp = expA + expB
      !resSignif = sA * sB
   in FloatingX resSignif resExp

{-# INLINE unsafeDivFx #-}
unsafeDivFx :: FloatingX -> FloatingX -> FloatingX
unsafeDivFx n@(FloatingX s1 e1) d@(FloatingX s2 e2) =
  -- \| d == FloatingX# 1.0## (fromInt64 0) = n
  -- \| isTrue# (s1# ==## 0.0##) = zero#
  -- \| isTrue# (s2# ==## 0.0##) = error "divide#: error divide by zero "
  -- \| otherwise
  let !resExp = e1 - e2
      !resSignif = s1 / s2
      -- !l1Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# e2#
      -- !l2Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# resExp#
      !(finalSignif, finalExp) = (resSignif, resExp)
   in -- in if (e1 `xor` e2) .&. (e1 `xor` resExp) < 0 || (resSignif < 1.0 && resExp == (minBound :: Integer))
      -- //TODO fix this next line
      -- in if W64# l1Word64# .&. W64# l2Word64# < 0 || (isTrue# (resSignif# <## 1.0##) && isTrue# (resExp# `leInt64#` intToInt64# 0#) )
      if finalSignif < 1.0 && finalExp <= 0
        then zeroFx
        else FloatingX finalSignif finalExp

{-# INLINE fsqraddFloatingX #-}
fsqraddFloatingX :: FloatingX -> FloatingX -> FloatingX
fsqraddFloatingX !(FloatingX (D# sA#) expA) !(FloatingX (D# sC#) expC)
  | diff == 0 = FloatingX (D# (fmaddDouble# sA# sA# sC#)) expC
  | otherwise = case updateDouble# sC# (int64ToInt# diff#) of sC_# -> FloatingX (D# (fmaddDouble# sA# sA# sC_#)) twoTimesExpA -- let !sC_# = updateDouble# sC# (int64ToInt# diff#) in FloatingX# (fmaddDouble# sA# sA# sC_#) twoTimesExpA#
  where
    !twoTimesExpA = 2 * expA
    !diff@(I64# diff#) = expC - twoTimesExpA

{-# INLINEABLE [1] floorFX #-} -- punting inlining to the last Phase 0
-- {-# INLINE [0] floorFX #-} -- punting inlining to the last Phase 0
{-# SPECIALIZE floorFX :: FloatingX -> Int #-}
{-# SPECIALIZE floorFX :: FloatingX -> Int64 #-}
{-# SPECIALIZE floorFX :: FloatingX -> Integer #-}
floorFX :: (Integral a) => FloatingX -> a
floorFX (FloatingX s e) = case fx2Double (FloatingX s e) of
  Just d -> floor d
  _ -> error "floorX#: fx2Double resulted in Nothing  " -- fromIntegral $ toLong (D# s#) (fromIntegral e)

{-# INLINE (!+##) #-}
(!+##) :: FloatingX# -> FloatingX# -> FloatingX#
(!+##) x y = x `addFx#` y

{-# INLINE (!*##) #-}
(!*##) :: FloatingX# -> FloatingX# -> FloatingX#
(!*##) x y = x `mulFx#` y

{-# INLINE (!/##) #-}
(!/##) :: FloatingX# -> FloatingX# -> FloatingX#
(!/##) x y = x `unsafeDivFx#` y ---- note this is the unsafest version of divide

(!<##) :: FloatingX# -> FloatingX# -> Bool
(!<##) (FloatingX# x# xe#) (FloatingX# y# ye#) = if isTrue# (xe# `eqInt64#` ye#) then isTrue# (x# <## y#) else if isTrue# (xe# `ltInt64#` ye#) then isTrue# (x# <## y#) else False
{-# INLINE (!<##) #-}

{-# INLINE (!**+##) #-}
(!**+##) :: FloatingX# -> FloatingX# -> FloatingX#
(!**+##) x y = x `fsqraddFloatingX#` y

{-# INLINE addFx# #-}
addFx# :: FloatingX# -> FloatingX# -> FloatingX#
addFx# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#)
  -- \| a == zero# = b
  -- \| b == zero# = a
  | isTrue# (expA# `eqInt64#` expB#) = FloatingX# (sA# +## sB#) expA#
  | isTrue# (expA# `gtInt64#` expB#) = combine a b
  | otherwise = combine b a
  where
    -- \| otherwise = FloatingX# (sA# +## sB#) expA# -- FloatingX (signifA + signifB) expA

    combine big@(FloatingX# sBig# expBig#) little@(FloatingX# sLittle# expLittle#) =
      let !scale# = expLittle# `subInt64#` expBig#
          !(D# !scaleD#) = fromIntegral (I64# scale#)
          !scaledLittle# = sLittle# *## (2.00## **## scaleD#)
          !resSignif# = sBig# +## scaledLittle#
       in FloatingX# resSignif# expBig#

{-# INLINE addFxNorm# #-}
addFxNorm# :: FloatingX# -> FloatingX# -> FloatingX#
addFxNorm# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#)
  -- \| a == zero# = b
  -- \| b == zero# = a
  | isTrue# (expA# `eqInt64#` expB#) = FloatingX# (sA# +## sB#) expA#
  | isTrue# (expA# `gtInt64#` expB#) = combine a b
  | otherwise = combine b a
  where
    -- \| otherwise = FloatingX# (sA# +## sB#) expA# -- FloatingX (signifA + signifB) expA

    combine big@(FloatingX# sBig# expBig#) little@(FloatingX# sLittle# expLittle#) =
      let !scale# = expLittle# `subInt64#` expBig#
          !(D# !scaleD#) = fromIntegral (I64# scale#)
          !scaledLittle# = sLittle# *## (2.00## **## scaleD#)
          !resSignif# = sBig# +## scaledLittle#
       in if isTrue# (resSignif# >=## 2.0##)
            then FloatingX# (resSignif# *## 0.5##) (expBig# `plusInt64#` 1#Int64)
            else FloatingX# resSignif# expBig#

{-# INLINE mulFx# #-}
mulFx# :: FloatingX# -> FloatingX# -> FloatingX#
mulFx# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#) =
  let !resExp# = expA# `plusInt64#` expB#
      !resSignif# = sA# *## sB#
   in FloatingX# resSignif# resExp#

{-# INLINE mulFx_# #-}
mulFx_# :: FloatingX# -> FloatingX# -> FloatingX#
mulFx_# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#)
  | isTrue# (sA# ==## 0.00##) = zeroFx#
  | isTrue# (sB# ==## 0.00##) = zeroFx#
  | isTrue# (sA# ==## 1.00##) && isTrue# (expA# `eqInt64#` 0#Int64) = b
  | isTrue# (sB# ==## 1.00##) && isTrue# (expB# `eqInt64#` 0#Int64) = a
  | otherwise =
      let !resExp# = expA# `plusInt64#` expB#
          !resSignif# = sA# *## sB#
       in FloatingX# resSignif# resExp#

{-# INLINE mulFxNorm# #-}
mulFxNorm# :: FloatingX# -> FloatingX# -> FloatingX#
mulFxNorm# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#)
  | isTrue# (sA# ==## 0.00##) = zeroFx#
  | isTrue# (sB# ==## 0.00##) = zeroFx#
  | isTrue# (sA# ==## 1.00##) && isTrue# (expA# `eqInt64#` 0#Int64) = b
  | isTrue# (sB# ==## 1.00##) && isTrue# (expB# `eqInt64#` 0#Int64) = a
  | otherwise =
      let !resExp# = expA# `plusInt64#` expB#
          !resSignif# = sA# *## sB#
       in if isTrue# (resSignif# >=## 2.0##) -- why is this not needed
            then FloatingX# (resSignif# *## 0.5##) (resExp# `plusInt64#` 1#Int64)
            else FloatingX# resSignif# resExp#

{-# INLINE sqr# #-}
sqr# :: FloatingX# -> FloatingX#
sqr# a@(FloatingX# sA# expA#)
  | isTrue# (sA# ==## 0.00##) = zeroFx#
  | isTrue# (sA# ==## 1.00##) && isTrue# (expA# `eqInt64#` 0#Int64) = a
  | otherwise =
      let !resExp# = expA# `plusInt64#` expA#
          !resSignif# = sA# *## sA#
       in if isTrue# (resSignif# >=## 2.0##)
            then FloatingX# (resSignif# *## 0.5##) (resExp# `plusInt64#` 1#Int64)
            else FloatingX# resSignif# resExp#

{-# INLINE divFxNorm# #-}
divFxNorm# :: FloatingX# -> FloatingX# -> FloatingX#
divFxNorm# n@(FloatingX# s1# e1#) d@(FloatingX# s2# e2#)
  | d == FloatingX# 1.0## (fromInt64 0) = n
  | isTrue# (s1# ==## 0.0##) = zeroFx#
  | isTrue# (s2# ==## 0.0##) = error "divide#: error divide by zero "
  | otherwise =
      let !resExp# = e1# `subInt64#` e2#
          !resSignif# = s1# /## s2#
          -- !l1Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# e2#
          -- !l2Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# resExp#
          !(# finalSignif#, finalExp# #) =
            if isTrue# (resSignif# <## 1.0##)
              then (# resSignif# *## 2.0##, resExp# `subInt64#` 1#Int64 #)
              else (# resSignif#, resExp# #)
       in -- in if (e1 `xor` e2) .&. (e1 `xor` resExp) < 0 || (resSignif < 1.0 && resExp == (minBound :: Integer))
          -- //TODO fix this next line
          -- in if W64# l1Word64# .&. W64# l2Word64# < 0 || (isTrue# (resSignif# <## 1.0##) && isTrue# (resExp# `leInt64#` intToInt64# 0#) )
          if isTrue# (resSignif# <## 1.0##) && isTrue# (resExp# `leInt64#` 0#Int64)
            then zeroFx#
            else FloatingX# finalSignif# finalExp#

{-# INLINE unsafeDivFxNorm# #-}
unsafeDivFxNorm# :: FloatingX# -> FloatingX# -> FloatingX#
unsafeDivFxNorm# n@(FloatingX# s1# e1#) d@(FloatingX# s2# e2#) =
  -- \| d == FloatingX# 1.0## (fromInt64 0) = n
  -- \| isTrue# (s1# ==## 0.0##) = zero#
  -- \| isTrue# (s2# ==## 0.0##) = error "divide#: error divide by zero "
  -- \| otherwise
  let !resExp# = e1# `subInt64#` e2#
      !resSignif# = s1# /## s2#
      -- !l1Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# e2#
      -- !l2Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# resExp#
      !(# finalSignif#, finalExp# #) =
        if isTrue# (resSignif# <## 1.0##)
          then (# resSignif# *## 2.0##, resExp# `subInt64#` 1#Int64 #)
          else (# resSignif#, resExp# #)
   in -- in if (e1 `xor` e2) .&. (e1 `xor` resExp) < 0 || (resSignif < 1.0 && resExp == (minBound :: Integer))
      -- //TODO fix this next line
      -- in if W64# l1Word64# .&. W64# l2Word64# < 0 || (isTrue# (resSignif# <## 1.0##) && isTrue# (resExp# `leInt64#` intToInt64# 0#) )
      if isTrue# (finalSignif# <## 1.0##) && isTrue# (finalExp# `leInt64#` 0#Int64)
        then zeroFx#
        else FloatingX# finalSignif# finalExp#

{-# INLINE unsafeDivFx# #-}
unsafeDivFx# :: FloatingX# -> FloatingX# -> FloatingX#
unsafeDivFx# n@(FloatingX# s1# e1#) d@(FloatingX# s2# e2#) =
  -- \| d == FloatingX# 1.0## (fromInt64 0) = n
  -- \| isTrue# (s1# ==## 0.0##) = zero#
  -- \| isTrue# (s2# ==## 0.0##) = error "divide#: error divide by zero "
  -- \| otherwise
  let !resExp# = e1# `subInt64#` e2#
      !resSignif# = s1# /## s2#
      -- !l1Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# e2#
      -- !l2Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# resExp#
      !(# finalSignif#, finalExp# #) = (# resSignif#, resExp# #)
   in -- in if (e1 `xor` e2) .&. (e1 `xor` resExp) < 0 || (resSignif < 1.0 && resExp == (minBound :: Integer))
      -- //TODO fix this next line
      -- in if W64# l1Word64# .&. W64# l2Word64# < 0 || (isTrue# (resSignif# <## 1.0##) && isTrue# (resExp# `leInt64#` intToInt64# 0#) )
      if isTrue# (finalSignif# <## 1.0##) && isTrue# (finalExp# `leInt64#` 0#Int64)
        then zeroFx#
        else FloatingX# finalSignif# finalExp#

{-# INLINE unsafestDivFx# #-}
unsafestDivFx# :: FloatingX# -> FloatingX# -> FloatingX#
unsafestDivFx# n@(FloatingX# s1# e1#) d@(FloatingX# s2# e2#) = FloatingX# (s1# /## s2#) (e1# `subInt64#` e2#)

{-# INLINE fsqraddFloatingX# #-}
fsqraddFloatingX# :: FloatingX# -> FloatingX# -> FloatingX#
fsqraddFloatingX# !(FloatingX# sA# expA#) !(FloatingX# sC# expC#)
  | isTrue# (diff# `eqInt64#` 0#Int64) = FloatingX# (fmaddDouble# sA# sA# sC#) expC#
  | otherwise = case updateDouble# sC# (int64ToInt# diff#) of sC_# -> FloatingX# (fmaddDouble# sA# sA# sC_#) twoTimesExpA# -- let !sC_# = updateDouble# sC# (int64ToInt# diff#) in FloatingX# (fmaddDouble# sA# sA# sC_#) twoTimesExpA#
  where
    !twoTimesExpA# = 2#Int64 `timesInt64#` expA#
    !diff# = expC# `subInt64#` twoTimesExpA#

{-# INLINE fm1addFloatingX# #-}
fm1addFloatingX# :: FloatingX# -> FloatingX# -> FloatingX#
fm1addFloatingX# a@(FloatingX# sA# expA#) c@(FloatingX# sC# expC#)
  | isTrue# (cExcessa# `geInt64#` 0#Int64) = FloatingX# (fmaddDouble# sA# 1.00## sC#) cExcessa#
  | otherwise = a !*## oneFx# !+## c -- default custom mult and add
  where
    !cExcessa# = expC# `subInt64#` expA#

{-# INLINE sqrtFX# #-}
sqrtFX# :: FloatingX# -> FloatingX#
sqrtFX# fx@(FloatingX# s# e#) = case sqrtFxSplitDbl## fx of (# sX#, eX# #) -> FloatingX# sX# eX# -- let !(D# sX#, I64# eX#) = sqrtSplitDbl (FloatingX (D# s#) (I64# e#)) in FloatingX# sX# eX#

{-# INLINE [0] floorX# #-}
{-# SPECIALIZE floorX# :: FloatingX# -> Int #-}
{-# SPECIALIZE floorX# :: FloatingX# -> Int64 #-}
{-# SPECIALIZE floorX# :: FloatingX# -> Integer #-}
floorX# :: (Integral a) => FloatingX# -> a
floorX# (FloatingX# s# e#) = case fx2Double (FloatingX (D# s#) (I64# e#)) of
  Just d -> floor d
  _ -> error "floorX#: fx2Double resulted in Nothing  " -- fromIntegral $ toLong (D# s#) (fromIntegral e)

{-# INLINE floorXW64## #-}
floorXW64## :: FloatingX# -> Word64#
floorXW64## f@(FloatingX# s# e#) = case floor (D# $ unsafefx2Double## f) of (W64# w#) -> w#

{-# INLINE floorXI64## #-}
floorXI64## :: FloatingX# -> Int64#
floorXI64## f@(FloatingX# s# e#) = case floor (D# $ unsafefx2Double## f) of (I64# i#) -> i#

scaleByPower2 :: Int64 -> FloatingX -> FloatingX
scaleByPower2 n (FloatingX s e) = if s == 0 then zeroFx else FloatingX s (e + n) -- normalizeFX# $ FloatingX# s# (e# `plusInt64#` n#)
{-# INLINE scaleByPower2 #-}

scaleByPower2# :: Int64# -> FloatingX# -> FloatingX#
scaleByPower2# n# (FloatingX# s# e#) = if isTrue# (s# ==## 0.00##) then zeroFx# else FloatingX# s# (e# `plusInt64#` n#) -- normalizeFX# $ FloatingX# s# (e# `plusInt64#` n#)
{-# INLINE scaleByPower2# #-}

{-# INLINE sqrtFx #-}
sqrtFx :: FloatingX -> FloatingX
sqrtFx fx@(FloatingX s e) = case sqrtFxSplitDbl fx of (sX, eX) -> FloatingX sX eX -- let !(D# sX#, I64# eX#) = sqrtSplitDbl (FloatingX (D# s#) (I64# e#)) in FloatingX# sX# eX#

-- | actual sqrt call to the hardware for custom type happens here
sqrtFxSplitDbl :: FloatingX -> (Double, Int64)
sqrtFxSplitDbl (FloatingX d e) -- //FIXME FOR zero case
  | even e = (sqrt d, shiftR e 1) -- even
  | otherwise = (sqrtOf2 * sqrt d, shiftR (e - 1) 1) -- odd
{-# INLINE sqrtFxSplitDbl #-}

-- -- | actual sqrt call to the hardware for custom type happens here
-- sqrtSplitDbl# :: FloatingX# -> (# Double#, Int64# #)
-- sqrtSplitDbl# (FloatingX# d# e#)
--   | isTrue# (d# ==## 0.00##) = case minBound :: Int64 of I64# mb# -> (# 0.0##, mb# #)
--   | even (I64# e#) = (# sqrtDouble# d#, e# `quotInt64#` 2#Int64 #) -- even
--   | otherwise = (# 1.4142135623730950488016887242097## *## sqrtDouble# d#, (e# `subInt64#` 1#Int64) `quotInt64#` 2#Int64 #) -- odd sqrt2 times sqrt d#
--   -- | otherwise = (# sqrtDouble# 2.00## *## d#, (e# `subInt64#` 1#Int64) `quotInt64#` 2#Int64 #) -- odd sqrt2 times sqrt d#
-- {-# INLINE sqrtSplitDbl# #-}

-- | actual sqrt call to the hardware for custom type happens here
sqrtFxSplitDbl## :: FloatingX# -> (# Double#, Int64# #)
sqrtFxSplitDbl## (FloatingX# d# e#)
  -- \| isTrue# (d# ==## 0.00##) = case minBound :: Int64 of I64# mb# -> (# 0.0##, mb# #)
  | yesEven = (# sqrtDouble# d#, quo64# #) -- even
  | otherwise = (# 1.4142135623730950488016887242097## *## sqrtDouble# d#, quo64# #) -- odd sqrt2 times sqrt d#
  where
    !(# yesEven, quo64# #) = _evenInt64# e#
{-# INLINE sqrtFxSplitDbl## #-}

fx2Double# :: FloatingX# -> Maybe Double
fx2Double# x@(FloatingX# s# e#) = fx2Double $ FloatingX (D# s#) (I64# e#) -- fromIntegral (I# $ int64ToInt# e#) in fx2Double $ FloatingX (D# s#) ei64
{-# INLINE fx2Double# #-}

fx2Double :: FloatingX -> Maybe Double
fx2Double (FloatingX d@(D# d#) e)
  | isNaN d = Nothing -- error "Input is NaN"
  | isInfinite d = Nothing -- error "Input is Infinity"
  | ex < 0 = Just $ fromIntegral m `divideDouble` (2 ^ (-ex)) -- this is necessary
  | otherwise =
      let !(I# ex#) = ex
          result# = encodeDoubleInteger m ex#
          !result = D# result#
       in if isInfinite result || isNaN result then Nothing else Just result
  where
    !(# m, n# #) = decodeDoubleInteger d#
    !ex = I# n# + fromIntegral e
{-# INLINE fx2Double #-}

unsafefx2Double :: FloatingX -> Double
unsafefx2Double (FloatingX d@(D# d#) e) =
  -- \| ex < 0 = fromIntegral m `divideDouble` (2 ^ (-ex)) -- this is necessary
  -- \| otherwise
  D# (encodeDoubleInteger m ex#)
  where
    !(# m, n# #) = decodeDoubleInteger d#
    !ex@(I# ex#) = I# n# + fromIntegral e
{-# INLINE [2] unsafefx2Double #-}

unsafefx2Double## :: FloatingX# -> Double#
unsafefx2Double## (FloatingX# d# 0#Int64) = d#
unsafefx2Double## (FloatingX# d# e#) =
  -- \| isTrue# (ex# <# 0#) = case fromIntegral m `divideDouble` (2 ^ (-(I# ex#))) of (D# do#) -> do# -- this is necessary
  -- \| otherwise
  encodeDoubleInteger m ex#
  where
    !(# m, n# #) = decodeDoubleInteger d#
    !ex# = n# +# int64ToInt# e#
{-# INLINE unsafefx2Double## #-}

{-# INLINE double2Fx# #-}
double2Fx# :: Double -> FloatingX#
double2Fx# d = case split d of (D# s#, I64# e#) -> FloatingX# s# e# -- let !(D# s#, I64# e#) = split d in FloatingX# s# e#

{-# INLINE double2Fx## #-}
double2Fx## :: Double# -> FloatingX#
double2Fx## d# = case split# d# of (# s#, e# #) -> FloatingX# s# e#

{-# INLINE bigNat2FloatingX## #-}
bigNat2FloatingX## :: BigNat# -> FloatingX#
bigNat2FloatingX## ibn#
  | bigNatIsZero ibn# = zeroFx#
  | itsOKtoUsePlainDoubleCalc = double2Fx## iDouble#
  | otherwise = unsafebigNat2FloatingX## ibn#
  where
    !(D# maxDouble#) = maxDouble
    !iDouble# = bigNatEncodeDouble# ibn# 0#
    !itsOKtoUsePlainDoubleCalc = isTrue# (iDouble# <## (fudgeFactor## *## maxDouble#)) where fudgeFactor## = 1.00## -- for safety it has to land within maxDouble (1.7*10^308) i.e. tC ^ 2 + tA <= maxSafeInteger

{-# INLINE unsafebigNat2FloatingX## #-}
unsafebigNat2FloatingX## :: BigNat# -> FloatingX#
unsafebigNat2FloatingX## ibn# = case cI2D2_ ibn# of (# s#, e_# #) -> FloatingX# s# e_# -- let !(# s#, e_# #) = cI2D2_ ibn# in FloatingX# s# e_# --cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble

{-# INLINE unsafeN2Fx# #-}
unsafeN2Fx# :: Integer -> FloatingX#
unsafeN2Fx# n = case convNToDblExp n of (# s#, e_# #) -> FloatingX# s# e_# -- let !(# s#, e_# #) = cI2D2_ ibn# in FloatingX# s# e_# --cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble

-- | untested. questionable. seems to not work
{-# INLINE unsafeN2Fx #-}
unsafeN2Fx :: Integer -> FloatingX
unsafeN2Fx n = case convNToDblExp n of (# s#, e_# #) -> FloatingX (D# s#) (I64# e_#) -- let !(# s#, e_# #) = cI2D2_ ibn# in FloatingX# s# e_# --cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble

{-# INLINE unsafeGtWordbn2Fx## #-}
unsafeGtWordbn2Fx## :: BigNat# -> FloatingX#
unsafeGtWordbn2Fx## ibn# = case bnToFxGtWord# ibn# of (# s#, e_# #) -> FloatingX# s# e_# -- let !(# s#, e_# #) = cI2D2_ ibn# in FloatingX# s# e_# --cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble

{-# INLINE [2] unsafeGtWordbn2Fx #-}
unsafeGtWordbn2Fx :: BigNat -> FloatingX
unsafeGtWordbn2Fx ibn = case bnToFxGtWord ibn of (s, e_) -> FloatingX s e_ -- let !(# s#, e_# #) = cI2D2_ ibn# in FloatingX# s# e_# --cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble

{-# INLINE int64ToFx# #-}
int64ToFx# :: Int64 -> FloatingX#
int64ToFx# i
  | i == 0 = zeroFx#
  | i < 0 = error "int64ToFx# : invalid negative argument"
  | otherwise = double2Fx# (fromIntegral i)

{-# INLINE unsafeword64ToFx# #-}
{-# SPECIALIZE unsafeword64ToFx# :: Integer -> FloatingX# #-}
unsafeword64ToFx# :: (Integral a) => a -> FloatingX#
unsafeword64ToFx# i = double2Fx# (fromIntegral i)

{-# INLINE unsafeword64ToFloatingX## #-}
unsafeword64ToFloatingX## :: Word64# -> FloatingX#
unsafeword64ToFloatingX## w# = case W64# w# of i -> unsafeword64ToFx# i

-- The maximum integral value that can be unambiguously represented as a
-- Double. Equal to 9,007,199,254,740,991 = maxsafeinteger
{-# INLINE cI2D2_ #-}
cI2D2_ :: BigNat# -> (# Double#, Int64# #)
cI2D2_ bn#
  | isTrue# (bigNatLeWord# bn# 0x1fffffffffffff##) = let d# = word2Double# (bigNatIndex# bn# 0#) in (# d#, 0#Int64 #)
  -- \| isTrue# (bnsz# <# thresh#) = (# bigNatEncodeDouble# bn# 0#, 0#Int64 #)
  | otherwise = case bigNatLog2# bn# of
      --  | otherwise = case _bigNatLog2# bn# bnsz# of
      l# -> case l# `minusWord#` 94## of
        rawSh# ->
          let !shift# = rawSh# `and#` (not# 1##)
           in case bigNatShiftR# bn# shift# of
                -- l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
                --   h# -> let !shift# = (2## `timesWord#` h#) in case bigNatShiftR# bn# shift# of
                mbn# -> (# bigNatEncodeDouble# mbn# 0#, intToInt64# (word2Int# shift#) #)

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
          let !shift# = rawSh# `and#` (not# 1##)
           in case shiftRInteger n (word2Int# shift#) of
                mbn -> case fromIntegral mbn of (D# dmbn#) -> (# dmbn#, intToInt64# (word2Int# shift#) #)

{-# INLINE bnToFxGtWord# #-}
bnToFxGtWord# :: BigNat# -> (# Double#, Int64# #)
bnToFxGtWord# bn# = case bigNatLog2# bn# of
  --  | otherwise = case _bigNatLog2# bn# bnsz# of
  l# -> case l# `minusWord#` 94## of -- //FIXME is shift# calc needed. workd without it.
    rawSh# ->
      let !shift# = rawSh# `and#` (not# 1##)
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
      let !shift = rawSh .&. (complement 1)
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

{-# INLINE [2] nextUpFX #-}
nextUpFX :: FloatingX -> FloatingX
nextUpFX (FloatingX s e)
  | s == 0 = minValueFx
  -- \| otherwise = case nextUp# s# of interimS# -> if isTrue# (interimS# >=## 2.0##) then FloatingX# (interimS# /## 2.00##) (e# `plusInt64#` 1#Int64) else FloatingX# interimS# e#
  | otherwise = case nextUp s of interimS -> FloatingX interimS e

{-# INLINE nextUpFX# #-}
nextUpFX# :: FloatingX# -> FloatingX#
nextUpFX# (FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) = minValueFx#
  -- \| otherwise = case nextUp# s# of interimS# -> if isTrue# (interimS# >=## 2.0##) then FloatingX# (interimS# /## 2.00##) (e# `plusInt64#` 1#Int64) else FloatingX# interimS# e#
  | otherwise = case nextUp# s# of interimS# -> FloatingX# interimS# e#

{-# INLINE nextUpFXNormalized# #-}
nextUpFXNormalized# :: FloatingX# -> FloatingX#
nextUpFXNormalized# (FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) = minValueFx#
  | otherwise = case nextUp# s# of interimS# -> if isTrue# (interimS# >=## 2.0##) then FloatingX# (interimS# /## 2.00##) (e# `plusInt64#` 1#Int64) else FloatingX# interimS# e#

{-# INLINE [2] nextDownFX #-}
nextDownFX :: FloatingX -> FloatingX
nextDownFX x@(FloatingX s e)
  | s == 0.0 || x == minValueFx = zeroFx
  -- \| otherwise = case nextDown# s# of interimS# -> if isTrue# (interimS# <## 1.0##) then FloatingX# (interimS# *## 2.00##) (e# `subInt64#` 1#Int64) else FloatingX# interimS# e#
  | otherwise = case nextDown s of interimS -> FloatingX interimS e

{-# INLINE nextDownFX# #-}
nextDownFX# :: FloatingX# -> FloatingX#
nextDownFX# x@(FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) || x == minValueFx# = zeroFx#
  -- \| otherwise = case nextDown# s# of interimS# -> if isTrue# (interimS# <## 1.0##) then FloatingX# (interimS# *## 2.00##) (e# `subInt64#` 1#Int64) else FloatingX# interimS# e#
  | otherwise = case nextDown# s# of interimS# -> FloatingX# interimS# e#

{-# INLINE nextDownFXNormalized# #-}
nextDownFXNormalized# :: FloatingX# -> FloatingX#
nextDownFXNormalized# x@(FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) || x == minValueFx# = zeroFx#
  | otherwise = case nextDown# s# of interimS# -> if isTrue# (interimS# <## 1.0##) then FloatingX# (interimS# *## 2.00##) (e# `subInt64#` 1#Int64) else FloatingX# interimS# e#
