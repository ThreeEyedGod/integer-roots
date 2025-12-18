{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump-simpl or ddump-asm dumps else not
-- removed -fexpose-all-unfoldings may not necessarily help improve max performance. See https://well-typed.com/blog/2024/04/choreographing-specialization-pt1/
-- {-# OPTIONS_GHC -Wmissed-specialisations -O2 -fkeep-auto-rules -threaded -optl-m64 -fliberate-case -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr -fstrictness -funbox-small-strict-fields  -fmax-worker-args=32 -optc-O3 -optc-ffast-math -optc-march=native -optc-mfpmath=sse #-}

-- |
-- Module:      Math.NumberTheory.Roots.Squares.Internal
-- Copyright:   (c) 2011 Daniel Fischer, 2016-2020 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Internal functions dealing with square roots. End-users should not import this module.
-- {-# OPTIONS -ddump-simpl -ddump-to-file #-}
module Math.NumberTheory.Roots.Squares.InternalBank_ where

-- \*********** BEGIN NEW IMPORTS
import Data.Bits (finiteBitSize)
import GHC.Exts (Double (..), Double#, Int (I#), Int#, Int64#, Word (..), Word#, Word64#, and#, eqWord#, eqWord64#, fmaddDouble#, gtWord#, inline, int64ToWord64#, isTrue#, ltInt64#, plusInt64#, quotInt#, sqrtDouble#, subInt64#, subWord64#, timesInt64#, timesWord2#, timesWord64#, uncheckedShiftRL#, word64ToInt64#, word64ToWord#, (*#), (+#), (+##), (-#), (/##), (<#), (==#))
import GHC.Int (Int64 (I64#))
import GHC.Natural (Natural (..))
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatAdd, bigNatZero#, bigNatAddWord#, bigNatEncodeDouble#, bigNatFromWord2#, bigNatFromWord64#, bigNatIndex#, bigNatLog2#, bigNatMul, bigNatMulWord#, bigNatOne#, bigNatSize#, bigNatSub, bigNatSubUnsafe, bigNatZero#)
import GHC.Num.Natural (naturalToBigNat#)
import GHC.Num.Primitives (Bool#)
import GHC.Word (Word64 (..))
import Math.NumberTheory.Utils.ArthMtic_
import Math.NumberTheory.Utils.FloatingX_

-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

data Itr = Itr {bnn# :: {-# UNPACK #-} !BigNat#, idx# :: {-# UNPACK #-} !Int#, a# :: {-# UNPACK #-} !Int#, yaccbn :: {-# UNPACK #-} !BigNat#, iRbn :: {-# UNPACK #-} !BigNat#, tbn# :: {-# UNPACK #-} !FloatingX#}

newappsqrt_ :: Natural -> Natural
newappsqrt_ n@(NatS# w#) = let !(W# wo#) = isqrtWord (W# w#) in NatS# wo# -- //FIXME insert our logic < 63 excised before here and check
  where
    isqrtWord :: Word -> Word
    isqrtWord x
      | x < (r * r)
          -- Double interprets values near maxBound as 2^64, we don't have that problem for 32 bits
          || finiteBitSize (0 :: Word) == 64 && r == 4294967296 =
          r - 1
      | otherwise = r
      where
        !r = (fromIntegral :: Int -> Word) . (truncate :: Double -> Int) . sqrt $ fromIntegral x
newappsqrt_ n@(NatJ# (BN# nbn#)) = -- //FIXME check to use wide-word package
  let !l@(I# l#) = lenRadixW32 n
      !(# evnLen#, szF# #) = if even l then (# 1#, l# `quotInt#` 2# #) else (# 0#, (l# +# 1#) `quotInt#` 2# #)
    in tni (tfi evnLen# nbn# (szF# -# 1#)) 
{-# INLINE newappsqrt_ #-}

{-# INLINE tfi #-}
tfi :: Bool# -> BigNat# -> Int# -> Itr
tfi !evnLen# bn# iidx#  =
  let
      !w# = bigNatIndex# bn# iidx# -- Word# for the limb (bigNat is little-endian, 64-bit) -- //FIXME see if indexing can be avoided
      !(# m#, l# #) = (# w# `uncheckedShiftRL#` 32#, w# `and#` 0xffffffff## #) -- Fast bit extraction instead of quotRemWord#: shift & mask are faster than division
      !i# = word64FromWordRvsrdTuple## (# l#, m# #) 4294967296#Word64
      !(# yVal, yWord#, rm #) = rmdrFn i#
   in Itr bn# iidx# 1# yVal rm (unsafeword64ToFloatingX## yWord#)
  where
    !rmdrFn = if isTrue# (evnLen# ==# 1#) then evenFirstRmdrBN# else oddFirstRmdrBN#
    -- \| Find the largest n such that n^2 <= w, where n is even. different for even length list of digits and odd length lists
    evenFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
    evenFirstRmdrBN# !w# =
      let yT64# = largestNSqLTE## w#
          ysq# = yT64# `timesWord64#` yT64#
          diff# = word64ToInt64# w# `subInt64#` word64ToInt64# ysq#
       in handleFirstRemBN## (# yT64#, diff# #) -- set 0 for starting cumulative yc--fstDgtRem i
      -- {-# INLINE evenFirstRmdrBN# #-}
    oddFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
    oddFirstRmdrBN# !w# =
      let yT64# = largestNSqLTE## w#
          ysq# = yT64# `timesWord64#` yT64#
          remIntegerW# = w# `subWord64#` ysq# -- no chance this will be negative
       in (# bigNatFromWord64# yT64#, yT64#, bigNatFromWord64# remIntegerW# #)
    -- {-# INLINE oddFirstRmdrBN# #-}

    handleFirstRemBN## :: (# Word64#, Int64# #) -> (# BigNat#, Word64#, BigNat# #)
    handleFirstRemBN## (# yi64#, ri_ #)
      | isTrue# (ri_ `ltInt64#` zero) =
          let !yAdj# = yi64# `subWord64#` 1#Word64
              !rdr = fixRemainder# yAdj# ri_
           in (# bigNatFromWord64# yAdj#, yAdj#, bigNatFromWord64# rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
      | otherwise = (# bigNatFromWord64# yi64#, yi64#, bigNatFromWord64# (int64ToWord64# ri_) #)
      where
        !(I64# zero) = 0
    -- {-# INLINE handleFirstRemBN## #-}

    -- -- Fix remainder accompanying a 'next downed digit' see algorithm
    fixRemainder# :: Word64# -> Int64# -> Word64#
    fixRemainder# !newYc# !rdr# = let x = rdr# `plusInt64#` two `timesInt64#` word64ToInt64# newYc# `plusInt64#` one in if isTrue# (x `ltInt64#` zero) then 0#Word64 else int64ToWord64# x
      where
        !(I64# two) = 2
        !(I64# one) = 1
        !(I64# zero) = 0

-- {-# INLINE fixRemainder# #-}

{-# INLINE tni #-}
tni :: Itr -> Natural 
tni (Itr _ 0# _ !yCAcc_ _ _) = NatJ# (BN# yCAcc_) -- final accumulator is the result
tni (Itr bn# idxx# !cl# !yCAcc_ !tA !t#) = 
  let 
      !w# = bigNatIndex# bn# (idxx# -# 1#)-- Word# for the limb (bigNat is little-endian, 64-bit) -- //FIXME see if indexing can be avoided
      !(# i1#, i2# #) = (# w# `uncheckedShiftRL#` 32#, w# `and#` 0xffffffff## #) -- Fast bit extraction instead of quotRemWord#: shift & mask are faster than division
      !(# x1, x2 #) = i1# `timesWord2#` radixW32w#
      !x = bigNatFromWord2# x1 x2
      !tA_ = (tA `bigNatMul` bnsp) `bigNatAdd` x `bigNatAddWord#` i2#
      !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
      !(# !ycUpdated#, !remFinal#, !yTildeFinal#, yTildeFinalFx# #) = let !yt = nxtDgtNatW64## tA_ tCFx# in rmdrDgt (bigNatMulWord# yCAcc_ 0x100000000##) yt tA_ -- 0x100000000## = 2^32 = radixW32
      !tcfx# = if isTrue# (cl# <# 3#) then tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- tcfx is already scaled by 32. Do not use normalize here
      -- weirdly the above is faster
      -- !tcfx# = if isTrue# (cl# <# 3#) then tCFx# !+## yTildeFinalFx## (# yTildeFinal#, yTildeFinalFx# #)  else tCFx# -- tcfx is already scaled by 32. Do not use normalize here
   in -- \| Early termination of tcfx# if more than the 3rd digit or if digit is 0
      tni (Itr bn# (idxx# -# 1#) (cl# +# 1#) ycUpdated# remFinal# tcfx#)
  where
    !bnsp = naturalToBigNat# secndPlaceW32Radix -- secondPlaceW32Radix as BigNat# does not fit into word!!!
    !(W# radixW32w#) = radixW32

    yTildeFinalFx## :: (# Word64#, FloatingX# #) -> FloatingX#
    yTildeFinalFx## (# !w#, !fx# #) = case fx# == zeroFx# of
      True -> if isTrue# (w# `eqWord64#` 0#Word64) then zeroFx# else unsafeword64ToFloatingX## w#
      !_ -> fx#
    {-# INLINE yTildeFinalFx## #-}

    rmdrDgt :: BigNat# -> (# Word64#, FloatingX# #) -> BigNat# -> (# BigNat#, BigNat#, Word64#, FloatingX# #)
    rmdrDgt !ycScaledbn# (# yTilde#, yTildeFx# #) ta# =
      let !sbtnd# = subtrahend# ycScaledbn# yTilde#
          !resTrial = ta# `bigNatSub` sbtnd#
          !ytrdr = case resTrial of
            (# | res# #) -> (# ycScaledbn# `bigNatAddWord#` word64ToWord# yTilde#, res#, yTilde#, yTildeFx# #)
            _ ->
              -- bigNat thankfully returns a zero if they are equal and it would go into above branch
              let !res# = sbtnd# `bigNatSubUnsafe` ta# -- since we know resTrial < 0 and this is safe
               in let !adjyt = yTilde# `subWord64#` 1#Word64
                      !adjacc = ycScaledbn# `bigNatAddWord#` word64ToWord# adjyt
                      !oneBigNat# = bigNatOne# (# #)
                      !adjres = (adjacc `bigNatMulWord#` 2## `bigNatAdd` oneBigNat#) `bigNatSubUnsafe` res#
                   in (# adjacc, adjres, adjyt, unsafeword64ToFloatingX## adjyt #) -- aligned fx# value to updated yTilde#
       in ytrdr
    {-# INLINE rmdrDgt #-}

    subtrahend# :: BigNat# -> Word64# -> BigNat#
    subtrahend# !yScaled# !yTilde# = case (yScaled# `bigNatAdd` yScaled#) `bigNatAddWord#` wyTilde# of
      !r1# -> r1# `bigNatMulWord#` wyTilde#
      where
        !wyTilde# = word64ToWord# yTilde#
    {-# INLINE subtrahend# #-}

nxtDgtNatW64## :: BigNat# -> FloatingX# -> (# Word64#, FloatingX# #)
nxtDgtNatW64## !bn# !tcfx#
  | isTrue# (ln# `gtWord#` threshW#) = inline computFxW64# (inline preComputFx## bn# ln# tcfx#) -- note the gtWord
  | itsZero = (# 0#Word64, zeroFx# #)
  | otherwise = (# inline nxtDgtDoubleFxW64## (bigNatEncodeDouble# bn# 0#) tcfx#, zeroFx# #) -- only 8 cases land here in tests
  where
    !ln# = bigNatLog2# bn#
    itsZero = isTrue# (ln# `eqWord#` 0##) -- lets this be lazy
    !threshW# = 512## -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
{-# INLINE nxtDgtNatW64## #-}

nxtDgtDoubleFxW64## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxW64## !pa# !tcfx# = case inline preComput pa# tcfx# of (# a#, c#, r# #) -> inline computDoubleW64# a# c# r#
{-# INLINE nxtDgtDoubleFxW64## #-}

preComput :: Double# -> FloatingX# -> (# Double#, Double#, Double# #)
preComput !ax# !tcfx# = case unsafefx2Double## tcfx# of c# -> (# ax#, c#, fmaddDouble# c# c# ax# #)
{-# INLINE preComput #-}

{-# INLINE computDoubleW64# #-}
computDoubleW64# :: Double# -> Double# -> Double# -> Word64#
computDoubleW64# !tAFX# !tCFX# !radFX# = case floor (D# (coreD# tAFX# tCFX# radFX#)) of (W64# w#) -> w#

coreD# :: Double# -> Double# -> Double# -> Double#
coreD# !da# !dc# !dr# = da# /## (sqrtDouble# dr# +## dc#)
{-# INLINE coreD# #-}

preComputFx## :: BigNat# -> Word# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
preComputFx## !tA__bn# !lgn# !tCFX# = case unsafeGtWordbn2Fx## tA__bn# lgn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE preComputFx## #-}

computFxW64# :: (# FloatingX#, FloatingX#, FloatingX# #) -> (# Word64#, FloatingX# #)
computFxW64# (# !tAFX#, !tCFX#, !radFX# #) = let !w64Fx# = coreFx# (# tAFX#, tCFX#, radFX# #) in (# floorXW64## w64Fx#, w64Fx# #)
{-# INLINE computFxW64# #-}

coreFx# :: (# FloatingX#, FloatingX#, FloatingX# #) -> FloatingX#
coreFx# (# tAFX#, tCFX#, radFX# #) = tAFX# !/## (sqrtFX# radFX# !+## tCFX#)
{-# INLINE coreFx# #-}
