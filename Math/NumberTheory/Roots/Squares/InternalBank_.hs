{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- {-# OPTIONS -ddump-simpl -ddump-to-file -dsuppress-all  #-}
-- -ddump-stg-final -dverbose-core2core -dsuppress-all -ddump-prep -dsuppress-idinfo -ddump-stg

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
module Math.NumberTheory.Roots.Squares.InternalBank_ (newappsqrt_) where

-- \*********** BEGIN NEW IMPORTS
import Data.Bits (finiteBitSize)
import GHC.Exts (Double (..), Double#, Int (..), Int#, Int64#, Int8#, Word (..), Word#, Word64#, and#, eqWord64#, fmaddDouble#, gtWord#, inline, int64ToWord64#, isTrue#, ltInt64#, ltInt8#, plusInt64#, plusInt8#, quotInt#, shiftL#, sqrtDouble#, subInt64#, subWord64#, timesInt64#, timesWord64#, uncheckedShiftRL#, word2Int#, word64ToInt64#, word64ToWord#, wordToWord64#, (+#), (+##), (-#), (/##), (==#))
import GHC.Float.RealFracMethods (floorDoubleInt)
import GHC.Natural (Natural (..))
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatAdd, bigNatAddWord#, bigNatEncodeDouble#, bigNatFromWord#, bigNatFromWord64#, bigNatIndex#, bigNatLog2#, bigNatMulWord#, bigNatShiftL#, bigNatSizeInBase#, bigNatSub, bigNatSubUnsafe)
import GHC.Num.Primitives (Bool#)
import GHC.Prim (int2Word#)
import Math.NumberTheory.Utils.ArthMtic_
import Math.NumberTheory.Utils.FloatingX_

-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

data Itr = Itr {bnn# :: {-# UNPACK #-} !BigNat#, idx# :: {-# UNPACK #-} !Int#, a# :: {-# UNPACK #-} !Int8#, yaccbn :: {-# UNPACK #-} !BigNat#, iRbn :: {-# UNPACK #-} !BigNat#, tbn# :: {-# UNPACK #-} !FloatingX#}

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
newappsqrt_ n@(NatJ# (BN# nbn#)) =
  let !szT# = bigNatSizeInBase# 4294967296#Word nbn#
      !(# !evnLen#, !szF# #) = if even (W# szT#) then (# 1#, word2Int# szT# `quotInt#` 2# #) else (# 0#, 1# +# word2Int# szT# `quotInt#` 2# #)
   in tni (tfi evnLen# nbn# (szF# -# 1#))
{-# NOINLINE newappsqrt_ #-}

{-# NOINLINE tfi #-}
tfi :: Bool# -> BigNat# -> Int# -> Itr
tfi !evnLen# !bn# !iidx# =
  let -- //FIXME see if indexing can be avoided
      !i# = let !w# = bigNatIndex# bn# iidx# in word64FromWordRvsrdTuple## (# w# `and#` 0xffffffff##, w# `uncheckedShiftRL#` 32# #)
      !(# yVal, yWord#, rm #) = rmdrFn i#
   in Itr bn# iidx# 1#Int8 yVal rm (unsafeword64ToFloatingX## yWord#)
  where
    !rmdrFn = if isTrue# (evnLen# ==# 1#) then evenFirstRmdrBN# else oddFirstRmdrBN#
    -- \| Find the largest n such that n^2 <= w, where n is even. different for even length list of digits and odd length lists
    evenFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
    evenFirstRmdrBN# !w# =
      let qr w =
            let y = largestNSqLTE## w
                diff = word64ToInt64# w `subInt64#` word64ToInt64# (y `timesWord64#` y)
             in (# y, diff #)
       in handleFirstRemBN## (qr w#)
    {-# INLINABLE evenFirstRmdrBN# #-}
    oddFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
    oddFirstRmdrBN# !w# =
      let qr w =
            let y = largestNSqLTE## w
                diff = w `subWord64#` (y `timesWord64#` y) -- no chance this will be negative
             in (# bigNatFromWord64# y, y, bigNatFromWord64# diff #)
       in qr w#
    {-# INLINABLE oddFirstRmdrBN# #-}
    handleFirstRemBN## :: (# Word64#, Int64# #) -> (# BigNat#, Word64#, BigNat# #)
    handleFirstRemBN## (# yi64#, ri_ #) =
      let qr y r
            | isTrue# (r `ltInt64#` 0#Int64) =
                let !y_ = y `subWord64#` 1#Word64
                    !rdr = fixRemainder# y_ r
                 in (# bigNatFromWord64# y_, y_, bigNatFromWord64# rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
            | otherwise = (# bigNatFromWord64# y, y, bigNatFromWord64# (int64ToWord64# r) #)
       in qr yi64# ri_
    {-# INLINABLE handleFirstRemBN## #-}

    -- -- Fix remainder accompanying a 'next downed digit' see algorithm
    fixRemainder# :: Word64# -> Int64# -> Word64#
    fixRemainder# !newYc# !rdr# = let x = rdr# `plusInt64#` 2#Int64 `timesInt64#` word64ToInt64# newYc# `plusInt64#` 1#Int64 in if isTrue# (x `ltInt64#` 0#Int64) then 0#Word64 else int64ToWord64# x
    {-# INLINABLE fixRemainder# #-}

{-# NOINLINE tni #-}
tni :: Itr -> Natural
tni (Itr _ 0# _ !yCAcc_ _ _) = NatJ# (BN# yCAcc_) -- final accumulator is the result
tni (Itr !bn# !idxx# !cl# !yCAcc_ !tA !t#) =
  let !tA_ =
        -- //FIXME see if indexing can be avoided
        let !(# i1w32#, i2w32# #) = let !w# = bigNatIndex# bn# (idxx# -# 1#) in (# w# `uncheckedShiftRL#` 32#, w# `and#` 0xffffffff## #) -- max of either of them is 2^32-1
         in let !x1 = i1w32# `shiftL#` 32# in (tA `bigNatShiftL#` 64##) `bigNatAdd` bigNatFromWord# x1 `bigNatAddWord#` i2w32#
      !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
      !(# !ycUpdated#, !remFinal#, !yTildeFinal#, yTildeFinalFx# #) = let !yt = nxtDgtNatW64## tA_ tCFx# in rmdrDgt (bigNatShiftL# yCAcc_ 32##) yt tA_ -- (bigNatMulWord# yCAcc_ 0x100000000##) === 0x100000000## = 2^32 = radixW32
      -- !tcfx# = if isTrue# (cl# <# 3#) then tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- tcfx is already scaled by 32. Do not use normalize here
      -- weirdly the above and below are both about the same
      !itr_ = if isTrue# (cl# `ltInt8#` 3#Int8) then Itr bn# (idxx# -# 1#) (cl# `plusInt8#` 1#Int8) ycUpdated# remFinal# (tCFx# !+## yTildeFinalFx## (# yTildeFinal#, yTildeFinalFx# #)) else Itr bn# (idxx# -# 1#) cl# ycUpdated# remFinal# tCFx# -- tcfx is already scaled by 32. Do not use normalize here
   in tni itr_ -- \| Early termination of tcfx# if more than the 3rd digit or if digit is 0. Also dont bother to increment it, once => 3Int8#.
  where
    yTildeFinalFx## :: (# Word64#, FloatingX# #) -> FloatingX#
    yTildeFinalFx## (# !w#, !fx# #) = case fx# == zeroFx# of
      True -> if isTrue# (w# `eqWord64#` 0#Word64) then zeroFx# else unsafeword64ToFloatingX## w#
      !_ -> fx#
    {-# INLINABLE yTildeFinalFx## #-}

    rmdrDgt :: BigNat# -> (# Word64#, FloatingX# #) -> BigNat# -> (# BigNat#, BigNat#, Word64#, FloatingX# #)
    rmdrDgt !ycScaledbn# (# yTilde#, yTildeFx# #) ta# =
      let !sbtnd# = subtrahend# ycScaledbn# yTilde#
          !ytrdr = case ta# `bigNatSub` sbtnd# of
            (# | res# #) -> (# ycScaledbn# `bigNatAddWord#` word64ToWord# yTilde#, res#, yTilde#, yTildeFx# #)
            _ ->
              -- bigNat thankfully returns a zero if they are equal and it would go into above branch
              let !res# = sbtnd# `bigNatSubUnsafe` ta# -- since we know resTrial < 0 and this is safe
               in let !adjyt = yTilde# `subWord64#` 1#Word64
                      !adjacc = ycScaledbn# `bigNatAddWord#` word64ToWord# adjyt
                      !adjres = (adjacc `bigNatMulWord#` 2## `bigNatAddWord#` 1##) `bigNatSubUnsafe` res#
                   in (# adjacc, adjres, adjyt, unsafeword64ToFloatingX## adjyt #) -- aligned fx# value to updated yTilde#
       in ytrdr
    {-# INLINABLE rmdrDgt #-}

    subtrahend# :: BigNat# -> Word64# -> BigNat#
    subtrahend# !yScaled# !yTilde# = let !wyTilde# = word64ToWord# yTilde# in ((yScaled# `bigNatAdd` yScaled#) `bigNatAddWord#` wyTilde#) `bigNatMulWord#` wyTilde#
    {-# INLINABLE subtrahend# #-}

nxtDgtNatW64## :: BigNat# -> FloatingX# -> (# Word64#, FloatingX# #)
nxtDgtNatW64## !bn# !tcfx#
  | isTrue# (ln# `gtWord#` threshW#) = inline computFxW64# (inline preComputFx## bn# ln# tcfx#) -- note the gtWord
  | otherwise = (# inline nxtDgtDoubleFxW64## (bigNatEncodeDouble# bn# 0#) tcfx#, zeroFx# #) -- only 8 cases land here in tests
  where
    !ln# = bigNatLog2# bn# -- //FIXME is this necessary and can it be used in the other branch too
    !threshW# = 512## -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
{-# INLINABLE nxtDgtNatW64## #-}

nxtDgtDoubleFxW64## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxW64## !pa# !tcfx# = case inline preComput pa# tcfx# of (# a_#, c#, r# #) -> inline computDoubleW64# a_# c# r#
{-# INLINABLE nxtDgtDoubleFxW64## #-}

preComput :: Double# -> FloatingX# -> (# Double#, Double#, Double# #)
preComput !ax# !tcfx# = case unsafefx2Double## tcfx# of c# -> (# ax#, c#, fmaddDouble# c# c# ax# #)
{-# INLINABLE preComput #-}

{-# INLINABLE computDoubleW64# #-}
computDoubleW64# :: Double# -> Double# -> Double# -> Word64#
computDoubleW64# !tAFX# !tCFX# !radFX# = case floorDoubleInt (D# (coreD# tAFX# tCFX# radFX#)) of (I# iI#) -> wordToWord64# (int2Word# iI#)

coreD# :: Double# -> Double# -> Double# -> Double#
coreD# !da# !dc# !dr# = da# /## (sqrtDouble# dr# +## dc#)
{-# INLINABLE coreD# #-}

preComputFx## :: BigNat# -> Word# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
preComputFx## !tA__bn# !lgn# !tCFX# = case unsafeGtWordbn2Fx## tA__bn# lgn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINABLE preComputFx## #-}

computFxW64# :: (# FloatingX#, FloatingX#, FloatingX# #) -> (# Word64#, FloatingX# #)
computFxW64# (# !tAFX#, !tCFX#, !radFX# #) = let !w64Fx# = coreFx# (# tAFX#, tCFX#, radFX# #) in (# floorXW64## w64Fx#, w64Fx# #)
{-# INLINABLE computFxW64# #-}

coreFx# :: (# FloatingX#, FloatingX#, FloatingX# #) -> FloatingX#
coreFx# (# !tAFX#, !tCFX#, !radFX# #) = tAFX# !/## (sqrtFX# radFX# !+## tCFX#)
{-# INLINABLE coreFx# #-}
