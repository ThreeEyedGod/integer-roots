{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- {-# OPTIONS -ddump-simpl -ddump-to-file -dsuppress-all  #-}
-- -ddump-stg-final -dverbose-core2core -dsuppress-all -ddump-prep -dsuppress-idinfo -ddump-stg

-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump-simpl or ddump-asm -ddump-to-file dumps else not
-- removed -fexpose-all-unfoldings may not necessarily help improve max performance. See https://well-typed.com/blog/2024/04/choreographing-specialization-pt1/
-- {-# OPTIONS_GHC -O2 -threaded -optl-m64  -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr -fstrictness -funbox-small-strict-fields  -fmax-worker-args=32 -optc-O3 -optc-ffast-math #-}

-- |
-- Module:      Math.NumberTheory.Roots.Squares.Internal
-- Copyright:   (c) 2011 Daniel Fischer, 2016-2020 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Internal functions dealing with square roots. End-users should not import this module.
-- {-# OPTIONS -ddump-simpl -ddump-to-file #-}
module Math.NumberTheory.Roots.Squares.Internal_
  ( karatsubaSqrt,
    isqrtB_,
  )
where

-- \*********** BEGIN NEW IMPORTS

import Data.Bits (finiteBitSize, unsafeShiftL, unsafeShiftR, (.&.), (.|.))
import GHC.Exts (Double (..), Double#, Int (..), Int#, Int64#, Int8#, Word (..), Word#, Word64#, and#, eqWord64#, fmaddDouble#, gtWord#, inline, int2Word#, int64ToWord64#, isTrue#, ltInt64#, ltInt8#, plusInt64#, plusInt8#, quotInt#, shiftL#, sqrtDouble#, subInt64#, subWord64#, timesInt64#, timesWord64#, uncheckedShiftRL#, word2Int#, word64ToInt64#, word64ToWord#, wordToWord64#, (+#), (+##), (-#), (/##), (==#))
import GHC.Float.RealFracMethods (floorDoubleInt)
import GHC.Natural (Natural (..))
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatAdd, bigNatAddWord#, bigNatEncodeDouble#, bigNatFromWord#, bigNatFromWord64#, bigNatIndex#, bigNatLog2#, bigNatMulWord#, bigNatShiftL#, bigNatSizeInBase#, bigNatSub, bigNatSubUnsafe)
import GHC.Num.Integer (integerFromNatural, integerLog2#)
import Math.NumberTheory.Utils.ArthMtic_
import Math.NumberTheory.Utils.FloatingX_

-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

{-# SPECIALIZE isqrtB_ :: Integer -> Integer #-}
isqrtB_ :: (Integral a) => a -> a
isqrtB_ 0 = 0
isqrtB_ n = fromInteger . integerFromNatural . newappsqrt_ . fromIntegral $ n

{-# INLINEABLE isqrtB_ #-}

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
      !(# !evnLen, !szF# #) = if even (W# szT#) then (# True, word2Int# szT# `quotInt#` 2# #) else (# False, 1# +# word2Int# szT# `quotInt#` 2# #)
   in tni (tfi evnLen nbn# (szF# -# 1#))
{-# INLINEABLE newappsqrt_ #-}

{-# INLINEABLE tfi #-}
tfi :: Bool -> BigNat# -> Int# -> Itr
tfi !evnLen !bn# !iidx# =
  let -- //FIXME see if indexing can be avoided
      !i# = let !w# = bigNatIndex# bn# iidx# in word64FromWordRvsrdTuple## (# w# `and#` 0xffffffff##, w# `uncheckedShiftRL#` 32# #)
      !(# yVal, yWord#, rm #) = rmdrFn i#
   in Itr bn# iidx# 1#Int8 yVal rm (unsafeword64ToFloatingX## yWord#)
  where
    !rmdrFn = if evnLen then evenFirstRmdrBN# else oddFirstRmdrBN#
    -- \| Find the largest n such that n^2 <= w, where n is even. different for even length list of digits and odd length lists
    evenFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
    evenFirstRmdrBN# !w# =
      let qr w =
            let y = largestNSqLTE## w
                diff = word64ToInt64# w `subInt64#` word64ToInt64# (y `timesWord64#` y)
             in (# y, diff #)
       in handleFirstRemBN## (qr w#)
    {-# INLINEABLE evenFirstRmdrBN# #-}
    oddFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
    oddFirstRmdrBN# !w# =
      let qr w =
            let y = largestNSqLTE## w
                diff = w `subWord64#` (y `timesWord64#` y) -- no chance this will be negative
             in (# bigNatFromWord64# y, y, bigNatFromWord64# diff #)
       in qr w#
    {-# INLINEABLE oddFirstRmdrBN# #-}
    handleFirstRemBN## :: (# Word64#, Int64# #) -> (# BigNat#, Word64#, BigNat# #)
    handleFirstRemBN## (# yi64#, ri_ #) =
      let qr y r
            | isTrue# (r `ltInt64#` 0#Int64) =
                let !y_ = y `subWord64#` 1#Word64
                    !rdr = fixRemainder# y_ r
                 in (# bigNatFromWord64# y_, y_, bigNatFromWord64# rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
            | otherwise = (# bigNatFromWord64# y, y, bigNatFromWord64# (int64ToWord64# r) #)
       in qr yi64# ri_
    {-# INLINEABLE handleFirstRemBN## #-}

    -- -- Fix remainder accompanying a 'next downed digit' see algorithm
    fixRemainder# :: Word64# -> Int64# -> Word64#
    fixRemainder# !newYc# !rdr# = let x = rdr# `plusInt64#` 2#Int64 `timesInt64#` word64ToInt64# newYc# `plusInt64#` 1#Int64 in if isTrue# (x `ltInt64#` 0#Int64) then 0#Word64 else int64ToWord64# x
    {-# INLINEABLE fixRemainder# #-}

{-# INLINEABLE tni #-}
tni :: Itr -> Natural
tni (Itr _ 0# _ !yCAcc_ _ _) = NatJ# (BN# yCAcc_) -- final accumulator is the result
tni (Itr !bn# !idxx# !cl# !yCAcc_ !tA !t#) =
  let !idyy# = idxx# -# 1#
      !tA_ =
        -- //FIXME see if indexing can be avoided
        let !(# i1w32#, i2w32# #) = let !w# = bigNatIndex# bn# idyy# in (# w# `uncheckedShiftRL#` 32#, w# `and#` 0xffffffff## #) -- max of either of them is 2^32-1
         in let !x1 = i1w32# `shiftL#` 32# in (tA `bigNatShiftL#` 64##) `bigNatAdd` bigNatFromWord# x1 `bigNatAddWord#` i2w32#
      !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
      !(# !ycUpdated#, !remFinal#, !yTildeFinal#, yTildeFinalFx# #) = let !yt = nxtDgtNatW64## tA_ tCFx# in rmdrDgt (bigNatShiftL# yCAcc_ 32##) yt tA_ -- (bigNatMulWord# yCAcc_ 0x100000000##) === 0x100000000## = 2^32 = radixW32
      -- !tcfx# = if isTrue# (cl# <# 3#) then tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- tcfx is already scaled by 32. Do not use normalize here
      -- weirdly the above and below are both about the same
      !itr_ = if isTrue# (cl# `ltInt8#` 3#Int8) then Itr bn# idyy# (cl# `plusInt8#` 1#Int8) ycUpdated# remFinal# (tCFx# !+## yTildeFinalFx## (# yTildeFinal#, yTildeFinalFx# #)) else Itr bn# idyy# cl# ycUpdated# remFinal# tCFx# -- tcfx is already scaled by 32. Do not use normalize here
   in tni itr_ -- \| Early termination of tcfx# if more than the 3rd digit or if digit is 0. Also dont bother to increment it, once => 3Int8#.
  where
    yTildeFinalFx## :: (# Word64#, FloatingX# #) -> FloatingX#
    yTildeFinalFx## (# !w#, !fx# #) = case fx# == zeroFx# of
      True -> if isTrue# (w# `eqWord64#` 0#Word64) then zeroFx# else unsafeword64ToFloatingX## w#
      !_ -> fx#
    {-# INLINEABLE yTildeFinalFx## #-}

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
    {-# INLINEABLE rmdrDgt #-}

    subtrahend# :: BigNat# -> Word64# -> BigNat#
    subtrahend# !yScaled# !yTilde# = let !wyTilde# = word64ToWord# yTilde# in ((yScaled# `bigNatAdd` yScaled#) `bigNatAddWord#` wyTilde#) `bigNatMulWord#` wyTilde#
    {-# INLINEABLE subtrahend# #-}

nxtDgtNatW64## :: BigNat# -> FloatingX# -> (# Word64#, FloatingX# #)
nxtDgtNatW64## !bn# !tcfx#
  | isTrue# (ln# `gtWord#` threshW#) = computFxW64# (preComputFx## bn# ln# tcfx#) -- note the gtWord
  | otherwise = (# nxtDgtDoubleFxW64## (bigNatEncodeDouble# bn# 0#) tcfx#, zeroFx# #) -- only 8 cases land here in tests
  where
    !ln# = bigNatLog2# bn# -- //FIXME is this necessary and can it be used in the other branch too
    !threshW# = 512## -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
{-# INLINEABLE nxtDgtNatW64## #-}

nxtDgtDoubleFxW64## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxW64## !pa# !tcfx# = case preComput pa# tcfx# of (# a_#, c#, r# #) -> computDoubleW64# a_# c# r#

{-# DUMMY nxtDgtDoubleFxW64## #-}

preComput :: Double# -> FloatingX# -> (# Double#, Double#, Double# #)
preComput !ax# !tcfx# = case unsafefx2Double## tcfx# of c# -> (# ax#, c#, fmaddDouble# c# c# ax# #)

{-# DUMMY preComput #-}

{-# DUMMY computDoubleW64# #-}
computDoubleW64# :: Double# -> Double# -> Double# -> Word64#
computDoubleW64# !tAFX# !tCFX# !radFX# = case floorDoubleInt (D# (coreD# tAFX# tCFX# radFX#)) of (I# iI#) -> wordToWord64# (int2Word# iI#)

coreD# :: Double# -> Double# -> Double# -> Double#
coreD# !da# !dc# !dr# = da# /## (sqrtDouble# dr# +## dc#)

{-# DUMMY coreD# #-}

preComputFx## :: BigNat# -> Word# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
preComputFx## !tA__bn# !lgn# !tCFX# = case unsafeGtWordbn2Fx## tA__bn# lgn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINEABLE preComputFx## #-}

computFxW64# :: (# FloatingX#, FloatingX#, FloatingX# #) -> (# Word64#, FloatingX# #)
computFxW64# (# !tAFX#, !tCFX#, !radFX# #) = let !w64Fx# = coreFx# (# tAFX#, tCFX#, radFX# #) in (# floorXW64## w64Fx#, w64Fx# #)
{-# INLINEABLE computFxW64# #-}

coreFx# :: (# FloatingX#, FloatingX#, FloatingX# #) -> FloatingX#
coreFx# (# !tAFX#, !tCFX#, !radFX# #) = tAFX# !/## (sqrtFX# radFX# !+## tCFX#)
{-# INLINEABLE coreFx# #-}

{-# INLINEABLE karatsubaSqrt #-}
karatsubaSqrt :: Integer -> (Integer, Integer)
karatsubaSqrt 0 = (0, 0)
karatsubaSqrt n
  | lgN < 2300 =
      let s = isqrtB_ n in (s, n - s * s)
  | otherwise =
      if lgN .&. 2 /= 0
        then
          karatsubaStep k (karatsubaSplit k n)
        else
          -- before we split n into 4 part we must ensure that the first part
          -- is at least 2^k/4, since this doesn't happen here we scale n by
          -- multiplying it by 4
          let n' = n `unsafeShiftL` 2
              (s, r) = karatsubaStep k (karatsubaSplit k n')
              r'
                | s .&. 1 == 0 = r
                | otherwise = r + double s - 1
           in (s `unsafeShiftR` 1, r' `unsafeShiftR` 2)
  where
    k = lgN `unsafeShiftR` 2 + 1
#ifdef MIN_VERSION_integer_gmp
    lgN = I# (integerLog2# n)
#else
    lgN = I# (word2Int# (integerLog2# n))
#endif

{-# INLINEABLE karatsubaStep #-}
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
    {-# INLINEABLE cat #-}

{-# INLINEABLE karatsubaSplit #-}
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
