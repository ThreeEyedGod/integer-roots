{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE ViewPatterns #-}

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
import Data.Word (Word32)
import GHC.Exts (Double (..), Double#, Int (..), Int#, Int64#, Word (..), Word#, Word32#, Word64#, and#, build, eqInt64#, eqWord#, eqWord64#, fmaddDouble#, geInt64#, gtInt64#, iShiftRL#, indexWordArray#, inline, int2Double#, int2Word#, int64ToInt#, int64ToWord64#, intToInt64#, isTrue#, leInt64#, leWord#, ltInt64#, minusWord#, neWord#, not#, or#, plusInt64#, plusWord#, plusWord64#, quotInt64#, quotRemWord#, remInt64#, sqrtDouble#, subInt64#, subWord64#, timesInt64#, timesWord#, timesWord2#, timesWord64#, uncheckedShiftL#, uncheckedShiftRL#, word2Double#, word2Int#, word32ToWord#, word64ToInt64#, word64ToWord#, wordToWord32#, wordToWord64#, (*#), (*##), (**##), (+#), (+##), (-#), (/##), (/=#), (<#), (<##), (<=#), (==#), (==##), (>#), (>=#), (>=##))
import GHC.Int (Int64 (I64#))
import GHC.Natural (Natural (..))
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatAdd, bigNatAddWord, bigNatAddWord#, bigNatEncodeDouble#, bigNatFromWord#, bigNatFromWord2#, bigNatFromWord64#, bigNatGe, bigNatGt, bigNatIndex#, bigNatIsZero, bigNatIsZero#, bigNatLeWord, bigNatLeWord#, bigNatLog2, bigNatLog2#, bigNatMul, bigNatMulWord, bigNatMulWord#, bigNatOne#, bigNatQuotRem#, bigNatQuotRemWord#, bigNatShiftL#, bigNatShiftR, bigNatShiftR#, bigNatSize#, bigNatSub, bigNatSubUnsafe, bigNatToWord, bigNatToWord#, bigNatToWordMaybe#, bigNatZero#)
import GHC.Num.Natural (naturalToBigNat#)
import GHC.Word (Word32 (..), Word64 (..))
import Math.NumberTheory.Utils.ArthMtic_
import Math.NumberTheory.Utils.FloatingX_

-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

tfi :: (Bool, (Word32, Word32)) -> (# BigNat#, Word64#, BigNat# #)
tfi (evenLen, (m, l)) = let !i# = word64FromRvsrdTuple# (l, m) 4294967296#Word64 in rmdrFn i#
  where
    !rmdrFn = if evenLen then evenFirstRmdrBN# else oddFirstRmdrBN#

{-# INLINE tni #-}
tni :: (# Word32#, Word32# #) -> Itr'' -> Itr'' -- // FIXME remove itr'' and just pass parameters
tni (# word32ToWord# -> i1, word32ToWord# -> i2 #) (Itr'' !cl# !yCAcc_ !tA !t#) =
  let !(# x1, x2 #) = i1 `timesWord2#` radixW32w#
      !x = bigNatFromWord2# x1 x2
      !tA_ = (tA `bigNatMul` bnsp) `bigNatAdd` x `bigNatAddWord#` i2
      !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
      !(# ycUpdated#, remFinal#, !yTildeFinal# #) = rmdrDgt (bigNatMulWord# yCAcc_ 0x100000000##) (nxtDgtNatW64## tA_ tCFx#) tA_ -- 0x100000000## = 2^32 = radixW32
      !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- tcfx is already scaled by 32. Do not use normalize here
   in -- \| Early termination of tcfx# if more than the 3rd digit or if digit is 0
      Itr'' (cl# +# 1#) ycUpdated# remFinal# tcfx#
  where
    !bnsp = naturalToBigNat# secndPlaceW32Radix -- secondPlaceW32Radix as BigNat# does not fit into word!!!
    !(W# radixW32w#) = radixW32

nxtDgtNatW64## :: BigNat# -> FloatingX# -> Word64#
nxtDgtNatW64## bn# tcfx#
  | isTrue# (bigNatIsZero# bn#) = 0#Word64
  | isTrue# (sz# ==# 1#),
    a0 <- indexWordArray# bn# 0# =
      inline nxtDgtDoubleFxW64## (word2Double# a0) tcfx#
  | isTrue# (sz# <# thresh#) = inline nxtDgtDoubleFxW64## (bigNatEncodeDouble# bn# 0#) tcfx#
  -- \| otherwise = inline computFxW64# (inline preComputFx## bn# tcfx#)
  -- //TODO WHAT'S EXACTLY HAPPENING HERE
  | otherwise = case unsafeGtWordbn2Fx## bn# of tAFX# -> if tAFX# !<## threshold# then inline computFxW64# (# tAFX#, tcfx#, tcfx# !**+## tAFX# #) else hndlOvflwW32## (floorXW64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (tcfx# !+## nextDownFX# tcfx#))))
  where
    sz# = bigNatSize# bn#
    threshold# = let !(I64# e64#) = 10 ^ 137 in FloatingX# 1.9## e64#
    -- where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
{-# INLINE nxtDgtNatW64## #-}

nxtDgtDoubleFxW64## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxW64## pa# tcfx# = case inline preComput pa# tcfx# of (# a#, c#, r# #) -> inline computDoubleW64# a# c# r#

coreD# :: Double# -> Double# -> Double# -> Double#
coreD# da# dc# dr# = nextUp# (nextUp# da# /## nextDown# (sqrtDouble# (nextDown# dr#) +## nextDown# dc#))
{-# INLINE coreD# #-}

coreFx# :: (# FloatingX#, FloatingX#, FloatingX# #) -> FloatingX#
coreFx# (# tAFX#, tCFX#, radFX# #) =
  nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))
{-# INLINE coreFx# #-}

{-# INLINE computDoubleW64# #-}
computDoubleW64# :: Double# -> Double# -> Double# -> Word64#
computDoubleW64# !tAFX# !tCFX# !radFX# = case floor (D# (coreD# tAFX# tCFX# radFX#)) of (W64# w#) -> hndlOvflwW32## w#

computFxW64# :: (# FloatingX#, FloatingX#, FloatingX# #) -> Word64#
computFxW64# (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwW32## (floorXW64## (coreFx# (# tAFX#, tCFX#, radFX# #)))
-- hndlOvflwW32## (floorXW64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE computFxW64# #-}

preComput :: Double# -> FloatingX# -> (# Double#, Double#, Double# #)
preComput a# tcfx# = case unsafefx2Double## tcfx# of c# -> (# a#, c#, fmaddDouble# c# c# a# #)
{-# INLINE preComput #-}

preComputFx## :: BigNat# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
preComputFx## tA__bn# tCFX# = case unsafeGtWordbn2Fx## tA__bn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE preComputFx## #-}

subtrahend# :: BigNat# -> Word64# -> BigNat#
subtrahend# yScaled# yTilde# = case (yScaled# `bigNatAdd` yScaled#) `bigNatAddWord#` wyTilde# of
  r1# -> r1# `bigNatMulWord#` wyTilde#
  where
    !wyTilde# = word64ToWord# yTilde#
{-# INLINE subtrahend# #-}

rmdrDgt :: BigNat# -> Word64# -> BigNat# -> (# BigNat#, BigNat#, Word64# #)
rmdrDgt ycScaledbn# yTilde# ta# =
  let !sbtnd# = subtrahend# ycScaledbn# yTilde#
      !reg = ta# `bigNatGe` sbtnd#
      !res# = case reg of
        True -> ta# `bigNatSubUnsafe` sbtnd#
        _ -> sbtnd# `bigNatSubUnsafe` ta#
      !ytrdr =
        if reg
          then
            (# ycScaledbn# `bigNatAddWord#` word64ToWord# yTilde#, res#, yTilde# #)
          else
            let adjyt = yTilde# `subWord64#` 1#Word64
                adjacc = ycScaledbn# `bigNatAddWord#` word64ToWord# adjyt
                adjres = (adjacc `bigNatMulWord#` 2## `bigNatAdd` oneBigNat#) `bigNatSubUnsafe` res#
             in (# adjacc, adjres, adjyt #)
   in -- (# ((ycScaledbn# `bigNatAddWord#` word64ToWord# yTilde# `bigNatSubUnsafe` oneBigNat#) `bigNatMulWord#` 2## `bigNatAdd` oneBigNat#) `bigNatSubUnsafe` res#, yTilde# `subWord64#` 1#Word64 #) -- watch out negate does not work
      ytrdr
  where
    oneBigNat# :: BigNat#
    !oneBigNat# = bigNatOne# (# #)
{-# INLINE rmdrDgt #-}

handleFirstRemBN## :: (# Word64#, Int64# #) -> (# BigNat#, Word64#, BigNat# #)
handleFirstRemBN## (# yi64#, ri_ #)
  | isTrue# (ri_ `ltInt64#` zero) =
      let !yAdj# = yi64# `subWord64#` 1#Word64
          !rdr = fixRemainder# yAdj# ri_
       in (# bigNatFromWord64# yAdj#, yAdj#, bigNatFromWord64# rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | otherwise = (# bigNatFromWord64# yi64#, yi64#, bigNatFromWord64# (int64ToWord64# ri_) #)
  where
    !(I64# zero) = 0
{-# INLINE handleFirstRemBN## #-}

-- -- Fix remainder accompanying a 'next downed digit' see algorithm
fixRemainder# :: Word64# -> Int64# -> Word64#
fixRemainder# !newYc# !rdr# = let x = rdr# `plusInt64#` two `timesInt64#` word64ToInt64# newYc# `plusInt64#` one in if isTrue# (x `ltInt64#` zero) then 0#Word64 else int64ToWord64# x
  where
    !(I64# two) = 2
    !(I64# one) = 1
    !(I64# zero) = 0
{-# INLINE fixRemainder# #-}

-- | Find the largest n such that n^2 <= w, where n is even. different for even length list of digits and odd length lists
evenFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
evenFirstRmdrBN# w# =
  let yT64# = hndlOvflwW32## (largestNSqLTEEven## w#)
      ysq# = yT64# `timesWord64#` yT64#
      diff# = word64ToInt64# w# `subInt64#` word64ToInt64# ysq#
   in handleFirstRemBN## (# yT64#, diff# #) -- set 0 for starting cumulative yc--fstDgtRem i
{-# INLINE evenFirstRmdrBN# #-}

oddFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
oddFirstRmdrBN# w# =
  let yT64# = largestNSqLTEOdd## w#
      ysq# = yT64# `timesWord64#` yT64#
      remIntegerW# = w# `subWord64#` ysq# -- no chance this will be negative
   in (# bigNatFromWord64# yT64#, yT64#, bigNatFromWord64# remIntegerW# #)
{-# INLINE oddFirstRmdrBN# #-}

grab2Word32BN## :: Int -> BigNat# -> (# Word32#, Word32#, BigNat# #) -- a more efficient version for Int = 1
grab2Word32BN## 1 !n#
  | isTrue# (bigNatSize# n# ==# 1#),
    a0 <- indexWordArray# n# 0# =
      let -- power2# = 1 -- radixW32 ^ (1 - 1) = radixW32 ^ 0 = 1 ; -- !(W# power1#) = radixW32 --bigNatShiftL# power2# 32##
          !(W# digit1#, W# yw#) = quotremradixW32 (W# a0)
          !(W# digit2#, W# z#) = quotrem1 (W# yw#) -- !(# digit2#, zbn# #) = ybn# `bigNatQuotRemWord#` power2#
       in (# wordToWord32# digit1#, wordToWord32# digit2#, bigNatFromWord# z# #)
  | otherwise =
      let -- power2# = 1 -- radixW32 ^ (1 - 1) = radixW32 ^ 0 = 1
          !(W# power1#) = radixW32 -- bigNatShiftL# power2# 32##
          !(# digit1#, yw# #) = n# `bigNatQuotRemWord#` power1#
          !(W# digit2#, W# z#) = quotrem1 (W# yw#) -- !(# digit2#, zbn# #) = ybn# `bigNatQuotRemWord#` power2#
       in (# wordToWord32# (bigNatToWord# digit1#), wordToWord32# digit2#, bigNatFromWord# z# #)
grab2Word32BN## 2 !n# -- //FIXME does this work correctly ? check
  | isTrue# (bigNatSize# n# ==# 1#),
    a0 <- indexWordArray# n# 0# =
      let -- power2# = 1 -- radixW32 ^ (1 - 1) = radixW32 ^ 0 = 1 ; -- !(W# power1#) = radixW32 --bigNatShiftL# power2# 32##
          !(W# digit1#, W# yw#) = (0, W# a0) -- a0 `quotRemWord#` 18446744073709551616## -- 18446744073709551616## = 2^64 = radixW32 ^ 2
          !(W# digit2#, W# z#) = quotremradixW32 (W# yw#) -- !(# digit2#, zbn# #) = ybn# `bigNatQuotRemWord#` power2#
       in (# wordToWord32# digit1#, wordToWord32# digit2#, bigNatFromWord# z# #)
  | otherwise =
      let -- power2# = 1 -- radixW32 ^ (1 - 1) = radixW32 ^ 0 = 1
          !(W# power1#) = radixW32 -- bigNatShiftL# power2# 32##
          !(# digit1#, yw# #) = n# `bigNatQuotRemWord#` power1#
          !(W# digit2#, W# z#) = quotrem1 (W# yw#) -- !(# digit2#, zbn# #) = ybn# `bigNatQuotRemWord#` power2#
       in (# wordToWord32# (bigNatToWord# digit1#), wordToWord32# digit2#, bigNatFromWord# z# #)
grab2Word32BN## !pow !n# =
  let !(I# predpow#) = pow - 1
      !power2# = powBigNat# (int2Word# predpow#) -- let ![power1, power2] = scanr1 (*) [radixW32, radixW32 ^ (pow - 1)]
      !power1# = bigNatShiftL# power2# 32## -- let ![power1, power2] = let !x  = radixW32 ^ (pow - 1) in [naturalShiftL x 32, x]
      !(# digit1#, ybn# #) = n# `bigNatQuotRem#` power1#
      !(# digit2#, zbn# #) = ybn# `bigNatQuotRem#` power2#
   in (# wordToWord32# (bigNatToWord# digit1#), wordToWord32# (bigNatToWord# digit2#), zbn# #)
{-# INLINE grab2Word32BN## #-}

data Itr'' = Itr'' {a# :: {-# UNPACK #-} !Int#, yaccbn :: {-# UNPACK #-} !BigNat#, iRbn :: {-# UNPACK #-} !BigNat#, tbn# :: {-# UNPACK #-} !FloatingX#}
newappsqrt_ :: Int -> Bool -> Natural -> Natural
newappsqrt_ l eY n@(NatS# w#) = let !(W# wo#) = isqrtWord (W# w#) in NatS# wo# where 
  isqrtWord :: Word -> Word
  isqrtWord n
    | n < (r * r)
        -- Double interprets values near maxBound as 2^64, we don't have that problem for 32 bits
        || finiteBitSize (0 :: Word) == 64 && r == 4294967296 =
        r - 1
    | otherwise = r
    where
      !r = (fromIntegral :: Int -> Word) . (truncate :: Double -> Int) . sqrt $ fromIntegral n

newappsqrt_ l eY n =
  let -- NatJ# (BN# $ yaccbn $ goBN# eY nbn# True (l - 1) (Itr'' 1# (bnConst# 0) (bnConst# 0) zeroFx#))
      !(NatJ# (BN# nbn#)) = n
   in NatJ# (BN# $ yaccbn $ goBN# eY nbn# True (l - 1) (Itr'' 1# (bnConst# 0) (bnConst# 0) zeroFx#))
  where 
    -- Extract digits from most significant to least significant and process them as they emerge 2 at a time in nextIterations
  goBN# :: Bool -> BigNat# -> Bool -> Int -> Itr'' -> Itr''
  goBN# !evn !n# !firstIter !p !acc
    | p <= 0 = acc
    | not firstIter -- && p >= 1 =
      =
        let !(# digit1, digit2, zbn# #) = grab2Word32BN## p n#
        in goBN# evn zbn# False (p - 2) (theNextIters (# digit1, digit2 #) acc)
    | firstIter && not evn =
        let !(I# pow#) = p
            !pw# = powBigNat# (int2Word# pow#)
            !(# digit#, ybn# #) = n# `bigNatQuotRem#` pw#
        in goBN# evn ybn# False (p - 1) (theFirstIter False (0, fromIntegral $ bigNatToWord digit#) acc)
    | otherwise -- firstIter && evn =
      =
        let !(# digit1, digit2, zbn# #) = grab2Word32BN## p n#
        in goBN# evn zbn# False (p - 2) (theFirstIter True (W32# digit1, W32# digit2) acc)
  {-# INLINE goBN# #-}
  -- | Iteration loop data
  theFirstIter :: Bool -> (Word32, Word32) -> Itr'' -> Itr''
  theFirstIter evn pairdgt _ = case tfi (evn, pairdgt) of (# yVal, yWord#, rem #) -> Itr'' 1# yVal rem (unsafeword64ToFloatingX## yWord#)
  {-# INLINE theFirstIter #-}
  theNextIters :: (# Word32#, Word32# #) -> Itr'' -> Itr''
  theNextIters (# x1, x2 #) (Itr'' currlen# yCumulatedAcc0 rmndr tbfx#) = tni (# x1, x2 #) (Itr'' currlen# yCumulatedAcc0 rmndr tbfx#)
  {-# INLINE theNextIters #-}
{-# INLINE newappsqrt_ #-}
