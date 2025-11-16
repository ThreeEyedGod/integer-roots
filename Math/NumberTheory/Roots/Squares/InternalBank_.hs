{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
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
import Data.Bits.Floating (nextDown, nextUp)
import Data.Word (Word32)
import GHC.Exts (Double (..), word32ToWord#, Double#, Int (..), Int#, Int64#, Word (..), Word#, Word64#, Word32#, and#, build, eqInt64#, eqWord#, eqWord64#, fmaddDouble#, geInt64#, gtInt64#, iShiftRL#, inline, int2Double#, int2Word#, int64ToInt#, int64ToWord64#, intToInt64#, isTrue#, leInt64#, leWord#, minusWord#, neWord#, not#, or#, plusInt64#, plusWord#, plusWord64#, quotInt64#, quotRemWord#, remInt64#, sqrtDouble#, subInt64#, subWord64#, timesInt64#, timesWord#, timesWord2#, timesWord64#, uncheckedShiftL#, uncheckedShiftRL#, word2Double#, word2Int#, word32ToWord#, word64ToInt64#, word64ToWord#, wordToWord64#, (*#), (*##), (**##), (+#), (+##), (-#), (/##), (/=#), (<#), (<##), (<=#), (==##), (>#), (>=#), (>=##))
import GHC.Float (divideDouble, int2Double, integerToDouble#, minusDouble, plusDouble, powerDouble, properFractionDouble, timesDouble)
import GHC.Int (Int64 (I64#))
import GHC.Natural (Natural (..), naturalFromInteger, naturalToInteger, quotRemNatural, timesNatural)
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatAdd, bigNatAddWord, bigNatAddWord#, bigNatEncodeDouble#, bigNatFromWord#, bigNatFromWord2#, bigNatFromWord64#, bigNatGe, bigNatGt, bigNatIndex#, bigNatIsZero, bigNatLeWord, bigNatLeWord#, bigNatLog2, bigNatLog2#, bigNatMul, bigNatMulWord, bigNatMulWord#, bigNatOne#, bigNatQuotRem#, bigNatQuotRemWord#, bigNatShiftL#, bigNatShiftR, bigNatShiftR#, bigNatSize#, bigNatSub, bigNatSubUnsafe, bigNatToWord, bigNatToWordMaybe#, bigNatZero#)
import GHC.Num.Integer (Integer (..), integerToBigNatClamp#, integerToNatural)
import GHC.Num.Natural (Natural (..), naturalAdd, naturalFromBigNat#, naturalMul, naturalShiftL, naturalSub, naturalToBigNat#)
import GHC.Word (Word64 (..))
import Math.NumberTheory.Utils.ArthMtic_
import Math.NumberTheory.Utils.FloatingX_
import Numeric.QuoteQuot
import Prelude hiding (pred)

-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

-- | Iteration loop data
data Itr'' = Itr'' {a# :: {-# UNPACK #-} !Int#, yaccbn :: {-# UNPACK #-} !BigNat#, iRbn :: {-# UNPACK #-} !BigNat#, tbn# :: {-# UNPACK #-} !FloatingX#}

tfi'' :: (Bool, [Word32]) -> (# BigNat#, Word64#, BigNat# #)
tfi'' (evenLen, dxs') = let !i# = word64From2ElemList# dxs' in rmdrFn i#
  where
    !rmdrFn = if evenLen then evenFirstRmdrBN# else oddFirstRmdrBN#

{-# INLINE tni'' #-}
tni'' :: (Word32, Word32) -> Itr'' -> Itr''
tni'' (!i1, !i2) (Itr'' !cl# !yCAcc_ !tA !t#) =
  let !tA_ = (tA `bigNatMul` bnsp) `bigNatAdd` naturalToBigNat# (fromIntegral i1 `naturalMul` radixW32) `bigNatAddWord` fromIntegral i2
      !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
      !(# !(NatJ# (BN# ycUpdated#)), !yTildeFinal#, !(NatJ# (BN# remFinal#)) #) = accRmdrDgt (NatJ# (BN# yCAcc_)) (NatJ# (BN# tA_)) (nxtDgtNatW64# (NatJ# (BN# tA_)) tCFx#)
      !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- tcfx is already scaled by 32. Do not use normalize here
   in -- \| Early termination of tcfx# if more than the 3rd digit or if digit is 0
      Itr'' (cl# +# 1#) ycUpdated# remFinal# tcfx#
  where
    !bnsp = naturalToBigNat# secndPlaceW32Radix -- secondPlaceW32Radix as BigNat# does not fit into word!!!

{-# INLINE tni #-} -- //FIXME unused and untested grab2Word32BN# also needs to be changed to work with Word32 inputs
tni :: (# Word32#, Word32# #) -> Itr'' -> Itr''
tni (# word32ToWord# -> i1, word32ToWord# -> i2 #) (Itr'' !cl# !yCAcc_ !tA !t#) =
  let 
      !(# x1, x2 #) = i1 `timesWord2#` radixW32w#
      !x = bigNatFromWord2# x1 x2 
      !tA_ = (tA `bigNatMul` bnsp) `bigNatAdd` x `bigNatAddWord#` i2
      !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
      !(# !(NatJ# (BN# ycUpdated#)), !yTildeFinal#, !(NatJ# (BN# remFinal#)) #) = accRmdrDgt (NatJ# (BN# yCAcc_)) (NatJ# (BN# tA_)) (nxtDgtNatW64# (NatJ# (BN# tA_)) tCFx#)
      !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- tcfx is already scaled by 32. Do not use normalize here
   in -- \| Early termination of tcfx# if more than the 3rd digit or if digit is 0
      Itr'' (cl# +# 1#) ycUpdated# remFinal# tcfx#
  where
    !bnsp = naturalToBigNat# secndPlaceW32Radix -- secondPlaceW32Radix as BigNat# does not fit into word!!!
    !(W# radixW32w#) = radixW32

nxtDgtNatW64# :: Natural -> FloatingX# -> Word64#
nxtDgtNatW64# 0 !_ = 0#Word64
nxtDgtNatW64# x@(NatJ# n@(BN# bn#)) tcfx#
  | isTrue# ((bigNatSize# bn#) <# thresh#) = inline nxtDgtDoubleFxW64## (bigNatEncodeDouble# bn# 0#) tcfx#
  -- \| otherwise = inline computFxW64# (inline preComputFx## bn# tcfx#)
  | otherwise = case unsafeGtWordbn2Fx## bn# of tAFX# -> if tAFX# !<## threshold# then inline computFxW64# (# tAFX#, tcfx#, tcfx# !**+## tAFX# #) else hndlOvflwW32## (floorXW64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (tcfx# !+## nextDownFX# tcfx#))))
  where
    threshold# = let !(I64# e64#) = 10 ^ 137 in FloatingX# 1.9## e64#
    -- where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgtNatW64# (NatS# ta#) tcfx# = inline nxtDgtDoubleFxW64## (word2Double# ta#) tcfx# -- chances are this branch is never taken (see how squares_. hs is structured)
{-# INLINE nxtDgtNatW64# #-}

nxtDgtDoubleFxW64## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxW64## pa# tcfx# = case inline preComput pa# tcfx# of (# a#, c#, r# #) -> inline computDoubleW64# a# c# r#

{-# INLINE computDouble# #-}
computDouble# :: Double# -> Double# -> Double# -> Integer
computDouble# !tAFX# !tCFX# !radFX# = hndlOvflwW32 $ floor (D# (coreD# tAFX# tCFX# radFX#))

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

accRmdrDgt :: Natural -> Natural -> Word64# -> (# Natural, Word64#, Natural #)
accRmdrDgt yc@(NatS# ycw#) ta@(NatS# taw#) yTw# =
  let !ycScaledBN# = case ycw# `timesWord2#` 0x100000000## of (# hi, lo #) -> bigNatFromWord2# hi lo -- 0x100000000## = 2^32 = radixW32
      !tabn# = bigNatFromWord# taw#
      !(# acc, r, d #) = rmdrDgt ycScaledBN# yTw# tabn#
   in (# NatJ# (BN# acc), d, NatJ# (BN# r) #)
accRmdrDgt yc@(NatJ# (BN# ycbn#)) ta@(NatS# taw#) yTw# =
  let !ycScaledBN# = bigNatMulWord# ycbn# 0x100000000## -- 0x100000000## = 2^32 = radixW32
      !tabn# = bigNatFromWord# taw#
      !(# acc, r, d #) = rmdrDgt ycScaledBN# yTw# tabn#
   in (# NatJ# (BN# acc), d, NatJ# (BN# r) #)
accRmdrDgt yc@(NatS# ycw#) ta@(NatJ# (BN# tabn#)) yTw# =
  let !ycScaledBN# = case ycw# `timesWord2#` 0x100000000## of (# hi, lo #) -> bigNatFromWord2# hi lo -- 0x100000000## = 2^32 = radixW32
      !(# acc, r, d #) = rmdrDgt ycScaledBN# yTw# tabn#
   in (# NatJ# (BN# acc), d, NatJ# (BN# r) #)
accRmdrDgt yc@(NatJ# (BN# ycbn#)) ta@(NatJ# (BN# tabn#)) yTw# =
  let !ycScaledBN# = bigNatMulWord# ycbn# 0x100000000## -- 0x100000000## = 2^32 = radixW32
      !(# acc, r, d #) = rmdrDgt ycScaledBN# yTw# tabn#
   in (# NatJ# (BN# acc), d, NatJ# (BN# r) #)
{-# INLINE accRmdrDgt #-}

subtrahend :: BigNat# -> BigNat# -> BigNat#
subtrahend yScaled# yTilde# = case (yScaled# `bigNatAdd` yScaled#) `bigNatAdd` yTilde# of
  r1# -> r1# `bigNatMul` yTilde#
{-# INLINE subtrahend #-}

rmdrDgt :: BigNat# -> Word64# -> BigNat# -> (# BigNat#, BigNat#, Word64# #)
rmdrDgt ycScaledbn# yTilde# ta# =
  let !sbtnd# = subtrahend ycScaledbn# (bigNatFromWord64# yTilde#)
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

handleFirstRemBN# :: (# Word64#, Integer #) -> (# BigNat#, Word64#, BigNat# #)
handleFirstRemBN# (# yi64#, ri_ #)
  | ri_ < 0 =
      let !yAdj# = yi64# `subWord64#` 1#Word64
          !adjYc = pred ycyi
          !rdr = fixRemainder adjYc ri_
       in (# bigNatFromWord64# yAdj#, yAdj#, integerToBigNatClamp# rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | otherwise = (# bigNatFromWord64# yi64#, yi64#, integerToBigNatClamp# ri_ #)
  where
    !ycyi = fromIntegral (W64# yi64#) -- accumulating the growing square root
{-# INLINE handleFirstRemBN# #-}

-- -- Fix remainder accompanying a 'next downed digit' see algorithm
fixRemainder :: Integer -> Integer -> Integer
fixRemainder !newYc !rdr = rdr + double newYc + 1
{-# INLINE fixRemainder #-}

-- | Find the largest n such that n^2 <= w, where n is even. different for even length list of digits and odd length lists
evenFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
evenFirstRmdrBN# w# =
  let yT64# = hndlOvflwW32## (largestNSqLTEEven## w#)
      ysq# = yT64# `timesWord64#` yT64#
      diff# = word64ToInt64# w# `subInt64#` word64ToInt64# ysq#
   in handleFirstRemBN# (# yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
{-# INLINE evenFirstRmdrBN# #-}

oddFirstRmdrBN# :: Word64# -> (# BigNat#, Word64#, BigNat# #)
oddFirstRmdrBN# w# =
  let yT64# = largestNSqLTEOdd## w#
      ysq# = yT64# `timesWord64#` yT64#
      remIntegerW# = w# `subWord64#` ysq# -- no chance this will be negative
   in (# bigNatFromWord64# yT64#, yT64#, bigNatFromWord64# remIntegerW# #)
{-# INLINE oddFirstRmdrBN# #-}

theFirstIter' :: Bool -> [Word32] -> Itr'' -> Itr''
theFirstIter' evn pairdgt _ = case tfi'' (evn, pairdgt) of (# yVal, yWord#, rem #) -> Itr'' 1# yVal rem (unsafeword64ToFloatingX## yWord#) -- rFinalXs

theNextIters' :: [Word32] -> Itr'' -> Itr''
theNextIters' [x1, x2] (Itr'' currlen# yCumulatedAcc0 rmndr tbfx#) = tni'' (x1, x2) (Itr'' currlen# yCumulatedAcc0 rmndr tbfx#)
theNextIters' _ _ = error "Poor inputs"

-- Equivalent to (`quot` radixw32).
quotremradixW32 :: Word -> (Word, Word)
quotremradixW32 = $$(quoteQuotRem 4294967296)

quotrem1 :: Word -> (Word, Word)
quotrem1 = $$(quoteQuotRem 1)

grab2Words# :: Int -> Word# -> (# Word32, Word32, Word# #)
grab2Words# 1 w# =
  let -- ![W# power1#, W# power2#] = scanr1 (*) [radixW32, 1]
      !(W# digit1#, W# y#) = quotremradixW32 (W# w#)
      -- !(# digit2#, z# #) = y# `quotRemWord#` 1##
      !(W# digit2#, W# z#) = quotrem1 (W# y#)
   in (# fromIntegral (W# digit1#), fromIntegral (W# digit2#), z# #)
grab2Words# 2 w# =
  let -- ![W# power1#, W# power2#] = scanr1 (*) [radixW32, radixW32 ^ (pow - 1)]
      !(# digit1#, y# #) = w# `quotRemWord#` 18446744073709551616##
      !(W# digit2#, W# z#) = quotremradixW32 (W# y#) -- y# `quotRemWord#` power2#
   in (# fromIntegral (W# digit1#), fromIntegral (W# digit2#), z# #)
grab2Words# pow w# =
  -- let ![W# power1#, W# power2#] = scanr1 (*) [radixW32, radixW32 ^ (pow - 1)]
  let ![W# power1#, W# power2#] = scanr1 mulHi [radixW32, radixW32 ^ (pow - 1)]
      !(# digit1#, y# #) = w# `quotRemWord#` power1# -- //FIXME HOW DOES THIS WORK?
      !(# digit2#, z# #) = y# `quotRemWord#` power2#
   in (# fromIntegral (W# digit1#), fromIntegral (W# digit2#), z# #)

grab2Word32BN# :: Int -> BigNat# -> (# Word32, Word32, BigNat# #)
grab2Word32BN# pow n# =
  -- let ![power1, power2] = scanr1 (*) [radixW32, radixW32 ^ (pow - 1)]
  -- let ![power1, power2] = let !x  = radixW32 ^ (pow - 1) in [naturalShiftL x 32, x]
  --     !power1# = naturalToBigNat# power1
  --     !power2# = naturalToBigNat# power2
  let !(I# predpow#) = pow - 1
      !power2# = powBigNat# (int2Word# predpow#)
      !power1# = bigNatShiftL# power2# 32##
      !(# digit1#, ybn# #) = n# `bigNatQuotRem#` power1#
      !(# digit2#, zbn# #) = ybn# `bigNatQuotRem#` power2#
   in (# fromIntegral $ bigNatToWord digit1#, fromIntegral $ bigNatToWord digit2#, zbn# #)

isqrtWord :: Word -> Word
isqrtWord n
  | n < (r * r)
      -- Double interprets values near maxBound as 2^64, we don't have that problem for 32 bits
      || finiteBitSize (0 :: Word) == 64 && r == 4294967296 =
      r - 1
  | otherwise = r
  where
    !r = (fromIntegral :: Int -> Word) . (truncate :: Double -> Int) . sqrt $ fromIntegral n

goWrd :: Bool -> Word# -> Bool -> Int -> Itr'' -> Itr''
goWrd eY w# !firstIter !p !acc
  | p > 0 =
      -- \| not firstIter && p > 0  =
      let !(# digit1, digit2, z# #) = grab2Words# p w#
       in goWrd eY z# False (p - 2) (theNextIters' [digit1, digit2] acc)
  | otherwise = acc -- note the case of 0 was not taken into account before

-- Extract digits from most significant to least significant and process them as they emerge 2 at a time in nextIterations
goBN# :: Bool -> BigNat# -> Bool -> Int -> Itr'' -> Itr''
goBN# eY n# !firstIter !p !acc
  | not firstIter && p >= 1 =
      let !(# digit1, digit2, zbn# #) = grab2Word32BN# p n#
       in go_ eY zbn# False (p - 2) (theNextIters' [digit1, digit2] acc)
  | firstIter && not eY =
      let !(I# pow#) = p
          !pw# = powBigNat# (int2Word# pow#)
          !(# digit#, ybn# #) = n# `bigNatQuotRem#` pw#
       in go_ eY ybn# False (p - 1) (theFirstIter' False [fromIntegral $ bigNatToWord digit#] acc)
  | firstIter && eY =
      let !(# digit1, digit2, zbn# #) = grab2Word32BN# p n#
       in go_ eY zbn# False (p - 2) (theFirstIter' True [digit1, digit2] acc) -- accFn True [fromIntegral digit,fromIntegral digit2] acc
  | p <= 0 = acc -- note the case of 0 was not taken into account before
  | otherwise = error "undefined entry in goBN#"

go_ :: Bool -> BigNat# -> Bool -> Int -> Itr'' -> Itr''
go_ eY bn@(bigNat2WrdMaybe# -> (# wrd, w# #)) !firstIter !p !acc -- uses viewpatterns
  | wrd = goWrd eY w# firstIter p acc -- will only be called in nextiterations (i.w not firstIter)
  | otherwise = goBN# eY bn firstIter p acc
{-# INLINE go_ #-}

bigNat2WrdMaybe# :: BigNat# -> (# Bool, Word# #) -- can also be implemented using NatS# and NatJ#
bigNat2WrdMaybe# bn# = case bigNatToWordMaybe# bn# of
  (# (# #) | #) -> (# False, 0## #)
  (# | w# #) -> (# True, w# #)
{-# INLINE bigNat2WrdMaybe# #-}

newappsqrt_ :: Int -> Bool -> Natural -> Natural
newappsqrt_ l eY n@(NatS# w#) = let !(W# wo#) = isqrtWord (W# w#) in NatS# wo#
newappsqrt_ l eY n@(NatJ# nbn@(BN# nbn#)) = NatJ# (BN# $ yaccbn $ go_ eY nbn# True (l - 1) (Itr'' 1# (bnConst# 0) (bnConst# 0) zeroFx#))
