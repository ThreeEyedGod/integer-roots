{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE UnboxedTuples #-}

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

import Data.List (foldl', unfoldr)
import Data.Bits.Floating (nextDown, nextUp)
import Data.Primitive.ByteArray (ByteArray, byteArrayFromList, foldrByteArray)
import qualified Data.Vector.Unboxed as VU
import Data.Word (Word32)
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
    inline,
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
import GHC.Float (divideDouble, int2Double, integerToDouble#, minusDouble, plusDouble, powerDouble, properFractionDouble, timesDouble)
import GHC.Int (Int64 (I64#))
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatEncodeDouble#, bigNatIndex#, bigNatIsZero, bigNatLeWord#, bigNatLog2, bigNatLog2#, bigNatShiftR, bigNatShiftR#, bigNatSize#)
import GHC.Num.Integer (Integer (..))
import GHC.Word (Word64 (..))
import Math.NumberTheory.Utils.ArthMtic_
import Math.NumberTheory.Utils.FloatingX_
import Prelude hiding (pred)

-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

-- | Iteration loop data - these records have vectors / lists in them
data ItrLst_ = ItrLst_ {lvlst# :: {-# UNPACK #-} !Int#, lstW32 :: {-# UNPACK #-} ![Word64], yCumulative_ :: !Integer, iRem :: {-# UNPACK #-} !Integer, tb___# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)
data ItrLstPP = ItrLstPP {lpp# :: {-# UNPACK #-} !Int#, lstW32pp :: {-# UNPACK #-} ![Word32], yCumulativePP :: !Integer, iRemPP :: {-# UNPACK #-} !Integer, tbPP# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

data ItrBA = ItrBA {lBA :: Int#, ba :: !ByteArray, ycBA :: Integer, irBA :: !Integer, tbBAFx :: !FloatingX#} deriving (Eq)

data ItrUV = ItrUV {luv :: Int#, uv :: !(VU.Vector Word64), ycuv :: !Integer, iruv :: !Integer, tbuvFx :: !FloatingX#} deriving (Eq)

data Itr__ = Itr__ {lv__# :: {-# UNPACK #-} !Int#, yCumulative___ :: !Integer, iRem___ :: {-# UNPACK #-} !Integer, tb__# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

data Itr' = Itr' {lv'# :: {-# UNPACK #-} !Int#, yCumulative' :: !Integer, iRem' :: {-# UNPACK #-} !Integer, tb' :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

theFirstCore :: (Bool, [Word32]) -> (# Integer, Word64#, Integer #)
theFirstCore (evenLen, dxs') = let !i# = word64FromRvsrd2ElemList# dxs' in rmdrFn i#
  where
    !rmdrFn = if evenLen then evenFirstRmdr else oddFirstRmdr

theFirstXs :: (Bool, [Word64], [Word32]) -> ItrLst_
theFirstXs (evenLen, passXs, dxs') = case theFirstCore (evenLen, dxs') of
  (# !yVal, !yWord#, !remInteger #) -> ItrLst_ 1# passXs yVal remInteger (unsafeword64ToFloatingX## yWord#)

-- | operates on normal list MSB -> LSB
theFirstCoreN :: (Bool, [Word32]) -> (# Integer, Word64#, Integer #)
theFirstCoreN (evenLen, dxs') = let !i# = word64From2ElemList# dxs' in rmdrFn i#
  where
    !rmdrFn = if evenLen then evenFirstRmdr else oddFirstRmdr

-- | operates on normal list MSB -> LSB
theFirstXsN :: (Bool, [Word64], [Word32]) -> ItrLst_
theFirstXsN (evenLen, passXs, dxs') = case theFirstCoreN (evenLen, dxs') of
  (# !yVal, !yWord#, !remInteger #) -> ItrLst_ 1# passXs yVal remInteger (unsafeword64ToFloatingX## yWord#)

-- | operates on normal list MSB -> LSB
theFirstPostProcess :: (Bool, [Word32]) -> (# Integer, Word64#, Integer #)
theFirstPostProcess (evenLen, dxs') = let !i# = word64From2ElemList# dxs' in rmdrFn i#
  where
    !rmdrFn = if evenLen then evenFirstRmdr else oddFirstRmdr

-- | operates on normal list MSB -> LSB
theFirstXsPostProcess :: (Bool, [Word32], [Word32]) -> ItrLstPP
theFirstXsPostProcess (evenLen, passXs, dxs') = case theFirstPostProcess (evenLen, dxs') of
  (# !yVal, !yWord#, !remInteger #) -> ItrLstPP 1# passXs yVal remInteger (unsafeword64ToFloatingX## yWord#)

theFirstBA :: (Bool, ByteArray, [Word32]) -> ItrBA
theFirstBA (evenLen, passBA, dxs') = case theFirstCore (evenLen, dxs') of
  (# !yVal, !yWord#, !remInteger #) -> ItrBA 1# passBA yVal remInteger (unsafeword64ToFloatingX## yWord#)

theFirstUV :: (Bool, VU.Vector Word64, [Word32]) -> ItrUV
theFirstUV (evenLen, passUV, dxs') = case theFirstCore (evenLen, dxs') of
  (# !yVal, !yWord#, !remInteger #) -> ItrUV 1# passUV yVal remInteger (unsafeword64ToFloatingX## yWord#)

{-# SPECIALIZE tniCore :: Integer -> Itr__ -> Itr__ #-}
{-# SPECIALIZE tniCore :: Word64 -> Itr__ -> Itr__ #-}
{-# SPECIALIZE tniCore :: Int64 -> Itr__ -> Itr__ #-}
{-# INLINE tniCore #-}
tniCore :: (Integral a) => a -> Itr__ -> Itr__
tniCore i (Itr__ !cl# !yCAcc_ !tA !t#) =
  let !tA_ = tA * secndPlaceW32Radix + fromIntegral i
      !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
      !(# ycUpdated, !yTildeFinal#, remFinal #) = computeRemW64# yCAcc_ tA_ (nxtDgtW64# tA_ tCFx#)
      !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
   in Itr__ (cl# +# 1#) ycUpdated remFinal tcfx# -- rFinalXs

{-# INLINE tniCorePP #-}
tniCorePP :: (Word32, Word32) -> Itr__ -> Itr__
tniCorePP (i1,i2) (Itr__ !cl# !yCAcc_ !tA !t#) =
  let !tA_ = tA * secndPlaceW32Radix + fromIntegral i1 * radixW32 + fromIntegral i2
      !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
      !(# ycUpdated, !yTildeFinal#, remFinal #) = computeRemW64# yCAcc_ tA_ (nxtDgtW64# tA_ tCFx#)
      !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
   in Itr__ (cl# +# 1#) ycUpdated remFinal tcfx# -- rFinalXs

theNextIterations :: ItrLst_ -> Integer -- //FIXME wrd64Xs should not be strict so that it can be streamed?
theNextIterations (ItrLst_ !currlen# wrd64Xs !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ foldr' tniCore (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) (fromIntegral <$> wrd64Xs)

theNextIterationsBA :: ItrBA -> Integer
theNextIterationsBA (ItrBA !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ foldrByteArray tni (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tni #-}
    tni :: Word64 -> Itr__ -> Itr__
    tni = tniCore

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
theNextIterationsUV :: ItrUV -> Integer
theNextIterationsUV (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ VU.foldr' tniCore (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
theNextIterationsUVI :: ItrUV -> Integer
theNextIterationsUVI (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ VU.foldr' tniCore (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
{-# NOINLINE theNextIterationsUVI #-}

theNextIterationsUVIrvrsd :: ItrUV -> Integer
theNextIterationsUVIrvrsd (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ VU.foldl' tniRvr (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tniRvr #-}
    tniRvr :: Itr__ -> Word64 -> Itr__
    tniRvr = flip tniCore

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
{-# NOINLINE theNextIterationsUVIrvrsd #-}

{-# INLINE theNextIterationsRvrsdSLCode #-}

toItr__ :: ItrLst_ -> Itr__
toItr__ (ItrLst_ l _ y r t) = Itr__ l y r t

fromPPtoItr__ :: ItrLstPP -> Itr__
fromPPtoItr__ (ItrLstPP l _ y r t) = Itr__ l y r t

-- | SL = Straight Line Code
theNextIterationsRvrsdSLCode :: ItrLst_ -> Integer
theNextIterationsRvrsdSLCode itrxs@(ItrLst_ !currlen# !wrd64Xs@(_) !yCumulatedAcc0 !rmndr !tbfx#) = yCumulative___ $ foldl' tniRvrsdSL (toItr__ itrxs) wrd64Xs -- inline go wrd64Xs (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#)
  where
    tniRvrsdSL :: Itr__ -> Word64 -> Itr__
    tniRvrsdSL = flip tniCore
    {-# INLINE tniRvrsdSL #-}
    go :: [Word64] -> Itr__ -> Integer
    go [] itracc = yCumulative___ itracc
    go (x1 : x2 : x3 : x4 : x5 : x6 : x7 : x8 : zs) acc = go zs (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL acc x1) x2) x3) x4) x5) x6) x7) x8)
    go (x1 : x2 : x3 : x4 : x5 : x6 : x7 : zs) acc = go zs ((tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL acc x1) x2) x3) x4) x5) x6) x7))
    go (x1 : x2 : x3 : x4 : x5 : x6 : zs) acc = go zs ((tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL acc x1) x2) x3) x4) x5) x6))
    go (x1 : x2 : x3 : x4 : zs) acc = go zs (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL (tniRvrsdSL acc x1) x2) x3) x4)
    go (x1 : x2 : zs) (Itr__ !cl# !yCAcc_ !tA !t#) =
      let !tA_ = tA * secndPlaceW32Radix + toInteger x1
          !tCFx# = inline scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
          !(# ycUpdated, !yTildeFinal#, remFinal #) = case inline nxtDgtW64# tA_ tCFx# of yTilde_# -> inline computeRemW64# yCAcc_ tA_ yTilde_#
          !tcfx# = if isTrue# (cl# <# 3#) then inline nextDownFX# $ tCFx# !+## inline unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
          !tA__ = remFinal * secndPlaceW32Radix + toInteger x2
          !tCFx__# = inline scaleByPower2# 32#Int64 tcfx# -- sqrtF previous digits being scaled right here
          !(# ycUpdated__, !yTildeFinal__#, remFinal__ #) = case inline nxtDgtW64# tA__ tCFx__# of yTilde__# -> inline computeRemW64# ycUpdated tA__ yTilde__#
          !tcfx__# = if isTrue# ((cl# +# 1#) <# 3#) then inline nextDownFX# $ tCFx__# !+## inline unsafeword64ToFloatingX## yTildeFinal__# else tCFx__# -- recall tcfx is already scaled by 32. Do not use normalize here
       in go zs (Itr__ (cl# +# 2#) ycUpdated__ remFinal__ tcfx__#) -- rFinalXs
    go [x1] itracc = go [] (inline tniRvrsdSL itracc x1)

-- | SL = Straight Line Code
theNextIterationsN_ :: ItrLst_ -> Integer
theNextIterationsN_ itrxs@(ItrLst_ !currlen# wrd64Xs !yCumulatedAcc0 !rmndr !tbfx#) = yCumulative___ $ foldl' tniRvrsdSL (toItr__ itrxs) wrd64Xs -- inline go wrd64Xs (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#)
  where
    tniRvrsdSL :: Itr__ -> Word64 -> Itr__
    tniRvrsdSL = flip tniCore
    {-# INLINE tniRvrsdSL #-}

-- Step 1: Pair up the list
pairUp :: [Word32] -> [(Word32, Word32)]
pairUp (x:y:rest) = (x, y) : pairUp rest
pairUp _          = []  -- drop last if odd number

pairUpUnfoldr :: [Word32] -> [(Word32, Word32)]
pairUpUnfoldr = unfoldr step
  where
    step (x:y:rest) = Just ((x, y), rest)
    step _          = Nothing

theNextIterationsPP :: Int -> ItrLstPP -> Integer
theNextIterationsPP len itrxs@(ItrLstPP !currlen# wrd32Xs !yCumulatedAcc0 !rmndr !tbfx#) = yCumulative___ $ foldl' tniRvrsdPP (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) (pairUpUnfoldr wrd32Xs) -- inline go wrd64Xs (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#)
  where
    tniRvrsdPP :: Itr__ -> (Word32, Word32) -> Itr__
    tniRvrsdPP = flip tniCorePP
    {-# INLINE tniRvrsdPP #-}


-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0

-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgtW64# :: Integer -> FloatingX# -> Word64#
-- nxtDgtW64# n tcfx# = computFxW64# (allInclusivePreComputNToFx## n tcfx#) -- works ! but not any faster
nxtDgtW64# 0 !_ = 0#Word64
nxtDgtW64# (IP bn#) tcfx# -- = computFxW64# (allInclusivePreComputFx## bn# tcfx#) -- works but not faster
  | isTrue# ((bigNatSize# bn#) <# thresh#) = inline nxtDgtDoubleFxW64## (bigNatEncodeDouble# bn# 0#) tcfx#
  -- \| otherwise = inline computFxW64# (inline preComputFx## bn# tcfx#)
  | otherwise = case unsafeGtWordbn2Fx## bn# of tAFX# -> if tAFX# !<## threshold# then inline computFxW64# (# tAFX#, tcfx#, tcfx# !**+## tAFX# #) else hndlOvflwW32## (floorXW64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (tcfx# !+## nextDownFX# tcfx#))))
  where
    threshold# = let !(I64# e64#) = 10 ^ 137 in FloatingX# 1.9## e64#
    -- where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgtW64# (IS ta#) tcfx# = inline nxtDgtDoubleFxW64## (int2Double# ta#) tcfx# -- chances are this branch is never taken (see how squares_. hs is structured)
nxtDgtW64# (IN _) !_ = error "nxtDgtW64# :: Invalid negative integer argument"

nxtDgtDoubleFxW64## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxW64## pa# tcfx# = case inline preComput pa# tcfx# of (# a#, c#, r# #) -> inline computDoubleW64# a# c# r#

nxtDgtDoubleFxHrbie## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxHrbie## pa# tcfx# = case isTrue# (c# <## threshold#) of
  True -> inline computDoubleW64# pa# c# (fmaddDouble# c# c# pa#)
  False -> case floor (D# (nextUp# (nextUp# pa# /## nextDown# (c# +## nextDown# c#)))) of (W64# w#) -> hndlOvflwW32## w#
  where
    !c# = unsafefx2Double## tcfx#
    !(D# threshold#) = 1.9 * 10 ^ 137

nxtDgtI64# :: Integer -> FloatingX# -> Int64#
nxtDgtI64# 0 !_ = 0#Int64
nxtDgtI64# (IS ta#) tcfx# = inline nxtDgtDoubleFxI64## (int2Double# ta#) tcfx#
nxtDgtI64# (IP bn#) tcfx# -- //FIXME = computFxW64# (allInclusivePreComputFx## bn# tcfx#) -- handles regular double as well
  | isTrue# ((bigNatSize# bn#) <# thresh#) = inline nxtDgtDoubleFxI64## (bigNatEncodeDouble# bn# 0#) tcfx#
  | otherwise = inline computFxI64# (preComputFx## bn# tcfx#)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgtI64# (IN _) !_ = error "nxtDgtI64# :: Invalid negative integer argument"

nxtDgtDoubleFxI64## :: Double# -> FloatingX# -> Int64#
nxtDgtDoubleFxI64## pa# tcfx# = case inline preComput pa# tcfx# of (# a#, c#, r# #) -> computDoubleI64# a# c# r#

-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgt# :: Integer -> FloatingX# -> Integer
nxtDgt# 0 _ = 0
nxtDgt# (IS ta#) tcfx# = inline nxtDgtDoubleFxI## (int2Double# ta#) tcfx#
nxtDgt# (IP bn#) tcfx#
  | isTrue# ((bigNatSize# bn#) <# thresh#) = inline nxtDgtDoubleFxI## (bigNatEncodeDouble# bn# 0#) tcfx#
  | otherwise = inline computFx# (preComputFx## bn# tcfx#)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgt# (IN _) !_ = error "nxtDgt :: Invalid negative integer argument"

nxtDgtDoubleFxI## :: Double# -> FloatingX# -> Integer
nxtDgtDoubleFxI## pa# tcfx# = case inline preComput pa# tcfx# of (# a#, c#, r# #) -> computDouble# a# c# r#

nxtDgt :: Integer -> FloatingX -> Integer
nxtDgt 0 _ = 0
nxtDgt n tcfx
  | n < 2 ^ 512 = nxtDgtDoubleFxI (fromIntegral n) tcfx
  | otherwise = computFx (preComputIFx n tcfx)
{-# INLINE nxtDgt #-}

-- | same as nxtDgt but without the small value shortcut, lots of branches cause impedance
nxtDgt_ :: Integer -> FloatingX -> Integer
nxtDgt_ 0 _ = 0
nxtDgt_ (IS ta#) tcfx = nxtDgtDoubleFxI (int2Double (I# ta#)) tcfx
nxtDgt_ (IP bn#) tcfx
  | isTrue# ((bigNatSize# bn#) <# thresh#) = nxtDgtDoubleFxI (D# (bigNatEncodeDouble# bn# 0#)) tcfx
  | otherwise = computFx (preComputFx (BN# bn#) tcfx)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgt_ (IN _) !_ = error "nxtDgt :: Invalid negative integer argument"
{-# INLINE nxtDgt_ #-}

nxtDgtDoubleFxI :: Double -> FloatingX -> Integer
nxtDgtDoubleFxI pa tcfx = case inline preComputDouble pa tcfx of (a, c, r) -> computDouble a c r

preComputDoubleT :: Double -> FloatingX -> (Double, Double, Double)
preComputDoubleT tADX_@(D# a#) tcfx = case unsafefx2Double tcfx of tCDX_@(D# c#) -> case fmaddDouble# c# c# a# of r# -> case (tADX_, tCDX_, (D# r#)) of (tADX, tCDX, radDX) -> (tADX, tCDX, radDX)

nxtDgtFused :: Integer -> FloatingX -> Integer
nxtDgtFused 0 _ = 0
nxtDgtFused (IS ta#) tcfx = case (unsafefx2Double tcfx, int2Double (I# ta#)) of (tCDX_@(D# c#), tADX_@(D# a#)) -> case fmaddDouble# c# c# a# of r# -> case (tADX_, tCDX_, (D# r#)) of (tADX, tCDX, radDX) -> hndlOvflwW32 $ floor (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))
-- nxtDgtFused (IS ta#) tcfx = case preComputDouble (int2Double (I# ta#)) tcfx of (tADX, tCDX, radDX) -> hndlOvflwW32 $ floorDouble (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))
nxtDgtFused n@(IP bn#) tcfx@(FloatingX s@(D# s#) e@(I64# e#))
  --  | isTrue# ((bigNatSize# bn#) <# thresh#) = case preComputDouble (D# (bigNatEncodeDouble# bn# 0#)) tcfx of (tADX, tCDX, radDX) -> hndlOvflwW32 $ floorDouble (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))
  | isTrue# ((bigNatSize# bn#) <# thresh#) = case (unsafefx2Double tcfx, D# (bigNatEncodeDouble# bn# 0#)) of (tCDX_@(D# c#), tADX_@(D# a#)) -> case fmaddDouble# c# c# a# of r# -> case (tADX_, tCDX_, (D# r#)) of (tADX, tCDX, radDX) -> hndlOvflwW32 $ floor (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))
  --  | otherwise = computFx (preComputFx (BN# bn#) (FloatingX s e)) --computFx (preComputFx bn# tcfx#)
  | otherwise = case unsafeGtWordbn2Fx (BN# bn#) of tAFX -> hndlOvflwW32 (floorFX (nextUpFX (nextUpFX tAFX !/ nextDownFX (sqrtFx (nextDownFX tcfx !**+ tAFX) !+ nextDownFX tcfx)))) -- computFx (tAFX, tcfx, tcfx !**+ tAFX)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgtFused (IN _) !_ = error "nxtDgtFused :: Invalid negative integer argument"
{-# INLINE [0] nxtDgtFused #-} -- phase 0 here seems to make a secondary difference

{-# INLINE computDouble #-}
computDouble :: Double -> Double -> Double -> Integer
computDouble !tADX !tCDX !radDX = hndlOvflwW32 $ floor (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))

{-# INLINE computDouble# #-}
computDouble# :: Double# -> Double# -> Double# -> Integer
computDouble# !tAFX# !tCFX# !radFX# = hndlOvflwW32 $ floor (D# (coreD# tAFX# tCFX# radFX#))

{-# INLINE computFx #-}
computFx :: (FloatingX, FloatingX, FloatingX) -> Integer
computFx (!tAFX, !tCFX, !radFX) = hndlOvflwW32 (floorFX (nextUpFX (nextUpFX tAFX !/ nextDownFX (sqrtFx (nextDownFX radFX) !+ nextDownFX tCFX))))

coreD# :: Double# -> Double# -> Double# -> Double#
coreD# da# dc# dr# = nextUp# (nextUp# da# /## nextDown# (sqrtDouble# (nextDown# dr#) +## nextDown# dc#))
{-# INLINE coreD# #-}

coreFx# :: (# FloatingX#, FloatingX#, FloatingX# #) -> FloatingX#
coreFx# (# tAFX#, tCFX#, radFX# #) =
  nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))
{-# INLINE coreFx# #-}

computFx# :: (# FloatingX#, FloatingX#, FloatingX# #) -> Integer
computFx# (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwW32 (floorX# (coreFx# (# tAFX#, tCFX#, radFX# #)))
-- hndlOvflwW32 (floorX# (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE computFx# #-}

{-# INLINE computDoubleW64# #-}
computDoubleW64# :: Double# -> Double# -> Double# -> Word64#
computDoubleW64# !tAFX# !tCFX# !radFX# = case floor (D# (coreD# tAFX# tCFX# radFX#)) of (W64# w#) -> hndlOvflwW32## w#

{-# INLINE computDoubleI64# #-}
computDoubleI64# :: Double# -> Double# -> Double# -> Int64#
computDoubleI64# !tAFX# !tCFX# !radFX# = case floor (D# (coreD# tAFX# tCFX# radFX#)) of (I64# i#) -> hndlOvflwI32## i#

computFxW64# :: (# FloatingX#, FloatingX#, FloatingX# #) -> Word64#
computFxW64# (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwW32## (floorXW64## (coreFx# (# tAFX#, tCFX#, radFX# #)))
-- hndlOvflwW32## (floorXW64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE computFxW64# #-}

computFxI64# :: (# FloatingX#, FloatingX#, FloatingX# #) -> Int64#
computFxI64# (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwI32## (floorXI64## (coreFx# (# tAFX#, tCFX#, radFX# #)))
-- hndlOvflwI32## (floorXI64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE computFxI64# #-}

preComputDouble :: Double -> FloatingX -> (Double, Double, Double)
preComputDouble a@(D# a#) (FloatingX (D# s#) (I64# e#)) = case preComput a# (FloatingX# s# e#) of (# a#, c#, r# #) -> (a, D# c#, D# r#)
{-# INLINE preComputDouble #-}

preComput :: Double# -> FloatingX# -> (# Double#, Double#, Double# #)
preComput a# tcfx# = case unsafefx2Double## tcfx# of c# -> (# a#, c#, fmaddDouble# c# c# a# #)
{-# INLINE preComput #-}

preComputFx :: BigNat -> FloatingX -> (FloatingX, FloatingX, FloatingX)
preComputFx tA__bn tCFX = case unsafeGtWordbn2Fx tA__bn of tAFX -> (tAFX, tCFX, tCFX !**+ tAFX) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE preComputFx #-}

preComputIFx :: Integer -> FloatingX -> (FloatingX, FloatingX, FloatingX)
preComputIFx tA tCFX = case unsafeN2Fx tA of tAFX -> (tAFX, tCFX, tCFX !**+ tAFX) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE preComputIFx #-}

preComputFx## :: BigNat# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
preComputFx## tA__bn# tCFX# = case unsafeGtWordbn2Fx## tA__bn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE preComputFx## #-}

-- | handles small/regular double as well. So just not bigNat only
allInclusivePreComputFx## :: BigNat# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
allInclusivePreComputFx## tA__bn# tCFX# = case bigNat2FloatingX## tA__bn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE allInclusivePreComputFx## #-}

-- | handles small/regular double as well. So just not bigNat only
allInclusivePreComputNToFx## :: Integer -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
allInclusivePreComputNToFx## tA tCFX# = case unsafeN2Fx# tA of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE allInclusivePreComputNToFx## #-}

computeRem :: Integer -> Integer -> Integer -> (Integer, Integer, Integer)
computeRem yc ta 0 = (yc * radixW32, 0, ta)
computeRem yc ta i =
  let !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta + (-i * (double ycS' + i)))
      !(yAdj, rdrAdj) = if rdr < 0 then (pred i, rdr + double (pred (ycScaled + i)) + 1) else (i, rdr)
   in -- !(yAdj, rdrAdj) = if rdr < 0 then (pred i, fixRemainder (pred (ycScaled + i)) rdr + 1) else (i, rdr)
      (yAdj + ycScaled, yAdj, rdrAdj)
{-# INLINE computeRem #-}

computeRemW64# :: Integer -> Integer -> Word64# -> (# Integer, Word64#, Integer #)
computeRemW64# yc ta 0#Word64 = (# yc * radixW32, 0#Word64, ta #)
computeRemW64# yc ta yTilde_# =
  let !i = toInteger (W64# yTilde_#)
      -- !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !(ycScaled, rdr) = rmdr yc ta i (fromIntegral (W64# yTilde_#))
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred (ycScaled + i)) + 1 #) else (# yTilde_#, rdr #)
   in -- !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, fixRemainder (pred (ycScaled + i)) rdr + 1 #) else (# yTilde_#, rdr #)
      (# toInteger (W64# yAdj#) + ycScaled, yAdj#, rdrAdj #)
{-# INLINE computeRemW64# #-}

computeRemI64# :: Integer -> Integer -> Int64# -> (# Integer, Int64#, Integer #)
computeRemI64# yc ta 0#Int64 = (# yc * radixW32, 0#Int64, ta #)
computeRemI64# yc ta yTilde_# =
  let !i = toInteger (I64# yTilde_#)
      -- !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !(ycScaled, rdr) = rmdr yc ta i (I64# yTilde_#)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subInt64#` 1#Int64, rdr + double (pred (ycScaled + i)) + 1 #) else (# yTilde_#, rdr #)
   in -- !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subInt64#` 1#Int64, fixRemainder (pred (ycScaled + i)) rdr + 1 #) else (# yTilde_#, rdr #)
      (# toInteger (I64# yAdj#) + ycScaled, yAdj#, rdrAdj #)
{-# INLINE computeRemI64# #-}

rmdr :: Integer -> Integer -> Integer -> Int64 -> (Integer, Integer)
rmdr yc ta i yTilde_ =
  let !intToUse = maxIntSizeAcross yc ta i
      !(ycScaled, rdr) = case intToUse of
        Is32 -> case radixW32 `safePosMul64` fromIntegral yc of
          Right ycScaled64 -> case yTilde_ `safePosAdd64` ycScaled64 of
            Right iPlusycScaled -> case ycScaled64 `safePosAdd64` iPlusycScaled of
              Right iPlusDoubleYcScaled -> case yTilde_ `safePosMul64` iPlusDoubleYcScaled of
                Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + fromIntegral ta of rdr64 -> (fromIntegral ycScaled64, fromIntegral rdr64)
                Left iTimesiPlusDoubleYcScaledIN -> (fromIntegral ycScaled64, ta - iTimesiPlusDoubleYcScaledIN)
              Left iPlusDoubleYcScaledIN -> (fromIntegral ycScaled64, ta - i * iPlusDoubleYcScaledIN)
            Left iPlusycScaledIN -> (fromIntegral ycScaled64, ta - i * (iPlusycScaledIN + fromIntegral ycScaled64))
          Left ycScaled' -> (ycScaled', ta - i * (double ycScaled' + i))
        (Is32; Is64; Is96) -> case radixW32 `safePosMul256` fromIntegral yc of
          Right ycScaled256 -> case fromIntegral yTilde_ `safePosAdd256` ycScaled256 of
            Right iPlusycScaled -> case ycScaled256 `safePosAdd256` iPlusycScaled of
              Right iPlusDoubleYcScaled -> case fromIntegral yTilde_ `safePosMul256` iPlusDoubleYcScaled of
                Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + fromIntegral ta of rdr256 -> (fromIntegral ycScaled256, fromIntegral rdr256)
                Left iTimesiPlusDoubleYcScaledIN -> (fromIntegral ycScaled256, ta - iTimesiPlusDoubleYcScaledIN)
              Left iPlusDoubleYcScaledIN -> (fromIntegral ycScaled256, ta - i * iPlusDoubleYcScaledIN)
            Left iPlusycScaledIN -> (fromIntegral ycScaled256, ta - i * (iPlusycScaledIN + fromIntegral ycScaled256))
          Left ycScaled' -> (ycScaled', ta - i * (double ycScaled' + i))
        (Is128; Is256; IsIN; _) -> let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
   in (ycScaled, rdr)

handleFirstRem :: (# Word64#, Integer #) -> (# Integer, Word64#, Integer #)
handleFirstRem (# yi64#, ri_ #)
  | ri_ < 0 =
      let !yAdj# = yi64# `subWord64#` 1#Word64
          !adjYc = pred ycyi
          !rdr = fixRemainder adjYc ri_
       in (# adjYc, yAdj#, rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | otherwise = (# ycyi, yi64#, ri_ #)
  where
    !ycyi = fromIntegral (W64# yi64#) -- accumulating the growing square root
{-# INLINE handleFirstRem #-}

-- -- Fix remainder accompanying a 'next downed digit'
fixRemainder :: Integer -> Integer -> Integer
fixRemainder !newYc !rdr = rdr + double newYc + 1
{-# INLINE fixRemainder #-}

-- | Find the largest n such that n^2 <= w, where n is even different for even length lists and odd length lists
evenFirstRmdr :: Word64# -> (# Integer, Word64#, Integer #)
evenFirstRmdr w# =
  let yT64# = hndlOvflwW32## (largestNSqLTEEven## w#)
      ysq# = yT64# `timesWord64#` yT64#
      diff# = word64ToInt64# w# `subInt64#` word64ToInt64# ysq#
   in handleFirstRem (# yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
{-# INLINE evenFirstRmdr #-}

oddFirstRmdr :: Word64# -> (# Integer, Word64#, Integer #)
oddFirstRmdr w# =
  let yT64# = largestNSqLTEOdd## w#
      y = W64# yT64#
      ysq# = yT64# `timesWord64#` yT64#
      remInteger = toInteger $ W64# (w# `subWord64#` ysq#) -- no chance this will be negative
   in (# toInteger y, yT64#, remInteger #)
{-# INLINE oddFirstRmdr #-}

-- | Staging the input list of Word32 into a list of Word64 by combining pairs of Word32
{-# INLINE stageList #-}
stageList :: [Word32] -> (Bool, [Word64], [Word32]) -- //FIXME WHY WORD64 LIST?
stageList xs = stageList_ (length xs) xs

{-# INLINE stageList_ #-}
stageList_ :: Int -> [Word32] -> (Bool, [Word64], [Word32]) -- //FIXME WHY WORD64 LIST?
stageList_ l xs =
  case splitFn xs l of
    (rstEvenLen, lastElems) -> (evenYes, mkIW32EvenRestLst l True rstEvenLen, lastElems)
  where
    !evenYes = even l
    !splitFn = if evenYes then splitLastTwo else splitLastOne

{-# INLINE stageListN_ #-} -- incoming xs is a normal format list of digits (MSB first)
stageListN_ :: Int -> [Word32] -> (Bool, [Word64], [Word32]) -- //FIXME WHY WORD64 LIST?
stageListN_ l xs =
  case splitFn xs l of
    (firstElems, rstEvenLen) -> (evenYes, mkIW32EvenRestLstN_ l True rstEvenLen, firstElems)
  where
    !evenYes = even l
    !splitFn = if evenYes then splitFirstTwo else splitFirstOne

{-# INLINE preProcessList #-} -- incoming xs is a normal format list of digits (MSB first)
preProcessList :: Int -> [Word32] -> (Bool, [Word32], [Word32]) 
preProcessList l xs =
  case splitFn xs l of
    (firstElems, rstEvenLen) -> (evenYes, rstEvenLen, firstElems)
  where
    !evenYes = even l
    !splitFn = if evenYes then splitFirstTwo else splitFirstOne

{-# INLINE stageListRvrsd #-}
stageListRvrsd :: [Word32] -> (Bool, [Word64], [Word32])
stageListRvrsd xs = stageListRvrsd_ (length xs) xs -- sndModifyWith reverse (stageList xs)

{-# INLINE stageListRvrsd_ #-}
stageListRvrsd_ :: Int -> [Word32] -> (Bool, [Word64], [Word32])
stageListRvrsd_ l xs = case stageList_ l xs of (evenLen, ws, lastElems) -> (evenLen, reverse ws, lastElems)

{-# INLINE stageBA #-}
stageBA :: [Word32] -> (Bool, ByteArray, [Word32])
stageBA xs = case stageList xs of (evenLen, ws, lastElems) -> (evenLen, byteArrayFromList ws, lastElems)

{-# INLINE stageBA_ #-}
stageBA_ :: Int -> [Word32] -> (Bool, ByteArray, [Word32])
stageBA_ l xs = case stageList_ l xs of (evenLen, ws, lastElems) -> (evenLen, byteArrayFromList ws, lastElems)

{-# INLINE stageUV #-}
stageUV :: [Word32] -> (Bool, VU.Vector Word64, [Word32])
stageUV xs = case stageList xs of (evenLen, ws, lastElems) -> (evenLen, VU.fromList ws, lastElems)

{-# INLINE stageUV_ #-}
stageUV_ :: Int -> [Word32] -> (Bool, VU.Vector Word64, [Word32])
stageUV_ l xs = case stageList_ l xs of (evenLen, ws, lastElems) -> (evenLen, VU.fromList ws, lastElems)

{-# INLINE stageUVrvrsd #-}
stageUVrvrsd :: [Word32] -> (Bool, VU.Vector Word64, [Word32])
stageUVrvrsd xs = case stageListRvrsd xs of (evenLen, ws, lastElems) -> (evenLen, VU.fromList ws, lastElems)

{-# INLINE stageUVrvrsd_ #-}
stageUVrvrsd_ :: Int -> [Word32] -> (Bool, VU.Vector Word64, [Word32])
stageUVrvrsd_ l xs = case stageListRvrsd_ l xs of (evenLen, ws, lastElems) -> (evenLen, VU.fromList ws, lastElems)

streamDigitsInOrder :: Int -> Bool -> Integer -> Integer
streamDigitsInOrder l eY n = yCumulative___ $ go n (radixW32^pm) pm pm (Itr__ 1# 0 0 zeroFx#) 
  where
    !pm = l - 1 
    -- Extract digits from most significant to least significant
    go :: Integer -> Integer -> Int -> Int -> Itr__ -> Itr__
    go x powr pMax p acc
      | not firstIter && p >= 1 = 
          let 
              ![_, power1, power2] = scanl div powr [radixW32, radixW32]
              !(digit1, y) = x `quotRem` power1
              !(digit2, z) = y `quotRem` power2
          in go z power2 pMax (p-2) (theNextIters [fromIntegral digit1,fromIntegral digit2] acc) 
      | firstIter && not eY  = 
          let 
              !(digit, y) = x `quotRem` powr
          in go y powr pMax (p - 1) (theFirstIter False [fromIntegral digit] acc) -- accFn False [fromIntegral digit] acc
      | firstIter && eY = 
          let 
              ![power1, power2] = scanl div powr [radixW32]
              !(digit1, y) = x `quotRem` power1 -- powr
              !(digit2, z) = y `quotRem` power2
          in go z power2 pMax (p-2) (theFirstIter True [fromIntegral digit1,fromIntegral digit2] acc) -- accFn True [fromIntegral digit,fromIntegral digit2] acc
      | p < 0  = acc
      | otherwise = error "undefined entry in go"
     where 
        !firstIter = p == pMax 
        theFirstIter :: Bool -> [Word32] -> Itr__ -> Itr__
        theFirstIter ev pairdgt _ = case theFirstPostProcess (ev, pairdgt) of  (# yVal, yWord#, remInteger #) -> Itr__ 1# yVal remInteger (unsafeword64ToFloatingX## yWord#) -- rFinalXs
        theNextIters :: [Word32] -> Itr__ -> Itr__
        theNextIters [x1,x2] (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) = tniCorePP (x1, x2) (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#)
        theNextIters _ _ = error "Poor inputs"
