{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnboxedTuples #-}
-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump-simpl or ddump-asm dumps else not
{-# OPTIONS_GHC -O2 -fkeep-auto-rules -threaded -optl-m64 -fliberate-case -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fstrictness -funbox-small-strict-fields -funfolding-use-threshold=16 -fmax-worker-args=32 -optc-O3 -optc-ffast-math -optc-march=native -optc-mfpmath=sse #-}
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
module Math.NumberTheory.Roots.Squares.InternalBank_ where

-- //FIXME Type conversion avoidance: Avoid boxing/unboxing and unnecessary type conversions within performance-critical code—especially inner numeric loops.

-- //FIXME Tighten representation: Operate on Int when possible, only converting to Double at the last possible moment, as converting on every loop iteration can cost performance.

-- // FIXME Specialized Data Structures: Choose appropriate containers like unboxed vectors instead of lists for large datasets
-- \*********** BEGIN NEW IMPORTS

-- he says it's coded to be as fast as possible
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
import GHC.Float (divideDouble, floorDouble, int2Double, integerToDouble#, minusDouble, plusDouble, powerDouble, timesDouble)
import GHC.Int (Int64 (I64#))
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatEncodeDouble#, bigNatIndex#, bigNatIsZero, bigNatLeWord#, bigNatLog2, bigNatLog2#, bigNatShiftR, bigNatShiftR#, bigNatSize#)
import GHC.Num.Integer (Integer (..))
import GHC.Word (Word64 (..))
import Math.NumberTheory.Utils.ArthMtic_
import Math.NumberTheory.Utils.FloatingX_

-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

-- | Iteration loop data - these records have vectors / lists in them
data ItrLst_ = ItrLst_ {lvlst# :: {-# UNPACK #-} !Int#, lstW32 :: {-# UNPACK #-} ![Word64], yCumulative_ :: !Integer, iRem :: {-# UNPACK #-} !Integer, tb___# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

data ItrBA = ItrBA {lBA :: Int#, ba :: !ByteArray, ycBA :: Integer, irBA :: !Integer, tbBAFx :: !FloatingX#} deriving (Eq)

data ItrUV = ItrUV {luv :: Int#, uv :: !(VU.Vector Word64), ycuv :: !Integer, iruv :: !Integer, tbuvFx :: !FloatingX#} deriving (Eq)

data Itr__ = Itr__ {lv__# :: {-# UNPACK #-} !Int#, yCumulative___ :: !Integer, iRem___ :: {-# UNPACK #-} !Integer, tb__# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

theFirstXs :: (Bool, [Word64], [Word32]) -> ItrLst_
theFirstXs (evenLen, passXs, dxs')
  | evenLen =
      let !(# !yc, !y1#, !remInteger #) = evenFirstRmdr i#
       in ItrLst_ 1# passXs yc remInteger (unsafeword64ToFloatingX## y1#)
  | otherwise = let !(# !y, !yT64#, !remInteger #) = oddFirstRmdr i#
       in ItrLst_ 1# passXs (toInteger y) remInteger (unsafeword64ToFloatingX## yT64#)
  where
    i# = word64FromRvsrd2ElemList# dxs'

evenFirstRmdr :: Word64# -> (# Integer, Word64#, Integer #)
evenFirstRmdr i# = let 
                yT64# = hndlOvflwW32## (largestNSqLTEEven## i#)
                ysq# = yT64# `timesWord64#` yT64#
                diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
             in handleFirstRem (# yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
{-# INLINE evenFirstRmdr #-}

oddFirstRmdr :: Word64# -> (# Integer, Word64#, Integer #)
oddFirstRmdr i# = let 
                yT64# = largestNSqLTEOdd## i#
                y = W64# yT64#
                ysq# = yT64# `timesWord64#` yT64#
                remInteger = toInteger $ W64# (i# `subWord64#` ysq#) -- no chance this will be negative
             in (# toInteger y, yT64#, remInteger #)
{-# INLINE oddFirstRmdr #-}

theFiBA :: [Word32] -> ItrBA
theFiBA xs
  | evenLen =
      let !(# !yc, !y1#, !remInteger #) =
            let yT64# = hndlOvflwW32## (largestNSqLTEEven## i#)
                ysq# = yT64# `timesWord64#` yT64#
                diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
             in handleFirstRem (# yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
       in ItrBA 1# passBA yc remInteger (unsafeword64ToFloatingX## y1#)
  | otherwise =
      let yT64# = largestNSqLTEOdd## i#
          y = W64# yT64#
          ysq# = yT64# `timesWord64#` yT64#
          !remInteger = toInteger $ W64# (i# `subWord64#` ysq#) -- no chance this will be negative
       in ItrBA 1# passBA (toInteger y) remInteger (unsafeword64ToFloatingX## yT64#)
  where
    !(evenLen, passBA, dxs') = stageBA xs
    i# = word64FromRvsrd2ElemList# dxs'

theFirstUV :: (Bool, VU.Vector Word64, [Word32]) -> ItrUV
theFirstUV (evenLen, passUV, dxs')
  | evenLen =
      let !(# !yc, !y1#, !remInteger #) = evenFirstRmdr i#
       in ItrUV 1# passUV yc remInteger (unsafeword64ToFloatingX## y1#)
  | otherwise = let !(# !y, !yT64#, !remInteger #) = oddFirstRmdr i#
       in ItrUV 1# passUV y remInteger (unsafeword64ToFloatingX## yT64#)
  where
    i# = word64FromRvsrd2ElemList# dxs'

{-# INLINE stageList #-}
stageList :: [Word32] -> (Bool, [Word64], [Word32]) -- //FIXME WHY WORD64 LIST?
stageList xs =
  if even l
    then
      let !(rstEvenLen, lastTwo) = splitLastTwo xs l
       in (True, mkIW32EvenRestLst l True rstEvenLen, lastTwo)
    else
      let !(rstEvenLen, lastOne) = splitLastOne xs l
       in (False, mkIW32EvenRestLst l True rstEvenLen, lastOne)
  where
    !l = length xs -- // FIXME can we remove this traversal?

stageListRvrsd :: [Word32] -> (Bool, [Word64], [Word32])
stageListRvrsd xs =
  if even l
    then
      let !(rstEvenLen, lastTwo) = splitLastTwo xs l
       in (True, reverse $ mkIW32EvenRestLst l True rstEvenLen, lastTwo)
    else
      let !(rstEvenLen, lastOne) = splitLastOne xs l
       in (False, reverse $ mkIW32EvenRestLst l True rstEvenLen, lastOne)
  where
    !l = length xs

{-# INLINE stageBA #-}
stageBA :: [Word32] -> (Bool, ByteArray, [Word32])
stageBA xs =
  if even l
    then
      let !(rstEvenLen, lastTwo) = splitLastTwo xs l
       in (True, byteArrayFromList (mkIW32EvenRestLst l True rstEvenLen :: [Word]), lastTwo)
    else
      let !(rstEvenLen, lastOne) = splitLastOne xs l
       in (False, byteArrayFromList (mkIW32EvenRestLst l True rstEvenLen :: [Word]), lastOne)
  where
    !l = length xs

{-# INLINE stageUV #-}
stageUV :: [Word32] -> (Bool, VU.Vector Word64, [Word32])
stageUV xs =
  if even l
    then
      let !(rstEvenLen, lastTwo) = splitLastTwo xs l
       in (True, VU.fromList (mkIW32EvenRestLst l True rstEvenLen), lastTwo)
    else
      let !(rstEvenLen, lastOne) = splitLastOne xs l
       in (False, VU.fromList (mkIW32EvenRestLst l True rstEvenLen), lastOne)
  where
    !l = length xs

{-# INLINE stageUVrvrsd #-}
stageUVrvrsd :: [Word32] -> (Bool, VU.Vector Word64, [Word32])
stageUVrvrsd xs =
  if even l
    then
      let !(rstEvenLen, lastTwo) = splitLastTwo xs l
       in (True, VU.fromList $ reverse (mkIW32EvenRestLst l True rstEvenLen), lastTwo)
    else
      let !(rstEvenLen, lastOne) = splitLastOne xs l
       in (False, VU.fromList $ reverse (mkIW32EvenRestLst l True rstEvenLen), lastOne)
  where
    !l = length xs

theNextIterations :: ItrLst_ -> Integer
theNextIterations (ItrLst_ !currlen# !wrd64Xs !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ foldr' tni (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64Xs
  where
    {-# INLINE tni #-}
    tni :: Word64 -> Itr__ -> Itr__
    tni sqW64 (Itr__ !cl# !yCAcc_ !tA !t#) =
      let !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
          !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
          !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgtW64# tA_ tCFx# of yTilde_# -> computeRemW64# yCAcc_ tA_ yTilde_#
          !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
       in (Itr__ (cl# +# 1#) ycUpdated remFinal tcfx#) -- rFinalXs

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
theNextIterationsBA :: ItrBA -> Integer
theNextIterationsBA (ItrBA !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ foldrByteArray tni (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tni #-}
    tni :: Word64 -> Itr__ -> Itr__
    tni sqW64 (Itr__ !cl# !yCAcc_ !tA !t#) =
      let !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
          !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
          !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgtW64# tA_ tCFx# of yTilde_# -> computeRemW64# yCAcc_ tA_ yTilde_#
          !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
       in (Itr__ (cl# +# 1#) ycUpdated remFinal tcfx#) -- rFinalXs

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
theNextIterationsUV :: ItrUV -> Integer
theNextIterationsUV (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ VU.foldr' tni (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tni #-}
    tni :: Word64 -> Itr__ -> Itr__
    tni sqW64 (Itr__ !cl# !yCAcc_ !tA !t#) =
      let !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
          !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
          !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgtW64# tA_ tCFx# of yTilde_# -> computeRemW64# yCAcc_ tA_ yTilde_#
          !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
       in (Itr__ (cl# +# 1#) ycUpdated remFinal tcfx#) -- rFinalXs

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
theNextIterationsUVI :: ItrUV -> Integer
theNextIterationsUVI (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ VU.foldr' tni (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tni #-}
    tni :: Word64 -> Itr__ -> Itr__
    tni sqW64 (Itr__ !cl# !yCAcc_ !tA t@(FloatingX# s# e#)) =
      let !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
          !tCFx@(FloatingX (D# s'#) (I64# e'#)) = inline scaleByPower2 32 (FloatingX (D# s#) (I64# e#)) -- sqrtF previous digits being scaled right here
          -- computeRem yCAcc_ tA_ yTilde :: manual fusing of the left code into the line below
          !(ycUpdated, !yTildeFinal, remFinal) = case nxtDgtFused tA_ tCFx of yTilde -> case radixW32 * yCAcc_ of ycScaled -> case (ycScaled, tA_ - yTilde * (double ycScaled + yTilde)) of (ycS', rdr) -> if rdr < 0 then (ycS' + pred yTilde, pred yTilde, rdr + double (pred (ycS' + yTilde)) + 1) else (ycS' + yTilde, yTilde, rdr)
          !(W64# yTildeFinal#) = fromIntegral yTildeFinal
          !tcfx@(FloatingX# s_# e_#) = if isTrue# (cl# <# 3#) then inline nextDownFX# $ (FloatingX# s'# e'#) !+## inline unsafeword64ToFloatingX## yTildeFinal# else (FloatingX# s'# e'#) -- recall tcfx is already scaled by 32. Do not use normalize here
       in (Itr__ (cl# +# 1#) ycUpdated remFinal (FloatingX# s_# e_#)) -- rFinalXs

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
{-# NOINLINE theNextIterationsUVI #-} -- //FIXME

theNextIterationsUVIrvrsd :: ItrUV -> Integer
theNextIterationsUVIrvrsd (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) =
  yCumulative___ $ VU.foldl' tniRvr (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tniRvr #-}
    tniRvr :: Itr__ -> Word64 -> Itr__
    tniRvr (Itr__ !cl# !yCAcc_ !tA t@(FloatingX# s# e#)) sqW64 =
      let !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
          !tCFx@(FloatingX (D# s'#) (I64# e'#)) = scaleByPower2 32 (FloatingX (D# s#) (I64# e#)) -- sqrtF previous digits being scaled right here
          !(ycUpdated, !yTildeFinal, remFinal) = case nxtDgt tA_ tCFx of yTilde -> computeRem yCAcc_ tA_ yTilde
          !(W64# yTildeFinal#) = fromIntegral yTildeFinal
          !tcfx@(FloatingX# s_# e_#) = if isTrue# (cl# <# 3#) then nextDownFX# $ (FloatingX# s'# e'#) !+## unsafeword64ToFloatingX## yTildeFinal# else (FloatingX# s'# e'#) -- recall tcfx is already scaled by 32. Do not use normalize here
       in (Itr__ (cl# +# 1#) ycUpdated remFinal (FloatingX# s_# e_#)) -- rFinalXs

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
{-# NOINLINE theNextIterationsUVIrvrsd #-} 

{-# INLINE theNextIterationsRvrsdSLCode #-}

-- | SL = Straight Line Code
theNextIterationsRvrsdSLCode :: ItrLst_ -> Integer
theNextIterationsRvrsdSLCode (ItrLst_ !currlen# !wrd64Xs@(_) !yCumulatedAcc0 !rmndr !tbfx#) = inline go wrd64Xs (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#)
  where
    -- yCumulative___ $ foldl' tniRvrsd (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64Xs
    tniRvrsdSL :: Itr__ -> Word64 -> Itr__
    tniRvrsdSL (Itr__ !cl# !yCAcc_ !tA !t#) sqW64 =
      let !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
          !tCFx# = inline scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
          !(# ycUpdated, !yTildeFinal#, remFinal #) = case inline nxtDgtW64# tA_ tCFx# of yTilde_# -> inline computeRemW64# yCAcc_ tA_ yTilde_#
          !tcfx# = if isTrue# (cl# <# 3#) then inline nextDownFX# $ tCFx# !+## inline unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
       in (Itr__ (cl# +# 1#) ycUpdated remFinal tcfx#) -- rFinalXs
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

-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0

-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgtW64# :: Integer -> FloatingX# -> Word64#
-- nxtDgtW64# n tcfx# = computFxW64# (allInclusivePreComputNToFx## n tcfx#) -- works ! but not any faster
nxtDgtW64# 0 !_ = 0#Word64
nxtDgtW64# (IS ta#) tcfx# = inline nxtDgtDoubleFxW64## (int2Double# ta#) tcfx#
nxtDgtW64# (IP bn#) tcfx# -- = computFxW64# (allInclusivePreComputFx## bn# tcfx#) -- works but not faster
  | isTrue# ((bigNatSize# bn#) <# thresh#) = inline nxtDgtDoubleFxW64## (bigNatEncodeDouble# bn# 0#) tcfx#
  -- | otherwise = inline computFxW64# (inline preComputFx## bn# tcfx#)
  | otherwise = case unsafeGtWordbn2Fx## bn# of tAFX# -> if (tAFX# !<## threshold#) then inline computFxW64# (# tAFX#, tcfx#, tcfx# !**+## tAFX# #) else hndlOvflwW32## (floorXW64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (tcfx# !+## nextDownFX# tcfx#))))
  where
    !(I64# e64#) = fromIntegral 10 ^ 137
    threshold# = FloatingX# 1.9## e64#
    -- where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgtW64# (IN _) !_ = error "nxtDgtW64# :: Invalid negative integer argument"

nxtDgtDoubleFxW64## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxW64## pa# tcfx# = case inline preComput pa# tcfx# of (# a#, c#, r# #) -> inline computDoubleW64# a# c# r#

nxtDgtDoubleFxHrbie## :: Double# -> FloatingX# -> Word64#
nxtDgtDoubleFxHrbie## pa# tcfx# = case isTrue# (c# <## threshold#) of
  True -> inline computDoubleW64# pa# c# (fmaddDouble# c# c# pa#)
  False -> case floorDouble (D# (nextUp# (nextUp# pa# /## nextDown# (c# +## nextDown# c#)))) of (W64# w#) -> hndlOvflwW32## w#
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
nxtDgt (IS ta#) tcfx = nxtDgtDoubleFxI (int2Double (I# ta#)) tcfx
nxtDgt n@(IP bn#) tcfx@(FloatingX s@(D# s#) e@(I64# e#))
  | isTrue# ((bigNatSize# bn#) <# thresh#) = nxtDgtDoubleFxI (D# (bigNatEncodeDouble# bn# 0#)) tcfx
  | otherwise = computFx (preComputFx (BN# bn#) (FloatingX s e)) -- computFx (preComputFx bn# tcfx#)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgt (IN _) !_ = error "nxtDgt :: Invalid negative integer argument"
{-# INLINE nxtDgt #-}

nxtDgtDoubleFxI :: Double -> FloatingX -> Integer
nxtDgtDoubleFxI pa tcfx = case inline preComputDouble pa tcfx of (a, c, r) -> computDouble a c r

preComputDoubleT :: Double -> FloatingX -> (Double, Double, Double)
preComputDoubleT tADX_@(D# a#) tcfx = case unsafefx2Double tcfx of tCDX_@(D# c#) -> case fmaddDouble# c# c# a# of r# -> case (tADX_, tCDX_, (D# r#)) of (tADX, tCDX, radDX) -> (tADX, tCDX, radDX)

nxtDgtFused :: Integer -> FloatingX -> Integer
nxtDgtFused 0 _ = 0
nxtDgtFused (IS ta#) tcfx = case (unsafefx2Double tcfx, (int2Double (I# ta#))) of (tCDX_@(D# c#), tADX_@(D# a#)) -> case fmaddDouble# c# c# a# of r# -> case (tADX_, tCDX_, (D# r#)) of (tADX, tCDX, radDX) -> hndlOvflwW32 $ floorDouble (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))
-- nxtDgtFused (IS ta#) tcfx = case preComputDouble (int2Double (I# ta#)) tcfx of (tADX, tCDX, radDX) -> hndlOvflwW32 $ floorDouble (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))
nxtDgtFused n@(IP bn#) tcfx@(FloatingX s@(D# s#) e@(I64# e#))
  --  | isTrue# ((bigNatSize# bn#) <# thresh#) = case preComputDouble (D# (bigNatEncodeDouble# bn# 0#)) tcfx of (tADX, tCDX, radDX) -> hndlOvflwW32 $ floorDouble (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))
  | isTrue# ((bigNatSize# bn#) <# thresh#) = case (unsafefx2Double tcfx, (D# (bigNatEncodeDouble# bn# 0#))) of (tCDX_@(D# c#), tADX_@(D# a#)) -> case fmaddDouble# c# c# a# of r# -> case (tADX_, tCDX_, (D# r#)) of (tADX, tCDX, radDX) -> hndlOvflwW32 $ floorDouble (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))
  --  | otherwise = computFx (preComputFx (BN# bn#) (FloatingX s e)) --computFx (preComputFx bn# tcfx#)
  | otherwise = case unsafeGtWordbn2Fx (BN# bn#) of tAFX -> hndlOvflwW32 (floorFX (nextUpFX (nextUpFX tAFX !/ nextDownFX (sqrtFx (nextDownFX tcfx !**+ tAFX) !+ nextDownFX tcfx)))) -- computFx (tAFX, tcfx, tcfx !**+ tAFX)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgtFused (IN _) !_ = error "nxtDgtFused :: Invalid negative integer argument"
{-# INLINE [0] nxtDgtFused #-} -- phase 0 here seems to make a secondary difference

{-# INLINE computDouble #-}
computDouble :: Double -> Double -> Double -> Integer
computDouble !tADX !tCDX !radDX = hndlOvflwW32 $ floorDouble (nextUp (nextUp tADX `divideDouble` nextDown (sqrt (nextDown radDX) `plusDouble` nextDown tCDX)))

{-# INLINE computDouble# #-}
computDouble# :: Double# -> Double# -> Double# -> Integer
computDouble# !tAFX# !tCFX# !radFX# = hndlOvflwW32 $ floorDouble (D# (nextUp# (nextUp# tAFX# /## nextDown# (sqrtDouble# (nextDown# radFX#) +## nextDown# tCFX#))))

computFx :: (FloatingX, FloatingX, FloatingX) -> Integer
computFx (!tAFX, !tCFX, !radFX) = hndlOvflwW32 (floorFX (nextUpFX (nextUpFX tAFX !/ nextDownFX (sqrtFx (nextDownFX radFX) !+ nextDownFX tCFX))))
{-# INLINE computFx #-}

computFx# :: (# FloatingX#, FloatingX#, FloatingX# #) -> Integer
computFx# (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwW32 (floorX# (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE computFx# #-}

{-# INLINE computDoubleW64# #-}
computDoubleW64# :: Double# -> Double# -> Double# -> Word64#
computDoubleW64# !tAFX# !tCFX# !radFX# = case floorDouble (D# (nextUp# (nextUp# tAFX# /## nextDown# (sqrtDouble# (nextDown# radFX#) +## nextDown# tCFX#)))) of (W64# w#) -> hndlOvflwW32## w#

computFxW64# :: (# FloatingX#, FloatingX#, FloatingX# #) -> Word64#
computFxW64# (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwW32## (floorXW64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE computFxW64# #-}

{-# INLINE computDoubleI64# #-}
computDoubleI64# :: Double# -> Double# -> Double# -> Int64#
computDoubleI64# !tAFX# !tCFX# !radFX# = case floorDouble (D# (nextUp# (nextUp# tAFX# /## nextDown# (sqrtDouble# (nextDown# radFX#) +## nextDown# tCFX#)))) of (I64# i#) -> hndlOvflwI32## i#

computFxI64# :: (# FloatingX#, FloatingX#, FloatingX# #) -> Int64#
computFxI64# (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwI32## (floorXI64## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
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
  let !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !(yAdj, rdrAdj) = if rdr < 0 then (pred i, rdr + double (pred (ycScaled + i)) + 1) else (i, rdr)
   in (yAdj + ycScaled, yAdj, rdrAdj)
{-# INLINE computeRem #-}

computeRemW64# :: Integer -> Integer -> Word64# -> (# Integer, Word64#, Integer #)
computeRemW64# yc ta 0#Word64 = (# yc * radixW32, 0#Word64, ta #)
computeRemW64# yc ta yTilde_# =
  let !i = toInteger (W64# yTilde_#)
      -- !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !(ycScaled, rdr) = rmdr yc ta i (fromIntegral (W64# yTilde_#))
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred (ycScaled + i)) + 1 #) else (# yTilde_#, rdr #)
   in (# toInteger (W64# yAdj#) + ycScaled, yAdj#, rdrAdj #)
{-# INLINE computeRemW64# #-}

computeRemI64# :: Integer -> Integer -> Int64# -> (# Integer, Int64#, Integer #)
computeRemI64# yc ta 0#Int64 = (# yc * radixW32, 0#Int64, ta #)
computeRemI64# yc ta yTilde_# =
  let !i = toInteger (I64# yTilde_#)
      -- !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !(ycScaled, rdr) = rmdr yc ta i (I64# yTilde_#)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subInt64#` 1#Int64, rdr + double (pred (ycScaled + i)) + 1 #) else (# yTilde_#, rdr #)
   in (# toInteger (I64# yAdj#) + ycScaled, yAdj#, rdrAdj #)
{-# INLINE computeRemI64# #-}

rmdr :: Integer -> Integer -> Integer -> Int64 -> (Integer, Integer)
rmdr yc ta i yTilde_ = let 
      !intToUse = maxIntSizeAcross yc ta i
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
