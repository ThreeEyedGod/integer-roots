{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OrPatterns #-}
-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump=simpl or ddump-asm dumps else not
{-# OPTIONS_GHC -O2 -threaded -optl-m64  -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fstrictness -funbox-small-strict-fields -funfolding-use-threshold=16 -fmax-worker-args=32 -optc-O3 -optc-ffast-math #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

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
    isqrtB  
  )
where

-- //FIXME Type conversion avoidance: Avoid boxing/unboxing and unnecessary type conversions within performance-critical code—especially inner numeric loops.

-- //FIXME Tighten representation: Operate on Int when possible, only converting to Double at the last possible moment, as converting on every loop iteration can cost performance.

-- // FIXME Specialized Data Structures: Choose appropriate containers like unboxed vectors instead of lists for large datasets
-- \*********** BEGIN NEW IMPORTS
import qualified Data.Vector.Unboxed as VU
import Data.Primitive.ByteArray (byteArrayFromList, foldrByteArray, ByteArray)
import Data.List  (unfoldr)
import Data.DoubleWord (Int96, Int256)
import Data.WideWord (Int128, Word256, zeroInt128) -- he says it's coded to be as fast as possible
import Data.Bits (finiteBitSize, complement, shiftR, unsafeShiftL, unsafeShiftR, (.&.), (.|.))
import Data.Bits.Floating (nextDown, nextUp)
import Data.FastDigits (digitsUnsigned, undigits)
import Data.Maybe (fromMaybe)
import Data.Word (Word32)
import GHC.Exts
  ( build, 
    word2Double#,
    Double (..),
    Double#,
    Word (..),
    Int (..),
    Int#,
    Int64#,
    Word64#,
    Word#, 
    int2Word#, 
    word2Int#,
    minusWord#,
    plusWord#,
    uncheckedShiftL#,
    eqInt64#,
    eqWord64#,
    fmaddDouble#,
    geInt64#,
    int2Double#,
    int64ToInt#,
    int64ToWord64#,
    intToInt64#,
    isTrue#,
    gtInt64#,
    leInt64#,
    minusWord#,
    plusInt64#,
    plusWord64#,
    quotInt64#,
    remInt64#, 
    sqrtDouble#,
    subInt64#,
    subWord64#,
    timesInt64#,
    timesWord#,
    timesWord64#,
    uncheckedShiftRL#,
    word2Int#,
    word32ToWord#,
    word64ToInt64#,
    wordToWord64#,
    neWord#,
    eqWord#,
    (*##),
    (**##),
    (+#),
    (+##),
    (/##),
    (<#),
    (<##),
    (==##),
    (>=##),
    (-#),
    (>=#),
    (/=#),
    and#,
    not#,
    or#,
    quotRemWord#
  )
import GHC.Float (divideDouble, powerDouble, timesDouble, floorDouble, integerToDouble#,int2Double, plusDouble,minusDouble)
import GHC.Int (Int32, Int64 (I64#))
import GHC.Integer (decodeDoubleInteger, encodeDoubleInteger)
import GHC.Num.BigNat (BigNat(..), BigNat#,BigNat,bigNatLog2, bigNatShiftR, bigNatLeWord#, bigNatIsZero, bigNatLog2#, bigNatIndex#, bigNatEncodeDouble#, bigNatIsZero, bigNatShiftR#, bigNatSize#)
import GHC.Num.Integer ( Integer (..), integerLog2#)
import GHC.Word (Word32 (..), Word64 (..))
import GHC.Integer.Logarithms (wordLog2#)
import Math.NumberTheory.Utils.ArthMtic_ 
import Math.NumberTheory.Utils.FloatingX_ 
-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

{-# SPECIALIZE isqrtB :: Integer -> Integer #-}
isqrtB :: (Integral a) => a -> a
isqrtB 0 = 0
-- isqrtB n = fromInteger . theNextIterationsUV . theFiUV . dgtsLstBase32 . fromIntegral $ n
isqrtB n = fromInteger . theNextIterationsUVIrvrsd . theFiUVRvr . dgtsLstBase32 . fromIntegral $ n
-- isqrtB n = fromInteger . theNextIterations . theFi . dgtsLstBase32 . fromIntegral $ n
{-# INLINEABLE isqrtB #-}

-- | Iteration loop data - these records have vectors / lists in them
data ItrLst_ = ItrLst_ {lvlst# :: {-# UNPACK #-} !Int#, lstW32 :: {-# UNPACK #-} ![Word64], yCumulative_ :: !Integer, iRem :: {-# UNPACK #-} !Integer, tb___# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)
data ItrBA = ItrBA {lBA :: Int#, ba :: !ByteArray, ycBA :: Integer, irBA :: !Integer, tbBAFx :: !FloatingX#} deriving (Eq)
data ItrUV = ItrUV {luv :: Int#, uv :: !(VU.Vector Word64), ycuv :: !Integer, iruv :: !Integer, tbuvFx :: !FloatingX#} deriving (Eq)
data Itr__ = Itr__ {lv__# :: {-# UNPACK #-} !Int#, yCumulative___ :: !Integer, iRem___ :: {-# UNPACK #-} !Integer, tb__# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

theFi :: [Word32] -> ItrLst_
theFi xs
  | evenLen =
      let !(# !yc, !y1#, !remInteger #) =
            let yT64# = hndlOvflwW32## (largestNSqLTEEven## i#)
                ysq# = yT64# `timesWord64#` yT64#
                diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
             in handleFirstRem (# yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
       in ItrLst_ 1# passXs yc remInteger (unsafeword64ToFloatingX## y1#) 
  | otherwise =
      let yT64# = largestNSqLTEOdd## i#
          y = W64# yT64#
          ysq# = yT64# `timesWord64#` yT64#
          !remInteger = toInteger $ W64# (i# `subWord64#` ysq#) -- no chance this will be negative
       in ItrLst_ 1# passXs (toInteger y) remInteger (unsafeword64ToFloatingX## yT64#)
  where
    !(evenLen, passXs, dxs') = stageList xs
    i# = word64FromRvsrd2ElemList# dxs'

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

theFiUV :: [Word32] -> ItrUV
theFiUV xs
  | evenLen =
      let !(# !yc, !y1#, !remInteger #) =
            let yT64# = hndlOvflwW32## (largestNSqLTEEven## i#)
                ysq# = yT64# `timesWord64#` yT64#
                diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
             in handleFirstRem (# yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
       in ItrUV 1# passUV yc remInteger (unsafeword64ToFloatingX## y1#) 
  | otherwise =
      let yT64# = largestNSqLTEOdd## i#
          y = W64# yT64#
          ysq# = yT64# `timesWord64#` yT64#
          !remInteger = toInteger $ W64# (i# `subWord64#` ysq#) -- no chance this will be negative
       in ItrUV 1# passUV (toInteger y) remInteger (unsafeword64ToFloatingX## yT64#)
  where
    !(evenLen, passUV, dxs') = stageUV xs
    i# = word64FromRvsrd2ElemList# dxs'

theFiUVRvr :: [Word32] -> ItrUV
theFiUVRvr xs
  | evenLen =
      let !(# !yc, !y1#, !remInteger #) =
            let yT64# = hndlOvflwW32## (largestNSqLTEEven## i#)
                ysq# = yT64# `timesWord64#` yT64#
                diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
             in handleFirstRem (# yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
       in ItrUV 1# passUV yc remInteger (unsafeword64ToFloatingX## y1#) 
  | otherwise =
      let yT64# = largestNSqLTEOdd## i#
          y = W64# yT64#
          ysq# = yT64# `timesWord64#` yT64#
          !remInteger = toInteger $ W64# (i# `subWord64#` ysq#) -- no chance this will be negative
       in ItrUV 1# passUV (toInteger y) remInteger (unsafeword64ToFloatingX## yT64#)
  where
    !(evenLen, passUV, dxs') = stageUVrvrsd xs
    i# = word64FromRvsrd2ElemList# dxs'

{-# INLINE stageList #-}
stageList :: [Word32] -> (Bool, [Word64], [Word32])
stageList xs =
  if even l
    then
      let !(rstEvenLen, lastTwo) = splitLastTwo xs l
       in (True, mkIW32EvenRestLst l True rstEvenLen, lastTwo)
    else
      let !(rstEvenLen, lastOne) = splitLastOne xs l
       in (False, mkIW32EvenRestLst l True rstEvenLen, lastOne)
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
    tni sqW64 (Itr__ !cl# !yCAcc_ !tA !t# )  =
          let 
              !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
              !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
              !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgtW64# tA_ tCFx# of yTilde_# -> computeRemW64# yCAcc_ tA_ yTilde_#
              !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
           in (Itr__ (cl# +# 1#)  ycUpdated remFinal tcfx#) --rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0

theNextIterationsBA :: ItrBA -> Integer
theNextIterationsBA (ItrBA !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) = 
  yCumulative___ $ foldrByteArray tni (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tni #-}
    tni :: Word64 -> Itr__ -> Itr__
    tni sqW64 (Itr__ !cl# !yCAcc_ !tA !t# )  =
          let 
              !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
              !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
              !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgtW64# tA_ tCFx# of yTilde_# -> computeRemW64# yCAcc_ tA_ yTilde_#
              !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
           in (Itr__ (cl# +# 1#)  ycUpdated remFinal tcfx#) --rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0

theNextIterationsUV :: ItrUV -> Integer
theNextIterationsUV (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) = 
  yCumulative___ $ VU.foldr' tni (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tni #-}
    tni :: Word64 -> Itr__ -> Itr__
    tni sqW64 (Itr__ !cl# !yCAcc_ !tA !t# )  =
          let 
              !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
              !tCFx# = scaleByPower2# 32#Int64 t# -- sqrtF previous digits being scaled right here
              !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgtW64# tA_ tCFx# of yTilde_# -> computeRemW64# yCAcc_ tA_ yTilde_#
              !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tCFx# !+## unsafeword64ToFloatingX## yTildeFinal# else tCFx# -- recall tcfx is already scaled by 32. Do not use normalize here
           in (Itr__ (cl# +# 1#)  ycUpdated remFinal tcfx#) --rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0

theNextIterationsUVI :: ItrUV -> Integer
theNextIterationsUVI (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) = 
  yCumulative___ $ VU.foldr' tni (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tni #-}
    tni :: Word64 -> Itr__ -> Itr__
    tni sqW64 (Itr__ !cl# !yCAcc_ !tA t@(FloatingX# s# e#) )  =
          let 
              !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
              !tCFx@(FloatingX (D# s'#) (I64# e'#)) = scaleByPower2 32 (FloatingX (D# s#) (I64# e#)) -- sqrtF previous digits being scaled right here
              !(ycUpdated, !yTildeFinal, remFinal) = case nxtDgt tA_ tCFx of yTilde -> computeRem yCAcc_ tA_ yTilde
              !(W64# yTildeFinal#) = fromIntegral yTildeFinal
              !tcfx@(FloatingX# s_# e_#) = if isTrue# (cl# <# 3#) then nextDownFX# $ (FloatingX# s'# e'#) !+## unsafeword64ToFloatingX## yTildeFinal# else (FloatingX# s'# e'#)  -- recall tcfx is already scaled by 32. Do not use normalize here
           in (Itr__ (cl# +# 1#)  ycUpdated remFinal (FloatingX# s_# e_#)) --rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
{-# NOINLINE theNextIterationsUVI #-} -- //FIXME 

theNextIterationsUVIrvrsd :: ItrUV -> Integer
theNextIterationsUVIrvrsd (ItrUV !currlen# !wrd64BA !yCumulatedAcc0 !rmndr !tbfx#) = 
  yCumulative___ $ VU.foldl' tniRvr (Itr__ currlen# yCumulatedAcc0 rmndr tbfx#) wrd64BA
  where
    {-# INLINE tniRvr #-}
    tniRvr :: Itr__ -> Word64 -> Itr__
    tniRvr (Itr__ !cl# !yCAcc_ !tA t@(FloatingX# s# e#) ) sqW64  =
          let 
              !tA_ = tA * secndPlaceW32Radix + toInteger sqW64
              !tCFx@(FloatingX (D# s'#) (I64# e'#)) = scaleByPower2 32 (FloatingX (D# s#) (I64# e#)) -- sqrtF previous digits being scaled right here
              !(ycUpdated, !yTildeFinal, remFinal) = case nxtDgt tA_ tCFx of yTilde -> computeRem yCAcc_ tA_ yTilde
              !(W64# yTildeFinal#) = fromIntegral yTildeFinal
              !tcfx@(FloatingX# s_# e_#) = if isTrue# (cl# <# 3#) then nextDownFX# $ (FloatingX# s'# e'#) !+## unsafeword64ToFloatingX## yTildeFinal# else (FloatingX# s'# e'#)  -- recall tcfx is already scaled by 32. Do not use normalize here
           in (Itr__ (cl# +# 1#)  ycUpdated remFinal (FloatingX# s_# e_#)) --rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
{-# NOINLINE theNextIterationsUVIrvrsd #-} -- //FIXME 

-- | Iteration loop data - these records have vectors / lists in them
data ItrLst'_ = ItrLst'_ {lvlst'# :: {-# UNPACK #-} !Int#, lstW32' :: {-# UNPACK #-} ![Integer], yCumulative'_ :: !Integer, iRem' :: {-# UNPACK #-} !Integer, tb'___# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)
data Itr'__ = Itr'__ {lv'__# :: {-# UNPACK #-} !Int#, yCumulative'___ :: !Integer, iRem'___ :: {-# UNPACK #-} !Integer, tb'__# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

theFi' :: [Word32] -> ItrLst'_
theFi' xs
  | evenLen =
      let !(# !yc, !y1#, !remInteger #) =
            let yT64# = hndlOvflwW32## (largestNSqLTEEven## i#)
                ysq# = yT64# `timesWord64#` yT64#
                diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
             in handleFirstRem (# yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
       in ItrLst'_ 1# passXs yc remInteger (unsafeword64ToFloatingX## y1#) 
  | otherwise =
      let yT64# = largestNSqLTEOdd## i#
          y = W64# yT64#
          ysq# = yT64# `timesWord64#` yT64#
          !remInteger = toInteger $ W64# (i# `subWord64#` ysq#) -- no chance this will be negative
       in ItrLst'_ 1# passXs (toInteger y) remInteger (unsafeword64ToFloatingX## yT64#)
  where
    !(evenLen, passXs, dxs') = stageList' xs
    i# = word64FromRvsrd2ElemList# dxs'

{-# INLINE stageList' #-}
stageList' :: [Word32] -> (Bool, [Integer], [Word32])
stageList' xs =
  if even l
    then
      let !(rstEvenLen, lastTwo) = splitLastTwo xs l
       in (True, mkIW32EvenRestLst l True rstEvenLen, lastTwo)
    else
      let !(rstEvenLen, lastOne) = splitLastOne xs l
       in (False, mkIW32EvenRestLst l True rstEvenLen, lastOne)
  where
    !l = length xs

theNextIterations' :: ItrLst'_ -> Integer
theNextIterations' (ItrLst'_ !currlen# !intgrXs !yCumulatedAcc0 !rmndr !tbfx#) = 
  yCumulative'___ $ foldr tni (Itr'__ currlen# yCumulatedAcc0 rmndr tbfx#) intgrXs
  where
    {-# INLINE tni #-}
    tni :: Integer -> Itr'__ -> Itr'__
    tni nxtTwoDgts (Itr'__ !cl# !yCAcc_ !tA (FloatingX# s# e#) )  =
          let 
              !tA_ = tA * secndPlaceW32Radix + nxtTwoDgts
              !tC_@(FloatingX (D# s_) (I64# e_)) = scaleByPower2 32 (FloatingX (D# s#) (I64# e#)) -- sqrtF previous digits being scaled right here
              !(ycUpdated, !yTildeFinal, remFinal) = case nxtDgt tA_ tC_ of yTilde -> computeRem yCAcc_ tA_ yTilde
              !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ (FloatingX# s_ e_) !+## unsafeword64ToFx# yTildeFinal else FloatingX# s_ e_  -- recall tcfx is already scaled by 32. Do not use normalize here
           in (Itr'__ (cl# +# 1#)  ycUpdated remFinal tcfx#) --rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0

-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgtW64# :: Integer -> FloatingX# -> Word64#
-- nxtDgtW64# n tcfx# = computFxW64# (allInclusivePreComputNToFx## n tcfx#) -- works ! but not any faster
nxtDgtW64# 0 !_ = 0#Word64
nxtDgtW64# (IS ta#) tcfx# = case preComput (int2Double# ta#) tcfx# of (# a#, c#, r# #) -> computDoubleW64# a# c# r#
nxtDgtW64# (IP bn#) tcfx#  -- = computFxW64# (allInclusivePreComputFx## bn# tcfx#) -- works but not faster 
     | isTrue# ((bigNatSize# bn#) <# thresh#) = case preComput (bigNatEncodeDouble# bn# 0#) tcfx# of (# a#, c#, r# #) -> computDoubleW64# a# c# r#
     | otherwise = computFxW64# (preComputFx## bn# tcfx#)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgtW64# (IN _) !_ = error "nxtDgtW64# :: Invalid negative integer argument"

nxtDgtI64# :: Integer -> FloatingX# -> Int64#
nxtDgtI64# 0 !_ = 0#Int64
nxtDgtI64# (IS ta#) tcfx# = case preComput (int2Double# ta#) tcfx# of (# a#, c#, r# #) -> computDoubleI64# a# c# r#
nxtDgtI64# (IP bn#) tcfx#  -- //FIXME = computFxW64# (allInclusivePreComputFx## bn# tcfx#) -- handles regular double as well
     | isTrue# ((bigNatSize# bn#) <# thresh#) = case preComput (bigNatEncodeDouble# bn# 0#) tcfx# of (# a#, c#, r# #) -> computDoubleI64# a# c# r#
     | otherwise = computFxI64# (preComputFx## bn# tcfx#)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgtI64# (IN _) !_ = error "nxtDgtI64# :: Invalid negative integer argument"


-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgt# :: Integer -> FloatingX# -> Integer
nxtDgt# 0 _ = 0
nxtDgt# (IS ta#) tcfx# = case preComput (int2Double# ta#) tcfx# of (# a#, c#, r# #) -> computDouble# a# c# r#
nxtDgt# (IP bn#) tcfx#
     | isTrue# ((bigNatSize# bn#) <# thresh#) = case preComput (bigNatEncodeDouble# bn# 0#) tcfx# of (# a#, c#, r# #) -> computDouble# a# c# r#
     | otherwise = computFx# (preComputFx## bn# tcfx#)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgt# (IN _) !_ = error "nxtDgt :: Invalid negative integer argument"

nxtDgt :: Integer -> FloatingX -> Integer
nxtDgt 0 _ = 0
nxtDgt (IS ta#) tcfx = case preComputDouble (int2Double (I# ta#)) tcfx of (a, c, r) -> computDouble a c r
nxtDgt n@(IP bn#) tcfx@(FloatingX s@(D# s#) e@(I64# e#))
     | isTrue# ((bigNatSize# bn#) <# thresh#) = case preComputDouble (D# (bigNatEncodeDouble# bn# 0#)) tcfx of (a, c, r) -> computDouble a c r
     | otherwise = computFx (preComputFx (BN# bn#) (FloatingX s e)) --computFx (preComputFx bn# tcfx#)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#
nxtDgt (IN _) !_ = error "nxtDgt :: Invalid negative integer argument"
{-# INLINE nxtDgt #-}

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
preComputDouble a@(D# a#) tcfx =
  let !c@(D# c#) = unsafefx2Double tcfx
      r# = fmaddDouble# c# c# a#
   in (a, c, (D# r#))
{-# INLINE preComputDouble #-}

preComput :: Double# -> FloatingX# -> (# Double#, Double#, Double# #)
preComput a# tcfx# =
  let !c# = unsafefx2Double## tcfx#
      !r# = fmaddDouble# c# c# a#
   in (# a#, c#, r# #)
{-# INLINE preComput #-}

preComputFx :: BigNat -> FloatingX -> (FloatingX, FloatingX, FloatingX)
preComputFx tA__bn tCFX = case unsafeGtWordbn2Fx tA__bn of tAFX -> (tAFX, tCFX, tCFX !**+ tAFX) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE preComputFx #-}

-- | handles small/regular double as well. So just not bigNat only
allInclusivePreComputFx## :: BigNat# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
allInclusivePreComputFx## tA__bn# tCFX# = case bigNat2FloatingX## tA__bn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE allInclusivePreComputFx## #-}

-- | handles small/regular double as well. So just not bigNat only
allInclusivePreComputNToFx## :: Integer -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
allInclusivePreComputNToFx## tA tCFX# = case unsafeN2Fx# tA of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE allInclusivePreComputNToFx## #-}

preComputFx## :: BigNat# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
preComputFx## tA__bn# tCFX# = case unsafeGtWordbn2Fx## tA__bn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE preComputFx## #-}

computeRem :: Integer -> Integer -> Integer -> (Integer, Integer, Integer)
computeRem yc ta 0 = (yc * radixW32, 0, ta)
computeRem yc ta i = let 
      !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !(yAdj, rdrAdj) = if rdr < 0 then (pred i, rdr + double (pred (ycScaled +  i)) + 1) else (i, rdr) 
    in (yAdj + ycScaled, yAdj, rdrAdj) 
{-# INLINE computeRem #-}

computeRemW64# :: Integer -> Integer -> Word64# -> (# Integer, Word64#, Integer #)
computeRemW64# yc ta 0#Word64 = (# yc * radixW32, 0#Word64, ta #)
computeRemW64# yc ta yTilde_# = let 
      !i = toInteger (W64# yTilde_#)
      -- !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !intToUse = maxIntSizeAcross yc ta i 
      !(ycScaled, rdr) = case intToUse of 
                  Is32 -> case radixW32 `safePosMul64` fromIntegral yc of 
                              Right ycScaled64 -> case fromIntegral (W64# yTilde_#) `safePosAdd64` ycScaled64 of 
                                          Right iPlusycScaled -> case ycScaled64 `safePosAdd64` iPlusycScaled of 
                                              Right iPlusDoubleYcScaled -> case fromIntegral (W64# yTilde_#)  `safePosMul64` iPlusDoubleYcScaled of 
                                                  Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + fromIntegral ta of rdr64 -> (fromIntegral ycScaled64,fromIntegral rdr64)
                                                  Left iTimesiPlusDoubleYcScaledIN ->  (fromIntegral ycScaled64, ta - iTimesiPlusDoubleYcScaledIN)
                                              Left iPlusDoubleYcScaledIN ->  (fromIntegral ycScaled64, ta - i * iPlusDoubleYcScaledIN)
                                          Left iPlusycScaledIN ->  (fromIntegral ycScaled64, ta - i * (iPlusycScaledIN + fromIntegral ycScaled64))
                              Left ycScaled' -> (ycScaled', ta - i * (double ycScaled' + i))
                  (Is32;Is64;Is96) -> case radixW32 `safePosMul256` fromIntegral yc of 
                              Right ycScaled256 -> case fromIntegral (W64# yTilde_#) `safePosAdd256` ycScaled256 of 
                                          Right iPlusycScaled -> case ycScaled256 `safePosAdd256` iPlusycScaled of 
                                              Right iPlusDoubleYcScaled -> case fromIntegral (W64# yTilde_#)  `safePosMul256` iPlusDoubleYcScaled of 
                                                  Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + fromIntegral ta of rdr256 -> (fromIntegral ycScaled256,fromIntegral rdr256)
                                                  Left iTimesiPlusDoubleYcScaledIN ->  (fromIntegral ycScaled256, ta - iTimesiPlusDoubleYcScaledIN)
                                              Left iPlusDoubleYcScaledIN ->  (fromIntegral ycScaled256, ta - i * iPlusDoubleYcScaledIN)
                                          Left iPlusycScaledIN ->  (fromIntegral ycScaled256, ta - i * (iPlusycScaledIN + fromIntegral ycScaled256))
                              Left ycScaled' -> (ycScaled', ta - i * (double ycScaled' + i))
                  (Is128;Is256;IsIN;_) -> let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred (ycScaled +  i)) + 1 #) else (# yTilde_#, rdr #) 
    in (# toInteger (W64# yAdj#) + ycScaled, yAdj#, rdrAdj #) 
{-# INLINE computeRemW64# #-}

computeRemI64# :: Integer -> Integer -> Int64# -> (# Integer, Int64#, Integer #)
computeRemI64# yc ta 0#Int64 = (# yc * radixW32, 0#Int64, ta #)
computeRemI64# yc ta yTilde_# = let 
      !i = toInteger (I64# yTilde_#)
      -- !(ycScaled, rdr) = let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !intToUse = maxIntSizeAcross yc ta i 
      !(ycScaled, rdr) = case intToUse of 
                  Is32 -> case radixW32 `safePosMul64` fromIntegral yc of 
                              Right ycScaled64 -> case (I64# yTilde_#) `safePosAdd64` ycScaled64 of 
                                          Right iPlusycScaled -> case ycScaled64 `safePosAdd64` iPlusycScaled of 
                                              Right iPlusDoubleYcScaled -> case (I64# yTilde_#)  `safePosMul64` iPlusDoubleYcScaled of 
                                                  Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + fromIntegral ta of rdr64 -> (fromIntegral ycScaled64,fromIntegral rdr64)
                                                  Left iTimesiPlusDoubleYcScaledIN ->  (fromIntegral ycScaled64, ta - iTimesiPlusDoubleYcScaledIN)
                                              Left iPlusDoubleYcScaledIN ->  (fromIntegral ycScaled64, ta - i * iPlusDoubleYcScaledIN)
                                          Left iPlusycScaledIN ->  (fromIntegral ycScaled64, ta - i * (iPlusycScaledIN + fromIntegral ycScaled64))
                              Left ycScaled' -> (ycScaled', ta - i * (double ycScaled' + i))
                  (Is32;Is64;Is96) -> case radixW32 `safePosMul256` fromIntegral yc of 
                              Right ycScaled256 -> case fromIntegral (I64# yTilde_#) `safePosAdd256` ycScaled256 of 
                                          Right iPlusycScaled -> case ycScaled256 `safePosAdd256` iPlusycScaled of 
                                              Right iPlusDoubleYcScaled -> case fromIntegral (I64# yTilde_#)  `safePosMul256` iPlusDoubleYcScaled of 
                                                  Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + fromIntegral ta of rdr256 -> (fromIntegral ycScaled256,fromIntegral rdr256)
                                                  Left iTimesiPlusDoubleYcScaledIN ->  (fromIntegral ycScaled256, ta - iTimesiPlusDoubleYcScaledIN)
                                              Left iPlusDoubleYcScaledIN ->  (fromIntegral ycScaled256, ta - i * iPlusDoubleYcScaledIN)
                                          Left iPlusycScaledIN ->  (fromIntegral ycScaled256, ta - i * (iPlusycScaledIN + fromIntegral ycScaled256))
                              Left ycScaled' -> (ycScaled', ta - i * (double ycScaled' + i))
                  (Is128;Is256;IsIN;_) -> let !ycS' = radixW32 * yc in (ycS', ta - i * (double ycS' + i))
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subInt64#` 1#Int64, rdr + double (pred (ycScaled +  i)) + 1 #) else (# yTilde_#, rdr #) 
    in (# toInteger (I64# yAdj#) + ycScaled, yAdj#, rdrAdj #) 
{-# INLINE computeRemI64# #-}


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

karatsubaSqrt :: Integer -> (Integer, Integer)
karatsubaSqrt 0 = (0, 0)
karatsubaSqrt n
  | lgN < 2300 =
      let s = isqrtB n in (s, n - s * s)
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
    lgN = I# (word2Int# (integerLog2# n))

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
    {-# INLINE cat #-}

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
