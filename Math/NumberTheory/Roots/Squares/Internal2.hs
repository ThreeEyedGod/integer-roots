{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
-- addition
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
-- addition
-- used everywhere within
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OrPatterns #-}
-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump=simpl or ddump-asm dumps else not
{-# OPTIONS_GHC -O2 -threaded -optl-m64  -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fstrictness -funbox-small-strict-fields -funfolding-use-threshold=16 -fmax-worker-args=32 #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

-- {-# OPTIONS_GHC -mfma -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fstrictness -funbox-small-strict-fields -funfolding-use-threshold=80 -fmax-worker-args=32 #-}

-- |
-- Module:      Math.NumberTheory.Roots.Squares.Internal
-- Copyright:   (c) 2011 Daniel Fischer, 2016-2020 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Internal functions dealing with square roots. End-users should not import this module.
-- {-# OPTIONS -ddump-simpl -ddump-to-file #-}
module Math.NumberTheory.Roots.Squares.Internal2
  ( karatsubaSqrt,
    isqrtB
  )
where

-- \*********** BEGIN NEW IMPORTS

-- import qualified Data.Vector.Unboxed as VU (Vector, unsafeIndex, unsafeHead, null, uncons, fromList, singleton, unsafeDrop, length, (!?))
import Control.Parallel.Strategies (NFData, parBuffer, parListChunk, parListSplitAt, rdeepseq, rpar, withStrategy)
import Data.DoubleWord (Int96, Int256)
import Data.WideWord (Int128, Word256, zeroInt128) -- he says it's coded to be as fast as possible
import Control.Arrow ((***), (&&&))
import Data.Bits (finiteBitSize, shiftR, unsafeShiftL, unsafeShiftR, (.&.), (.|.))
import Data.Bits.Floating (nextDown, nextUp)
import Data.FastDigits (digitsUnsigned, undigits)
import Data.List
import Data.Maybe (fromMaybe)
import Data.Word (Word32)
import GHC.Exts
  ( Double (..),
    Double#,
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
    (*##),
    (**##),
    (+#),
    (+##),
    (/##),
    (<#),
    (<##),
    (==##),
    (>=##),
  )
import GHC.Float (divideDouble, floorDouble)
import GHC.Int (Int32, Int64 (I64#))
import GHC.Integer (decodeDoubleInteger, encodeDoubleInteger)
import GHC.Num.BigNat (BigNat#, bigNatIsZero, bigNatLog2#, bigNatIndex#, bigNatEncodeDouble#, bigNatIsZero, bigNatShiftR#, bigNatSize#)
import GHC.Num.Integer ( Integer (..), integerLog2#)
import GHC.Word (Word32 (..), Word64 (..))
import Math.NumberTheory.Logarithms (integerLogBase')
import GHC.Integer.Logarithms (wordLog2#)
import qualified Data.Sequence (Seq, empty, singleton, fromList, null, length, splitAt) -- 0.8 does not work results in conflicts
import Data.Sequence ( ViewR( EmptyR ) , ViewL( EmptyL ), ViewL( (:<) ), ViewR( (:>) ), (<|), pattern (:<|), viewr, viewl, Seq (Empty))
import Math.NumberTheory.Utils.ShortCircuit (firstTrueOf)
-- *********** END NEW IMPORTS

-- BEGIN isqrtB ****************************************************************

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

{-# SPECIALIZE isqrtB :: Integer -> Integer #-}
isqrtB :: (Integral a) => a -> a
isqrtB 0 = 0
-- isqrtB n = fromInteger . theNextIterations . theFi . dgtsLstBase32 . fromIntegral $ n
isqrtB n = fromInteger . theNextIterationsSeq . theFi_ . dgtsLstBase32 . fromIntegral $ n
{-# INLINEABLE isqrtB #-}

-- | Iteration loop data - these records have vectors / lists in them
data Itr = Itr {lv# :: {-# UNPACK #-} !Int#, lstW32_ :: {-# UNPACK #-} ![Word64], yCumulative :: !Integer, iRem_ :: {-# UNPACK #-} !Integer, tb# :: {-# UNPACK #-} !FloatingX#, yCumLst :: ![Word64], iR :: ![Int96]} deriving (Eq)
data Itr_ = Itr_ {lv_# :: {-# UNPACK #-} !Int#, seqW32_ :: {-# UNPACK #-} Data.Sequence.Seq Word64, yCumulative__ :: !Integer, iRem__ :: {-# UNPACK #-} !Integer, tb_# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

theFi :: [Word32] -> Itr
theFi xs
  | evenLen =
      let !(# ycOutXs, !yc, !y1#, !remInteger #) =
            let yT64# = hndlOvflwW32## (largestNSqLTEEven## i#)
                ysq# = yT64# `timesWord64#` yT64#
                diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
             in handleRems (# [], 0, yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
       in Itr 1# passXs yc remInteger (unsafeword64ToFloatingX## y1#) ycOutXs [fromIntegral remInteger]
  | otherwise =
      let yT64# = largestNSqLTEOdd## i#
          y = W64# yT64#
          !remInteger = fromIntegral $ W64# (i# `subWord64#` (yT64# `timesWord64#` yT64#)) -- no chance this will be negative
       in Itr 1# passXs (fromIntegral y) remInteger (unsafeword64ToFloatingX## yT64#) [y] [fromIntegral remInteger]
  where
    !(evenLen, passXs, dxs') = stageList xs
    i# = word64FromRvsrd2ElemList# dxs'

theFi_ :: [Word32] -> Itr_
theFi_ xs
  | evenLen =
      let !(# !yc, !y1#, !remInteger #) =
            let yT64# = hndlOvflwW32## (largestNSqLTEEven## i#)
                ysq# = yT64# `timesWord64#` yT64#
                diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
             in handleRemsSeq (# [], yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
       in Itr_ 1# passSeq yc remInteger (unsafeword64ToFloatingX## y1#) 
  | otherwise =
      let yT64# = largestNSqLTEOdd## i#
          y = W64# yT64#
          !remInteger = fromIntegral $ W64# (i# `subWord64#` (yT64# `timesWord64#` yT64#)) -- no chance this will be negative
       in Itr_ 1# passSeq (fromIntegral y) remInteger (unsafeword64ToFloatingX## yT64#)
  where
    !(evenLen, passSeq, dseq') = stageSeq xs
    i# = word64FromRvsrd2ElemSeq# dseq'

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

{-# INLINE stageSeq #-}
stageSeq :: [Word32] -> (Bool, Data.Sequence.Seq Word64, Data.Sequence.Seq Word32)
stageSeq sq =
  if even l
    then
      let !(rstEvenLen, lastTwo) = splitLastTwoSeq sq l
       in (True, mkIW32EvenRestSeq l True rstEvenLen, lastTwo)
    else
      let !(rstEvenLen, lastOne) = splitLastOneSeq sq l
       in (False, mkIW32EvenRestSeq l True rstEvenLen, lastOne)
  where
    !l = length sq


-- Keep it this way: Inlining this lowers performance.
theNextIterations :: Itr -> Integer
-- theNextIterations (Itr !currlen# !wrd64Xs yCumulated iRem !tbfx# yCumLst iRLst) = tni currlen# wrd64Xs tbfx# yCumLst iRLst
-- theNextIterations (Itr !currlen# !wrd64Xs yCumulated iRem !tbfx# yCumLst iRLst) = tniI currlen# wrd64Xs tbfx# yCumulated iRem
theNextIterations (Itr !currlen# !wrd64Xs yCumulated iRem !tbfx# yCumLst iRLst) = tniISq currlen# (Data.Sequence.fromList wrd64Xs) tbfx# yCumulated iRem
  where
    tni :: Int# -> [Word64] -> FloatingX# -> [Word64] -> [Int96] -> Integer
    tni !cl# !xs !t# !ycXs !irXs =
      if null xs
        then undigits_ radixW32 ycXs -- yC
        else
          let !(xsPass, twoLSPlaces) = fromMaybe ([], 0) (unsnoc xs)
              !updRemXs = fromIntegral twoLSPlaces : 0 : irXs
              -- !tA_= undigits radixW32 updRemXs 
              -- yC_ = undigits radixW32 ycXs
              !(tA_, yC_) = pairUndigits radixW32 (updRemXs, ycXs) -- !tA_= undigits radixW32 updRemXs and then yC_ = undigits radixW32 ycXs
              !tC_ = scaleByPower2 32#Int64 t# -- sqrtF previous digits being scaled right here
              !(# ycXsOut, !yTildeFinal#, remFinal #) = case nxtDgt_# tA_ tC_ of yTilde_# -> computeRemIXS yC_ tA_ yTilde_# ycXs
              -- !(# ycXsOut, !yTildeFinal#, rFinalXs #) = case nxtDgt_# tA_ tC_ of yTilde_# -> computeRemXs yTilde_# ycXs updRemXs
              -- !(# ycXsOut, !yTildeFinal#, rFinalXs #) = case nxtDgt_# tA_ tC_ of yTilde_# -> computeRem yC_ tA_ yTilde_# ycXs updRemXs
              -- !(# ycXsOut, !yTildeFinal#, rFinalXs #) = case nxtDgt_# tA_ tC_ of yTilde_# -> computeRem_ yC_ tA_ yTilde_# ycXs updRemXs
              !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tC_ !+## unsafeword64ToFloatingX## yTildeFinal# else tC_ -- recall tcfx is already scaled by 32. Do not use normalize here
           in tni (cl# +# 1#) xsPass tcfx# ycXsOut (fromIntegral <$> digitsUnsigned radixW32 (fromIntegral remFinal)) --rFinalXs
    tniI :: Int# -> [Word64] -> FloatingX# -> Integer -> Integer -> Integer
    tniI !cl# !xs !t# !yC_ !tA =
      if null xs
        then yC_
        else
          let 
              -- !(xsPass, twoLSPlaces) = fromMaybe ([], 0) (unsnoc xs)
              !(xsPass, twoLSPlaces) = (init &&& last) xs --(init xs, last xs)
              !tA_ = tA * secndPlaceW32Radix + fromIntegral twoLSPlaces
              !tC_ = scaleByPower2 32#Int64 t# -- sqrtF previous digits being scaled right here
              !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgt_# tA_ tC_ of yTilde_# -> computeRemII yC_ tA_ yTilde_#
              !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tC_ !+## unsafeword64ToFloatingX## yTildeFinal# else tC_ -- recall tcfx is already scaled by 32. Do not use normalize here
           in tniI (cl# +# 1#) xsPass tcfx# ycUpdated remFinal--rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0
    tniISq :: Int# -> Data.Sequence.Seq Word64 -> FloatingX# -> Integer -> Integer -> Integer
    tniISq !cl# !sq !t# !yC_ !tA =
      if Data.Sequence.null sq
        then yC_
        else
          let 
              -- !(xsPass, twoLSPlaces) = fromMaybe ([], 0) (unsnoc xs)
              -- !(xsPass, twoLSPlaces) = (init &&& last)  --(init xs, last xs)
              -- !(sqPass, twoLSPlaces) = fromMaybe (Data.Sequence.empty,0) (breakDownSeq sq)
              !(sqPass, twoLSPlaces) = breakDownSeq sq
              !tA_ = tA * secndPlaceW32Radix + fromIntegral twoLSPlaces
              !tC_ = scaleByPower2 32#Int64 t# -- sqrtF previous digits being scaled right here
              !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgt_# tA_ tC_ of yTilde_# -> computeRemFitted yC_ tA_ yTilde_#
              !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tC_ !+## unsafeword64ToFloatingX## yTildeFinal# else tC_ -- recall tcfx is already scaled by 32. Do not use normalize here
           in tniISq (cl# +# 1#) sqPass tcfx# ycUpdated remFinal--rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0

-- Keep it this way: Inlining this lowers performance.
theNextIterationsSeq :: Itr_ -> Integer
-- theNextIterations (Itr !currlen# !wrd64Xs yCumulated iRem !tbfx# yCumLst iRLst) = tni currlen# wrd64Xs tbfx# yCumLst iRLst
-- theNextIterations (Itr !currlen# !wrd64Xs yCumulated iRem !tbfx# yCumLst iRLst) = tniI currlen# wrd64Xs tbfx# yCumulated iRem
theNextIterationsSeq (Itr_ !currlen# !wrd64Seq yCumulated iRem !tbfx#) = tniISq currlen# wrd64Seq tbfx# yCumulated iRem
  where
    tniISq :: Int# -> Data.Sequence.Seq Word64 -> FloatingX# -> Integer -> Integer -> Integer
    tniISq !cl# !sq !t# !yC_ !tA =
      if Data.Sequence.null sq
        then yC_
        else
          let 
              -- !(xsPass, twoLSPlaces) = fromMaybe ([], 0) (unsnoc xs)
              -- !(xsPass, twoLSPlaces) = (init &&& last)  --(init xs, last xs)
              -- !(sqPass, twoLSPlaces) = fromMaybe (Data.Sequence.empty,0) (breakDownSeq sq)
              !(sqPass, twoLSPlaces) = breakDownSeq sq
              !tA_ = tA * secndPlaceW32Radix + fromIntegral twoLSPlaces
              !tC_ = scaleByPower2 32#Int64 t# -- sqrtF previous digits being scaled right here
              !(# ycUpdated, !yTildeFinal#, remFinal #) = case nxtDgt_# tA_ tC_ of yTilde_# -> computeRemII256 yC_ tA_ yTilde_#
              !tcfx# = if isTrue# (cl# <# 3#) then nextDownFX# $ tC_ !+## unsafeword64ToFloatingX## yTildeFinal# else tC_ -- recall tcfx is already scaled by 32. Do not use normalize here
           in tniISq (cl# +# 1#) sqPass tcfx# ycUpdated remFinal--rFinalXs
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0


-- breakDownSeq :: Data.Sequence.Seq Word64 -> Maybe (Data.Sequence.Seq Word64, Word64)
-- breakDownSeq s = case Data.Sequence.viewr s of
--         rest :> x -> Just (rest, x)
--         _ -> Nothing

breakDownSeq :: Data.Sequence.Seq Word64 -> (Data.Sequence.Seq Word64, Word64)
breakDownSeq s = case Data.Sequence.viewr s of
        rest :> x -> (rest, x)
        _ -> (Data.Sequence.empty, 0)


-- | Using (***): lifts two arrows to work on a pair of inputs
pairUndigits :: (Integral a, Integral b, Integral c) => a -> ([b], [c]) -> (Integer, Integer)
pairUndigits base = undigits_ base *** undigits_ base
{-# INLINE pairUndigits #-}

-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgt_# :: Integer -> FloatingX# -> Word64#
nxtDgt_# (IN _) !_ = error "nxtDgt_ :: Invalid negative integer argument"
nxtDgt_# 0 !_ = 0#Word64
nxtDgt_# (IS ta#) tcfx# = case preComput (int2Double# ta#) tcfx# of (# a#, c#, r# #) -> computDouble# a# c# r#
nxtDgt_# n@(IP bn#) tcfx#
  | isTrue# ((bigNatSize# bn#) <# thresh#) = case preComput (bigNatEncodeDouble# bn# 0#) tcfx# of (# a#, c#, r# #) -> computDouble# a# c# r#
  | otherwise = comput_ (preComput_ bn# tcfx#)
  where
    thresh# :: Int#
    thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14#

{-# INLINE computDouble# #-}
computDouble# :: Double# -> Double# -> Double# -> Word64#
computDouble# !tAFX# !tCFX# !radFX# = case floorDouble (D# (nextUp# (nextUp# tAFX# /## nextDown# (sqrtDouble# (nextDown# radFX#) +## nextDown# tCFX#)))) of (W64# w#) -> hndlOvflwW32## w#

-- computDouble# !tAFX# !tCFX# !radFX# = let !(I64# i#) = floorDouble (D# (nextUp# (nextUp# tAFX# /## nextDown# (fmaddDouble# (sqrtDouble# (nextDown# radFX#)) 1.00## (nextDown# tCFX#)) ))) in hndlOvflwW32# i#

preComput :: Double# -> FloatingX# -> (# Double#, Double#, Double# #)
preComput a# tcfx# =
  let !c# = unsafefx2Double## tcfx#
      !r# = fmaddDouble# c# c# a#
   in (# a#, c#, r# #)
{-# INLINE preComput #-}

preComput_ :: BigNat# -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
preComput_ tA__bn# tCFX# = case unsafebigNat2FloatingX## tA__bn# of tAFX# -> (# tAFX#, tCFX#, tCFX# !**+## tAFX# #) -- last item is radFX# and uses custom fx# based fused square (multiply) and add
{-# INLINE preComput_ #-}

comput_ :: (# FloatingX#, FloatingX#, FloatingX# #) -> Word64#
comput_ (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwW32## (floorX## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE comput_ #-}

computeRem :: Integer -> Integer -> Word64# -> [Word64] -> [Int96] -> (# [Word64], Word64#, [Int96] #)
computeRem _ _ 0#Word64 yXs rXs = (# 0:yXs, 0#Word64, rXs #)
computeRem yc ta yTilde_# yXs rXs@(x : 0 : xs ) = let 
      !i = W64# yTilde_#-- W64
      -- xMinusISq = x - fromIntegral (W64# (yTilde_# `timesWord64#` yTilde_#))  -- Integer
      -- negI2ycInteger = negate (fromIntegral i *  double yc)--negate i2yc_ -- integer and it will be negative 
      -- rdrXs = fromIntegral xMinusISq : negI2ycInteger : (fromIntegral <$> xs) -- keep this as integer list and this works !
      -- !rdr = undigits_ radixW32 rdrXs -- (i * double yc_ * radixW32 + i*i)
      !rdr = ta - fromIntegral i * (double yc * radixW32 + fromIntegral i)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred ((yc * radixW32) + fromIntegral i)) + 1 #) else (# yTilde_#, rdr #) 
    in (# W64# yAdj# : yXs, yAdj#, fromIntegral <$> digitsUnsigned radixW32 (fromIntegral rdrAdj) #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
computeRem _ _ _ _ _ = error "wrong"
{-# INLINE computeRem #-}

computeRemXs :: Word64# -> [Word64] -> [Int96] -> (# [Word64], Word64#, [Int96] #)
computeRemXs 0#Word64 yXs rXs = (# 0:yXs, 0#Word64, rXs #)
computeRemXs yTilde_# yXs rXs@(x : 0 : xs ) = let 
      !i = W64# yTilde_#-- W64
      xMinusISq = x - fromIntegral (W64# (yTilde_# `timesWord64#` yTilde_#))  -- Integer
      yc_ = undigits_ radixW32 yXs 
      negI2ycInteger = negate (fromIntegral i *  double yc_)--negate i2yc_ -- integer and it will be negative 
      rdrXs = fromIntegral xMinusISq : negI2ycInteger : (fromIntegral <$> xs) -- keep this as integer list and this works !
      !rdr = undigits_ radixW32 rdrXs -- (i * double yc_ * radixW32 + i*i)
      -- !rdr = ta - fromIntegral i * (double yc * radixW32 + fromIntegral i)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred ((yc_ * radixW32) + fromIntegral i)) + 1 #) else (# yTilde_#, rdr #) 
    in (# W64# yAdj# : yXs, yAdj#, fromIntegral <$> digitsUnsigned radixW32 (fromIntegral rdrAdj) #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
computeRemXs _ _ _ = error "wrong"
{-# INLINE computeRemXs #-}

computeRemII :: Integer -> Integer -> Word64# -> (# Integer, Word64#, Integer #)
computeRemII yc ta 0#Word64 = (# yc * radixW32, 0#Word64, ta #)
computeRemII yc ta yTilde_# = let 
      !i = fromIntegral $ W64# yTilde_#-- W64
      !ycScaled = yc * radixW32
      !rdr = if fitsInMaxInt64 ta then 
        case fromIntegral i `safeAdd64` fromIntegral ycScaled of 
            Right iPlusycScaled -> case fromIntegral ycScaled `safeAdd64` iPlusycScaled of 
                Right iPlusDoubleYcScaled -> case fromIntegral i `safeMul64` iPlusDoubleYcScaled of 
                    Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled `safeAdd64` fromIntegral ta of 
                        Right rdr64 -> fromIntegral rdr64 
                        Left rdrIN -> rdrIN
                    Left iTimesiPlusDoubleYcScaledIN ->  ta - iTimesiPlusDoubleYcScaledIN
                Left iPlusDoubleYcScaledIN ->  ta - i * iPlusDoubleYcScaledIN
            Left iPlusycScaledIN ->  ta - i * (iPlusycScaledIN + ycScaled)
        else 
          ta - i * (double ycScaled + i)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred (ycScaled +  i)) + 1 #) else (# yTilde_#, rdr #) 
    in (# fromIntegral (W64# yAdj#) + ycScaled, yAdj#, rdrAdj #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
{-# INLINE computeRemII #-}

computeRemII96 :: Integer -> Integer -> Word64# -> (# Integer, Word64#, Integer #)
computeRemII96 yc ta 0#Word64 = (# yc * radixW32, 0#Word64, ta #)
computeRemII96 yc ta yTilde_# = let 
      !i = fromIntegral $ W64# yTilde_#-- W64
      !ycScaled = yc * radixW32
      !rdr = if fitsInMaxInt96 ta then 
        case fromIntegral i `safeAdd96` fromIntegral ycScaled of 
            Right iPlusycScaled -> case fromIntegral ycScaled `safeAdd96` iPlusycScaled of 
                Right iPlusDoubleYcScaled -> case fromIntegral i `safeMul96` iPlusDoubleYcScaled of 
                    Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled `safeAdd96` fromIntegral ta of 
                        Right rdr64 -> fromIntegral rdr64 
                        Left rdrIN -> rdrIN
                    Left iTimesiPlusDoubleYcScaledIN ->  ta - iTimesiPlusDoubleYcScaledIN
                Left iPlusDoubleYcScaledIN ->  ta - i * iPlusDoubleYcScaledIN
            Left iPlusycScaledIN ->  ta - i * (iPlusycScaledIN + ycScaled)
        else 
          ta - i * (double ycScaled + i)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred (ycScaled +  i)) + 1 #) else (# yTilde_#, rdr #) 
    in (# fromIntegral (W64# yAdj#) + ycScaled, yAdj#, rdrAdj #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
{-# INLINE computeRemII96 #-}

computeRemII256 :: Integer -> Integer -> Word64# -> (# Integer, Word64#, Integer #)
computeRemII256 yc ta 0#Word64 = (# yc * radixW32, 0#Word64, ta #)
computeRemII256 yc ta yTilde_# = let 
      !ycScaled = yc * radixW32
      !intToUse = whichInt ta 
      !rdr = case intToUse of 
                  Is64 -> let (i64, ycScaled64, ta64) = (fromIntegral $ W64# yTilde_#, fromIntegral ycScaled, fromIntegral ta) in case i64 `safePosAdd64` ycScaled64 of 
                                    Right iPlusycScaled -> case ycScaled64 `safePosAdd64` iPlusycScaled of 
                                        Right iPlusDoubleYcScaled -> case i64 `safeMul64` iPlusDoubleYcScaled of 
                                            Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + ta64 of rdr64 -> fromIntegral rdr64
                                            -- Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled `safeAdd64` ta64 of 
                                            --     Right rdr64 -> fromIntegral rdr64 
                                            --     Left rdrIN -> rdrIN
                                            Left iTimesiPlusDoubleYcScaledIN ->  ta - iTimesiPlusDoubleYcScaledIN
                                        Left iPlusDoubleYcScaledIN ->  ta - fromIntegral (W64# yTilde_#) * iPlusDoubleYcScaledIN
                                    Left iPlusycScaledIN ->  ta - fromIntegral (W64# yTilde_#) * (iPlusycScaledIN + ycScaled)
                  Is128 -> let (i128, ycScaled128, ta128) = (fromIntegral $ W64# yTilde_#, fromIntegral ycScaled, fromIntegral ta) in case i128 `safePosAdd128` ycScaled128 of 
                                          Right iPlusycScaled -> case ycScaled128 `safePosAdd128` iPlusycScaled of 
                                              Right iPlusDoubleYcScaled -> case i128 `safeMul128` iPlusDoubleYcScaled of 
                                                  Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + ta128 of rdr128 -> fromIntegral rdr128
                                                  -- Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled `safeAdd256` ta256 of 
                                                  --     Right rdr64 -> fromIntegral rdr256 
                                                  --     Left rdrIN -> rdrIN
                                                  Left iTimesiPlusDoubleYcScaledIN ->  ta - iTimesiPlusDoubleYcScaledIN
                                              Left iPlusDoubleYcScaledIN ->  ta - fromIntegral (W64# yTilde_#) * iPlusDoubleYcScaledIN
                                          Left iPlusycScaledIN ->  ta - fromIntegral (W64# yTilde_#) * (iPlusycScaledIN + ycScaled)
                  Is256 -> let (i256, ycScaled256, ta256) = (fromIntegral $ W64# yTilde_#, fromIntegral ycScaled, fromIntegral ta)  in case i256 `safePosAdd256` ycScaled256 of 
                                          Right iPlusycScaled -> case ycScaled256 `safePosAdd256` iPlusycScaled of 
                                              Right iPlusDoubleYcScaled -> case i256 `safeMul256` iPlusDoubleYcScaled of 
                                                  Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + ta256 of rdr256 -> fromIntegral rdr256
                                                  -- Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled `safeAdd256` ta256 of 
                                                  --     Right rdr64 -> fromIntegral rdr256 
                                                  --     Left rdrIN -> rdrIN
                                                  Left iTimesiPlusDoubleYcScaledIN ->  ta - iTimesiPlusDoubleYcScaledIN
                                              Left iPlusDoubleYcScaledIN ->  ta - fromIntegral (W64# yTilde_#) * iPlusDoubleYcScaledIN
                                          Left iPlusycScaledIN ->  ta - fromIntegral (W64# yTilde_#) * (iPlusycScaledIN + ycScaled)
                  _ -> case fromIntegral $ W64# yTilde_# of i -> ta - i * (double ycScaled + i)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred (ycScaled +  fromIntegral (W64# yTilde_#))) + 1 #) else (# yTilde_#, rdr #) 
    in (# fromIntegral (W64# yAdj#) + ycScaled, yAdj#, rdrAdj #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
{-# INLINE computeRemII256 #-}

computeRemFitted :: Integer -> Integer -> Word64# -> (# Integer, Word64#, Integer #)
computeRemFitted yc ta 0#Word64 = (# yc * radixW32, 0#Word64, ta #)
computeRemFitted yc ta yTilde_# = let 
      !ycScaled = yc * radixW32
      !i = fromIntegral (W64# yTilde_#)
      !intToUse = allWithin yc ta i 
      !rdr = case intToUse of 
                  Is32 -> let (i64, ycScaled64, ta64) = (fromIntegral (W64# yTilde_#) :: Int64, fromIntegral ycScaled :: Int64, fromIntegral ta :: Int64) in  fromIntegral (ta64 - i64 * (2 * ycScaled64 + i64))
                  -- (Is64) -> let (i64, ycScaled64, ta64) = (fromIntegral (W64# yTilde_#) :: Int64, fromIntegral ycScaled :: Int64, fromIntegral ta :: Int64) in  fromIntegral (ta64 - i64 * (2 * ycScaled64 + i64))
                  -- (Is96; Is128) -> let (i128, ycScaled128, ta128) = (fromIntegral $ W64# yTilde_# :: Int128, fromIntegral ycScaled :: Int128, fromIntegral ta :: Int128) in fromIntegral (ta128 - i128 * (2 *  ycScaled128 + i128))
                  Is256 -> let (i256, ycScaled256, ta256) = (fromIntegral $ W64# yTilde_# :: Word256, fromIntegral ycScaled :: Word256, fromIntegral ta :: Word256) in case i256 `safeAddW256` ycScaled256 of 
                                          Right iPlusycScaled -> case ycScaled256 `safeAddW256` iPlusycScaled of 
                                              Right iPlusDoubleYcScaled -> case i256 `safeMulW256` iPlusDoubleYcScaled of 
                                                  Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled + ta256 of rdr256 -> fromIntegral rdr256
                                                  -- Right iTimesiPlusDoubleYcScaled -> case negate iTimesiPlusDoubleYcScaled `safeAdd256` ta256 of 
                                                  --     Right rdr64 -> fromIntegral rdr256 
                                                  --     Left rdrIN -> rdrIN
                                                  Left iTimesiPlusDoubleYcScaledIN ->  ta - iTimesiPlusDoubleYcScaledIN
                                              Left iPlusDoubleYcScaledIN ->  ta - i * iPlusDoubleYcScaledIN
                                          Left iPlusycScaledIN ->  ta - i * (iPlusycScaledIN + ycScaled)
                  (IsIN; _) -> ta - i * (double ycScaled + i)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred (ycScaled +  i)) + 1 #) else (# yTilde_#, rdr #) 
    in (# fromIntegral (W64# yAdj#) + ycScaled, yAdj#, rdrAdj #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
{-# INLINE computeRemFitted #-}

fitsInInt64 :: Integral a => a -> Bool 
fitsInInt64 x = fromIntegral x >= toInteger (minBound :: Int64)
             && fromIntegral x <= toInteger (maxBound :: Int64)

fitsInMaxInt32 :: Integer -> Bool 
fitsInMaxInt32 x = x <= toInteger (maxBound :: Int32)
{-# INLINE fitsInMaxInt32 #-}

fitsInMaxInt64 :: Integer -> Bool 
fitsInMaxInt64 x = x <= toInteger (maxBound :: Int64)
{-# INLINE fitsInMaxInt64 #-}

fitsInMaxInt96 :: Integer -> Bool 
fitsInMaxInt96 x = x <= toInteger (maxBound :: Int96)
{-# INLINE fitsInMaxInt96 #-}

fitsInMaxInt128 :: Integer -> Bool 
fitsInMaxInt128 x = x <= toInteger (maxBound :: Int128)
{-# INLINE fitsInMaxInt128 #-}

fitsInMaxInt256 :: Integer -> Bool 
fitsInMaxInt256 x = x <= toInteger (maxBound :: Int256)
{-# INLINE fitsInMaxInt256 #-}

fitsInMaxWord256 :: Integer -> Bool 
fitsInMaxWord256 x = x <= toInteger (maxBound :: Word256)
{-# INLINE fitsInMaxWord256 #-}

data MaxBounds
  = Is32
  | Is64
  | Is96
  | Is128
  | Is256
  | IsIN
  deriving (Eq, Show, Ord)

whichInt :: Integer -> MaxBounds 
whichInt n = fromMaybe IsIN $ firstTrueOf [if fitsInMaxInt64 n then Just Is64 else Nothing, if fitsInMaxInt128 n then Just Is128 else Nothing, if fitsInMaxInt256 n then Just Is256 else Nothing, Just IsIN]
{-# INLINE whichInt #-}

allWithin :: Integer -> Integer -> Integer -> MaxBounds 
allWithin n1 n2 n3 = maximum (fromMaybe IsIN <$> firstTrueOf <$> lazyXsFits <$> [n1,n2,n3])
{-# INLINE allWithin #-}

lazyXsFits :: Integer -> [Maybe MaxBounds]
lazyXsFits n = [if fitsInMaxInt32 n then Just Is32 else Nothing, if fitsInMaxInt64 n then Just Is64 else Nothing, if fitsInMaxInt96 n then Just Is96 else Nothing, if fitsInMaxInt128 n then Just Is128 else Nothing, if fitsInMaxWord256 n then Just Is256 else Nothing, Just IsIN]

-- based on analysis and this is a heuristic
goForInt :: Integer -> Integer -> MaxBounds 
goForInt n1 n2 = case firstTrueOf (lazyXsFits n1) of 
                          Just Is32 -> case firstTrueOf (lazyXsFits n2) of
                            Just Is32 -> Is64
                            Just Is64 -> Is128 
                            Just Is96 -> Is256
                            Just Is128 -> IsIN 
                            (Just Is256; Just IsIN; _) -> IsIN 
                          Just Is64 -> case firstTrueOf (lazyXsFits n2) of
                                                        Just Is32 -> Is128
                                                        Just Is64 -> Is256
                                                        Just Is96 -> IsIN
                                                        Just Is128 -> IsIN 
                                                        (Just Is256; Just IsIN; _) -> IsIN 
                          Just Is96 ->  case firstTrueOf (lazyXsFits n2) of
                                                        Just Is32 -> Is256
                                                        Just Is64 -> IsIN 
                                                        Just Is96 -> IsIN
                                                        Just Is128 -> IsIN 
                                                        (Just Is256; Just IsIN; _) -> IsIN 
                          Just Is128 -> case firstTrueOf (lazyXsFits n2) of
                                                        Just Is32 -> Is256
                                                        Just Is64 -> IsIN 
                                                        Just Is96 -> IsIN
                                                        Just Is128 -> IsIN
                                                        (Just Is256; Just IsIN; _) -> IsIN 
                          (Just Is256; Just IsIN; _) -> IsIN 
{-# INLINE goForInt #-}

safeAdd64 :: Int64 -> Int64 -> Either Integer Int64
safeAdd64 x y =
  let !result = x + y
  in if (x > 0 && y > 0 && result < 0) || (x < 0 && y < 0 && result > 0)
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safeAdd64 #-}

safePosAdd64 :: Int64 -> Int64 -> Either Integer Int64
safePosAdd64 x y =
  let !result = x + y
  in if result < 0 
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safePosAdd64 #-}

safeMul64 :: Int64 -> Int64 -> Either Integer Int64
safeMul64 x y =
  let !result = x * y
      -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
  in if y /= 0 && result `div` y /= x
     then Left (toInteger x * toInteger y)
     else Right result
{-# INLINE safeMul64 #-}

safeAdd128 :: Int128 -> Int128 -> Either Integer Int128
safeAdd128 x y =
  let !result = x + y
  in if (x > 0 && y > 0 && result < 0) || (x < 0 && y < 0 && result > 0)
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safeAdd128 #-}

safePosAdd128 :: Int128 -> Int128 -> Either Integer Int128
safePosAdd128 x y =
  let !result = x + y
  in if result < zeroInt128  
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safePosAdd128 #-}

safeMul128 :: Int128 -> Int128 -> Either Integer Int128
safeMul128 x y =
  let !result = x * y
      -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
  in if y /= zeroInt128 && result `div` y /= x
     then Left (toInteger x * toInteger y)
     else Right result
{-# INLINE safeMul128 #-}

safeAdd96 :: Int96 -> Int96 -> Either Integer Int96
safeAdd96 x y =
  let !result = x + y
  in if (x > 0 && y > 0 && result < 0) || (x < 0 && y < 0 && result > 0)
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safeAdd96 #-}

safeMul96 :: Int96 -> Int96 -> Either Integer Int96
safeMul96 x y =
  let !result = x * y
      -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
  in if y /= 0 && result `div` y /= x
     then Left (toInteger x * toInteger y)
     else Right result
{-# INLINE safeMul96 #-}

safeAdd256 :: Int256 -> Int256 -> Either Integer Int256
safeAdd256 x y =
  let !result = x + y
  in if (x > 0 && y > 0 && result < 0) || (x < 0 && y < 0 && result > 0)
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safeAdd256 #-}

safeAddW256 :: Word256 -> Word256 -> Either Integer Word256
safeAddW256 x y =
  let !result = x + y
  in if (x > 0 && y > 0 && result < 0) || (x < 0 && y < 0 && result > 0)
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safeAddW256 #-}

safeSubW256 :: Word256 -> Word256 -> Either Integer Word256
safeSubW256 x y =
  let !result = x + (negate y)
  in if (x > 0 && y > 0 && result < 0) || (x < 0 && y < 0 && result > 0)
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safeSubW256 #-}

safePosAdd256 :: Int256 -> Int256 -> Either Integer Int256
safePosAdd256 x y =
  let !result = x + y
  in if result < 0 
     then Left (toInteger x + toInteger y)
     else Right result
{-# INLINE safePosAdd256 #-}

safeMul256 :: Int256 -> Int256 -> Either Integer Int256
safeMul256 x y =
  let !result = x * y
      -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
  in if y /= 0 && result `div` y /= x
     then Left (toInteger x * toInteger y)
     else Right result
{-# INLINE safeMul256 #-}

safeMulW256 :: Word256 -> Word256 -> Either Integer Word256
safeMulW256 x y =
  let !result = x * y
      -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
  in if y /= 0 && result `div` y /= x
     then Left (toInteger x * toInteger y)
     else Right result
{-# INLINE safeMulW256 #-}


computeRemIXS :: Integer -> Integer -> Word64# -> [Word64] -> (# [Word64], Word64#, Integer #)
computeRemIXS _ ta 0#Word64 yXs  = (# 0:yXs, 0#Word64, ta #)
computeRemIXS yc ta yTilde_# yXs = let 
      !i = W64# yTilde_#-- W64
      !rdr = ta - fromIntegral i * (double yc * radixW32 + fromIntegral i)
      !(# yAdj#, rdrAdj #) = if rdr < 0 then (# yTilde_# `subWord64#` 1#Word64, rdr + double (pred ((yc * radixW32) + fromIntegral i)) + 1 #) else (# yTilde_#, rdr #) 
    in (# W64# yAdj# : yXs, yAdj#, rdrAdj #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
{-# INLINE computeRemIXS #-}

-- | compute the remainder. It may be that the trial "digit" may need to be reworked
-- that happens in handleRems_
-- if the trial digit is zero skip computing remainder
computeRem_ :: Integer -> Integer -> Word64# -> [Word64] -> [Int96] -> (# [Word64], Word64#, [Int96] #)
computeRem_ _ _ 0#Word64 yXs rXs = (# 0:yXs, 0#Word64, rXs #)
computeRem_ yc ta yTilde_# yXs rXs = case calcRemainder2 yTilde_# yc yXs rXs of (rTrial, rTrialXs, scaledby32yC) -> handleRems2 (# yXs, yTilde_#, rTrial, rTrialXs, scaledby32yC #)
-- computeRem_ yc ta yTilde_# yXs rXs = case calcRemainder1 yTilde_# yc ta of (rTrial, rTrialXs, scaledby32yC) ->  handleRems2 (# yXs, yTilde_#, rTrial, rTrialXs, scaledby32yC #)
-- computeRem_ yc ta yTilde_# yXs rXs = case calcRemainder1 yTilde_# ta yc of (rTrial, rTrialXs, scaledby32yC) -> handleRems (# scaledby32yC, yTilde_#, rTrial #)
{-# INLINE computeRem_ #-}


handleRemsSeq :: (# [Word64], Word64#, Integer #) -> (# Integer, Word64#, Integer #)
handleRemsSeq (# ycXs, yi64#, ri_ #)
  | ri_ < 0 =
      let !yAdj# = yi64# `subWord64#` 1#Word64
          !adjYc = pred ycyi
          !rdr = fixRemainder adjYc ri_
       in (# adjYc, yAdj#, rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | otherwise = (# ycyi, yi64#, ri_ #)
  where
    -- !ycyi = ycScaled_ + fromIntegral (W64# yi64#) -- accumulating the growing square root
    !ycyi = undigits radixW32 (W64# yi64# : ycXs) -- accumulating the growing square root
{-# INLINE handleRemsSeq #-}


handleRems :: (# [Word64], Integer, Word64#, Integer #) -> (# [Word64], Integer, Word64#, Integer #)
handleRems (# ycXs, ycScaled_, yi64#, ri_ #)
  | ri_ < 0 =
      let !yAdj# = yi64# `subWord64#` 1#Word64
          !adjYc = pred ycyi
          !rdr = fixRemainder adjYc ri_
       in (# W64# yAdj# : ycXs, adjYc, yAdj#, rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | otherwise = (# W64# yi64# : ycXs, ycyi, yi64#, ri_ #)
  where
    -- !ycyi = ycScaled_ + fromIntegral (W64# yi64#) -- accumulating the growing square root
    !ycyi = undigits radixW32 (W64# yi64# : ycXs) -- accumulating the growing square root
{-# INLINE handleRems #-}

handleRems2 :: (# [Word64], Word64#, Integer, [Int96], Integer #) -> (# [Word64], Word64#, [Int96] #)
handleRems2 (# !ycXs, !yi64#, !ri_, !ri_Xs, ycScaled_ #)
  | ri_ < 0 =
      let !yAdj# = yi64# `subWord64#` 1#Word64
          -- !ycyi = undigits_ radixW32 ycXsOutAsIs -- accumulating the growing square root
          !adjYc = pred ycyi
          !rdr = fixRemainder adjYc ri_ -- this is an integer, in digitsUnsigned the argument is a natural below
       in (# W64# yAdj# : ycXs, yAdj#, fromIntegral <$> digitsUnsigned radixW32 (fromIntegral rdr) #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  -- | ri_ > 0 && excessLengthBy3 = let  -- is this check needed ?
  --                           !modulus3 = radixW32 ^ 3
  --                           !adjustedRemainder3 = ri_ `mod` modulus3
  --                           !riAdjustedXs = fromIntegral <$> digitsUnsigned radixW32 (fromIntegral adjustedRemainder3)
  --                         in (# ycXsOutAsIs, yi64#, riAdjustedXs #)
  | otherwise = (# ycXsOutAsIs, yi64#, ri_Xs #)
  where
    yiW64 = W64# yi64#
    yi = fromIntegral yiW64
    ycyi = ycScaled_ + yi -- accumulating the growing square root
    ycXsOutAsIs = yiW64 : ycXs
    lenCurrRemainder = 1 + integerLogBase' radixW32 yi -- //TODO THIS TAKES UP A CHUNK OF TIME length (digits (fromIntegral b) ri) makes little diff
    lenCurrSqrt = 1 + integerLogBase' radixW32 yi
    excessLengthBy3 = lenCurrRemainder >= lenCurrSqrt + 3
{-# INLINE handleRems2 #-}

-- Calculate remainder accompanying a 'digit'
calcRemainder2 :: Word64# -> Integer -> [Word64] -> [Int96] -> (Integer, [Int96], Integer)
calcRemainder2 0#Word64 !yc_ _ rXs = (undigits radixW32 rXs, rXs, yc_ * radixW32)
calcRemainder2 !dgt64# !yc_ !ycXs rXs@(x : 0 : xs) =
  let !i = W64# dgt64# -- W64
      !xMinusISq = x - fromIntegral (W64# (dgt64# `timesWord64#` dgt64#))  -- Integer
      !yc = yc_--undigits_ radixW32 ycXs
      !negI2ycInteger = negate (fromIntegral i *  double yc)--negate i2yc_ -- integer and it will be negative 
      !rdrXs = fromIntegral xMinusISq : negI2ycInteger : (fromIntegral <$> xs) -- keep this as integer list and this works !
      !rdr = undigits_ radixW32 rdrXs -- (i * double yc_ * radixW32 + i*i)
      !rdrXsInteger = if rdr < 0 then [] else fromIntegral <$> digitsUnsigned radixW32 (fromIntegral rdr) --fromIntegral <$> rdrXs -- xMinusISq : negI2ycInteger : xs -- does not work
   in (rdr, rdrXsInteger, yc * radixW32) -- tAI - ((double i * tc) + i * i)
calcRemainder2 _ _ _ _ = error "error"
{-# INLINE calcRemainder2 #-}

-- Calculate remainder accompanying a 'digit'
calcRemainder1 :: Word64# -> Integer -> Integer -> (Integer, [Int96], Integer)
calcRemainder1 0#Word64 !yc_ tAI   = (tAI, fromIntegral <$> digitsUnsigned radixW32 (fromIntegral tAI), yc_ * radixW32)
calcRemainder1 !dgt64# !yc_ tAI   =
  let !i = fromIntegral (W64# dgt64#)
      !ycScaled = yc_ * radixW32
      !rdr = tAI - i * (double ycScaled + i)
      !rdrXsInteger = if rdr < 0 then [] else fromIntegral <$> digitsUnsigned radixW32 (fromIntegral rdr) --fromIntegral <$> rdrXs -- xMinusISq : negI2ycInteger : xs -- does not work
   in (rdr, rdrXsInteger, ycScaled) -- tAI - ((double i * tc) + i * i)
{-# INLINE calcRemainder1 #-}

-- -- Fix remainder accompanying a 'next downed digit'
fixRemainder :: Integer -> Integer -> Integer
fixRemainder !tcplusdgtadj !rdr = rdr + double tcplusdgtadj + 1
{-# INLINE fixRemainder #-}

-- | HELPER functions
{-# INLINE dgtsLstBase32 #-}
dgtsLstBase32 :: Integer -> [Word32]
dgtsLstBase32 n = mkIW32Lst n radixW32

-- | Word64# from a "reversed" List of at least 1 and at most 2 Word32 digits
word64FromRvsrd2ElemList# :: [Word32] -> Word64#
word64FromRvsrd2ElemList# [] = error "word64FromRvsrd2ElemList# : null list"
word64FromRvsrd2ElemList# [llsb] = word64FromRvsrdTuple# (llsb, 0) 4294967296#Word64
word64FromRvsrd2ElemList# [llsb, lmsb] = word64FromRvsrdTuple# (llsb, lmsb) 4294967296#Word64
word64FromRvsrd2ElemList# (_ : _ : _) = error "word64FromRvsrd2ElemList# : more than 2 elems list"
{-# INLINE word64FromRvsrd2ElemList# #-}

-- | Word64# from a "reversed" Seq of at least 1 and at most 2 Word32 digits
word64FromRvsrd2ElemSeq# :: Data.Sequence.Seq Word32 -> Word64#
word64FromRvsrd2ElemSeq# Data.Sequence.Empty = error "word64FromRvsrd2ElemSeq# : null list"
word64FromRvsrd2ElemSeq# (llsb :<| Data.Sequence.Empty) = word64FromRvsrdTuple# (llsb, 0) 4294967296#Word64
word64FromRvsrd2ElemSeq# (llsb :<| lmsb :<| Data.Sequence.Empty) = word64FromRvsrdTuple# (llsb, lmsb) 4294967296#Word64
word64FromRvsrd2ElemSeq# (_ :<| _ :<| _ :<| _) = error "word64FromRvsrd2ElemSeq# : more than 2 elems list"
{-# INLINE word64FromRvsrd2ElemSeq# #-}

{-# INLINE mkIW32Lst #-}

-- | Spit out the Word32 List from digitsUnsigned which comes in reversed format.
mkIW32Lst :: Integer -> Word -> [Word32]
mkIW32Lst 0 _ = [0] -- safety
mkIW32Lst i b = wrd2wrd32 (iToWrdListBase i b)

{-# INLINE splitLastTwo #-}
splitLastTwo :: [a] -> Int -> ([a], [a])
splitLastTwo xs l = splitAt (l - 2) xs

{-# INLINE splitLastTwoSeq #-}
splitLastTwoSeq :: [a] -> Int -> (Data.Sequence.Seq a, Data.Sequence.Seq a)
splitLastTwoSeq xs l = Data.Sequence.splitAt (l - 2) (Data.Sequence.fromList xs)

{-# INLINE splitLastOne #-}
splitLastOne :: [a] -> Int -> ([a], [a])
splitLastOne xs l = splitAt (l - 1) xs

{-# INLINE splitLastOneSeq #-}
splitLastOneSeq :: [a] -> Int -> (Data.Sequence.Seq a, Data.Sequence.Seq a)
splitLastOneSeq xs l = Data.Sequence.splitAt (l - 1) (Data.Sequence.fromList xs)

{-# INLINE pairUp #-}
pairUp :: Bool -> [a] -> [(a, a)]
pairUp True (x : y : rs) = (x, y) : pairUp True rs
pairUp True [] = []
pairUp _ [_] = error "pairUp: Invalid singleton list"
pairUp False _ = error "pairUp: Invalid odd length of list"

{-# INLINE pairUpSeq #-}
pairUpSeq
  :: Bool            -- ^ allow an unmatched final element?
  -> Seq a           -- ^ input sequence
  -> Seq (a, a)      -- ^ output sequence of pairs
pairUpSeq allowIncomplete = go
  where
    go xs = case Data.Sequence.viewl xs of
      -- at least one element: x
      x :< xs' -> case viewl xs' of
        -- at least two elements: x,y
        y :< rest ->
          -- cons (x,y) and continue
          (x, y) <| go rest

        -- exactly one element x, and nothing else
        EmptyL
          | allowIncomplete -> Data.Sequence.empty
          | otherwise       ->
              error "pairUpSeq: Invalid odd length of sequence"

      -- no elements → done
      EmptyL -> Data.Sequence.empty

{-# INLINE integerOfNxtPairsLst #-}
integerOfNxtPairsLst :: Int -> [(Word32, Word32)] -> [Word64]
integerOfNxtPairsLst l = if l < 8 then map iFrmTupleBaseW32 else parallelMap Chunk 2 iFrmTupleBaseW32 -- assuming even dual core 
-- integerOfNxtPairsLst l = map iFrmTupleBaseW32

{-# INLINE integerOfNxtPairsSeq #-}
integerOfNxtPairsSeq :: Int -> Data.Sequence.Seq (Word32, Word32) -> Data.Sequence.Seq Word64
integerOfNxtPairsSeq _ = fmap iFrmTupleBaseW32

-- | Strategies that may be used with parallel calls
data Strats
  = Chunk
  | Buffer
  | Split
  deriving (Eq)

-- | parallel map with 3 optional strategies
parallelMap :: (NFData a, NFData b) => Strats -> Int -> (a->b) -> [a] -> [b]
parallelMap strat stratParm f = case strat of
  Chunk -> withStrategy (parListChunk stratParm rdeepseq) . map f
  Buffer -> withStrategy (parBuffer stratParm rpar) . map f
  Split -> withStrategy (parListSplitAt stratParm rdeepseq rdeepseq) . map f

{-# INLINE iFrmTupleBaseW32 #-}
iFrmTupleBaseW32 :: (Word32, Word32) -> Word64
iFrmTupleBaseW32 tu = word64FromRvsrdTuple tu radixW32

{-# INLINE mkIW32EvenRestLst #-}
mkIW32EvenRestLst :: Int -> Bool -> [Word32] -> [Word64]
mkIW32EvenRestLst len evenLen xs = integerOfNxtPairsLst len (pairUp evenLen xs)

{-# INLINE mkIW32EvenRestSeq #-}
mkIW32EvenRestSeq :: Int -> Bool -> Data.Sequence.Seq Word32 -> Data.Sequence.Seq Word64
mkIW32EvenRestSeq len evenLen sq = integerOfNxtPairsSeq len (pairUpSeq evenLen sq)


--- END helpers
--- BEGIN Core numeric helper functions
--- ***********************************

{-# INLINE intgrFromRvsrdTuple #-}

-- | Integer from a "reversed" tuple of Word32 digits
intgrFromRvsrdTuple :: (Word32, Word32) -> Integer -> Integer
intgrFromRvsrdTuple (0, 0) 0 = 0
intgrFromRvsrdTuple (0, lMSB) base = fromIntegral lMSB * base
intgrFromRvsrdTuple (lLSB, 0) _ = fromIntegral lLSB
intgrFromRvsrdTuple (lLSB, lMSB) base = fromIntegral lMSB * base + fromIntegral lLSB

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

{-# INLINE doubleFromRvsrdTuple #-}

-- | double from a "reversed" tuple of Word32 digits
doubleFromRvsrdTuple :: (Word32, Word32) -> Integer -> Double
doubleFromRvsrdTuple (l1, l2) base = fromIntegral l2 * fromIntegral base + fromIntegral l1

{-# INLINE largestNSqLTEOdd #-}
largestNSqLTEOdd :: Word64 -> Word64
largestNSqLTEOdd i = floorDouble (sqrt (fromIntegral i) :: Double)

{-# INLINE largestNSqLTEEven #-}
largestNSqLTEEven :: Word64 -> Word64
largestNSqLTEEven i = let d_ = nextUp (fromIntegral i :: Double) in floorDouble (nextUp (sqrt d_))

{-# INLINE largestNSqLTEOdd## #-}
largestNSqLTEOdd## :: Word64# -> Word64#
largestNSqLTEOdd## w# = case floorDouble (sqrt (fromIntegral (W64# w#)) :: Double) of (W64# r#) -> r#

{-# INLINE largestNSqLTEEven## #-}
largestNSqLTEEven## :: Word64# -> Word64#
largestNSqLTEEven## w# =
  let !d_ = nextUp (fromIntegral (W64# w#) :: Double)
      !(W64# r#) = floorDouble (nextUp (sqrt d_))
   in r#

-- | handle overflow
{-# INLINE hndlOvflwW32 #-}
hndlOvflwW32 :: (Integral a) => a -> a
hndlOvflwW32 i = if i == maxW32 then pred maxW32 else i where maxW32 = radixW32

{-# INLINE hndlOvflwW32## #-}
hndlOvflwW32## :: Word64# -> Word64#
hndlOvflwW32## w64# = if isTrue# (w64# `eqWord64#` maxW32#) then predmaxW32# else w64#
  where
    !(W64# maxW32#) = radixW32
    !(W64# predmaxW32#) = predRadixW32

scaleByPower2 :: Int64# -> FloatingX# -> FloatingX#
scaleByPower2 n# (FloatingX# s# e#) = if isTrue# (s# ==## 0.00##) then zero# else FloatingX# s# (e# `plusInt64#` n#) -- normalizeFX# $ FloatingX# s# (e# `plusInt64#` n#)
{-# INLINE scaleByPower2 #-}

{-# INLINE wrd2wrd32 #-}
wrd2wrd32 :: [Word] -> [Word32]
wrd2wrd32 xs = fromIntegral <$> xs

{-# INLINE iToWrdListBase #-}
iToWrdListBase :: Integer -> Word -> [Word]
iToWrdListBase 0 _ = [0]
iToWrdListBase i b = digitsUnsigned b (fromIntegral i) -- digits come in reversed format

{-# INLINE convertBase #-}
convertBase :: Word -> Word -> [Word] -> [Word]
convertBase _ _ [] = []
convertBase from to xs = digitsUnsigned to $ fromIntegral (undigits from xs)

{-# INLINE intgrFrom3DigitsBase32 #-}

-- | Integer from a 3rd place plus a "reversed" tuple of 2 Word32 digits on base
intgrFrom3DigitsBase32 :: Integer -> (Word32, Word32) -> Integer
intgrFrom3DigitsBase32 i (l1, l2) = (i * secndPlaceW32Radix) + intgrFromRvsrdTuple (l1, l2) radixW32

-- | Custom Double Type and its arithmetic
data FloatingX = FloatingX !Double !Int64 deriving (Eq) -- ! for strict data type

-- | Custom double "unboxed" and its arithmetic
data FloatingX# = FloatingX# {signif# :: {-# UNPACK #-} !Double#, expnnt# :: {-# UNPACK #-} !Int64#} deriving (Eq) -- ! for strict data type

{-# INLINE floorX# #-}
floorX# :: FloatingX# -> Int64
floorX# (FloatingX# s# e#) = case fx2Double (FloatingX (D# s#) (I64# e#)) of
  Just d -> floor d
  _ -> error "floorX#: fx2Double resulted in Nothing  " -- fromIntegral $ toLong (D# s#) (fromIntegral e)

{-# INLINE floorX## #-}
floorX## :: FloatingX# -> Word64#
floorX## f@(FloatingX# s# e#) = case floorDouble (D# $ unsafefx2Double## f) of (W64# w#) -> w#

{-# INLINE zero# #-}
zero# :: FloatingX#
zero# = let !(I64# mb#) = minBound :: Int64 in FloatingX# 0.0## mb#

{-# INLINE one# #-}
one# :: FloatingX#
one# = FloatingX# 1.0## 0#Int64

{-# INLINE minValue# #-}
minValue# :: FloatingX#
minValue# = FloatingX# 1.0## 0#Int64

{-# INLINE (!+##) #-}
(!+##) :: FloatingX# -> FloatingX# -> FloatingX#
(!+##) x y = x `add#` y

{-# INLINE (!*##) #-}
(!*##) :: FloatingX# -> FloatingX# -> FloatingX#
(!*##) x y = x `mul#` y

{-# INLINE (!/##) #-}
(!/##) :: FloatingX# -> FloatingX# -> FloatingX#
(!/##) x y = x `unsafeDivide#` y

{-# INLINE (!**+##) #-}
(!**+##) :: FloatingX# -> FloatingX# -> FloatingX#
(!**+##) x y = x `fsqraddFloatingX#` y

{-# INLINE add# #-}
add# :: FloatingX# -> FloatingX# -> FloatingX#
add# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#)
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

{-# INLINE mul# #-}
mul# :: FloatingX# -> FloatingX# -> FloatingX#
-- mul# (FloatingX# 1.0## 0#) b = b
-- mul# a (FloatingX# 1.00## 0.00##) = a
mul# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#) =
  -- \| isTrue# (sA# ==## 0.00##) = zero#
  -- \| isTrue# (sB# ==## 0.00##) = zero#
  -- \| isTrue# (sA# ==## 1.00##) && isTrue# (expA# `eqInt64#` 0#Int64) = b
  -- \| isTrue# (sB# ==## 1.00##) && isTrue# (expB# `eqInt64#` 0#Int64) = a
  -- \| otherwise
  let !resExp# = expA# `plusInt64#` expB#
      !resSignif# = sA# *## sB#
   in if isTrue# (resSignif# >=## 2.0##)
        then FloatingX# (resSignif# *## 0.5##) (resExp# `plusInt64#` 1#Int64)
        else FloatingX# resSignif# resExp#

{-# INLINE sqr# #-}
sqr# :: FloatingX# -> FloatingX#
sqr# a@(FloatingX# sA# expA#)
  | isTrue# (sA# ==## 0.00##) = zero#
  | isTrue# (sA# ==## 1.00##) && isTrue# (expA# `eqInt64#` 0#Int64) = a
  | otherwise =
      let !resExp# = expA# `plusInt64#` expA#
          !resSignif# = sA# *## sA#
       in if isTrue# (resSignif# >=## 2.0##)
            then FloatingX# (resSignif# *## 0.5##) (resExp# `plusInt64#` 1#Int64)
            else FloatingX# resSignif# resExp#

{-# INLINE divide# #-}
divide# :: FloatingX# -> FloatingX# -> FloatingX#
divide# n@(FloatingX# s1# e1#) d@(FloatingX# s2# e2#)
  | d == FloatingX# 1.0## (fromInt64 0) = n
  | isTrue# (s1# ==## 0.0##) = zero#
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
            then zero#
            else FloatingX# finalSignif# finalExp#

{-# INLINE unsafeDivide# #-}
unsafeDivide# :: FloatingX# -> FloatingX# -> FloatingX#
unsafeDivide# n@(FloatingX# s1# e1#) d@(FloatingX# s2# e2#) =
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
      if isTrue# (resSignif# <## 1.0##) && isTrue# (resExp# `leInt64#` 0#Int64)
        then zero#
        else FloatingX# finalSignif# finalExp#

{-# INLINE fsqraddFloatingX# #-}
fsqraddFloatingX# :: FloatingX# -> FloatingX# -> FloatingX#
fsqraddFloatingX# (FloatingX# sA# expA#) (FloatingX# sC# expC#)
  | isTrue# (diff# `eqInt64#` 0#Int64) = FloatingX# (fmaddDouble# sA# sA# sC#) expC#
  | otherwise = case updateDouble# sC# (int64ToInt# diff#) of sC_# -> FloatingX# (fmaddDouble# sA# sA# sC_#) twoTimesExpA# -- let !sC_# = updateDouble# sC# (int64ToInt# diff#) in FloatingX# (fmaddDouble# sA# sA# sC_#) twoTimesExpA#
  where
    !twoTimesExpA# = 2#Int64 `timesInt64#` expA# 
    !diff# = expC# `subInt64#` twoTimesExpA#

{-# INLINE fm1addFloatingX# #-}
fm1addFloatingX# :: FloatingX# -> FloatingX# -> FloatingX#
fm1addFloatingX# a@(FloatingX# sA# expA#) c@(FloatingX# sC# expC#)
  | isTrue# (cExcessa# `geInt64#` 0#Int64) = FloatingX# (fmaddDouble# sA# 1.00## sC#) cExcessa#
  | otherwise = a !*## one# !+## c -- default custom mult and add
  where
    !cExcessa# = expC# `subInt64#` expA#

{-# INLINE sqrtFX# #-}
sqrtFX# :: FloatingX# -> FloatingX#
sqrtFX# fx@(FloatingX# s# e#) = case sqrtSplitDbl# fx of (# sX#, eX# #) -> FloatingX# sX# eX# -- let !(D# sX#, I64# eX#) = sqrtSplitDbl (FloatingX (D# s#) (I64# e#)) in FloatingX# sX# eX#

-- | actual sqrt call to the hardware for custom type happens here
sqrtSplitDbl :: FloatingX -> (Double, Int64)
sqrtSplitDbl (FloatingX d e) -- //FIXME FOR zero case
  | even e = (sqrt d, shiftR e 1) -- even
  | otherwise = (sqrtOf2 * sqrt d, shiftR (e - 1) 1) -- odd
{-# INLINE sqrtSplitDbl #-}

-- -- | actual sqrt call to the hardware for custom type happens here
-- sqrtSplitDbl# :: FloatingX# -> (# Double#, Int64# #)
-- sqrtSplitDbl# (FloatingX# d# e#)
--   | isTrue# (d# ==## 0.00##) = case minBound :: Int64 of I64# mb# -> (# 0.0##, mb# #)
--   | even (I64# e#) = (# sqrtDouble# d#, e# `quotInt64#` 2#Int64 #) -- even
--   | otherwise = (# 1.4142135623730950488016887242097## *## sqrtDouble# d#, (e# `subInt64#` 1#Int64) `quotInt64#` 2#Int64 #) -- odd sqrt2 times sqrt d#
--   -- | otherwise = (# sqrtDouble# 2.00## *## d#, (e# `subInt64#` 1#Int64) `quotInt64#` 2#Int64 #) -- odd sqrt2 times sqrt d#
-- {-# INLINE sqrtSplitDbl# #-}

-- | actual sqrt call to the hardware for custom type happens here
sqrtSplitDbl# :: FloatingX# -> (# Double#, Int64# #)
sqrtSplitDbl# (FloatingX# d# e#)
  -- | isTrue# (d# ==## 0.00##) = case minBound :: Int64 of I64# mb# -> (# 0.0##, mb# #)
  | yesEven = (# sqrtDouble# d#, quo64# #) -- even
  | otherwise = (# sqrtDouble# 2.00## *## d#, quo64# #) -- odd sqrt2 times sqrt d#
 where 
  !(# yesEven, quo64# #) = _evenInt64# e#
{-# INLINE sqrtSplitDbl# #-}

_even, _odd       :: (Integral a) => a -> (Bool, a)
_even n          =  let !(q,r) = n `quotRem` 2 in (r == 0, q) 
_odd             =  _even
{-# INLINE _even  #-}
{-# INLINE _odd  #-}

_evenInt64#, _oddInt64#       :: Int64# -> (# Bool, Int64# #)
_evenInt64# n#         =   (# isTrue# (remInt64# n# 2#Int64 `eqInt64#` 0#Int64), n# `quotInt64#` 2#Int64 #) 
_oddInt64#             =  _evenInt64#
{-# INLINE _evenInt64#  #-}
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

toInt64 :: Int64# -> Int64
toInt64 = I64#
{-# INLINE toInt64 #-}

fromInt64 :: Int64 -> Int64#
fromInt64 (I64# x#) = x#
{-# INLINE fromInt64 #-}

fx2Double# :: FloatingX# -> Maybe Double
fx2Double# x@(FloatingX# s# e#) = fx2Double $ FloatingX (D# s#) (I64# e#) -- fromIntegral (I# $ int64ToInt# e#) in fx2Double $ FloatingX (D# s#) ei64
{-# INLINE fx2Double# #-}

unsafefx2Double# :: FloatingX# -> Double
unsafefx2Double# x@(FloatingX# s# e#) = unsafefx2Double $ FloatingX (D# s#) (I64# e#) -- fromIntegral (I# $ int64ToInt# e#) in fx2Double $ FloatingX (D# s#) ei64
{-# INLINE unsafefx2Double# #-}

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

{-# INLINE updateDouble# #-}
updateDouble# :: Double# -> Int# -> Double#
updateDouble# d# ex# = case decodeDoubleInteger d# of (# m, n# #) -> encodeDoubleInteger m (n# +# ex#)

unsafefx2Double :: FloatingX -> Double
unsafefx2Double (FloatingX d@(D# d#) e) =
  -- \| ex < 0 = fromIntegral m `divideDouble` (2 ^ (-ex)) -- this is necessary
  -- \| otherwise
  D# (encodeDoubleInteger m ex#)
  where
    !(# m, n# #) = decodeDoubleInteger d#
    !ex@(I# ex#) = I# n# + fromIntegral e
{-# INLINE unsafefx2Double #-}

unsafefx2Double## :: FloatingX# -> Double#
unsafefx2Double## (FloatingX# d# e#) =
  -- \| isTrue# (ex# <# 0#) = case fromIntegral m `divideDouble` (2 ^ (-(I# ex#))) of (D# do#) -> do# -- this is necessary
  -- \| otherwise
  encodeDoubleInteger m ex#
  where
    !(# m, n# #) = decodeDoubleInteger d#
    !ex# = n# +# int64ToInt# e#
{-# INLINE unsafefx2Double## #-}

{-# INLINE double2FloatingX# #-}
double2FloatingX# :: Double -> FloatingX#
double2FloatingX# d = case split d of (D# s#, I64# e#) -> FloatingX# s# e# -- let !(D# s#, I64# e#) = split d in FloatingX# s# e#

{-# INLINE double2FloatingX## #-}
double2FloatingX## :: Double# -> FloatingX#
double2FloatingX## d# = case split# d# of (# s#, e# #) -> FloatingX# s# e#

{-# INLINE bigNat2FloatingX## #-}
bigNat2FloatingX## :: BigNat# -> FloatingX#
bigNat2FloatingX## ibn#
  | bigNatIsZero ibn# = zero#
  -- \| itsOKtoUsePlainDoubleCalc = double2FloatingX## iDouble#
  | otherwise = case cI2D2_ ibn# of (# s#, e_# #) -> FloatingX# s# e_# -- cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble
  -- where
  --   !(D# maxDouble#) = maxDouble
  --   !iDouble# =  bigNatEncodeDouble# ibn# 0#
  --   !itsOKtoUsePlainDoubleCalc = isTrue# (iDouble# <## (fudgeFactor## *## maxDouble#)) where fudgeFactor## = 1.00## -- for safety it has to land within maxDouble (1.7*10^308) i.e. tC ^ 2 + tA <= maxSafeInteger

{-# INLINE unsafebigNat2FloatingX## #-}
unsafebigNat2FloatingX## :: BigNat# -> FloatingX#
unsafebigNat2FloatingX## ibn# = case cI2D2_ ibn# of (# s#, e_# #) -> FloatingX# s# e_# -- let !(# s#, e_# #) = cI2D2_ ibn# in FloatingX# s# e_# --cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble

{-# INLINE int64ToFloatingX# #-}
int64ToFloatingX# :: Int64 -> FloatingX#
int64ToFloatingX# i
  | i == 0 = zero#
  | i < 0 = error "int64ToFloatingX# : invalid negative argument"
  | otherwise = double2FloatingX# (fromIntegral i)

{-# INLINE unsafeword64ToFloatingX# #-}
unsafeword64ToFloatingX# :: Word64 -> FloatingX#
unsafeword64ToFloatingX# i = double2FloatingX# (fromIntegral i)

{-# INLINE unsafeword64ToFloatingX## #-}
unsafeword64ToFloatingX## :: Word64# -> FloatingX#
unsafeword64ToFloatingX## w# = case W64# w# of i -> unsafeword64ToFloatingX# i

-- The maximum integral value that can be unambiguously represented as a
-- Double. Equal to 9,007,199,254,740,991 = maxsafeinteger
{-# INLINE cI2D2_ #-}
cI2D2_ :: BigNat# -> (# Double#, Int64# #)
cI2D2_ bn#
  | isTrue# (bnsz# <# thresh#) = (# bigNatEncodeDouble# bn# 0#, 0#Int64 #)
  | otherwise = case bigNatLog2# bn# of
  -- | otherwise = case _bigNatLog2# bn# bnsz# of
      l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
        h# -> let !shift# = (2## `timesWord#` h#) in case bigNatShiftR# bn# shift# of
          mbn# -> (# bigNatEncodeDouble# mbn# 0#, intToInt64# (word2Int# shift#) #) 
  where
    !bnsz# = bigNatSize# bn# 
    thresh# :: Int#
    !thresh# = 9# -- if finiteBitSize (0 :: Word) == 64 then 9# else 14# -- aligned to the other similar usage and it workd

-- | Base 2 logarithm a bit faster
_bigNatLog2# :: BigNat# -> Int# -> Word#
_bigNatLog2# a s -- s = bigNatSize# a 
   | bigNatIsZero a = 0##
   | otherwise           =
      -- let i = int2Word# (bigNatSize# a) `minusWord#` 1##
      let i = int2Word# s `minusWord#` 1##
      in int2Word# (wordLog2# (bigNatIndex# a (word2Int# i))) `plusWord#` (i `uncheckedShiftL#` 6#) --WORD_SIZE_BITS_SHIFT#)

{-# INLINE split #-}
split :: Double -> (Double, Int64)
split (D# d#) = case split# d# of (# s#, ex# #) -> (D# s#, I64# ex#) -- let !(# s#, ex# #) = split# d# in (D# s#, I64# ex#)

{-# INLINE split# #-}
split# :: Double# -> (# Double#, Int64# #)
split# d# =
  let !(# s, expInt# #) = decodeDoubleInteger d#
      !(D# s#) = fromIntegral s
      !ex# = intToInt64# expInt#
   in (# s#, ex# #)

-- | Some Constants
radixW32 :: (Integral a) => a
radixW32 = 4294967296 -- 2 ^ finiteBitSize (0 :: Word32)
{-# INLINE radixW32 #-}

predRadixW32 :: (Integral a) => a
predRadixW32 = 4294967295 -- 2 ^ finiteBitSize (0 :: Word32) -1

secndPlaceW32Radix :: Integer
secndPlaceW32Radix = 18446744073709551616 -- radixW32 * radixW32
{-# INLINE secndPlaceW32Radix #-}

radixW32Squared :: Integer
radixW32Squared = 18446744073709551616 -- secndPlaceRadix

radixW32Cubed :: Integer
radixW32Cubed = 79228162514264337593543950336 -- secndPlaceRadix * radixW32

sqrtOf2 :: Double
sqrtOf2 = 1.4142135623730950488016887242097
{-# INLINE sqrtOf2 #-}

maxDouble :: Double
maxDouble = 1.7976931348623157e308

minDouble :: Double
minDouble = 4.9406564584124654e-324 -- Minimum positive normalized value for Double as per IEEE 754

doublePrecisionBinary :: Int
doublePrecisionBinary = 53

doublePrecisionDecimal :: Int
doublePrecisionDecimal = 308

doublePrecisionRadix32 :: Int
doublePrecisionRadix32 = 32

maxSafeInteger :: Integer
maxSafeInteger = 9007199254740991 -- 2^53 -1 this is the max integer that can be represented without losing precision

-- This is approximately 1.8 x 10^308 representable as Double but will lose precision
maxUnsafeInteger :: Integer
maxUnsafeInteger = 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368

-- https://stackoverflow.com/questions/1848700/biggest-integer-that-can-be-stored-in-a-double

-- | Floating Point nextUp/nextDown funxctions
{-# INLINE nextUp# #-}
nextUp# :: Double# -> Double#
nextUp# dIn# = case nextUp (D# dIn#) of (D# dOut#) -> dOut# -- let !(D# dOut#) = nextUp (D# dIn#) in dOut#

{-# INLINE nextDown# #-}
nextDown# :: Double# -> Double#
nextDown# dIn# = case nextDown (D# dIn#) of (D# dOut#) -> dOut# -- let !(D# dOut#) = nextDown (D# dIn#) in dOut#

{-# INLINE nextUpFX# #-}
nextUpFX# :: FloatingX# -> FloatingX#
nextUpFX# (FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) = minValue#
  | otherwise = case nextUp# s# of interimS# -> if isTrue# (interimS# >=## 2.0##) then FloatingX# (interimS# /## 2.00##) (e# `plusInt64#` 1#Int64) else FloatingX# interimS# e#

{-# INLINE nextDownFX# #-}
nextDownFX# :: FloatingX# -> FloatingX#
nextDownFX# x@(FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) || x == minValue# = zero#
  | otherwise = case nextDown# s# of interimS# -> if isTrue# (interimS# <## 1.0##) then FloatingX# (interimS# *## 2.00##) (e# `subInt64#` 1#Int64) else FloatingX# interimS# e#

--- *********************
-- -- Integer square root with remainder, using the Karatsuba Square Root
-- -- algorithm from
-- -- Paul Zimmermann. Karatsuba Square Root. [Research Report] RR-3805, 1999,
-- -- pp.8. <inria-00072854>

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

double :: Integer -> Integer
double x = x `unsafeShiftL` 1
{-# INLINE double #-}

-- | Return an integer, built from given digits in reverse order.
--   Condition 0 ≤ digit < base is not checked.
undigits_ ::
  (Integral a, Integral b) =>
  -- | The base to use
  a ->
  -- | The list of digits to convert
  [b] ->
  Integer
undigits_ = undigits
{-# INLINE undigits_ #-}
{-# SPECIALIZE undigits_ :: Word -> [Word] -> Integer #-}
{-# SPECIALIZE undigits_ :: Int -> [Int] -> Integer #-}
{-# SPECIALIZE undigits_ :: Int64 -> [Int64] -> Integer #-}
{-# SPECIALIZE undigits_ :: Word64 -> [Word64] -> Integer #-}
{-# SPECIALIZE undigits_ :: Integer -> [Integer] -> Integer #-}
{-# SPECIALIZE undigits_ :: Integer -> [Integer] -> Integer #-}
