{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
-- addition
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
-- addition
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump=simpl or ddump-asm dumps else not
{-# OPTIONS_GHC -O2 -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fstrictness -funbox-small-strict-fields -funfolding-use-threshold=80 -fmax-worker-args=32 #-}
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
  (   karatsubaSqrt
    , isqrtB
  )
where

import Data.Bits (finiteBitSize, unsafeShiftL, unsafeShiftR, (.&.), (.|.))

-- *********** BEGIN NEW IMPORTS
import Data.WideWord
import GHC.Int      (Int64(I64#))
import GHC.Word ( Word64(..), Word32(..))
#ifdef MIN_VERSION_integer_gmp
import GHC.Exts (uncheckedIShiftRA#, (*#), (-#))
import GHC.Integer.GMP.Internals (Integer(..), shiftLInteger, shiftRInteger, sizeofBigNat#)
import GHC.Integer.Logarithms (integerLog2#)
#define IS S#
#define IP Jp#
#define bigNatSize sizeofBigNat
#else
import GHC.Exts (uncheckedShiftRL#, word2Int#, minusWord#, timesWord#,fmaddDouble#, Int64#, Word64#, Word32#)
import GHC.Num.BigNat (bigNatSize#)
#endif

import Data.Bits (shiftR)
import qualified Data.Bits.Floating as DB (nextDown, nextUp)
import Data.FastDigits (digitsUnsigned, undigits)
import qualified Data.Vector.Unboxed as VU (Vector, unsafeIndex, unsafeHead, null, uncons, fromList, singleton, unsafeDrop, length)
import Data.Word (Word32)
import GHC.Exts
  ( Double (..),
    Double#,
    Int (..),
    Int#,
    Int64#,
    double2Int#,
    gtInt64#,
    geInt64#, 
    int2Double#,
    int64ToInt#,
    intToInt64#,
    timesInt64#,
    eqInt64#,
    eqWord64#, 
    gtWord64#,
    subWord64#,
    timesWord64#, 
    word64ToInt64#,
    word32ToWord#,
    wordToWord64#,
    isTrue#,
    leInt64#,
    ltInt64#,
    minusWord#,
    plusInt64#,
    plusWord64#,
    subWord64#, 
    sqrtDouble#,
    subInt64#,
    timesWord#,
    uncheckedIShiftRA#,
    uncheckedShiftRL#,
    word2Int#,
    (*##),
    (**##),
    (+#),
    (+##),
    (-#),
    (/##),
    (<#),
    (<##),
    (==##),
    (>=##),
    quotInt64#,
    indexDoubleArray#
  )
import GHC.Float ( divideDouble, floorDouble)
import GHC.Integer (decodeDoubleInteger, encodeDoubleInteger)
import GHC.Num.Integer
  ( Integer (..),
    integerDecodeDouble#,
    integerEncodeDouble,
    integerFromInt,
    integerFromInt#,
    integerFromInt64#,
    integerFromWordList,
    integerLog2#,
    integerLogBase,
    integerLogBase#,
    integerQuotRem,
    integerShiftL#,
    integerShiftR#,
    integerToInt,
  )

-- *********** END NEW IMPORTS


-- BEGIN isqrtB ****************************************************************

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

{-# SPECIALIZE isqrtB :: Integer -> Integer #-}
isqrtB :: (Integral a) => a -> a
isqrtB 0 = 0
isqrtB n = fromInteger . theNextIterations . theFi . dgtsVecBase32__ . fromIntegral $ n
{-# INLINEABLE isqrtB #-}

-- | Iteration loop data - these records have vectors / lists in them
data Itr = Itr {lv# :: {-# UNPACK #-} !Int#, vecW32_ :: {-# UNPACK #-} !(VU.Vector Word32), l_ :: {-# UNPACK #-} !Int#, yCumulative :: !Integer, iRem_ :: {-# UNPACK #-} !Integer, tb# :: {-# UNPACK #-} !FloatingX#} deriving (Eq)

theFi :: VU.Vector Word32 -> Itr 
theFi v 
    | VU.null v = error "theFI: Invalid Argument null vector "
    | VU.length v == 1 && VU.unsafeHead v == 0 = Itr 1# v 0# 0 0 zero#
    | evenLen = let 
             l'# = l# -# 2#
             !(# !yc, !y1#, !remInteger #) = let 
                  yT64# = hndlOvflwW32# (largestNSqLTEEven## i#)                                     
                  ysq# = yT64# `timesWord64#` yT64#
                  diff# = word64ToInt64# i# `subInt64#` word64ToInt64# ysq#
                in handleRems (# 0, yT64#, fromIntegral (I64# diff#) #) -- set 0 for starting cumulative yc--fstDgtRem i
          in Itr 1# v l'# yc remInteger (unsafeword64ToFloatingX## y1#) 
    | otherwise = let 
             l'# = l# -# 1#
             yT64# = largestNSqLTEOdd## i# 
             y = W64# yT64#
             !remInteger = fromIntegral $ W64# (i# `subWord64#` (yT64# `timesWord64#` yT64#)) -- no chance this will be negative
          in Itr 1# v l'# (fromIntegral y) remInteger (unsafeword64ToFloatingX## yT64#) 
 where 
      !l@(I# l#) = VU.length v 
      !evenLen = even l 
      !dxsVec' = if evenLen then brkVec v (l-2) else brkVec v (l-1) -- //FIXME could be made with indexing like in tni
      i# = word64FromRvsrd2ElemVec# dxsVec'

-- Keep it this way: Inlining this lowers performance.
theNextIterations :: Itr -> Integer
theNextIterations itr@(Itr !currlen# !w32Vec !l# !yCumulated !iRem !tbfx#) = tni currlen# w32Vec l# yCumulated iRem tbfx#
  where
    tni :: Int# -> VU.Vector Word32 -> Int# -> Integer -> Integer -> FloatingX# -> Integer 
    tni cl# v l_# yC iR t# =
      if I# l_# == 0 || VU.null v
        then yC
        else
          let 
              !(n1_, nl_) = (VU.unsafeIndex v (I# l_# - 2), VU.unsafeIndex v (I# l_# - 1))
              !tA_= intgrFrom3DigitsBase32 iR (n1_, nl_) 
              !tC_= scaleByPower2 (fromInt64 32) t# -- sqrtF previous digits being scaled right here
              !(# !yc, !yTildeFinal#, !remFinal #) = let !yTilde_# = nxtDgt_# tA_ tC_ in computeRem_ yC tA_ yTilde_#
              !tcfx# = if isTrue# (currlen# <# 2#) && isTrue# (yTildeFinal# `gtWord64#` 0#Word64) then nextDownFX# $ tC_ !+## unsafeword64ToFloatingX# (W64# yTildeFinal#) else tC_ -- recall tcfx is already scaled by 32. Do not use normalize here
           in tni (cl# +# 1#) v (l_# -# 2#) yc remFinal tcfx# -- do not VU.force ri32V
-- | Early termination of tcfx# if more than the 3rd digit or if digit is 0 

-- | numeric loop records

-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgt_# :: Integer -> FloatingX# -> Word64#
nxtDgt_# (IN _) !_ = error "nxtDgt_ :: Invalid negative integer argument"
nxtDgt_# 0 !_ = 0#Word64
nxtDgt_# (IS ta#) tcfx# = let 
            c# = unsafefx2Double## tcfx# --fromMaybe 0 (fx2Double# tCFX#) 
            a# = int2Double# ta#
            !r# = fmaddDouble# c# c# a#
          in 
            computDouble# a# c# r#
nxtDgt_# ta@(IP bn#) tcfx#
    | isTrue# ((bigNatSize# bn#) <# thresh#) = let 
            c# = unsafefx2Double## tcfx# --fromMaybe 0 (fx2Double# tCFX#) 
            !(D# a#) = fromIntegral ta :: Double 
            !r# = fmaddDouble# c# c# a#
          in 
            computDouble# a# c# r#
    | otherwise = comput_ (preComput_ ta tcfx#)--nxtDgt__# ta tcfx#
    where
        -- threshold for shifting vs. direct fromInteger
        -- we shift when we expect more than 256 bits
        thresh# :: Int#
        thresh# = if finiteBitSize (0 :: Word) == 64 then 9# else 14#

{-# INLINE computDouble# #-}
computDouble# :: Double# -> Double# -> Double# -> Word64#
computDouble# !tAFX# !tCFX# !radFX# = let !(W64# i#) = floorDouble (D# (nextUp# (nextUp# tAFX# /## nextDown# (sqrtDouble# (nextDown# radFX#) +## nextDown# tCFX#)))) in hndlOvflwW32# i#
-- computDouble# !tAFX# !tCFX# !radFX# = let !(I64# i#) = floorDouble (D# (nextUp# (nextUp# tAFX# /## nextDown# (fmaddDouble# (sqrtDouble# (nextDown# radFX#)) 1.00## (nextDown# tCFX#)) ))) in hndlOvflwW32# i#

preComput_ :: Integer -> FloatingX# -> (# FloatingX#, FloatingX#, FloatingX# #)
preComput_ tA__ tCFX# =
  let !tAFX# = unsafeinteger2FloatingX# tA__ 
      !radFX# = tCFX# !**+## tAFX# -- fused square (multiply) and add 
   in (# tAFX#, tCFX#, radFX# #)
{-# INLINE preComput_ #-}

comput_ :: (# FloatingX#, FloatingX#, FloatingX# #)-> Word64#
comput_ (# !tAFX#, !tCFX#, !radFX# #) = hndlOvflwW32# (floorX## (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE comput_ #-}

-- | compute the remainder. It may be that the trial "digit" may need to be reworked
-- that happens in handleRems_
-- if the trial digit is zero skip computing remainder
computeRem_ :: Integer -> Integer -> Word64# -> (# Integer, Word64#, Integer #)
computeRem_ tc ta yTilde_# = let !rTrial = calcRemainder ta tc yTilde_# in handleRems (# tc, yTilde_#, rTrial #)
{-# INLINE computeRem_ #-}

handleRems :: (# Integer, Word64#, Integer #) -> (# Integer, Word64#, Integer #)
handleRems (# yc_, yi64#, ri_ #)
  | ri_ < 0 = let 
                !yAdj# = yi64# `subWord64#` 1#Word64 
                !adjYc = pred ycyi
                !rdr = fixRemainder adjYc ri_ in (# adjYc, yAdj#, rdr #) -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | otherwise = (# ycyi, yi64#, ri_ #)
  where
    !yc = yc_ * radixW32
    !ycyi = yc + fromIntegral (W64# yi64#) -- accumulating the growing square root
{-# INLINE handleRems #-}

-- Calculate remainder accompanying a 'digit'
calcRemainder :: Integer -> Integer -> Word64# -> Integer
calcRemainder tAI !_ 0#Word64 = tAI
calcRemainder tAI tc_ dgt64# = let 
        !i = fromIntegral (W64# dgt64#) 
        !tc = tc_ * radixW32
    in tAI - i * (double tc + i) --tAI - ((double i * tc) + i * i)
{-# INLINE calcRemainder #-}

-- Fix remainder accompanying a 'next downed digit'
fixRemainder :: Integer -> Integer -> Integer
fixRemainder tcplusdgtadj rdr = rdr + double tcplusdgtadj + 1
{-# INLINE fixRemainder #-}

-- | HELPER functions
{-# INLINE dgtsVecBase32__ #-}
dgtsVecBase32__ :: Integer -> VU.Vector Word32
dgtsVecBase32__ n | n < 0 = error "dgtsVecBase32_: Invalid negative argument"
dgtsVecBase32__ 0 = VU.singleton 0
dgtsVecBase32__ n = mkIW32Vec n radixW32

{-# INLINE brkVec #-}
brkVec :: VU.Vector Word32 -> Int -> VU.Vector Word32
brkVec v loc = VU.unsafeDrop loc v

{-# INLINE mkIW32Vec #-}

-- | Spit out the unboxed Vector as-is from digitsUnsigned which comes in reversed format.
mkIW32Vec :: Integer -> Word -> VU.Vector Word32
mkIW32Vec 0 _ = VU.singleton 0 -- safety
mkIW32Vec i b = VU.fromList $ mkIW32Lst i b

{-# INLINE intgrFromRvsrd2ElemVec #-}

-- | Integer from a "reversed" Vector of Word32 digits
intgrFromRvsrd2ElemVec :: VU.Vector Word32 -> Integer
intgrFromRvsrd2ElemVec v2ElemW32s =
  let (llsb, lmsb) = case VU.uncons v2ElemW32s of
        Just (u, v) -> if VU.null v then (u, 0) else (u, VU.unsafeHead v)
        Nothing -> error "intgrFromRvsrd2ElemVec : Invalid Vector - empty " 
   in intgrFromRvsrdTuple (llsb, lmsb) radixW32

{-# INLINE word64FromRvsrd2ElemVec #-}

-- | Word64 from a "reversed" Vector of 2 Word32 digits
word64FromRvsrd2ElemVec :: VU.Vector Word32 -> Word64
word64FromRvsrd2ElemVec v2ElemW32s =
  let (llsb, lmsb) = case VU.uncons v2ElemW32s of
        Just (u, v) -> if VU.null v then (u, 0) else (u, VU.unsafeHead v)
        Nothing -> error "int64FromRvsrd2ElemVec : Invalid Vector - empty " 
   in word64FromRvsrdTuple (llsb, lmsb) radixW32

-- | Word64# from a "reversed" Vector of 2 Word32 digits
word64FromRvsrd2ElemVec# :: VU.Vector Word32 -> Word64#
word64FromRvsrd2ElemVec# v2ElemW32s =
  let (llsb, lmsb) = case VU.uncons v2ElemW32s of
        Just (u, v) -> if VU.null v then (u, 0) else (u, VU.unsafeHead v)
        Nothing -> error "int64FromRvsrd2ElemVec : Invalid Vector - empty " 
   in word64FromRvsrdTuple# (llsb, lmsb) 4294967296#Word64

{-# INLINE mkIW32Lst #-}

-- | Spit out the Word32 List from digitsUnsigned which comes in reversed format.
mkIW32Lst :: Integer -> Word -> [Word32]
mkIW32Lst 0 _ = [0] -- safety
mkIW32Lst i b = wrd2wrd32 (iToWrdListBase i b)

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
word64FromRvsrdTuple# (W32# lLSB#, 0) _ =  wordToWord64# (word32ToWord# lLSB#) 
word64FromRvsrdTuple# (W32# lLSB#, W32# lMSB#) base# = (wordToWord64# (word32ToWord# lMSB#) `timesWord64#` base#) `plusWord64#` wordToWord64# (word32ToWord# lLSB#)

{-# INLINE doubleFromRvsrdTuple #-}

-- | double from a "reversed" tuple of Word32 digits
doubleFromRvsrdTuple :: (Word32, Word32) -> Integer -> Double
doubleFromRvsrdTuple (l1, l2) base = fromIntegral l2 * fromIntegral base + fromIntegral l1

{-# INLINE largestNSqLTEOdd #-}
largestNSqLTEOdd :: Word64 -> Word64
largestNSqLTEOdd i =  floorDouble (sqrt (fromIntegral i) :: Double)

{-# INLINE largestNSqLTEEven #-}
largestNSqLTEEven :: Word64 -> Word64
largestNSqLTEEven i = let d_ = nextUp (fromIntegral i :: Double) in floorDouble (nextUp (sqrt d_)) 

{-# INLINE largestNSqLTEOdd## #-}
largestNSqLTEOdd## :: Word64# -> Word64#
largestNSqLTEOdd## w# =  let !(W64# r#) = floorDouble (sqrt (fromIntegral (W64# w#)) :: Double) in r#

{-# INLINE largestNSqLTEEven## #-}
largestNSqLTEEven## :: Word64# -> Word64#
largestNSqLTEEven## w# = let 
        d_ = nextUp (fromIntegral (W64# w#) :: Double) 
        !(W64# r#) = floorDouble (nextUp (sqrt d_)) 
      in r#

-- | handle overflow
{-# INLINE hndlOvflwW32 #-}
hndlOvflwW32 :: Integral a => a  -> a
hndlOvflwW32 i = if i == maxW32 then pred maxW32 else i where maxW32 = radixW32

{-# INLINE hndlOvflwW32# #-}
hndlOvflwW32# :: Word64# -> Word64#
hndlOvflwW32# i# = if isTrue# (i# `eqWord64#` maxW32#) then predmaxW32# else i# 
    where 
      !(W64# maxW32#) = radixW32
      !(W64# predmaxW32#) = predRadixW32

scaleByPower2 :: Int64# -> FloatingX# -> FloatingX#
scaleByPower2 n# (FloatingX# s# e#) = if isTrue# (s# ==## 0.00##) then zero# else FloatingX# s# (e# `plusInt64#` n#)--normalizeFX# $ FloatingX# s# (e# `plusInt64#` n#)
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
floorX## (FloatingX# s# e#) = case fx2Double (FloatingX (D# s#) (I64# e#)) of
        Just d -> let !(W64# d#) = floor d in d# 
        _ -> error "floorX##: fx2Double resulted in Nothing  " -- fromIntegral $ toLong (D# s#) (fromIntegral e)

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
(!/##) x y = x `divide#` y

{-# INLINE (!**+##) #-}
(!**+##) :: FloatingX# -> FloatingX# -> FloatingX#
(!**+##) x y = x `fsqraddFloatingX#` y

{-# INLINE add# #-}
add# :: FloatingX# -> FloatingX# -> FloatingX#
add# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#)
  | a == zero# = b
  | b == zero# = a
  | isTrue# (expA# `gtInt64#` expB#) = combine a b
  | isTrue# (expA# `ltInt64#` expB#) = combine b a
  | otherwise = FloatingX# (sA# +## sB#) expA# -- FloatingX (signifA + signifB) expA
  where
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
mul# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#)
  | isTrue# (sA# ==## 0.00##) = zero#
  | isTrue# (sB# ==## 0.00##) = zero#
  | isTrue# (sA# ==## 1.00##) && isTrue# (expA# `eqInt64#` 0#Int64) = b
  | isTrue# (sB# ==## 1.00##) && isTrue# (expB# `eqInt64#` 0#Int64) = a
  | otherwise =
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

{-# INLINE fsqraddFloatingX# #-}
fsqraddFloatingX# :: FloatingX# -> FloatingX# -> FloatingX#
fsqraddFloatingX# a@(FloatingX# sA# expA#) c@(FloatingX# sC# expC#) 
    | isTrue# (diff# `eqInt64#` 0#Int64) = FloatingX# (fmaddDouble# sA# sA# sC#) expC#
    | otherwise = let sC_# = updateDouble# sC# (int64ToInt# diff#) in FloatingX# (fmaddDouble# sA# sA# sC_#) twoTimesExpA#
    -- | isTrue# (diff# `gtInt64#` 0#Int64) = let sC_# = updateDouble# sC# (int64ToInt# diff#) in FloatingX# (fmaddDouble# sA# sA# sC_#) twoTimesExpA#
    -- | isTrue# (diff# `ltInt64#` 0#Int64) = let sC_# = updateDouble# sC# (int64ToInt# diff#) in FloatingX# (fmaddDouble# sA# sA# sC_#) twoTimesExpA#
    -- | otherwise =  sqr# a !+## c -- default custom mult and add
 where 
    twoTimesExpA# = 2#Int64 `timesInt64#` expA# -- lazy till its needed in otherwise 
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
sqrtFX# (FloatingX# s# e#) =
  let !(D# sX#, I64# eX#) = sqrtSplitDbl (FloatingX (D# s#) (I64# e#))
   in FloatingX# sX# eX#

sqrtSplitDbl :: FloatingX -> (Double, Int64)
sqrtSplitDbl (FloatingX d e)
  | d == 0 = (0, 0)
  | d == 1 = (1, 0)
  | even e = (s, shiftR e 1) -- even
  | otherwise = (sqrtOf2 * s, shiftR (e - 1) 1) -- odd
  where
    -- !s = sqrtDX d
    !s = unsafesqrtDX d
{-# INLINE sqrtSplitDbl #-}

sqrtDX :: Double -> Double
sqrtDX d
  | d == 0 = 0
  | isNaN d = 0
  | isInfinite d = maxDouble
  | d == 1 = 1
  | otherwise = sqrt d -- actual call to "the floating point square root" {sqrt_fsqrt, sqrt, sqrtC, sqrtLibBF, sqrthpmfr or other }
{-# INLINE sqrtDX #-}

unsafesqrtDX :: Double -> Double
unsafesqrtDX d
  | d == 0 = 0
  | d == 1 = 1
  | otherwise = sqrt d -- actual call to "the floating point square root" {sqrt_fsqrt, sqrt, sqrtC, sqrtLibBF, sqrthpmfr or other }
{-# INLINE unsafesqrtDX #-}

toInt64 :: Int64# -> Int64
toInt64 = I64#
{-# INLINE toInt64 #-}

fromInt64 :: Int64 -> Int64#
fromInt64 (I64# x#) = x#
{-# INLINE fromInt64 #-}

fx2Double# :: FloatingX# -> Maybe Double
fx2Double# x@(FloatingX# s# e#) = fx2Double $ FloatingX (D# s#) (I64# e#)--fromIntegral (I# $ int64ToInt# e#) in fx2Double $ FloatingX (D# s#) ei64
{-# INLINE fx2Double# #-}

unsafefx2Double# :: FloatingX# -> Double
unsafefx2Double# x@(FloatingX# s# e#) = unsafefx2Double $ FloatingX (D# s#) (I64# e#)--fromIntegral (I# $ int64ToInt# e#) in fx2Double $ FloatingX (D# s#) ei64
{-# INLINE unsafefx2Double# #-}

fx2Double :: FloatingX -> Maybe Double
fx2Double (FloatingX d@(D# d#) e)
  | isNaN d = Nothing -- error "Input is NaN"
  | isInfinite d = Nothing -- error "Input is Infinity"
  | ex < 0 = Just $ fromIntegral m `divideDouble` (2 ^ (-ex)) -- this is necessary
  | otherwise =
      let 
          !(I# ex#) = ex
          result# = encodeDoubleInteger m ex#
          !result = D# result#
       in if isInfinite result || isNaN result then Nothing else Just result
  where
    !(# m, n# #) = decodeDoubleInteger d#
    !ex = I# n# + fromIntegral e
{-# INLINE fx2Double #-}

{-# INLINE updateDouble# #-}
updateDouble# :: Double# -> Int# -> Double#
updateDouble# d# ex# = let 
    !(# m, n# #) = decodeDoubleInteger d#
    !exUpd# = n# +# ex# 
  in 
    encodeDoubleInteger m exUpd#

unsafefx2Double :: FloatingX -> Double
unsafefx2Double (FloatingX d@(D# d#) e)
  | ex < 0 = fromIntegral m `divideDouble` (2 ^ (-ex)) -- this is necessary
  | otherwise =
      let 
          !(I# ex#) = ex
          result# = encodeDoubleInteger m ex#
          !result = D# result#
       in result
  where
    !(# m, n# #) = decodeDoubleInteger d#
    !ex = I# n# + fromIntegral e
{-# INLINE unsafefx2Double #-}

unsafefx2Double## :: FloatingX# -> Double#
unsafefx2Double## (FloatingX# d# e#)
  | isTrue# (ex# <# 0#) = let !(D# d#) = fromIntegral m `divideDouble` (2 ^ (-(I# ex#))) in d# -- this is necessary
  | otherwise =
      let 
          result# = encodeDoubleInteger m ex#
       in result#
  where
    !(# m, n# #) = decodeDoubleInteger d#
    ex# = n# +# int64ToInt# e#
{-# INLINE unsafefx2Double## #-}

{-# INLINE double2FloatingX# #-}
double2FloatingX# :: Double -> FloatingX#
double2FloatingX# d =
  let !(D# s#, I64# e#) = split d
   in FloatingX# s# e#

{-# INLINE double2FloatingX## #-}
double2FloatingX## :: Double# -> FloatingX#
double2FloatingX## d# =
  case split# d# of
    (# s#, e# #) -> FloatingX# s# e#

{-# INLINE integer2FloatingX# #-}
integer2FloatingX# :: Integer -> FloatingX#
integer2FloatingX# i
  | i == 0 = zero#
  | i < 0 = error "integer2FloatingX# : invalid negative argument"
  | itsOKtoUsePlainDoubleCalc = double2FloatingX# (fromIntegral i)
  | otherwise =
      let !(i_, e_) = cI2D2_ i --cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble
          !(D# s#) = fromIntegral i_
          !(I# e_#) = e_
       in FloatingX# s# (intToInt64# e_#)
  where
    !(D# maxDouble#) = maxDouble
    !(D# iDouble#) = fromIntegral i
    itsOKtoUsePlainDoubleCalc = isTrue# (iDouble# <## (fudgeFactor## *## maxDouble#)) where fudgeFactor## = 1.00## -- for safety it has to land within maxDouble (1.7*10^308) i.e. tC ^ 2 + tA <= maxSafeInteger

{-# INLINE unsafeinteger2FloatingX# #-}
unsafeinteger2FloatingX# :: Integer -> FloatingX#
unsafeinteger2FloatingX# i = 
      let !(i_, e_) = cI2D2_ i --cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble
          !(D# s#) = fromIntegral i_
          !(I# e_#) = e_
       in FloatingX# s# (intToInt64# e_#)

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
unsafeword64ToFloatingX## w# = double2FloatingX# (fromIntegral (W64# w#))

-- The maximum integral value that can be unambiguously represented as a
-- Double. Equal to 9,007,199,254,740,991 = maxsafeinteger
{-# INLINE cI2D2_ #-}
cI2D2_ :: Integer -> (Integer, Int)
cI2D2_ i@(IS i#) = (i, 0)
cI2D2_ n@(IP bn#)
    | isTrue# ((bigNatSize# bn#) <# thresh#) = (n,0)
    | otherwise = case integerLog2# n of
#ifdef MIN_VERSION_integer_gmp
                    l# -> case uncheckedIShiftRA# l# 1# -# 47# of
                            h# -> case shiftRInteger n (2# *# h#) of
                                    m -> (m, I# 2# *# h#)
#else
                    l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
                            h# -> case integerShiftR# n (2## `timesWord#` h#) of
                                    m -> (m, 2 * I# (word2Int# h#))
#endif
    where
        -- threshold for shifting vs. direct fromInteger
        -- we shift when we expect more than 256 bits
        thresh# :: Int#
        thresh# = if finiteBitSize (0 :: Word) == 64 then 9# else 14# -- aligned to the other similar usage and it workd
cI2D2_ _ = error "cI2D2_': negative argument"

{-# INLINE split #-}
split :: Double -> (Double, Int64)
split (D# d#) = let !(# s#, ex# #) = split# d# in (D# s#, I64# ex#)

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

predRadixW32 :: (Integral a) => a
predRadixW32 = 4294967295 -- 2 ^ finiteBitSize (0 :: Word32) -1 

secndPlaceW32Radix :: Integer
secndPlaceW32Radix = 18446744073709551616 -- radixW32 * radixW32

radixW32Squared :: Integer
radixW32Squared = 18446744073709551616 -- secndPlaceRadix

radixW32Cubed :: Integer
radixW32Cubed = 79228162514264337593543950336 -- secndPlaceRadix * radixW32

sqrtOf2 :: Double
sqrtOf2 = 1.4142135623730950488016887242097

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

{-# INLINE nextUp #-}
nextUp :: Double -> Double
nextUp = DB.nextUp -- NFI.nextUp

{-# INLINE nextDown #-}
nextDown :: Double -> Double
nextDown = DB.nextDown -- NFI.nextDown

{-# INLINE nextUp# #-}
nextUp# :: Double# -> Double#
nextUp# dIn# = let !(D# dOut#) = nextUp (D# dIn#) in dOut#

{-# INLINE nextDown# #-}
nextDown# :: Double# -> Double#
nextDown# dIn# = let !(D# dOut#) = nextDown (D# dIn#) in dOut#

{-# INLINE nextUpFX# #-}
nextUpFX# :: FloatingX# -> FloatingX#
nextUpFX# (FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) = minValue#
  | otherwise =
      let !interimS# = nextUp# s#
       in if isTrue# (interimS# >=## 2.0##) then FloatingX# (interimS# /## 2.00##) (e# `plusInt64#` 1#Int64) else FloatingX# interimS# e#

{-# INLINE nextDownFX# #-}
nextDownFX# :: FloatingX# -> FloatingX#
nextDownFX# x@(FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) || x == minValue# = zero#
  | otherwise =
      let !interimS# = nextDown# s#
       in if isTrue# (interimS# <## 1.0##) then FloatingX# (interimS# *## 2.00##) (e# `subInt64#` 1#Int64) else FloatingX# interimS# e#


--- *********************
-- Integer square root with remainder, using the Karatsuba Square Root
-- algorithm from
-- Paul Zimmermann. Karatsuba Square Root. [Research Report] RR-3805, 1999,
-- pp.8. <inria-00072854>

karatsubaSqrt :: Integer -> (Integer, Integer)
karatsubaSqrt 0 = (0, 0)
karatsubaSqrt n
    | lgN < 2300 =
        let s = isqrtB n in (s, n - s * s)
    | otherwise =
        if lgN .&. 2 /= 0 then
            karatsubaStep k (karatsubaSplit k n)
        else
            -- before we split n into 4 part we must ensure that the first part
            -- is at least 2^k/4, since this doesn't happen here we scale n by
            -- multiplying it by 4
            let n' = n `unsafeShiftL` 2
                (s, r) = karatsubaStep k (karatsubaSplit k n')
                r' | s .&. 1 == 0 = r
                   | otherwise = r + double s - 1
            in  (s `unsafeShiftR` 1, r' `unsafeShiftR` 2)
  where
    k = lgN `unsafeShiftR` 2 + 1
#ifdef MIN_VERSION_integer_gmp
    lgN = I# (integerLog2# n)
#else
    lgN = I# (word2Int# (integerLog2# n))
#endif

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