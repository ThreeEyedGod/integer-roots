{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OrPatterns #-}
-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump-simpl or ddump-asm -ddump-to-file dumps else not
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
    inline, 
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
import Math.NumberTheory.Roots.Squares.InternalBank_ 
import Math.NumberTheory.Utils.ArthMtic_ 
import Math.NumberTheory.Utils.FloatingX_ 
-- *********** END NEW IMPORTS

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

{-# SPECIALIZE isqrtB :: Integer -> Integer #-}
isqrtB :: (Integral a) => a -> a
isqrtB 0 = 0
-- isqrtB n = fromInteger . theNextIterationsUVIrvrsd . theFirstUV . stageUVrvrsd . dgtsLstBase32 . fromIntegral $ n
-- isqrtB n = fromInteger . theNextIterationsUVI . theFirstUV . stageUV .dgtsLstBase32 . fromIntegral $ n
-- isqrtB n = fromInteger . theNextIterations . theFirstXs . stageList . dgtsLstBase32 . fromIntegral $ n
isqrtB n = fromInteger . theNextIterationsRvrsdSLCode . theFirstXs . stageListRvrsd . dgtsLstBase32 . fromIntegral $ n
{-# INLINEABLE isqrtB #-}

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
