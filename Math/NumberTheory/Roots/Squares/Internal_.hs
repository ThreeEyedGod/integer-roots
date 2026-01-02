{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}

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

import Data.Bits (unsafeShiftL, unsafeShiftR, (.&.), (.|.))
import GHC.Exts
  ( Int (..),
    word2Int#,
  )
import GHC.Num.Integer (integerFromNatural, integerLog2#)
import Math.NumberTheory.Roots.Squares.InternalBank_
import Math.NumberTheory.Utils.ArthMtic_

-- | Square root using Fabio Romano's Faster Bombelli method.

--- https ://arxiv.org/abs/2406.07751
--- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

{-# SPECIALIZE isqrtB_ :: Integer -> Integer #-}
isqrtB_ :: (Integral a) => a -> a
isqrtB_ 0 = 0
isqrtB_ n = fromInteger . integerFromNatural . newappsqrt_ . fromIntegral $ n
{-# DUMMY isqrtB_ #-}


-- //FIXME pickup karatsuba from package poly? (dense.hs)
karatsubaSqrt :: Integer -> (Integer, Integer)
karatsubaSqrt 0 = (0, 0)
karatsubaSqrt n
  | lgN < 513 = -- lgN < 2300 =
      let s = isqrtB_ n in (s, n - s * s)
  | otherwise =
      if lgN .&. 2 /= 0 -- //FIXME check if logic needs to be updated
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
