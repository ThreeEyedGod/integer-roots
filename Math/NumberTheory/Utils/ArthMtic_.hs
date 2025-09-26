{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnboxedTuples #-}
-- addition (also note -mfma flag used to add in suppport for hardware fused ops)
-- note that not using llvm results in fsqrt appearing in ddump=simpl or ddump-asm dumps else not
-- removed -fexpose-all-unfoldings may not necessarily help improve max performance. See https://well-typed.com/blog/2024/04/choreographing-specialization-pt1/

{-# OPTIONS_GHC -O2 -threaded -optl-m64  -fllvm -fexcess-precision -mfma -funbox-strict-fields -fspec-constr  -fstrictness -funbox-small-strict-fields -funfolding-use-threshold=16 -fmax-worker-args=32 -optc-O3 -optc-ffast-math #-}
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
module Math.NumberTheory.Utils.ArthMtic_
  ( maxIntSizeAcross,
    _evenInt64#,
    _oddInt64#,
    _even,
    _odd,
    nextDown#,
    nextUp#,
    updateDouble#,
    split,
    split#,
    fromInt64,
    sqrtOf2,
    MaxBounds (..),
    double,
    radixW32,
    safePosAdd256,
    safePosMul256,
    safePosMul64,
    safePosAdd64,
    hndlOvflwW32,
    hndlOvflwW32##,
    hndlOvflwI32##,
    secndPlaceW32Radix,
    mkIW32EvenRestLst,
    splitLastOne,
    splitLastTwo,
    word64FromRvsrd2ElemList#,
    largestNSqLTEEven##,
    largestNSqLTEOdd##,
    dgtsLstBase32,
    maxDouble,
    maxSafeInteger,
    maxUnsafeInteger,
    foldr',
    pred,
    lenRadixW32,
  )
where

-- \*********** BEGIN NEW IMPORTS
import Prelude hiding (pred)
import Control.Parallel.Strategies (NFData, parBuffer, parListChunk, parListSplitAt, rdeepseq, rpar, withStrategy)
-- he says it's coded to be as fast as possible
import Data.Bits (unsafeShiftL)
import Data.Bits.Floating (nextDown, nextUp)
import Data.DoubleWord (Int256, Int96)
import Data.FastDigits (digitsUnsigned, undigits)
import Data.List (unfoldr)
import Data.Maybe (fromMaybe)
import Data.WideWord (Int128, Word256, zeroInt128)
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
import GHC.Float (floorDouble)
import GHC.Int (Int32, Int64 (I64#))
import GHC.Integer (decodeDoubleInteger, encodeDoubleInteger)
import GHC.Num.Integer (integerLogBase#)
import GHC.Num.Integer (integerLogBaseWord)
import GHC.Num.BigNat (BigNat (..), BigNat#, bigNatEncodeDouble#, bigNatIndex#, bigNatIsZero, bigNatLeWord#, bigNatLog2, bigNatLog2#, bigNatShiftR, bigNatShiftR#, bigNatSize#)
import GHC.Word (Word32 (..), Word64 (..))
import Math.NumberTheory.Utils.ShortCircuit_ (firstTrueOf)
import Control.Parallel (par, pseq)
import Numeric.Natural (Natural)

-- *********** END NEW IMPORTS

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
  deriving (Eq, Show, Ord) -- Ord for using maximum later on

maxIntSizeAcross :: Integer -> Integer -> Integer -> MaxBounds
maxIntSizeAcross n1 n2 n3 = maximum (fromMaybe IsIN <$> firstTrueOf <$> lazyXsFits <$> [n1, n2, n3])
{-# INLINE maxIntSizeAcross #-}

lazyXsFits :: Integer -> [Maybe MaxBounds]
lazyXsFits n = [if fitsInMaxInt32 n then Just Is32 else Nothing, if fitsInMaxInt64 n then Just Is64 else Nothing, if fitsInMaxInt96 n then Just Is96 else Nothing, if fitsInMaxInt128 n then Just Is128 else Nothing, if fitsInMaxWord256 n then Just Is256 else Nothing, Just IsIN]
{-# INLINE lazyXsFits #-}

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
   in -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
      if y /= 0 && result `div` y /= x
        then Left (toInteger x * toInteger y)
        else Right result
{-# INLINE safeMul64 #-}

safePosMul64 :: Int64 -> Int64 -> Either Integer Int64
safePosMul64 x y =
  let !result = x * y
   in -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
      if result `div` y /= x
        then Left (toInteger x * toInteger y)
        else Right result
{-# INLINE safePosMul64 #-}

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
   in -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
      if y /= zeroInt128 && result `div` y /= x
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
   in -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
      if y /= 0 && result `div` y /= x
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

-- //todo not working ?
safeAddW256 :: Word256 -> Word256 -> Either Integer Word256
safeAddW256 x y =
  let !result = x + y
   in if (x > 0 && y > 0 && result < 0) || (x < 0 && y < 0 && result > 0)
        then Left (toInteger x + toInteger y)
        else Right result
{-# INLINE safeAddW256 #-}

-- //todo not working ?
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
   in -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
      if y /= 0 && result `div` y /= x
        then Left (toInteger x * toInteger y)
        else Right result
{-# INLINE safeMul256 #-}

safePosMul256 :: Int256 -> Int256 -> Either Integer Int256
safePosMul256 x y =
  let !result = x * y
   in -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
      if result `div` y /= x
        then Left (toInteger x * toInteger y)
        else Right result
{-# INLINE safePosMul256 #-}

-- //todo not working ?
safeMulW256 :: Word256 -> Word256 -> Either Integer Word256
safeMulW256 x y =
  let !result = x * y
   in -- Overflow detection: if y ≠ 0 and result ÷ y ≠ x, overflow occurred
      if y /= 0 && result `div` y /= x
        then Left (toInteger x * toInteger y)
        else Right result
{-# INLINE safeMulW256 #-}

-- | HELPER functions
{-# INLINE [0] dgtsLstBase32 #-}
dgtsLstBase32 :: Integer -> [Word32]
dgtsLstBase32 n = mkIW32Lst n radixW32

-- | Word64# from a "reversed" List of at least 1 and at most 2 Word32 digits
word64FromRvsrd2ElemList# :: [Word32] -> Word64#
word64FromRvsrd2ElemList# [] = error "word64FromRvsrd2ElemList# : null list"
word64FromRvsrd2ElemList# [llsb] = word64FromRvsrdTuple# (llsb, 0) 4294967296#Word64
word64FromRvsrd2ElemList# [llsb, lmsb] = word64FromRvsrdTuple# (llsb, lmsb) 4294967296#Word64
word64FromRvsrd2ElemList# (_ : _ : _) = error "word64FromRvsrd2ElemList# : more than 2 elems list"
{-# INLINE word64FromRvsrd2ElemList# #-}

{-# INLINE mkIW32Lst #-}

-- | Spit out the Word32 List from digitsUnsigned which comes in reversed format.
mkIW32Lst :: Integer -> Word -> [Word32]
mkIW32Lst 0 _ = [0] -- safety
mkIW32Lst i b = wrd2wrd32 (iToWrdListBase i b)

{-# INLINE splitLastTwo #-}
splitLastTwo :: [a] -> Int -> ([a], [a])
splitLastTwo xs l = splitAt (l - 2) xs

{-# INLINE splitLastOne #-}
splitLastOne :: [a] -> Int -> ([a], [a])
splitLastOne xs l = splitAt (l - 1) xs

{-# INLINE pairUp #-}
pairUp :: Bool -> [a] -> [(a, a)]
pairUp True (x : y : rs) = (x, y) : pairUp True rs
pairUp True [] = []
pairUp _ [_] = error "pairUp: Invalid singleton list"
pairUp False _ = error "pairUp: Invalid odd length of list"

{-# INLINE pairUpAcc #-}
pairUpAcc :: [a] -> [(a, a)]
pairUpAcc xs = go xs []
  where
    go (x : y : zs) !acc = go zs ((x, y) : acc)
    go [] acc = reverse acc
    go [_] _ = error "pairUp: odd length"

{-# INLINE pairUpUnfold #-}
pairUpUnfold :: [a] -> [(a, a)]
pairUpUnfold = unfoldr step
  where
    step (x : y : zs) = Just ((x, y), zs)
    step [] = Nothing
    step [_] = error "pairUp: odd length"

{-# INLINE pairUpBuild #-}
pairUpBuild :: [a] -> [(a, a)]
pairUpBuild xs = build (\c n -> go c n xs)
  where
    go c n (x : y : zs) = c (x, y) (go c n zs)
    go _ n [] = n
    go _ _ [_] = error "pairUp: odd length"

-- | trying a bit of parallelization here given that incoming is a small but heavy bunch of word32s list
{-# INLINE [0] integerOfNxtPairsLst #-}
{-# SPECIALIZE integerOfNxtPairsLst :: Int -> [(Word32, Word32)] -> [Word64] #-}
{-# SPECIALIZE integerOfNxtPairsLst :: Int -> [(Word32, Word32)] -> [Integer] #-}
integerOfNxtPairsLst :: (NFData a, Integral a) => Int -> [(Word32, Word32)] -> [a]
integerOfNxtPairsLst l = if l < 8 then map iFrmTupleBaseW32 else parallelMap Split 2 iFrmTupleBaseW32 -- assuming even dual core Split/Buffer work better than Chunk

-- | Strategies that may be used with parallel calls
data Strats
  = Chunk
  | Buffer
  | Split
  deriving (Eq)

-- | parallel map with 3 optional strategies
parallelMap :: (NFData a, NFData b) => Strats -> Int -> (a -> b) -> [a] -> [b]
parallelMap strat stratParm f = case strat of
  Chunk -> withStrategy (parListChunk stratParm rdeepseq) . map f
  Buffer -> withStrategy (parBuffer stratParm rpar) . map f
  Split -> withStrategy (parListSplitAt stratParm rdeepseq rdeepseq) . map f

{-# INLINE [1] iFrmTupleBaseW32 #-}

{-# RULES
"iFrmTupleBaseW32/Integer" iFrmTupleBaseW32 = intgrFromRvsrdTuple
"iFrmTupleBaseW32/Word64" iFrmTupleBaseW32 = word64FromRvsrdTuple
  #-}

iFrmTupleBaseW32 :: (Integral a) => (Word32, Word32) -> a
iFrmTupleBaseW32 tu = integralFromRvsrdTuple tu radixW32

{-# INLINE [0] mkIW32EvenRestLst #-}
{-# SPECIALIZE mkIW32EvenRestLst :: Int -> Bool -> [Word32] -> [Integer] #-}
{-# SPECIALIZE mkIW32EvenRestLst :: Int -> Bool -> [Word32] -> [Word64] #-}
{-# SPECIALIZE mkIW32EvenRestLst :: Int -> Bool -> [Word32] -> [Word] #-}
mkIW32EvenRestLst :: (NFData a, Integral a) => Int -> Bool -> [Word32] -> [a]
mkIW32EvenRestLst len evenLen xs = integerOfNxtPairsLst len (pairUpBuild xs) -- (pairUpUnfold xs) --(pairUpAcc xs) --(pairUp evenLen xs)

--- END helpers
--- BEGIN Core numeric helper functions
--- ***********************************

{-# INLINE [0] integralFromRvsrdTuple #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Integer -> Integer #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Word64 -> Word64 #-}
{-# SPECIALIZE integralFromRvsrdTuple :: (Word32, Word32) -> Word256 -> Word256 #-}

-- | Integer from a "reversed" tuple of Word32 digits
-- Base 4.21 shipped with ghc 9.12.1 had a toInteger improvement : https://github.com/haskell/core-libraries-committee/issues/259
integralFromRvsrdTuple :: (Integral a) => (Word32, Word32) -> a -> a
integralFromRvsrdTuple (0, 0) 0 = 0
integralFromRvsrdTuple (0, lMSB) base = fromIntegral lMSB * base
integralFromRvsrdTuple (lLSB, 0) _ = fromIntegral lLSB
integralFromRvsrdTuple (lLSB, lMSB) base = fromIntegral lMSB * base + fromIntegral lLSB

{-# INLINE intgrFromRvsrdTuple #-}

-- | Integer from a "reversed" tuple of Word32 digits
-- Base 4.21 shipped with ghc 9.12.1 had a toInteger improvement : https://github.com/haskell/core-libraries-committee/issues/259
intgrFromRvsrdTuple :: (Word32, Word32) -> Integer -> Integer
intgrFromRvsrdTuple (0, 0) 0 = 0
intgrFromRvsrdTuple (0, lMSB) base = toInteger lMSB * base
intgrFromRvsrdTuple (lLSB, 0) _ = toInteger lLSB
intgrFromRvsrdTuple (lLSB, lMSB) base = toInteger lMSB * base + toInteger lLSB

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
{-# INLINE [0] hndlOvflwW32 #-} -- does delaying inlining to phase 0 make a significant difference?
{-# SPECIALIZE hndlOvflwW32 :: Integer -> Integer #-}
{-# SPECIALIZE hndlOvflwW32 :: Word64 -> Word64 #-}
hndlOvflwW32 :: (Integral a) => a -> a
hndlOvflwW32 i = if i == maxW32 then pred maxW32 else i where maxW32 = radixW32

{-# INLINE hndlOvflwW32## #-}
hndlOvflwW32## :: Word64# -> Word64#
hndlOvflwW32## w64# = if isTrue# (w64# `eqWord64#` maxW32#) then predmaxW32# else w64#
  where
    !(W64# maxW32#) = radixW32
    !(W64# predmaxW32#) = predRadixW32

{-# INLINE hndlOvflwI32## #-}
hndlOvflwI32## :: Int64# -> Int64#
hndlOvflwI32## i64# = if isTrue# (i64# `eqInt64#` maxW32#) then predmaxW32# else i64#
  where
    !(I64# maxW32#) = radixW32
    !(I64# predmaxW32#) = predRadixW32

{-# INLINE radixW32Length #-} -- this works 
radixW32Length :: Integer -> Word
radixW32Length n
  | n == 0    = 1
  | otherwise = integerLogBaseWord radixW32 n + 1

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

-- | custom even and odd to handle what we need
_even, _odd :: (Integral a) => a -> (Bool, a)
_even n = let !(q, r) = n `quotRem` 2 in (r == 0, q)
_odd = _even
{-# INLINE _even #-}
{-# INLINE _odd #-}

_evenInt64#, _oddInt64# :: Int64# -> (# Bool, Int64# #)
_evenInt64# n# = (# isTrue# (remInt64# n# 2#Int64 `eqInt64#` 0#Int64), n# `quotInt64#` 2#Int64 #)
_oddInt64# = _evenInt64#
{-# INLINE _evenInt64# #-}
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

{-# INLINE updateDouble# #-}
updateDouble# :: Double# -> Int# -> Double#
updateDouble# d# ex# = case decodeDoubleInteger d# of (# m, n# #) -> encodeDoubleInteger m (n# +# ex#)

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
{-# INLINE radixW32 #-}
{-# SPECIALIZE radixW32 :: Integer #-}
{-# SPECIALIZE radixW32 :: Word64 #-}
{-# SPECIALIZE radixW32 :: Int64 #-}
radixW32 :: (Integral a) => a
radixW32 = 4294967296 -- 2 ^ finiteBitSize (0 :: Word32)

{-# INLINE predRadixW32 #-}
{-# SPECIALIZE predRadixW32 :: Integer #-}
{-# SPECIALIZE predRadixW32 :: Word64 #-}
{-# SPECIALIZE predRadixW32 :: Int64 #-}
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
{-# INLINE [0] undigits_ #-}
{-# SPECIALIZE undigits_ :: Word -> [Word] -> Integer #-}
{-# SPECIALIZE undigits_ :: Int -> [Int] -> Integer #-}
{-# SPECIALIZE undigits_ :: Int64 -> [Int64] -> Integer #-}
{-# SPECIALIZE undigits_ :: Word64 -> [Word64] -> Integer #-}
{-# SPECIALIZE undigits_ :: Integer -> [Integer] -> Integer #-}
{-# SPECIALIZE undigits_ :: Integer -> [Integer] -> Integer #-}

-- | Extract nth digit using fast-digits (note: digits are in reverse order)
nthDigitFast :: Integer -> Int -> Word32
nthDigitFast n pos = 
      let digitList = digitsUnsigned radixW32 (fromIntegral n)  -- Gets digits in reverse order
          len = length digitList
      in fromIntegral $ digitList !! (len - (pos-1))

doubleDigitInteger :: Integer -> (Int, Int) -> Word64#
doubleDigitInteger n (dl, dr) = word64FromRvsrd2ElemList# [nthDigitFast n dl , nthDigitFast n dr]
{-# INLINE doubleDigitInteger #-}

{-# SPECIALISE lenRadixW32 :: Integer -> Int #-}
{-# SPECIALISE lenRadixW32 :: Word64 -> Int #-}
{-# SPECIALISE lenRadixW32 :: Natural -> Int #-}
lenRadixW32 :: (Integral a) => a -> Int
lenRadixW32 n = I# (word2Int# (integerLogBase# radixW32 (fromIntegral n))) + 1
{-# INLINEABLE lenRadixW32 #-}

foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' f z xs = go xs
  where
    go [] = z
    go (x : xs) = f x $! go xs
{-# INLINEABLE foldr' #-}

-- | Compute two functions in parallel and return their results as a tuple.
{-# INLINE computePar #-}
computePar :: (a -> d) -> (b -> c -> e) -> a -> b -> c -> (d, e)
computePar f1 f2 x y z =
  let r1 = f1 x
      r2 = f2 y z 
  in r1 `par` (r2 `pseq` (r1, r2))

-- | because pred is Enum. this version blow is marginally faster
{-# SPECIALISE pred :: Integer -> Integer  #-}
{-# SPECIALISE pred :: Word64 -> Word64  #-}
{-# SPECIALISE pred :: Int -> Int  #-}
{-# SPECIALISE pred :: Int64 -> Int64  #-}
pred :: Integral a => a -> a
pred x = x + (- 1)
{-# INLINE pred #-}

-- //FIXME floor seems to trigger off missing specialization and also properFractionDouble. 