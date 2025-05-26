-- |
-- Module:      Math.NumberTheory.Roots.Squares.Internal
-- Copyright:   (c) 2011 Daniel Fischer, 2016-2020 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Internal functions dealing with square roots. End-users should not import this module.
--{-# OPTIONS -ddump-simpl -ddump-to-file #-}
{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE CPP              #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE UnboxedTuples #-} -- addition
{-# LANGUAGE LinearTypes #-}  --addition 
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Math.NumberTheory.Roots.Squares.Internal
  ( karatsubaSqrt
  , isqrtA
  , isqrtB
  ) where

-- *********** BEGIN NEW IMPORTS   
import GHC.Exts ((+#), (-#),(/##), (+##), (>=##),(**##), plusInt64#, (==##), subInt64#, gtInt64#, ltInt64#, leInt64#, uncheckedIShiftRA#)
import qualified Data.Bits.Floating as DB (nextUp, nextDown)
import GHC.Integer (decodeDoubleInteger, encodeDoubleInteger)
import GHC.Num.Integer
    ( integerDecodeDouble#, integerShiftL#, integerFromInt,integerFromWordList,
      integerFromInt#,
      integerFromInt64#,
      integerShiftR#,
      integerLog2#,
      integerLogBase#,
      integerLogBase, 
      integerQuotRem, integerToInt, integerLogBase, integerEncodeDouble, integerLogBase#)
import GHC.Float (divideDouble, isDoubleDenormalized, ceilingDouble, floorDouble)
import Data.FastDigits (digitsUnsigned, digits, undigits)
import qualified Data.Vector.Unboxed as VU (Vector,(//), unsafeSlice,length, replicate, unsafeHead, snoc, unsnoc, uncons, empty, ifoldl', singleton, fromList, null, length, splitAt, force, unsafeLast, toList)
import Data.Int (Int64)
import Data.Word (Word32)
import GHC.Exts ((<##), (*##), Double(..), Double#, Int64#, intToInt64#, int64ToInt#)
-- *********** END NEW IMPORTS 

import Data.Bits (finiteBitSize, unsafeShiftL, unsafeShiftR, (.&.), (.|.))

import GHC.Exts (Int(..), Int#, isTrue#, int2Double#, sqrtDouble#, double2Int#, (<#))
#ifdef MIN_VERSION_integer_gmp
import GHC.Exts (uncheckedIShiftRA#, (*#), (-#))
import GHC.Integer.GMP.Internals (Integer(..), shiftLInteger, shiftRInteger, sizeofBigNat#)
import GHC.Integer.Logarithms (integerLog2#)
#define IS S#
#define IP Jp#
#define bigNatSize sizeofBigNat
#else
import GHC.Exts (uncheckedShiftRL#, word2Int#, minusWord#, timesWord#)
import GHC.Num.BigNat (bigNatSize#)
import GHC.Num.Integer (Integer(..), integerLog2#, integerShiftR#, integerShiftL#)
import Control.Applicative (Alternative(empty))
import qualified Data.List as DL
-- import Data.Vector (create, convert)
#endif

-- Find approximation to square root in 'Integer', then
-- find the integer square root by the integer variant
-- of Heron's method. Takes only a handful of steps
-- unless the input is really large.
{-# SPECIALISE isqrtA :: Integer -> Integer #-}
isqrtA :: Integral a => a -> a
isqrtA 0 = 0
isqrtA n = isqrtB n --heron n (fromInteger . appSqrt . fromIntegral $ n) -- replace with isqrtB n

-- Heron's method for integers. First make one step to ensure
-- the value we're working on is @>= r@, then we have
-- @k == r@ iff @k <= step k@.
{-# SPECIALISE heron :: Integer -> Integer -> Integer #-}
heron :: Integral a => a -> a -> a
heron n a = go (step a)
      where
        step k = (k + n `quot` k) `quot` 2
        go k
            | m < k     = go m
            | otherwise = k
              where
                m = step k

-- Find a fairly good approximation to the square root.
-- At most one off for small Integers, about 48 bits should be correct
-- for large Integers.
appSqrt :: Integer -> Integer
appSqrt n@(IS i#) = IS (double2Int# (sqrtDouble# (int2Double# i#)))
appSqrt n@(IP bn#)
    | isTrue# ((bigNatSize# bn#) <# thresh#) =
          floor (sqrt $ fromInteger n :: Double)
    | otherwise = case integerLog2# n of
#ifdef MIN_VERSION_integer_gmp
                    l# -> case uncheckedIShiftRA# l# 1# -# 47# of
                            h# -> case shiftRInteger n (2# *# h#) of
                                    m -> case floor (sqrt $ fromInteger m :: Double) of
                                            r -> shiftLInteger r h#
#else
                    l# -> case uncheckedShiftRL# l# 1# `minusWord#` 47## of
                            h# -> case integerShiftR# n (2## `timesWord#` h#) of
                                    m -> case floor (sqrt $ fromInteger m :: Double) of
                                            r -> integerShiftL# r h#
#endif
    where
        -- threshold for shifting vs. direct fromInteger
        -- we shift when we expect more than 256 bits
        thresh# :: Int#
        thresh# = if finiteBitSize (0 :: Word) == 64 then 5# else 9#
-- There's already a check for negative in integerSquareRoot,
-- but integerSquareRoot' is exported directly too.
appSqrt _ = error "integerSquareRoot': negative argument"


-- Integer square root with remainder, using the Karatsuba Square Root
-- algorithm from
-- Paul Zimmermann. Karatsuba Square Root. [Research Report] RR-3805, 1999,
-- pp.8. <inria-00072854>

karatsubaSqrt :: Integer -> (Integer, Integer)
karatsubaSqrt 0 = (0, 0)
karatsubaSqrt n
    | lgN < 2300 =
        let s = isqrtA n in (s, n - s * s)
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

-- BEGIN isqrtB ****************************************************************
-- BEGIN isqrtB ****************************************************************
-- | Square root using Fabio Romano's Faster Bombelli method.
--- https ://arxiv.org/abs/2406.07751
-- A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic

{-# SPECIALIZE isqrtB :: Integer -> Integer #-}
isqrtB :: (Integral a) => a -> a
isqrtB 0 = 0
isqrtB n = fromInteger . theNextIterations . theFi . dgtsVecBase32__ . fromIntegral $ n

-- BEGIN data structures for lists, vectors, sequences  ****************************************************************
-- BEGIN ****************************************************************

-- | Iteration loop data - these records have vectors / lists in them 
data Itr = Itr {lv :: {-# UNPACK #-} !Int, vecW32_ :: {-# UNPACK #-} !(VU.Vector Word32), l_ :: {-# UNPACK #-} !Int#, yCumulative :: Integer, iRem_ :: {-# UNPACK #-} !Integer, tb# :: FloatingX#} deriving (Eq)
data LoopArgs = LoopArgs {position :: {-# UNPACK #-} !Int#, inArgs_ :: !IterArgs_, residuali32Vec :: !(VU.Vector Word32)} deriving (Eq)          
data ProcessedVec  = ProcessedVec {theRest :: VU.Vector Word32, firstTwo :: VU.Vector Word32, len :: !Int} deriving (Eq)
data RestNextTwo = RestNextTwo {pairposition :: {-# UNPACK #-} !Int#, theRestVec :: !(VU.Vector Word32), firstWord32 :: {-# UNPACK #-} !Word32, secondWord32 :: {-# UNPACK #-} !Word32} deriving Eq

-- END data structures for lists, vectors, sequences ****************************************************************
-- END ****************************************************************

-- BEGIN using vectors ****************************************************************
-- BEGIN ****************************************************************

preFI ::  VU.Vector Word32 -> ProcessedVec
preFI v  
  | VU.null v = error "preFI: Invalid Argument null vector "
  | VU.length v == 1 && VU.unsafeHead v == 0 = ProcessedVec VU.empty VU.empty 0
  | otherwise = splitVec v

{-# INLINE splitVec #-}        
-- | also evenizes the vector of digits
splitVec :: VU.Vector Word32 -> ProcessedVec
splitVec vec = let !l = VU.length vec in if even l then brkVecPv vec (l-2) else evenizePv (brkVecPv vec (l-1))

fi :: ProcessedVec -> Itr
fi (ProcessedVec w32Vec dxsVec' (I# l'#)) = let 
      !(IterRes !yc !y1 !remInteger) = fstDgtRem (intgrFromRvsrd2ElemVec dxsVec' radixW32) 
    in Itr 1 w32Vec l'# yc remInteger (intNormalizedFloatingX# y1) 

-- | The First iteration
theFi :: VU.Vector Word32 -> Itr
theFi = fi . preFI

{-# INLINE prepA_ #-}
prepA_ :: Int# -> VU.Vector Word32 -> RestNextTwo
prepA_ l# w32Vec = let 
          -- !p# = l# `uncheckedIShiftRA#` 1# -# 1# -- Use bit-shift for division by 2
          -- !(I# p#) = pred $ I# l# `quot` 2 -- last pair is position "0"
          (rst,nxt2) = brkVec w32Vec (I# l# - 2)
        -- in RestNextTwo p# rst (VU.unsafeHead nxt2) (VU.unsafeLast nxt2)
        in RestNextTwo l# rst (VU.unsafeHead nxt2) (VU.unsafeLast nxt2)

prepB_ :: Integer -> FloatingX# -> RestNextTwo -> IterArgs_
prepB_ iRem tBFX# (RestNextTwo _ _ !n1_ !nl_) = IterArgs_ (intgrFrom3DigitsBase32 iRem (n1_, nl_)) (scaleByPower2 (intToInt64# 32#) tBFX# )-- sqrtF previous digits being scaled right here
{-# INLINE prepB_ #-} 

{-# INLINE prepArgs_ #-}
prepArgs_ :: Itr -> LoopArgs
prepArgs_ (Itr _ w32Vec l# _ iRem tBFX_#) = let           
          !rnxt2@(RestNextTwo p# ri32Vec _ _) = prepA_ l# w32Vec
          iargs = prepB_ iRem tBFX_# rnxt2
        in 
          LoopArgs p# iargs ri32Vec

-- Keep it this way: Inlining this lowers performance. 
theNextIterations :: Itr -> Integer
theNextIterations itr@(Itr currlen w32Vec l# yCumulated iRem tbfx#) 
  | VU.null w32Vec = yCumulated 
  | otherwise =
      let 
          (LoopArgs _ !inA_ !ri32V ) = prepArgs_ itr 
          (IterRes !yc !yTildeFinal !remFinal) = nxtDgtRem yCumulated inA_ -- number crunching only
       in theNextIterations $ Itr (succ currlen)(VU.force ri32V) (l# -# 2#) yc remFinal (fixTCFX# inA_ currlen yTildeFinal)

-------------------------------------------------------------------------------------

-- END using vectors ****************************************************************
-- END ****************************************************************

-------------------------------------------------------------------------------------

-- | numeric loop records 
data IterArgs_ = IterArgs_ {tA_ :: Integer, tC_ :: FloatingX#} deriving (Eq)
data IterRes = IterRes {yCum :: Integer, yTilde :: {-# UNPACK #-}!Int64, ri :: Integer} deriving (Eq) 
data CoreArgs  = CoreArgs {tA# :: !FloatingX#, tC# :: !FloatingX#, rad# :: !FloatingX#} deriving (Eq)

---------------------------------------------------------------------------------------
-- | core of computations. Functions from this point on are doing only number crunching
fstDgtRem :: Integer -> IterRes
fstDgtRem i = let !y = optmzedLrgstSqrtN i in IterRes y (fromIntegral y) (hndlOvflwW32 $ i - y * y)

nxtDgtRem :: Integer -> IterArgs_-> IterRes 
nxtDgtRem yCumulat iterargs_= let !yTilde_ = nxtDgt_# iterargs_ in computeRem_ (yCumulat*radixW32) iterargs_ yTilde_ 
{-# INLINE nxtDgtRem #-}

fixTCFX# :: IterArgs_ -> Int -> Int64 -> FloatingX#
fixTCFX# ia currlen yTildeFinal = let tcfx# = tC_ ia in if currlen <= 2 then nextDownFX# $ tcfx# !+##  integer2FloatingX# (fromIntegral yTildeFinal) else tcfx#  -- recall tcfx is already scaled by 32. Do not use normalize here

-- | Next Digit. In our model a 32 bit digit.   This is the core of the algorithm 
-- for small values we can go with the standard double# arithmetic
-- for larger than what a double can hold, we resort to our custom "Float" - FloatingX
nxtDgt_# :: IterArgs_ -> Int64
nxtDgt_# (IterArgs_ 0 !_) = 0 
nxtDgt_# iax = comput (preComput iax) 
{-# INLINE nxtDgt_# #-}

preComput :: IterArgs_ -> CoreArgs
preComput (IterArgs_ tA__ tCFX#) = let  
      !tAFX# = intNormalizedFloatingX# tA__
      !radFX# = tCFX# !*## tCFX# !+## tAFX#
    in CoreArgs tAFX# tCFX# radFX#
{-# INLINE preComput #-}    

comput :: CoreArgs -> Int64 
comput (CoreArgs !tAFX# !tCFX# !radFX#) = hndlOvflwW32 (floorX# (nextUpFX# (nextUpFX# tAFX# !/## nextDownFX# (sqrtFX# (nextDownFX# radFX#) !+## nextDownFX# tCFX#))))
{-# INLINE comput #-}    

-- | compute the remainder. It may be that the trial "digit" may need to be reworked
-- that happens in handleRems_
computeRem_ :: Integer -> IterArgs_ -> Int64 -> IterRes
computeRem_ tc iArgs_ yTilde_ = let !rTrial = calcRemainder (tA_ iArgs_) tc yTilde_ in handleRems_ (IterRes tc yTilde_ rTrial)
{-# INLINE computeRem_ #-}

-- | if the remainder is negative it's a clear sign to decrement the candidate digit
-- if it's positive but far larger in length of the current accumulated root, then also it signals a need for current digit rework 
-- if it's positive and far larger in size then also the current digit rework 
handleRems_ :: IterRes -> IterRes
handleRems_ (IterRes yc yi ri_)
  | (ri_ < 0) && (yi > 0) = let rdr = fixRemainder yc ri_ (yi-1) in IterRes (ycyi-1) (yi-1) rdr -- IterRes nextDownDgt0 $ calcRemainder iArgs iArgs_ nextDownDgt0 -- handleRems (pos, yCurrList, yi - 1, ri + 2 * b * tB + 2 * fromIntegral yi + 1, tA, tB, acc1 + 1, acc2) -- the quotient has to be non-zero too for the required adjustment
  | otherwise = IterRes ycyi yi ri_
 where 
  !ycyi = yc+fromIntegral yi
{-# INLINE handleRems_ #-}
  
-- Calculate remainder accompanying a 'digit'
calcRemainder :: Integer -> Integer -> Int64 -> Integer
calcRemainder tAI !_ 0 =  tAI 
calcRemainder tAI tc dgt =  let !i = fromIntegral dgt in tAI - ((double i * tc) + i*i)
{-# INLINE calcRemainder #-}

-- Fix remainder accompanying a 'next downed digit'
fixRemainder :: Integer -> Integer -> Int64 -> Integer
fixRemainder tc rdr dgt =  rdr + double tc + double (fromIntegral dgt) + 1
{-# INLINE fixRemainder #-}

------------------------------------------------------------------------
-- | HELPER functions

--- BEGIN helpers for Sequences, Lists and Vectors
--- ***********************************

-- // FIXME TAKES DOWN PERFORMANCE
{-# INLINE dgtsVecBase32__ #-}
dgtsVecBase32__ :: Integer -> VU.Vector Word32
dgtsVecBase32__ n | n < 0 = error "dgtsVecBase32_: Invalid negative argument"
dgtsVecBase32__ 0 = VU.singleton 0 
dgtsVecBase32__ n = mkIW32Vec n radixW32

brkVec :: VU.Vector Word32 -> Int -> (VU.Vector Word32, VU.Vector Word32)
brkVec v loc = let !(hd, rst) = VU.splitAt loc v in (VU.force hd, VU.force rst)
{-# INLINE brkVec #-}

brkVecPv :: VU.Vector Word32 -> Int -> ProcessedVec
brkVecPv v loc = let !(hd, rst) = brkVec v loc in ProcessedVec hd rst loc

-- | a bit tricky it leaves l alone in the predicate that brkVecPv-brkLst-brkLstSeq does the right thing //FIXME HMMM
evenizePv :: ProcessedVec -> ProcessedVec
evenizePv (ProcessedVec he re l) = ProcessedVec he (VU.force $ VU.snoc re 0) l
{-# INLINE evenizePv #-}

{-# INLINE mkIW32Vec #-}
-- spit out the unboxed Vector as-is from digitsUnsigned which comes in reversed format.
mkIW32Vec :: Integer -> Word -> VU.Vector Word32
mkIW32Vec 0 _ = VU.singleton 0 -- safety
mkIW32Vec i b = VU.fromList $ mkIW32Lst i b

{-# INLINE intgrFromRvsrd2ElemVec #-}
-- | Integer from a "reversed" list of Word32 digits
intgrFromRvsrd2ElemVec :: VU.Vector Word32 -> Integer -> Integer
intgrFromRvsrd2ElemVec v2ElemW32s base =
  let (l1, l2) = case (VU.uncons v2ElemW32s, VU.unsnoc v2ElemW32s) of
        (Just u, Just v) -> (fst u, snd v)
        (_,_)           -> error "intgrFromRvsrd2ElemVec : Empty Vector" -- (Nothing, _) and (_, Nothing)
      in intgrFromRvsrdTuple (l1, l2) base

{-# INLINE mkIW32Lst #-}
--spit out the Word32 List from digitsUnsigned which comes in reversed format.
mkIW32Lst :: Integer -> Word -> [Word32]
mkIW32Lst 0 _ = [0]-- safety
mkIW32Lst i b = wrd2wrd32 (iToWrdListBase i b) 

evenizeLstRvrsdDgts :: [Word32] -> ([Word32], Int)
evenizeLstRvrsdDgts [] = ([0], 1)
evenizeLstRvrsdDgts xs = let l = length xs in if even l then (xs, l) else (xs ++ [0], succ l)

-- {-# INLINE vectorToInteger #-}
-- -- | Convert a vector of Word32 values to an Integer with base 2^32 (radixW32).
-- -- This function takes a vector of Word32 values, where each element represents a digit in base 2^32,
-- -- and combines them to form a single Integer.
-- -- Function to convert a vector of Word32 values to an Integer with base 2^32 (radixw32)
-- vectorToInteger :: VU.Vector Word32 -> Integer
-- vectorToInteger = VU.ifoldl' (\acc i w -> acc + fromIntegral w * radixW32 ^ i) 0 

--- END helpers for Sequences, Lists and Vectors
--- END ***********************************

--- BEGIN Core numeric helper functions
--- ***********************************
{-# INLINE intgrFromRvsrd2ElemLst #-}
-- | Integer from a "reversed" list of Word32 digits
intgrFromRvsrd2ElemLst :: [Word32] -> Integer -> Integer
intgrFromRvsrd2ElemLst xs2ElemW32s@[l1,l2] base = intgrFromRvsrdTuple (l1, l2) base

{-# INLINE intgrFromRvsrdTuple #-}
-- | Integer from a "reversed" tuple of Word32 digits
intgrFromRvsrdTuple :: (Word32,Word32) -> Integer -> Integer
intgrFromRvsrdTuple (0,0) 0 = 0
intgrFromRvsrdTuple (0,l2) base = fromIntegral l2 * base 
intgrFromRvsrdTuple (l1,0) _ = fromIntegral l1
intgrFromRvsrdTuple (l1,l2) base = fromIntegral l2 * base + fromIntegral l1

{-# INLINE doubleFromRvsrdTuple #-}
-- | double from a "reversed" tuple of Word32 digits
doubleFromRvsrdTuple :: (Word32,Word32) -> Integer -> Double
doubleFromRvsrdTuple (l1,l2) base = fromIntegral l2 * fromIntegral base + fromIntegral l1

{-# INLINE intNormalizedFloatingX# #-}
{-# SPECIALIZE intNormalizedFloatingX# :: Int64 -> FloatingX# #-}
{-# SPECIALIZE intNormalizedFloatingX# :: Integer -> FloatingX# #-}
intNormalizedFloatingX# :: Integral a => a -> FloatingX#
intNormalizedFloatingX# 0 = zero#
intNormalizedFloatingX# i64 = normalizeFX# $ integer2FloatingX# (fromIntegral i64)

{-# INLINE optmzedLrgstSqrtN #-}
optmzedLrgstSqrtN :: Integer -> Integer 
optmzedLrgstSqrtN i = hndlOvflwW32 (largestNSqLTE (startAt i radixW32Squared 0) i) -- overflow trap

{-# INLINE startAt #-}
{-# SPECIALIZE startAt :: Int64 -> Int64 -> Int64 -> Int64 #-}
{-# SPECIALIZE startAt :: Integer -> Integer -> Integer -> Integer #-}
startAt :: Integral a => a -> a -> a -> a 
startAt i mx mi = pred $ floorDouble (sqrt (fromIntegral i) :: Double)--if i >= mx then mx else mi 

-- | handle overflow 
{-# INLINE hndlOvflwW32 #-}
{-# SPECIALIZE hndlOvflwW32 :: Int64 -> Int64 #-}
hndlOvflwW32 :: Integral a => a -> a 
hndlOvflwW32 i = if i == maxW32 then pred maxW32 else i where maxW32 = radixW32

scaleByPower2 :: Int64# -> FloatingX# -> FloatingX#
scaleByPower2 n# (FloatingX# s# e#) = if isTrue# (s# ==## 0.00##) then zero# else normalizeFX# $ FloatingX# s# (e# `plusInt64#` n#)
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
    
{-# INLINE largestNSqLTE #-}
largestNSqLTE :: Integer -> Integer -> Integer 
largestNSqLTE bot n = go bot (n + 1)
  where
    go a b
      | a + 1 == b = a
      | m * m <= n = go m b
      | otherwise = go a m
      where
        !m = (a + b) `div` 2

{-# INLINE intgrFrom3DigitsBase32 #-}
-- | Integer from a 3rd place plus a "reversed" tuple of 2 Word32 digits on base 
intgrFrom3DigitsBase32 :: Integer -> (Word32,Word32) -> Integer
intgrFrom3DigitsBase32 i (l1,l2)  = (i * secndPlaceW32Radix) + intgrFromRvsrdTuple (l1,l2) radixW32

-- | Custom Double Type and its arithmetic        
data FloatingX = FloatingX !Double !Int64 deriving (Eq, Show) -- ! for strict data type
-- | Custom double "unboxed" and its arithmetic
data FloatingX# = FloatingX# {signif# :: {-# UNPACK #-}!Double#, expnnt# :: {-# UNPACK #-}!Int64#} deriving (Eq) -- ! for strict data type

{-# INLINE floorX# #-}
{-# SPECIALIZE floorX# :: FloatingX# -> Integer #-}
{-# SPECIALIZE floorX# :: FloatingX# -> Int64 #-}
floorX# :: (Integral a) => FloatingX# -> a
-- floorX# (FloatingX# s# e#) = case fx2Double (FloatingX (D# s#) e) of
--     Just d -> floor d
--     _ -> error "floorX#: fx2Double resulted in Nothing  " --fromIntegral $ toLong (D# s#) (fromIntegral e)
--   where 
--     e = fromIntegral (I# $ int64ToInt# e#)
floorX# (FloatingX# s# e#) = let e = fromIntegral (I# $ int64ToInt# e#) 
  in case fx2Double (FloatingX (D# s#) e) of
    Just d -> floor d
    _ -> error "floorX#: fx2Double resulted in Nothing  " --fromIntegral $ toLong (D# s#) (fromIntegral e)

{-# INLINE zero# #-}    
zero# :: FloatingX#
zero# = let 
        !(I# minBoundInt#) = fromIntegral (minBound :: Int64) 
        !minBound64# = intToInt64# minBoundInt#
  in FloatingX# 0.0## minBound64# 

minValue# :: FloatingX#
minValue# = let 
        !(I# zeroInt#) = fromIntegral (0 :: Int64) 
        !zero64# = intToInt64# zeroInt#
  in FloatingX# 1.0## zero64#

{-# INLINE (!+##) #-}
(!+##) :: FloatingX# -> FloatingX# -> FloatingX#
(!+##) x y = x `add#` y

{-# INLINE (!*##) #-}
(!*##) :: FloatingX# -> FloatingX# -> FloatingX#
(!*##) x y = x `mul#` y

{-# INLINE (!/##) #-}
(!/##) :: FloatingX# -> FloatingX# -> FloatingX#
(!/##) x y = x `divide#` y

{-# INLINE add# #-}
add# :: FloatingX# -> FloatingX# -> FloatingX#
add# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#)
  | a == zero# = b
  | b == zero# = a 
  | isTrue# (expA# `gtInt64#` expB#) = combine a b
  | isTrue# (expA# `ltInt64#` expB#) = combine b a
  | otherwise = FloatingX# (sA# +## sB#) expA# --FloatingX (signifA + signifB) expA
  where
    combine big@(FloatingX# sBig# expBig#) little@(FloatingX# sLittle# expLittle#) =
      let !scale# = expLittle# `subInt64#` expBig#
          !scaleD# = int2Double# (int64ToInt# scale#) 
          !scaledLittle# = sLittle# *## (2.00## **## scaleD#)
          !resSignif# = sBig# +## scaledLittle#
       in if isTrue# (resSignif# >=## 2.0##) 
            then FloatingX# (resSignif# /## 2.0##) (expBig# `plusInt64#` intToInt64# 1#)
            else FloatingX# resSignif# expBig#

{-# INLINE mul# #-}
mul# :: FloatingX# -> FloatingX# -> FloatingX#
-- mul# (FloatingX# 1.0## 0#) b = b
-- mul# a (FloatingX# 1.00## 0.00##) = a
mul# a@(FloatingX# sA# expA#) b@(FloatingX# sB# expB#) 
    | isTrue# (sA# ==## 0.00##) = zero#
    | isTrue# (sB# ==## 0.00##) = zero#
    | isTrue# (sA# ==## 1.00##) = b -- //FIXME THIS IS WRONG
    | isTrue# (sB# ==## 1.00##) = a -- //FIXME this is wrong
    | otherwise = 
          let !resExp# = expA# `plusInt64#` expB#
              !resSignif# = sA# *## sB#
          in if isTrue# (resSignif# >=## 2.0##)
                then FloatingX# (resSignif# /## 2.0##) (resExp# `plusInt64#` intToInt64# 1#)
                else FloatingX# resSignif# resExp#

{-# INLINE divide# #-}
divide# :: FloatingX# -> FloatingX# -> FloatingX#
divide# n@(FloatingX# s1# e1#) d@(FloatingX# s2# e2#)
    | d == FloatingX# 1.0## (intToInt64# 0#) = n 
    | isTrue# (s1# ==## 0.0##) = zero#
    | isTrue# (s2# ==## 0.0##) = error "divide#: error divide by zero " 
    | otherwise = 
        let !resExp# = e1# `subInt64#` e2#
            !resSignif# = s1# /## s2#
            -- !l1Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# e2#
            -- !l2Word64# = int64ToWord64# e1# `xor64#` int64ToWord64# resExp#
            !(# finalSignif#, finalExp# #) = if isTrue# (resSignif# <## 1.0##)
                                      then (# resSignif# *## 2.0##, resExp# `subInt64#` intToInt64# 1# #)
                                      else (# resSignif#, resExp# #)
        -- in if (e1 `xor` e2) .&. (e1 `xor` resExp) < 0 || (resSignif < 1.0 && resExp == (minBound :: Integer))
          -- //TODO fix this next line
        -- in if W64# l1Word64# .&. W64# l2Word64# < 0 || (isTrue# (resSignif# <## 1.0##) && isTrue# (resExp# `leInt64#` intToInt64# 0#) )
        in if isTrue# (resSignif# <## 1.0##) && isTrue# (resExp# `leInt64#` intToInt64# 0#) 
           then zero#
           else FloatingX# finalSignif# finalExp#

{-# INLINE sqrtFX# #-}
sqrtFX# :: FloatingX# -> FloatingX#
sqrtFX# (FloatingX# s# e#)  = let
    !(D# sX#, eX) = sqrtSplitDbl (FloatingX (D# s#) (fromIntegral (I# (int64ToInt# e#)))) 
    !(I# eX#) = fromIntegral eX
 in FloatingX# sX# (intToInt64# eX#) 

sqrtSplitDbl :: FloatingX -> (Double, Int64) 
sqrtSplitDbl (FloatingX d e) 
  | d == 0 = (0,0) 
  | d == 1 = (1,0)
  | even e = (s,fromIntegral $ integerShiftR# (integerFromInt $ fromIntegral e) 1##) -- even 
  | otherwise = (sqrtOf2 * s, fromIntegral $ integerShiftR# (integerFromInt $ fromIntegral e-1) 1##) -- odd 
 where 
    !s = sqrtDX d 
{-# INLINE sqrtSplitDbl #-}

sqrtDX :: Double -> Double
sqrtDX d
  | d == 0 = 0
  | isNaN d = 0
  | isInfinite d = maxDouble
  | d == 1 = 1
  | otherwise = sqrt d -- actual call to "the floating point square root" {sqrt_fsqrt, sqrt, sqrtC, sqrtLibBF, sqrthpmfr or other }
{-# INLINE sqrtDX #-}

-- sqrtDoublehmpfr :: Double -> Double
-- sqrtDoublehmpfr d = M.toDouble M.Near $ M.sqrt M.Near 1000 (M.fromDouble M.Near 1000 d)

-- foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h sqrt_fsqrt" sqrt_fsqrt :: Double -> Double
-- foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h sqrtC" sqrtC :: Double -> Double
-- foreign import capi "/Users/mandeburung/Documents/integer-roots/Math/c/fsqrt.h toLong" toLong :: Double -> CLong -> CLong
fx2Double :: FloatingX -> Maybe Double
fx2Double (FloatingX d@(D# d#) e)
    | isNaN d = Nothing --error "Input is NaN"
    | isInfinite d = Nothing -- error "Input is Infinity"
    | ex < 0 = Just $ fromIntegral m `divideDouble` (2^(-ex)) -- this is necessary 
    | otherwise = 
        let result# = encodeDoubleInteger m ex# 
            !(I# ex#) = ex
            !result = D# result#
           in if isInfinite result || isNaN result then Nothing else Just result 
    where 
        !(# m, n# #) = decodeDoubleInteger d# 
        !ex = I# n# + fromIntegral e 
{-# INLINE fx2Double #-}

{-# INLINE double2FloatingX# #-}
double2FloatingX# :: Double -> FloatingX#
double2FloatingX# d = let 
   !(D# s#, e) = split d 
   !(I# eInt#) = fromIntegral e 
   !e# = intToInt64# eInt#
  in FloatingX# s# e#

{-# INLINE integer2FloatingX# #-}
integer2FloatingX# :: Integer -> FloatingX#
integer2FloatingX# i
  | i == 0 = zero#
  | i < 0 = error "integer2FloatingX# : invalid negative argument"
  | itsOKtoUsePlainDoubleCalc =  double2FloatingX# (fromIntegral i) 
  | otherwise =  let 
      !(i_, e_) = cI2D2 i -- so that i_ is below integral equivalent of maxUnsafeInteger=maxDouble
      !(D# s#) = fromIntegral i_
      !(I# e_#) = e_
    in FloatingX# s# (intToInt64# e_#)
  where
    !(D# maxDouble#) = maxDouble
    !(D# iDouble#) = fromIntegral i 
    itsOKtoUsePlainDoubleCalc = isTrue# (iDouble# <## (fudgeFactor## *## maxDouble#)) where fudgeFactor## = 1.00## -- for safety it has to land within maxDouble (1.7*10^308) i.e. tC ^ 2 + tA <= maxSafeInteger

-- The maximum integral value that can be unambiguously represented as a
-- Double. Equal to 9,007,199,254,740,991 = maxsafeinteger
{-# INLINE cI2D2 #-}
cI2D2 :: Integer -> (Integer, Int)
cI2D2  = cI2D2'
    where 
      cI2D2' 0 = (0, 0)
      cI2D2' i | i <= maxSafeInteger = (i, 0)
      cI2D2' i = go 0 i
          where
            go e n
              | n <= maxUnsafeInteger = (n, e)
              | otherwise = go (e + shiftAmount) (n `unsafeShiftR` shiftAmount) 
              where
                exPlus = fromIntegral (integerLogBase 10 n - 308 `quot` 100) -- would be dynamic (100-10)
                shiftAmount = max 1 exPlus

{-# INLINE split #-}
split :: Double -> (Double, Int64)
split (D# d#) = 
  case split# d# of
    (# s#, ex# #) -> (D# s#, fromIntegral (integerFromInt64# ex#))

{-# INLINE split# #-}
split# :: Double# -> (# Double#, Int64# #) 
split# d#  = let 
        !(# s, expInt# #) = decodeDoubleInteger d# 
        !(D# s#) = fromIntegral s 
        !ex# = intToInt64# expInt#
  in (# s#, ex# #) 

 -- | Normalising functions for our custom double  
{-# INLINE normalize #-}
normalize :: Double -> Double 
normalize x
  -- | NFI.isNormal x = x 
  | x == 0 || isNegativeZero x = minDouble 
  | isInfinite x || isNaN x = error "normalize: Infinite or NaN "
  | isDoubleDenormalized x == 1 = x 
  | isIEEE x  = x 
  | otherwise =
      let !(# m, e# #) = integerDecodeDouble# x#
          !n = floatRadix x
          !(mantissa, expo) =  normalizeIter (abs (fromIntegral m)) (fromIntegral (I# e#)) n
       in 
            case fx2Double (FloatingX mantissa expo) of 
                Just result -> result -- normalized 
                _          -> x  -- return as-is
  where
    !(D# x#) = x 
    normalizeIter = go
      where 
        go m' e' n' 
          | m' >= fromIntegral n' = go (m' / fromIntegral n') (e' + 1) n'
          | m' < 1 = go (m' * fromIntegral n') (e' - 1) n'
          | otherwise = (m', e')

{-# INLINE normalizeFX# #-}
normalizeFX# :: FloatingX# -> FloatingX#
normalizeFX# (FloatingX# d# ex#) = let
    !(D# nd#) = normalize (D# d#)
    !(# s#, e# #) = split# nd#
    !expF# = ex# `plusInt64#` e#
  in FloatingX# s# expF#

----------------------------------------------------------------------------
-- | Some Constants 
radixW32 :: Integral a => a 
radixW32 = 4294967296 --2 ^ finiteBitSize (0 :: Word32)

secndPlaceW32Radix :: Integer
secndPlaceW32Radix = 18446744073709551616 --radixW32 * radixW32

radixW32Squared :: Integer
radixW32Squared = 18446744073709551616 --secndPlaceRadix

radixW32Cubed :: Integer
radixW32Cubed = 79228162514264337593543950336 --secndPlaceRadix * radixW32

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

-----------------------------------------------------------------------------------------------
-- | Floating Point nextUp/nextDown funxctions 
{-# INLINE nextUp #-}
nextUp :: Double -> Double
nextUp = DB.nextUp --NFI.nextUp

{-# INLINE nextDown #-}
nextDown :: Double -> Double
nextDown = DB.nextDown --NFI.nextDown

{-# INLINE nextUp# #-}
nextUp# :: Double# -> Double#
nextUp# dIn# = let 
    !d = D# dIn#
    !(D# dOut#) = nextUp d
  in dOut# 

{-# INLINE nextDown# #-}
nextDown# :: Double# -> Double#
nextDown# dIn# = let 
        !d = D# dIn#
        !(D# dOut#) = nextDown d 
    in dOut# 

{-# INLINE nextUpFX# #-}
nextUpFX# :: FloatingX# -> FloatingX#
nextUpFX# (FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) = minValue#
  | otherwise = let 
     !interimS# = nextUp# s#
    in
      if isTrue# (interimS# >=## 2.0##) then FloatingX# (interimS# /## 2.00##) (e# `plusInt64#` intToInt64# 1#) else FloatingX# interimS# e#

{-# INLINE nextDownFX# #-}
nextDownFX# :: FloatingX# -> FloatingX#
nextDownFX# x@(FloatingX# s# e#)
  | isTrue# (s# ==## 0.0##) || x == minValue# = zero#
  | otherwise = let 
      !interimS# = nextDown# s#
     in 
        if isTrue# (interimS# <## 1.0##) then FloatingX# (interimS# *## 2.00##) (e# `subInt64#` intToInt64# 1#) else FloatingX# interimS# e#

-- END isqrtB ****************************************************************
-- END isqrtB ****************************************************************
