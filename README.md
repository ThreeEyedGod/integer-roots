<!-- # integer-roots [![Hackage](http://img.shields.io/hackage/v/integer-roots.svg)](https://hackage.haskell.org/package/integer-roots) [![Stackage LTS](http://stackage.org/package/integer-roots/badge/lts)](http://stackage.org/lts/package/integer-roots) [![Stackage Nightly](http://stackage.org/package/integer-roots/badge/nightly)](http://stackage.org/nightly/package/integer-roots) -->

## Updated Integer Square Root
Implementation of this paper: [A square root algorithm faster than Newton's method for multiprecision numbers, using floating-point arithmetic](https://arxiv.org/abs/2406.07751).   As of now, it's not at parity in speed to the original, let alone faster in an as-is comparison. HOWEVER - when the size of the test integers is increased to "Humungous" from merely "Huge",  performance benefits become apparent. isqrtB runs in ~980s vis-a-vis isqrtA in ~1044s - a 4% performance speedup. Such numbers may be useful in cryptography and space-related calculations. 
    
    Change the 63 to 255 in the test code in Wrappers.hs 
        instance (Num a, Arbitrary a) => Arbitrary (Huge a) where
        arbitrary = do
            Positive l <- arbitrary
            ds <- vector l
            return $ Huge $ foldl1 (\acc n -> acc * 2 ^ (63 :: Int) + n) ds

### Code changes in Math.NumberTheory.Roots.Squares.Internal. Updated integer-roots.cabal. For 'Humongous' testing see note above.


## Original readme
Calculating integer roots and testing perfect powers of arbitrary precision.

## Integer square root

The [integer square root](https://en.wikipedia.org/wiki/Integer_square_root)
(`integerSquareRoot`)
of a non-negative integer
_n_
is the greatest integer
_m_
such that
<img src="https://render.githubusercontent.com/render/math?math=m\le\sqrt{n}">.
Alternatively, in terms of the
[floor function](https://en.wikipedia.org/wiki/Floor_and_ceiling_functions),
<img src="https://render.githubusercontent.com/render/math?math=m = \lfloor\sqrt{n}\rfloor">.

For example,

```haskell
> integerSquareRoot 99
9
> integerSquareRoot 101
10
```

It is tempting to implement `integerSquareRoot` via `sqrt :: Double -> Double`:

```haskell
integerSquareRoot :: Integer -> Integer
integerSquareRoot = truncate . sqrt . fromInteger
```

However, this implementation is faulty:

```haskell
> integerSquareRoot (3037000502^2)
3037000501
> integerSquareRoot (2^1024) == 2^1024
True
```

The problem here is that `Double` can represent only
a limited subset of integers without precision loss.
Once we encounter larger integers, we lose precision
and obtain all kinds of wrong results.

This library features a polymorphic, efficient and robust routine
`integerSquareRoot :: Integral a => a -> a`,
which computes integer square roots by
[Karatsuba square root algorithm](https://hal.inria.fr/inria-00072854/PDF/RR-3805.pdf)
without intermediate `Double`s.

## Integer cube roots

The integer cube root
(`integerCubeRoot`)
of an integer
_n_
equals to
<img src="https://render.githubusercontent.com/render/math?math=\lfloor\sqrt[3]{n}\rfloor">.

Again, a naive approach is to implement `integerCubeRoot`
via `Double`-typed computations:

```haskell
integerCubeRoot :: Integer -> Integer
integerCubeRoot = truncate . (** (1/3)) . fromInteger
```

Here the precision loss is even worse than for `integerSquareRoot`:

```haskell
> integerCubeRoot (4^3)
3
> integerCubeRoot (5^3)
4
```

That is why we provide a robust implementation of
`integerCubeRoot :: Integral a => a -> a`,
which computes roots by
[generalized Heron algorithm](https://en.wikipedia.org/wiki/Nth_root_algorithm).

## Higher powers

In spirit of `integerSquareRoot` and `integerCubeRoot` this library
covers the general case as well, providing
`integerRoot :: (Integral a, Integral b) => b -> a -> a`
to compute integer _k_-th roots of arbitrary precision.

There is also `highestPower` routine, which tries hard to represent
its input as a power with as large exponent as possible. This is a useful function
in number theory, e. g., elliptic curve factorisation.

```haskell
> map highestPower [2..10]
[(2,1),(3,1),(2,2),(5,1),(6,1),(7,1),(2,3),(3,2),(10,1)]
```
