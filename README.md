# ContinuedFractions
A Haskell implementation of Gosper's algorithm for arithmetic on continued fractions. This implementation avoids all difficulties with infinite loops (which can occur if the algorithm is implemented naively). All computations and comparisons are done on the CF representation with integer arithmetic; conversion to float only happens if we explicitly convert a result. All CF terms, except possibly the first, are greater than or equal to 1. See cfAlgorithm.tex for (many) more details.

Sample usage:

	user@Users-MacBook-Pro ContinuedFractions % ghci
	GHCi, version 8.10.7: https://www.haskell.org/ghc/  :? for help
	Prelude> :load gosper.hs 
	[1 of 1] Compiling Main             ( gosper.hs, interpreted )
	Ok, one module loaded.
	*Main> sqrt2 = makeCF (1:(cycle [2])) -- create CF from list of Integer terms
	*Main> sqrt2
	cf[1,2,2,2,2,2,2,2,2,2,2,2,2,2]
	*Main>:type sqrt2
	sqrt2 :: CF
	
By default, we display enough terms of a CF to get accuracy within 2^(-32). Internally we use Haskell's lazy evaluation and infinite data structures (and the `Data.Ratio` module) to maintain theoretically infinite precision. We prepend "cf" to make it obvious that the expression being shown is *not* of type `[Integer]`. The type `CF` is an instance of `Num`, `Fractional`, `Ord`, and `Eq`; comparison and equality also use default accuracy of 2^(-32):

	*Main> pie = floatToCF pi -- create CF from Numeric type
	*Main> pie
	cf[3,7,15,1,292,1,1]
	*Main> (pie + sqrt2)/3
	cf[1,1,1,12,1,15,2,29,4]
	*Main> pie < sqrt2
	False
	*Main> sqrt2 ^ 2
	cf[2]
	*Main> sqrt2 ^ 2 == 2
	True

We can convert among CFs, floats, rationals, and lists of integers, specifying the required accuracy or using the default:

	*Main> e = makeCF ([2, 1, 2] ++ (concat [ [1,1,4+2*k] | k <- [0..] ]))
	*Main> e            -- unlike pi, the terms have a simple pattern
	cf[2,1,2,1,1,4,1,1,6,1,1,8,1,1,10]
	*Main> 
	*Main> cfToTerms e  -- evaluates to list of Integers
	[2,1,2,1,1,4,1,1,6,1,1,8,1,1,10]
	*Main> cfToTermsWithin (2**(-64)) e
	[2,1,2,1,1,4,1,1,6,1,1,8,1,1,10,1,1,12,1,1,14,1,1,16]
	*Main> 
	*Main> cfToFloat e
	2.7182818284454013
	*Main> cfToFloatWithin (2**(-64)) e -- limited by float accuracy; last digit is wrong
	2.7182818284590455
	*Main> cfToFloatWithin (2**(-128)) e  
	2.7182818284590455
	*Main> cfToRatWithin (2**(-64)) e
	14013652689 % 5155334720
	*Main> cfToRatWithin (2**(-128)) e -- rational approximation to any desired accuracy
	163627140912497702175 % 60195061159370501504
	
We can also do comparison to a specified accuracy:

	*Main> x = makeCF [1,2,2,2,2,2,2]
	*Main> x^2
	cf[1,1,28560]
	*Main> x^2 == 2
	False
	*Main> eqWithin (2**(-13)) (x^2) 2
	True
	*Main> eqWithin (2**(-14)) (x^2) 2
	False

Note that there is no function which, given integer `n`, will simply return the first `n`  terms of a CF. To see why, consider asking for the first few terms of `sqrt2^2`. Any terminating computation can only make use of some finite prefix of the infinte list `[1,2,2,2 ...]`. But no such prefix is enough to rule out the possibility that the value is slightly less than the square root of 2; if that is the case, the first term should be 1. Otherwise it should be 2. So it is not always meaningful to ask for terms of a CF without reference to a degree of accuracy.

We have also implemented Gosper's algorithm for extracting the square root of a CF:

	*Main> x = floatToCF 42.1703
	*Main> sqrt_x = cfSqrt x
	*Main> x
	cf[42,5,1,6,1,4,3,6,1,1,3931940]
	*Main> sqrt_x
	cf[6,2,40,3,1,6,2,4,1,3]
	*Main> sqrt_x^2
	cf[42,5,1,6,1,4,3,6,2]	
	
## TODO
* Sanity checking; return useful error if user tries to construct CF with negative terms, take square root of negative number, et cetera.
* Fix problem with Fractional vs. Floating: currently, if `x` is of type `CF`, we can do `x+3.141` or `x*3.141` but not `x+pi` or `x*pi` et cetera.
* Integrate with other Haskell packages for high-precision and arbitrary-precision arithmetic: Data.Scientific, AERN, et cetera.