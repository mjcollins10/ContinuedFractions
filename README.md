# ContinuedFractions
A Haskell implementation of Gosper's algorithm for arithmetic on continued fractions. This implementation avoids all difficulties with infinite loops (which can occur if the algorithm is implemented naively). All computations and comparisons are done on the CF representation with integer arithmetic; conversion to float only happens if we explicitly convert a result. We also implement exponential, log, and trig functions.

We consider only *regular* CFs, i.e. all terms, except possibly the first, are greater than or equal to 1. See cfAlgorithm.tex for (many) more details.

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

	*Main> cfE = makeCF ([2, 1, 2] ++ (concat [ [1,1,4+2*k] | k <- [0..] ]))
	*Main> cfE            -- unlike pi, the terms of e=2.71828... have a simple pattern
	cf[2,1,2,1,1,4,1,1,6,1,1,8,1,1,10]
	*Main> 
	*Main> cfToTerms cfE  -- evaluates to list of Integers
	[2,1,2,1,1,4,1,1,6,1,1,8,1,1,10]
	*Main> cfToTermsWithin (2**(-64)) cfE
	[2,1,2,1,1,4,1,1,6,1,1,8,1,1,10,1,1,12,1,1,14,1,1,16]
	*Main> 
	*Main> cfToFloat cfE
	2.7182818284454013
	*Main> cfToFloatWithin (2**(-64)) cfE -- limited by float accuracy; last digit is wrong
	2.7182818284590455
	*Main> cfToFloatWithin (2**(-128)) cfE  
	2.7182818284590455
	*Main> cfToRatWithin (2**(-64)) cfE
	14013652689 % 5155334720
	*Main> cfToRatWithin (2**(-128)) cfE -- rational approximation to any desired accuracy
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

Note that there is no function which, given integer `n`, will simply return the first `n`  terms of a CF. To see why, consider asking for the first few terms of `sqrt2^2`. Any terminating computation can only make use of some finite prefix of the infinte list `[1,2,2,2 ...]`. But no such prefix is enough to rule out the possibility that the thing being squared is slightly less than the square root of 2; if that is the case, the first term should be 1. Otherwise it should be 2. So it is not always meaningful to ask for terms of a CF without reference to a degree of accuracy.

We have also implemented Gosper's algorithm for extracting the square root of a CF:

	*Main> x = floatToCF 42.1703
	*Main> sqrt_x = cfSqrt x
	*Main> x
	cf[42,5,1,6,1,4,3,6,1,1,3931940]
	*Main> sqrt_x
	cf[6,2,40,3,1,6,2,4,1,3]
	*Main> sqrt_x^2
	cf[42,5,1,6,1,4,3,6,2]	
	
	*Main> p x = 3*x^2 - 5*x - 1
	*Main> floatD = sqrt $ 5*5 + 4*3 -- discriminant of quadratic
	*Main> cfD    = cfSqrt $ makeCF [5*5 + 4*3]
	*Main> 
	*Main> p $ (5 + floatD)/(2*3)  -- quadratic formula
	0.0
	*Main> p $ (5 - floatD)/(2*3)  -- almost right
	-3.3306690738754696e-16
	*Main> 
	*Main> p $ (5 + cfD)/(2*3)
	cf[0]
	*Main> p $ (5 - cfD)/(2*3)  -- exactly right
	cf[0]
	
We can also compute exponentials, logs, and trig functions (see cfAlgorithm.tex for details of how this is implemented):

	*Main> cfExp (cfSqrt 2)
	cf[4,8,1,4,1,7,2,12,1,18]
	*Main> cfToFloat $ cfExp (cfSqrt 2)
	4.113250378715521
	*Main> exp (sqrt 2)
	4.1132503787829275
	
	*Main> cfToTermsWithin (1%(2^128)) cfPi -- infinite precision
	[3,7,15,1,292,1,1,1,2,1,3,1,14,2,1,1,2,2,2,2,1,84,2,1,1,15,3,13,1,4,2,6,6,104]
	*Main> 
	*Main> cfExp (2*cfPi)
	cf[535,2,29,2,5,1,2,1,6,4]
	*Main> (cfExp cfPi)^2
	cf[535,2,29,2,5,1,2,1,6,4]
	*Main> 
	*Main> cfLog cfPi
	cf[1,6,1,10,24,1,3,1,11]
	*Main> cfExp( cfLog cfPi )
	cf[3,7,15,1,292,1,5]
	*Main> cfLog (cfExp cfPi)
	cf[3,7,15,1,292,1,2]
	*Main> 
	*Main> cfCos (cfPi/3)
	cf[0,2]
	*Main> cfCos (cfPi/4) -- 1/(sqrt 2)
	cf[0,1,2,2,2,2,2,2,2,2,2,2,2,2,4]
	
## TODO
* Sanity checking; return useful error if user tries to construct CF with negative terms, take square root of negative number, et cetera.
* Make CF a `Floating` class
* Integrate with other Haskell packages for high-precision and arbitrary-precision arithmetic: Data.Scientific, AERN, et cetera.