# ContinuedFractions
A Haskell implementation of Gosper's algorithm for arithmetic on continued fractions. All computations and comparisons are done on the CF representation with integer arithmetic; conversion to float only happens if we explicitly convert a result. See cfAlgorithm.tex for (many) more details.

Sample usage:

	user@Users-MacBook-Pro ContinuedFractions % ghci
	GHCi, version 8.10.7: https://www.haskell.org/ghc/  :? for help
	Prelude> :load gosper.hs 
	[1 of 1] Compiling Main             ( gosper.hs, interpreted )
	Ok, one module loaded.
	*Main> sqrt2 = makeCF (1:(cycle [2])) -- create CF from list of integer terms
	*Main> sqrt2
	cf[1,2,2,2,2,2,2,2,2,2,2,2,2,2]
	*Main>:type sqrt2
	sqrt2 :: CF
	*Main> 
	
By default, we display enough terms of a CF to get accuracy within 2^(-32); Haskell's lazy evaluation and infinite data structures enable us to attain arbitrary accuracy. We prepend "cf" to make it obvious that the value being shown is not of type [Integer]. CF is an instance of Num, Fractional, Ord, and Eq:

	*Main> pie = floatToCF pi -- create CF from Numeric type
	*Main> pie
	cf[3,7,15,1,292,1,1]
	*Main> (pie + sqrt2)/3
	cf[1,1,1,12,1,15,2,29,3]
	*Main> pie < sqrt2
	False
	*Main> sqrt2 * sqrt2
	cf[2]
