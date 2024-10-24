# ContinuedFractions
A Haskell implementation of Gosper's algorithm for arithmetic on continued Fractions. All computations and comparisons are done on the CF representation; conversion to float only happens if we explicitly convert a result. See cfAlgorithm.tex for more details.
Sample usage:



	user@Users-MacBook-Pro ContinuedFractions % ghci
	GHCi, version 8.10.7: https://www.haskell.org/ghc/  :? for help
	Prelude> :load gosper.hs 
	[1 of 1] Compiling Main             ( gosper.hs, interpreted )
	Ok, one module loaded.
	*Main> sqrt2 = MakeCF (1:(cycle [2]))  -- CF is a wrapper for [Integer]
	*Main> piCF  = floatToCF pi            -- create CF from Numeric
	*Main> piCF                            -- show 8 terms by default
	[3,7,15,1,292,1,1,1]
	*Main> showNterms 15 piCF              -- view more terms
	[3,7,15,1,292,1,1,1,2,1,3,1,14,3,3]
	*Main> fromCF piCF                  -- convert to Float with default accuracy
	3.141592653589793
	*Main> evalCF 2 piCF               -- evaluate to given number of terms
	3.141509433962264
	*Main> sqrt2 + 3*piCF              -- arithmetic operators
	[10,1,5,4,1,2,1,7]
	*Main> sqrt2 < piCF                -- comparison operators
	True






Infinite loops are an inherent problem when computing with CFs; we need
infinitely many terms to know that sqrt2/sqrt2 == 1, since a finite number 
of terms is never enough to tell us that the numerator and denominator are
equal! In fact we need to read infinitely many terms of input just to get
the first term of output, since finitely many terms are not enough to tell
us if the numerator is larger or smaller than the denominator. In this 
version we deal with the problem in the crudest possible way, by just 
terminating computations that go on for a large number of iterations and
taking the closest approximation. This is hardly satisfactory, although it
gives correct answers in many cases -- i.e. when the correct answer is a 
rational number with reasonaby small denominator:

	*Main> piCF/piCF
	[1]
	*Main> sqrt2*sqrt2
	[2]

In a future version we will deal with this correctly, by letting the user
specify a threshold for how close two numbers must be to be considered
equal, and taking all computations to that much accuracy.
