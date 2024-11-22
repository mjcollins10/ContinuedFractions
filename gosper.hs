{-
 - Gosper's algorithm for arithmetic on CFs
 - with modifications to avoid infinite loops
 -}

import Data.Ratio -- get (%) operator for rational arithmetic

termToBound n =  (n%1, (n+1)%1) -- generalized internal representation of CF term
epsDefault = 1 % 2^32 -- default threshold for 'equality'
infinity :: Integer
infinity = 999999999
nobound = (1%1, infinity%1)
pmInfinity = (-infinity%1, infinity%1) 

-- range_ is min,max of *integer part* of bihomomorphic matrix (axy + bx +cy + d)/(exy + fx + gy + h)
-- as x,y vary independently from *zero* to infinity
-- 'normally' this is min,max of {a/e, b/f, c/g, d/h}
-- ratRange_ is min,max of bihomomorphic matrix
openceil n d = (div n d) + if (mod n d) == 0 then -1 else 0 -- if asymptotic upper bound is k, integer part is <= k-1
getmin n d = if d /= 0 then (div n d)      else (signum n)*infinity 
getmax n d = if d /= 0 then (openceil n d) else (signum n)*infinity 
getrat n d = if d /= 0 then (n%d)          else ((signum n)*infinity)%1 
range_ [numr,denr] | any (>0) denr && any (<0) denr && any (/= 0) numr = (-infinity,infinity) -- sign change in denominator
                   | otherwise = ( fromIntegral (minimum [ getmin n d | (n,d) <- zip numr denr , (n,d) /= (0,0) ]),
                                   fromIntegral (maximum [ getmax n d | (n,d) <- zip numr denr , (n,d) /= (0,0) ]) )

ratRange_ [numr,denr] | any (>0) denr && any (<0) denr && any (/= 0) numr = pmInfinity -- sign change in denominator
                      | otherwise = ( minimum [ getrat n d | (n,d) <- zip numr denr , (n,d) /= (0,0) ],
                                      maximum [ getrat n d | (n,d) <- zip numr denr , (n,d) /= (0,0) ] )

-- aside from the leading term, can assume all terms of a CF are >= 1;
-- to compute range of a bihomomorphic matrix as x,y vary from 1 to infinity
-- it is convenient to shift xx,yy = x-1,y-1 and find range assuming xx,yy > 0
shift [a,b,c,d] = [a, a+b, a+c, a+b+c+d]

-- find min,max value of matrix subject to bounds on x,y
range (matrix, boundX, boundY) = range_ (map shift matrixWithBounds)
                              where matrixWithBounds = (substituteY boundY (substituteX boundX matrix))
ratRange (matrix, boundX, boundY) = ratRange_ (map shift matrixWithBounds)
                              where matrixWithBounds = (substituteY boundY (substituteX boundX matrix))

-- if we know that the floor of x equals n, we can make the 
-- substitution x <- n + 1/x (and now x represents the next term of output);
-- otherwise just update bounds, leaving matrix the same; new bound will always be tighter
isTerm (lo,hi) = (denominator lo == 1) && (denominator hi == 1) && ((numerator hi == 1 + numerator lo) || (numerator lo == infinity))
ingestX termOrBound (matrix,boundX,boundY) | isTerm termOrBound = (substituteX termOrBound matrix , nobound, boundY)
                                           | otherwise          = (matrix, termOrBound, boundY)

ingestY termOrBound (matrix,boundX,boundY) | isTerm termOrBound = (substituteY termOrBound matrix , boundX, nobound)
                                           | otherwise          = (matrix, boundX, termOrBound)

-- transform bihomomorphic matrix (axy + bx +cy + d)/(exy + fx + gy + h)
-- by substitution x <- n/q + r/(sx); i.e. x ranges from n/q to n/q + r/s
-- if we know that the floor of x equals n, we have q == r == s == 1
substituteX (lo,hi) [[a,b,c,d],[e,f,g,h]] | all (==0) [a,b,e,f]   = [[0,0,c,d],[0,0,g,h]] -- no x terms in matrix
                                          | (lo,hi) == nobound    = [[a,b,c,d],[e,f,g,h]] -- nothing changes
                                          | n == infinity         = [[0,0,a,b],[0,0,e,f]] -- limit as x -> \infty
                                          | (lo,hi) == pmInfinity = [[-a, -b, 2*a, 2*b],[-e, -f, 2*e, 2*f]] 
                                          | otherwise             = [[n*a*s + c*q*s, n*b*s + d*q*s, a*q*r, b*q*r],
                                                                   [n*e*s + g*q*s, n*f*s + h*q*s, e*q*r, f*q*r]]
                                              -- rewrite the bound (lo,hi) as (lo, delta)==(lo,hi-lo)
                                              where  (n,q) = (numerator lo, denominator lo) 
                                                     (r,s) = (numerator (hi-lo), denominator (hi-lo))

substituteY (lo,hi) [[a,b,c,d],[e,f,g,h]] | all (==0) [a,c,e,g] = [[0,b,0,d],[0,f,0,h]] -- no y terms in matrix
                                          | (lo,hi) == nobound  = [[a,b,c,d],[e,f,g,h]] -- nothing changes
                                          | n == infinity       = [[0,a,0,c],[0,e,0,g]] -- limit as y -> \infty
                                          | (lo,hi) == pmInfinity = [[-a, 2*a, -c, 2*c],[-e, 2*e, -g, 2*f]] 
                                          | otherwise           = [[n*a*s + b*q*s, a*q*r, n*c*s + d*q*s, c*q*r],
                                                                   [n*e*s + f*q*s, e*q*r, n*g*s + h*q*s, g*q*r]]
                                              -- rewrite the bound (lo,hi) as (lo, delta)==(lo,hi-lo)
                                              where  (n,q) = (numerator lo, denominator lo)  
                                                     (r,s) = (numerator (hi-lo), denominator (hi-lo))

-- when we know that the next term of output is n, the matrix representing the rest of the output
-- is (numerator/denominator - n)^{-1}
produce n ([num, den], boundX, boundY) = ( [den, [j-n*k | (j,k) <- zip num den]], boundX, boundY )

-- finite (i.e. rational) CF is implicitly terminated by infinite list of infinite terms
head_ [] = (infinity%1, infinity%1)
head_ xs = head xs
tail_ [] = []
tail_ xs = tail xs

-- one iteration of Gosper's algorithm:
-- produce the next term of output if we can; otherwise read both x and y and produce range
-- current state is ( (unread part of x, unread part of y),
--                    ((current bihomomorphic matrix, bound on x, bound on y), last output) )
-- ingesting term changes matrix and sets bound to [1,Inf]
-- ingesting bound does nothing to matrix, just updates bound
gosper ((x,y),(curM,_))  | low == hi  = ((x,y), (produce hi curM, termToBound hi))  -- produce another term of output 
                         | otherwise  = ((tail_ x,tail_ y), (ingestY (head_ y) (ingestX (head_ x) curM), ratRange curM)) -- get next x,y
                              where (low,hi) = range curM

-- always start by ingesting leading terms
arithCF_ x y initM = iterate gosper ((tail_ x, tail_ y), ( (ingestY (head_ y) (ingestX (head_ x) initM)) , ratRange initM)) 
-- iterate as long as we do not see an infinite term 
-- extract ouput cf (i.e. list of bounds) from sequence of computational sates
notInf (_, (_, bn)) = bn /= (infinity%1,infinity%1)
arithCF initialMatrix x y = map (snd.snd) (takeWhile notInf (arithCF_ x y initialMatrix) )

{-
 - turn continued fractions into a type with operator overloading
 - mathematically, a CF is a sequence of integer terms [z_0, z_1, z_2, ...]
 - internally, a CF is a sequence of bounds on the 'tails' [z_k, z_{k+1}, ...]
 - when we get a bound of the form (n,n+1) we know that z_k == n
 - and can go on to bounding [z_{k+1}, z_{k+2}, ...]
 -}

newtype CF = MakeCF_ { getCF_ :: [(Ratio Integer, Ratio Integer)] }
makeCF terms = MakeCF_ (map termToBound terms)

-- matrix initializations for arithmetic
addCF_ = arithCF ( [[0,1,1,0],[0,0,0,1]],  pmInfinity, pmInfinity )
subCF_ = arithCF ( [[0,1,-1,0],[0,0,0,1]], pmInfinity, pmInfinity )
mulCF_ = arithCF ( [[1,0,0,0],[0,0,0,1]],  pmInfinity, pmInfinity )
divCF_ = arithCF ( [[0,1,0,0],[0,0,1,0]],  pmInfinity, pmInfinity )

instance Num CF where
  fromInteger n  = makeCF [n]
  x + y = MakeCF_ (addCF_ (getCF_ x) (getCF_ y))
  x - y = MakeCF_ (subCF_ (getCF_ x) (getCF_ y))
  x * y = MakeCF_ (mulCF_ (getCF_ x) (getCF_ y))
  abs x | x >= 0    = x
        | otherwise = -x
  signum x | x == 0    = 0
           | x > 0     = 1
           | otherwise = -1

instance Fractional CF where
  x / y          = MakeCF_ (divCF_ (getCF_ x) (getCF_ y))
  fromRational x = floatToCF x

instance Eq CF where
  -- true iff abs(x-y) <= epsDefault
  x == y = containedIn 0 (upperLower (extractFiniteCF_ epsDefault (x-y)))
instance Ord CF where
  -- true iff y >= x - epsDefault
  x <= y = below 0  (upperLower (extractFiniteCF_ epsDefault (y-x)))
containedIn t (lo, hi) = t >= (min lo hi) && t <= (max lo hi)
below       t (lo, hi) = t <= (max lo hi)
above       t (lo, hi) = t >= (min lo hi)

{-
 - convert among CF, [Integer], and Numeric
 - names ending with "_" indicate functions operating on [(Ratio Integer, Ratio Integer)]
 - (i.e. lists of bounds); these are intended to be private
 -}

floatToCF x           = makeCF (floatToCFterms x)
cfToTerms x           = map fromIntegral (display_ (extractFiniteCF_ epsDefault x))
cfToTermsWithin eps x = map fromIntegral (display_ (extractFiniteCF_ eps      x))
cfToFloat x           = fracEval $ cfToTerms x
cfToFloatWithin eps x = fracEval $ cfToTermsWithin eps x
cfToRat x             = ratEval $ cfToTerms x
cfToRatWithin eps x   = ratEval $ cfToTermsWithin eps x
eqWithin eps x y      = containedIn 0 (upperLower (extractFiniteCF_ eps (x-y)))

floatToCFterms x | x == floor_x   = [floor x]
                 | otherwise      = (floor x):(floatToCFterms (1/(x - floor_x)))
                    where floor_x = fromIntegral (floor x)

-- evaluate a finite sequence of terms
fracEval []     = fromIntegral infinity
fracEval (a:[]) = a
fracEval (a:as) = a + 1/(fracEval as)

ratEval []     = infinity % 1
ratEval (a:[]) = a % 1
ratEval (a:as) = (a%1) + 1/(ratEval as)

-- convert a finite list of bounds to a finite list of terms
display_ [] = []
display_ (bd:bds) | isTerm bd = (numerator $ fst bd):(display_ bds)
                  | null bds  = [floor $ snd bd] -- final bound is never resolved to term, so estimate
                  | otherwise = display_ bds     -- skip this bound since the next will be tighter

{-
 - internal functions for extracting finite approximations within given accuracy
 -}

-- given possibly infinite list of bounds, generate finite prefixes
-- with redundant bounds removed (i.e. 'reduced' prefixes)
reduce ([], bd:bds) = ([bd], bds)
reduce (cf, [])     = (cf ++ [(infinity%1,infinity%1)], [])              -- finite CF terminated by infinity 
reduce (cf, bd:bds) | isTerm $ last cf = (cf              ++ [bd], bds)  -- go on to next term
                    | otherwise        = ((removeLast cf) ++ [bd], bds)  -- improve bound on current term
removeLast cf = reverse (drop 1 (reverse cf))

-- get upper and lower bounds on value of a *finite* continued fraction
-- cf is generated by iterating 'reduce' on a potentially infinite list of bounds
-- cf might end with an arbitrary bound; otherwise bounds look like (n,n+1)
upperLower [] = (infinity%1, infinity%1)
upperLower cf = (fracEval cfLo, fracEval cfHi)
             where cfStart = map fst (removeLast cf)
                   cfLo = cfStart ++ [fst $ last cf] -- eval using lowest possible value for tail of continued fraction
                   cfHi = cfStart ++ [snd $ last cf] -- eval using highest possible value for tail of continued fraction
-- get width of interval which must contain actual value
delta cf = abs ((fst limits) - (snd limits))
             where limits = upperLower cf

-- evaluate CF up to given accuracy
extractFiniteCF_ eps (MakeCF_ bounds) = head (dropWhile (unfinished (toRational eps)) approximations) -- return first sufficient approximation
                                         where approximations = map fst (iterate reduce ([head validBounds], tail validBounds))
                                               validBounds = filter (/= pmInfinity) bounds
-- current finite view of cf is unfinished if value is not yet bounded tightly enough
unfinished eps cf = (delta cf) > eps

-- display CFs to default accuracy
-- prepend "cf" so it is clear that the value being shown is not of type [Integer]
-- do not show infinite term at end of finite CF
instance Show CF where
  show x = "cf" ++ (show ( filter (/= infinity) $ display_ (extractFiniteCF_ epsDefault x)))

{-
 - TODO: (piCF + 3.14159) works but (piCF + pi) does not;
 - problem is Fractional vs. Floating
-}

