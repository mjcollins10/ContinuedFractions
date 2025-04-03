{-
 - Gosper's algorithm for arithmetic on CFs
 - with modifications to avoid infinite loops
 -}

import Data.Ratio -- get (%) operator for rational arithmetic

termToBound n =  (n%1, (n+1)%1) -- generalized internal representation of CF term n
-- a bound of the form (n,n+1) gives us n as the next CF term
isTerm (lo,hi) = (denominator lo == 1) && (denominator hi == 1) && (hi == 1 + lo || lo == ratInfinity)
infinity :: Integer
infinity = 999999999999
ratInfinity = infinity%1
epsDefault = 1%(2^32) -- default threshold for 'equality'
nobound = (1%1, infinity%1)
pmInf = (-infinity%1, infinity%1) 

-- range_ is min,max of *integer part* of bihomomorphic matrix (axy + bx +cy + d)/(exy + fx + gy + h)
-- as x,y vary independently from *zero* to infinity
-- with no sign change in denominator this is min,max of {a/e, b/f, c/g, d/h}
-- ratRange_ is min,max of bihomomorphic matrix
openceil n d   = (div n d) + if (mod n d) == 0 then -1 else 0 -- if asymptotic upper bound is k, integer part is <= k-1
getmin adj n d = if d /= 0 then (div n d)      else adj*(signum n)*infinity 
getmax adj n d = if d /= 0 then (openceil n d) else adj*(signum n)*infinity 
getrat adj n d = if d /= 0 then (n%d)          else (adj*(signum n)*infinity)%1 
range_ [numr,denr] | any (>0) denr && any (<0) denr && any (/= 0) numr = (-infinity,infinity) -- sign change in denominator
                   | otherwise = ( fromIntegral (minimum [ getmin adj n d | (n,d) <- zip numr denr , (n,d) /= (0,0) ]),
                                   fromIntegral (maximum [ getmax adj n d | (n,d) <- zip numr denr , (n,d) /= (0,0) ]) )
                                      where adj = if all (<= 0) denr && any (<0) denr then (-1) else 1 -- negative as denominator approaches zero

ratRange_ [numr,denr] | any (>0) denr && any (<0) denr && any (/= 0) numr = pmInf -- sign change in denominator
                      | otherwise = ( minimum [ getrat adj n d | (n,d) <- zip numr denr , (n,d) /= (0,0) ],
                                      maximum [ getrat adj n d | (n,d) <- zip numr denr , (n,d) /= (0,0) ] )
                                      where adj = if all (<= 0) denr && any (<0) denr then (-1) else 1 -- negative as denominator approaches zero

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
ingestX termOrBound (matrix,boundX,boundY) | isTerm termOrBound = (substituteX termOrBound matrix , nobound, boundY)
                                           | otherwise          = (matrix, termOrBound, boundY)

ingestY termOrBound (matrix,boundX,boundY) | isTerm termOrBound = (substituteY termOrBound matrix , boundX, nobound)
                                           | otherwise          = (matrix, boundX, termOrBound)

-- transform bihomomorphic matrix (axy + bx +cy + d)/(exy + fx + gy + h)
-- by substitution x <- n/q + r/(sx); i.e. x ranges from n/q to n/q + r/s
-- if we know that the floor of x equals n, we have q == r == s == 1
substituteX (lo,hi) [[a,b,c,d],[e,f,g,h]] | all (==0) [a,b,e,f]   = [[0,0,c,d],[0,0,g,h]] -- no x terms in matrix
                                          | (lo,hi) == nobound    = [[a,b,c,d],[e,f,g,h]] -- nothing changes; 1 <= x <= \infty
                                          | n == infinity         = limXinf [[a,b,c,d],[e,f,g,h]]
                                          | hi >= (infinity%1)    = [[q_*a, q_*b, n_*a+q_*c, q_*d+n_*b], -- x <- lo - 1 + x
                                                                     [q_*e, q_*f, n_*e+q_*g, q_*h+n_*f]]
                                          | (lo,hi) == pmInf      = [[-a, -b, 2*a, 2*b],[-e, -f, 2*e, 2*f]] -- will this ever happen?
                                          | otherwise             = [[n*a*s + c*q*s, n*b*s + d*q*s, a*q*r, b*q*r],
                                                                     [n*e*s + g*q*s, n*f*s + h*q*s, e*q*r, f*q*r]]
                                              -- rewrite the bound (lo,hi) as (lo, delta)==(lo,hi-lo)
                                              where  (n,q) = (numerator lo, denominator lo) 
                                                     (r,s) = (numerator (hi-lo), denominator (hi-lo))
                                                     (n_, q_) = (numerator (lo-1), denominator (lo-1))

substituteY (lo,hi) [[a,b,c,d],[e,f,g,h]] | all (==0) [a,c,e,g] = [[0,b,0,d],[0,f,0,h]] -- no y terms in matrix
                                          | (lo,hi) == nobound  = [[a,b,c,d],[e,f,g,h]] -- nothing changes
                                          | n == infinity       = limYinf [[a,b,c,d],[e,f,g,h]] 
                                          | hi >= (infinity%1)  = [[q_*a, n_*a+q_*b, q_*c, q_*d+n_*c], -- y <- lo - 1 + y
                                                                   [q_*e, n_*e+q_*f, q_*g, q_*h+n_*g]] 
                                          | (lo,hi) == pmInf    = [[-a, 2*a, -c, 2*c],[-e, 2*e, -g, 2*f]] 
                                          | otherwise           = [[n*a*s + b*q*s, a*q*r, n*c*s + d*q*s, c*q*r],
                                                                   [n*e*s + f*q*s, e*q*r, n*g*s + h*q*s, g*q*r]]
                                              -- rewrite the bound (lo,hi) as (lo, delta)==(lo,hi-lo)
                                              where  (n,q) = (numerator lo, denominator lo)  
                                                     (r,s) = (numerator (hi-lo), denominator (hi-lo))
                                                     (n_, q_) = (numerator (lo-1), denominator (lo-1))

-- deal with various special cases of computing limits as x or y approaches infinity
limXinf [[a,b,c,d],[e,f,g,h]] | (a,b) /= (0,0) && (e,f) /= (0,0) = [[0,0,a,b],[0,0,e,f]] -- limit of (axy+bx)/(exy+fx) as x -> \infty
                              | (a,b) == (0,0)                   = [[0,0,0,0],[0,0,0,1]] -- we know (e,f) \=0, so denom -> \infty
                              | (a,c) == (0,0) && (e,g) == (0,0) = [[0,0,0,(signum b)*infinity],[0,0,0,signum h]] -- no y terms in matrix, constant denominator
                              | otherwise                        = [[0,0,0,-infinity],[0,0,0,1]] -- use -infinity to denote invalid result of div by zero

limYinf [[a,b,c,d],[e,f,g,h]] | (a,c) /= (0,0) && (e,g) /= (0,0) = [[0,a,0,c],[0,e,0,g]] -- limit of (axy+cy)/(exy+gy) as y -> \infty
                              | (a,c) == (0,0)                   = [[0,0,0,0],[0,0,0,1]] -- we know (e,g) /=0, so denom -> \infty
                              | (a,b) == (0,0) && (e,f) == (0,0) = [[0,0,0,(signum c)*infinity],[0,0,0,signum h]] -- no x terms in matrix, constant denominator
                              | otherwise                        = [[0,0,0,-infinity],[0,0,0,1]] -- use -infinity to denote invalid result of div by zero

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
--                    (current bihomomorphic matrix, bound on x, bound on y) )
-- ingesting term changes matrix and sets bound to [1,Inf]
-- ingesting bound does nothing to matrix, just updates bound
gosper x y curM  | low == hi  = (termToBound hi):(gosper x y (produce hi curM))   -- produce another term of output 
                 | otherwise  = (ratRange curM):(gosper (tail_ x) (tail_ y) (ingestY (head_ y) (ingestX (head_ x) curM))) -- get next x,y
                              where (low,hi) = range curM

notInf bn = bn /= (infinity%1,infinity%1)
arithCF_ initM x y = takeWhile notInf (gosper (tail_ x) (tail_ y) (ingestY (head_ y) (ingestX (head_ x) (initM, pmInf, pmInf))))

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
addCF_ = arithCF_  [[0,1,1,0],[0,0,0,1]]
subCF_ = arithCF_  [[0,1,-1,0],[0,0,0,1]]
mulCF_ = arithCF_  [[1,0,0,0],[0,0,0,1]]
divCF_ = arithCF_  [[0,1,0,0],[0,0,1,0]]

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
  x == y = containedIn 0 (lowerUpper (extractFiniteCF_ epsDefault (x-y)))
instance Ord CF where
  -- true iff y >= x - epsDefault
  x <= y = below 0  (lowerUpper (extractFiniteCF_ epsDefault (y-x)))
containedIn t (lo, hi) = t >= lo && t <= hi
below       t (lo, hi) = t <= hi
above       t (lo, hi) = t >= lo

{-
 - convert among CF, [Integer], and Numeric
 - names ending with "_" indicate functions operating on [(Ratio Integer, Ratio Integer)]
 - (i.e. lists of bounds); these are intended to be private
 -}

floatToCF x           = makeCF (floatToCFterms x)
cfToTerms x           = map fromIntegral (display_ (extractFiniteCF_ epsDefault x))
cfToTermsWithin eps x = map fromIntegral (display_ (extractFiniteCF_ eps        x))
cfToFloat x           = fracEval $ cfToTerms x
cfToFloatWithin eps x = fracEval $ cfToTermsWithin eps x
cfToRat x             = ratEval $ cfToTerms x
cfToRatWithin eps x   = ratEval $ cfToTermsWithin eps x
eqWithin eps x y      = containedIn 0 (lowerUpper (extractFiniteCF_ eps (x-y)))

floatToCFterms x | x == floor_x   = [floor x]
                 | otherwise      = (floor x):(floatToCFterms (1/(x - floor_x)))
                    where floor_x = fromIntegral (floor x)

-- evaluate a finite sequence of terms
fracEval []     = fromIntegral infinity
fracEval (a:[]) = a
fracEval (a:as) = a + 1/(fracEval as)

ratEval []     = ratInfinity
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
removeRedundantBounds ([], bd:bds) = ([bd], bds)
removeRedundantBounds (cf, [])     = (cf ++ [(infinity%1,infinity%1)], [])              -- finite CF terminated by infinity 
removeRedundantBounds (cf, bd:bds) | isTerm $ last cf = (cf              ++ [bd], bds)  -- go on to next term
                                   | otherwise        = ((init cf) ++ [bd], bds)  -- improve bound on current term

-- get upper and lower bounds on value of a *finite* continued fraction
-- cf is generated by iterating 'removeRedundantBounds' on a potentially infinite list of bounds
-- cf might end with an arbitrary bound; otherwise bounds look like (n,n+1)
lowerUpper [] = pmInf
lowerUpper cf = inOrder (fracEval cfLo, fracEval cfHi)
             where cfStart = map fst (init cf) -- a list of integer terms
                   cfLo = cfStart ++ [fst $ last cf] -- eval using lowest possible value for tail of continued fraction
                   cfHi = cfStart ++ [snd $ last cf] -- eval using highest possible value for tail of continued fraction
inOrder (a,b) = if a < b then (a,b) else (b,a)
-- get width of interval which must contain actual value
delta cf = hi - lo
             where (lo, hi) = lowerUpper cf

-- evaluate CF up to given accuracy
extractFiniteCF_ eps (MakeCF_ bounds) = head (dropWhile (unfinished (toRational eps)) reducedPrefixes) -- return first sufficient approximation
                                         where reducedPrefixes = map fst (iterate removeRedundantBounds ([], validBounds))
                                               validBounds = filter (/= pmInf) bounds
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
 -
 - TODO: negative exponents: x**y 
-}

{-
 - Extract square root of a CF
 -}

-- Given bihomomorphic M, return the homomorphic M_r
-- which we get by fixing x=r
lowestterms [[p,q],[r,s]] = [[div p c, div q c], [div r c, div s c]]
                              where c = gcd (gcd p q) (gcd r s)
fixvar [[a,b,c,d],[e,f,g,h]] x | [[a,b],[e,f]] == [[0,0],[0,0]] = [[c,d],[g,h]] -- x terms already gone
                               | x == (infinity%1) = [[a,b], [e,f]] -- limit as x -> \infty
                               | otherwise = lowestterms [[a*xn+c*xd, b*xn+d*xd], [e*xn+g*xd, f*xn+h*xd]]
                                   where (xn, xd) = (numerator x, denominator x)

-- evaluate a homomorphic matrix as a rational function
evalMat    [[p,q],[r,s]] y = (p*y+q)%(r*y+s)
evalMatRat [[p,q],[r,s]] y = (p*n+q*d)%(r*n+s*d)
                               where (n,d) = (numerator y, denominator y)-- y is already a ratio

-- binary search to get floor of fixed point of *self-inverse* homographic M;
-- i.e. find y such that y equals either floor M(y) or 1 + floor M(y);
-- then the next term is floor M(y)
-- make use of fact that, for any y, fixpoint is between y and M(y)
-- search limited to where M(y) > 0: y > -s/r
hmat a b c = [[a,b],[c,-a]] -- for testing
fixpoint [[p,q],[r,s]] = fixpoint_ [[p,q],[r,s]] firstGuess
                          where firstGuess = if r > 0 then max 1 (1 + ceiling (-s%r)) else 1 
fixpoint_ mat guess | mfloor == guess || mceil == guess = mfloor
                    -- handle annoying case where mval is actually an integer; otherwise
                    -- for instance mat = [[0,2],[1,0]] cycles between guess == 1,2
                    | mvalDen==1 && (mvalNum == guess + 1 || mvalNum == guess - 1) = min mvalNum guess
                    | otherwise = fixpoint_ mat newguess 
                        where mval   = evalMat mat guess
                              mfloor = floor mval
                              mceil  = ceiling mval
                              (mvalNum, mvalDen) = (numerator mval, denominator mval)
                              newguess = if mfloor > guess then ceiling ((guess + mceil)%2) 
                                          else floor ((guess + mfloor)%2) -- new guess halfway between

-- rational estimates of fixpoint
-- binary search until | y - M(y) | < epsilon
-- splitting binary search with mediant or average leads to very large numerators and denominators
-- so we instead find the simplest dyadic rational in the search interval
fixpointRat_ eps mat guess | abs (guess - mval) < eps = (min guess mval, max guess mval)
                           | otherwise                = fixpointRat_ eps mat (dyadicBetween guess mval)
                                where mval = evalMatRat mat guess

-- return a range (lo,hi) which contains the fixed point of (px+q)/(rx+s), with hi - lo < eps
fixpointRat :: Integral a => Ratio a -> [[a]] -> (Ratio a, Ratio a)
fixpointRat eps [[p,q],[r,s]] = fixpointRat_  eps [[p,q],[r,s]] firstGuess
                                  where firstGuess = ((abs p)+(abs q))%1-- if r > 0 then max 1 (1 + (-s%r)) else (1%1) 

isint rat = (denominator rat) == 1
dyadicBetween lo hi | hi < lo = dyadicBetween hi lo
                    | (ceiling lo) <  (floor hi) = integerBetween (ceiling lo) (floor hi)
                    | (ceiling lo) == (floor hi) = eqCase lo hi
                    | otherwise                  = ((floor lo)%1) + (between lo_ hi_)
                        where lo_ = lo - (fromIntegral (floor lo))
                              hi_ = hi - (fromIntegral (floor lo))

eqCase lo hi | not (isint lo || isint hi) = (floor hi)%1 -- unique integer strictly between
             | isint lo  = lo + (approxDiff (hi - lo))
             | otherwise = hi - (approxDiff (hi - lo)) -- isint hi
-- dyadic approximation; returns something positive and strictly less than delta
approxDiff d = if d > (1%2) then (1%2) else (approxDiff (2*d))/2

-- called only with lo < hi and 2 or more integers between
integerBetween lo hi | hi == lo + 1 = (lo%1) + (1%2)
                     | otherwise    = (floor ((lo+hi)%2))%1

-- lo, hi are in the interval [0,1]; find dyadic rational strictly between
-- proof of termination: difference between arguments doubles on each recursive call
between lo hi | lo < (1%2) && hi > (1%2) = (1%2)
              | hi <= (1%2) = (between (2*lo) (2*hi))/2
              | otherwise = (1%2) + (between (2*lo-1) (2*hi-1))/2

-- will always need to ingest first term of x, so just do it
-- iteration assumes all terms >= 1
cfSqrt (MakeCF_ x) =  if (MakeCF_ x) < 1 then 1/(cfSqrt (1/(MakeCF_ x))) else MakeCF_ $ cfSqrtIter ( ingestX (head_ x) ( [[0,1,0,0], [0,0,1,0]], nobound, nobound ) ) (tail_ x) 
-- advance to next stage of square-root computation
-- if floor of fixed point of mat does not depend on x, we can get next
-- term of output; else ingest another term of x into mat
-- must output ambiguous terms to prevent stalling (see cfAlgorithm.tex)
cfSqrtIter mat x | all (==0) (m!!1) = [] -- have reached end of computing rational result
                 | y <= 0 = []
                 | matHasFixpoint = (termToBound y):(cfSqrtIter (produce y (ingestY (termToBound y) mat)) x) 
                 | otherwise      = yBound:(cfSqrtIter (ingestX (head_ x) mat) (tail_ x)) -- output ambiguous term
                      where y   = fixpoint (fixvar m xLo)
                            yHi = fixpoint (fixvar m xHi) 
                            (m, boundX, boundY) = mat
                            (xLo, xHi) = boundX
                            matHasFixpoint = y == yHi
                            -- if floor of fixpoint is undetermined, generate ambiguous terms
                            eps = min (1%3) (xHi - xLo) -- match accuracy of boundX 
                            yBound =  checkForNegFixpoint (fixpointRat eps (fixvar m xLo)) (fixpointRat eps  (fixvar m xHi)) 
                            -- true fixpoint can be irrational, need rational bounds: tight enough to always converge
                            -- so match accuracy of boundX

-- negative fixpoint means y -> \infty as x -> \infty; see cfAlgorithm.tex
checkForNegFixpoint (w,x) (y,z) = if minAll > 0 then (minAll, maxAll) else (maxAll, infinity%1)
                                    where (minAll, maxAll) = (min w y, max x z) -- the normal case

{- 
 - implement Taylor series for exp(x)
 - eventually will extend to trig and log functions
 -}

cfE = makeCF $ [2, 1, 2] ++ (concat [ [1,1,4+2*k] | k <- [0..] ])
cfSqrtE = makeCF $ [1, 1] ++ (concat [ [1, 1, 5+4*k] | k <- [0..]])
-- rewrite exp(n+r) as e^n * e^r where n is integer and abs r < 1
cfExp x | floorXint > 0 = (cfE^floorXint)*(cfExp_ (x - floorXnum))
        | floorXint < 0 = (cfExp_ (x - floorXnum))/(cfE^(abs floorXint))
        | otherwise  = cfExp_ x
            where floorXint =  nearestInt x
                  floorXnum =  fromIntegral floorXint
-- take bounds until we have an integer close to x
nearestInt (MakeCF_ bounds) = getInt (head (dropWhile tooWide bounds))
-- bound is too wide if interval contains more than one integer
tooWide (lo, hi) = hi > lo + 1
-- get an integer n such that abs(x-n) < 1 for all x in (lo, hi)
getInt (lo, hi) = if isTerm (lo,  hi) then (numerator lo) else floor hi

-- error term for Taylor polynomial of degree n, assuming abs x <= 1
errorTerm n = 3%(product [1..n+1])
-- represent Taylor polynomial as composition of bihomographic matrices
m n x y = arithCF_ [[1,0,0,n],[0,0,0,n]] x y -- 1 + x*y/n
funcs x = [m n x | n <- [1..]]
compose = foldr (.) id
-- ordinary take has type Int -> [a] -> [a], which is problematic
take_ _ [] = []
take_ 0 _  = []
take_ k (a:as) = a:(take_ (k-1) as)
-- optimized implementation of 1 + x + (sum [(x^k)/(fromIntegral $ (product [1..k])) | k <- [2..n]]) 
-- write as 1 + x*( 1 + (x/2)*( 1 + (x/3)* ...
taylor n x = MakeCF_ $ compose (take_ n (funcs (getCF_ x))) $ (getCF_ (makeCF [1]))


-- given a CF representation of a real number x, get a sequence of intervals converging to x
-- note these need not be nested
getIntervals (MakeCF_ bounds) = map lowerUpper reducedPrefixes 
                                   where reducedPrefixes = map fst (iterate removeRedundantBounds ([], validBounds))
                                         validBounds = filter (/= pmInf) bounds
-- expand intervals with error term
widen eps (lo, hi) = (lo-eps, hi+eps)
-- given a sequence of nested intervals whose intersection contains x, extract CF expansion of x
extractNested_ _ [] = []
extractNested_ (lo, hi) ((lo_, hi_):as) = nextInterval:(extractNested_ nextInterval as)
                                            where nextInterval = (max lo lo_, min hi hi_)
extractNested intervals = extractNested_ pmInf intervals

-- intervalsToCF assumes nested input
determinesNextTerm (lo,hi) = isTerm (lo,hi) || (floor lo) == (floor hi)
intervalToTerm     (lo,hi) = floor lo
intervalsToCF_ _ [] = []
-- mat extracts the terms we already know; i.e. if the interval (lo,hi) tell us that the next term is 3,
-- the following term comes from the interval (1/(hi-3), 1/(lo-3)) et cetera
-- must generate ambiguous terms since we cannot guarantee there will ever be an unambiguous bound
intervalsToCF_ mat (b:bs) = if determinesNextTerm transformedInterval 
                            then (termToBound nextTerm):(intervalsToCF_ newmat (b:bs)) 
                            else    transformedInterval:(intervalsToCF_ mat     bs) -- ambiguous bound in CF
                               where [[p,q],[r,s]] = mat
                                     (lo, hi) = b
                                     transformedInterval = inOrder (evalMatRat mat hi, evalMatRat mat lo)
                                     nextTerm = intervalToTerm transformedInterval
                                     newmat = [[r, s], [p - nextTerm*r, q - nextTerm*s]] -- x <- 1/(x-nextTerm)
intervalsToCF intervals = MakeCF_ ( intervalsToCF_ [[1,0], [0,1]] intervals )

taylorIntervals deg x = getIntervals (taylor deg x)
taylorApproximations deg x = extractNested $ map (widen (errorTerm deg)) (taylorIntervals deg x)
wide deg (lo,hi) = hi - lo > 3*(errorTerm deg) -- width is always at least 2*error
-- when error term becomes larger than uncertainty in computing polynomial, move to higher degree
-- but always take at least one
taylorApproxLimited deg x = (head aprxmtns):(takeWhile (wide deg) (tail aprxmtns))
                             where aprxmtns = taylorApproximations deg x
cfExp_ x = intervalsToCF (extractNested $ concat [taylorApproxLimited deg x | deg <- [4..]])

