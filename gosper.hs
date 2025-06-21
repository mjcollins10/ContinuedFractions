{-
 - Gosper's algorithm for arithmetic on CFs
 - with modifications to avoid infinite loops
 -}

import Data.Ratio -- get (%) operator for rational arithmetic

termToBound n =  (n%1, (n+1)%1) -- generalized internal representation of CF term n
-- a bound of the form (n,n+1) gives us n as the next CF term
isTerm (lo,hi) = (denominator lo == 1) && (denominator hi == 1) && (hi == 1 + lo || lo == ratInfinity)
boundToTerm (lo, hi) = numerator lo
infinity :: Integer
infinity = 999999999999
ratInfinity = infinity%1
epsDefault = 1%(2^32) -- default threshold for 'equality'
nobound = (1%1, infinity%1)
pmInf = (-infinity%1, infinity%1) 
intersect (lo, hi) (lo_, hi_) = (max lo lo_, min hi hi_)
-- given bounds on x, get bounds on x' where x = n + 1/x'
invert n (lo, hi) | n >= ratInfinity = nobound
                  | otherwise = (max (1/(hi - n)) (1%1), if lo <= n then ratInfinity else 1/(lo-n))

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
-- substitution x <- n + 1/x (and now x represents the tail of the input)
-- otherwise just update bounds, leaving matrix the same; new bound will always be tighter
ingestX interval (matrix,boundX,boundY) | isTerm interval = (substituteX interval matrix, invert n boundX, boundY)
                                        | otherwise       = (matrix, intersect boundX interval, boundY)
                                              where n = fst interval

ingestY interval (matrix,boundX,boundY) | isTerm interval = (substituteY interval matrix, boundX, invert n boundY)
                                        | otherwise       = (matrix, boundX, intersect boundY interval)
                                              where n = fst interval

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
produce n ([num, den], boundX, boundY) = ( prod n [num, den], boundX, boundY )
prod n [num, den]  =  [den, [j-n*k | (j,k) <- zip num den]]

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
  -- true iff abs(x-y) <= epsDefault, i.e. eqWithin epsDefault
  x == y = containedIn 0 (lohi aprxState)
             where aprxState = approxUntil epsDefault ([], [[1,0],[0,1]], pmInf, getCF_ (x-y))    

instance Ord CF where
  -- true iff y >= x - epsDefault
  x <= y = below 0 (lohi aprxState)
             where aprxState = approxUntil epsDefault ([], [[1,0],[0,1]], pmInf, getCF_ (y-x))   
containedIn t (lo, hi) = t >= lo && t <= hi
below       t (lo, hi) = t <= hi
above       t (lo, hi) = t >= lo

{-
 - convert among CF, [Integer], and Numeric
 - names ending with "_" indicate functions operating on [(Ratio Integer, Ratio Integer)]
 - (i.e. lists of bounds); these are intended to be private
 -}

floatToCF x           = makeCF (floatToCFterms x)
cfToTerms x           = approx epsDefault x
cfToTermsWithin eps x = approx eps x
cfToFloat x           = fracEval (cfToTerms x)
cfToFloatWithin eps x = fracEval (cfToTermsWithin eps x)
cfToRat x             = ratEval $ cfToTerms x
cfToRatWithin eps x   = ratEval $ cfToTermsWithin eps x
eqWithin eps x y      = containedIn 0 (lohi aprxState)
                          where aprxState = approxUntil eps ([], [[1,0],[0,1]], pmInf, getCF_ (x-y))   

floatToCFterms x | x == floor_x   = [floor x]
                 | otherwise      = (floor x):(floatToCFterms (1/(x - floor_x)))
                    where floor_x = fromIntegral (floor x)

-- evaluate a finite sequence of terms
fracEval as     = fromRational $ ratEval as

ratEval []     = ratInfinity
ratEval (a:[]) = a % 1
ratEval (a:as) | theRest == 0 = ratInfinity
               | otherwise = (a%1) + if theRest == ratInfinity  then 0 else 1/theRest
                    where theRest = ratEval as

-- display CFs to default accuracy
-- prepend "cf" so it is clear that the value being shown is not of type [Integer]
instance Show CF where
  show x = "cf" ++ (show (approx epsDefault x))

-- better algorithm for displaying prefix to desired accuracy
-- advance current state; multiply matrix by [[n,1],[1,0]]
matmult [[pp, p],[qq,q]] n | n == infinity = [[infinity,pp],[infinity,qq]]
                           | otherwise = [[n*pp+p,pp],[n*qq+q,qq]]
advApprox (terms, matrix, lastBound, unread) | isTerm xi = (terms++[n], matmult matrix n, nobound, tail_ unread)
                                             | otherwise = (terms, matrix, xi, tail_ unread)
                                                where xi = head_ unread
                                                      n = numerator (fst xi)
                                                    
approxUntil eps curState = if narrowerThan eps curState then curState else approxUntil eps (advApprox curState) 
-- get upper, lower bounds on value of CF
inOrder (a,b) = if a < b then (a,b) else (b,a)
lohi (terms, [[pp,p],[qq,q]], lastBound, unread) | lastBound == nobound = inOrder ((pp+p)%(qq+q), pp%qq)
                                                 | otherwise = inOrder (ratMult lo [[pp,p],[qq,q]], ratMult hi [[pp,p],[qq,q]])
                                                    where (lo,hi) = lastBound
-- insert rational number as final term of CF
ratMult a [[pp,p],[qq,q]] = (pp*n + p*d)%(qq*n+q*d)
                            where (n,d) = (numerator a, denominator a)

-- advance state until bounds on CF are sufficiently narrow
narrowerThan eps (t,m,b,u) = hi-lo  < eps
                        where (lo,hi) = lohi (t,m,b,u)   
approx eps (MakeCF_ x) = t ++ lastTermApprox
                         where (t,m,b,u) = approxUntil eps ([], [[1,0],[0,1]], pmInf, x) 
                               lastTermApprox = if b == nobound then [] else [floor (snd b)]

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

-- n^{th} degree taylor polynomial is composition of mat 1, mat 2, ... mat n
mat n = [[1,0,0,n],[0,0,0,n]] -- 1 + xy/n
expIter n x = (1 - 2%(3*n), 1 + 2%n):(arithCF_ (mat n) x (expIter (n+1) x))
-- this is correct only when abs x <= 1
cfExp_ (MakeCF_ x) = MakeCF_ (expIter 1 x)

{-
 - Log x 
 -}

-- Tylor series for g(w) = 1 + w/3 + w^2/5 + w^3/7 + ...
logMat n = [[2*n-1,0,0,1],[0,0,0,2*n-1]] -- 1/(2*n-1) + xy
logMatProd0 n = [[0,0,0,2*n-1],[2*n-1,0,0,1]] -- 1/M_(x,n)(y)
logMatProd1 n =  [[0,0,0,2*n-1],[2*n-1,0,0,2-2*n]] -- 1/(M_(x,n)(y) - 1)
-- force intervals to be monotonic; interval bd is inherited from last iteration
-- new bound is intersection of old bound with 'ordinary' bounds on curM
gosperLog bd x y curM  | low == hi  = (termToBound hi):(gosperLog nobound x y (produce hi curM))   -- produce another term of output 
                       | otherwise  = (lowR, hiR):(gosperLog (lowR, hiR) (tail_ x) (tail_ y) (ingestY (head_ y) (ingestX (head_ x) curM))) -- get next x,y
                              where (prevLo, prevHi) = bd
                                    (low_,hi_) = range curM
                                    low = max (floor prevLo) low_
                                    hi = min (floor prevHi) hi_
                                    (lowR_, hiR_) = ratRange curM
                                    lowR = max prevLo lowR_
                                    hiR = min prevHi hiR_
                              
arithCFlog_ bd initM x y = takeWhile notInf (gosperLog bd (tail_ x) (tail_ y) (ingestY (head_ y) (ingestX (head_ x) (initM, pmInf, pmInf))))
gIter n w | n == 1    = (termToBound 1):(arithCFlog_ (3%1, ratInfinity) (logMatProd1 1) w (gIter 2 w))
          | otherwise = (termToBound 0):((6*n-3)%4, (2*n-1)%1):(arithCFlog_ ((6*n-3)%4, (2*n-1)%1) (logMatProd0 n) w (gIter (n+1) w))

g w = gIter 1 w
cfLog x | x > cfE = 1 + (cfLog (x/cfE))
        | x < 1 = -(cfLog (1/x))
        | otherwise = 2 * z * (MakeCF_ (g (getCF_ (z^2))))
            where z = (x-1)/(x+1) -- todo; implement as single bihomographic expression

{-
 - trigonometric fuctions
 -}

-- pi, using Gosper's accelerated series
piMat i = [[0, i*(2*i-1), 0, (5*i-2)*3*(3*i+1)*(3*i+2)],
           [0, 0,         0, 3*(3*i+1)*(3*i+2)]]
piInterval i = ( (27*i-12)%5, (675*i - 216)%125  )
piIter i | i == 1    = (termToBound 3):(arithCF_ (prod 3 (piMat i)) (piIter (i+1)) [termToBound 0])
         | otherwise =  (piInterval i):(arithCF_ (piMat i)          (piIter (i+1)) [termToBound 0])
cfPi = MakeCF_ (piIter 1)

trigMat n = [[-1,0,0,2*n*(2*n-1)],[0,0,0,2*n*(2*n-1)]] -- 1 - xy/(2n(2n-1)) 
-- valid for -pi/2 <= x <= pi/2
cfCos x  | (abs x) <= cfPi/2 = MakeCF_ (cfCosIter 1 (getCF_ (x^2)))
         | (abs x) <= cfPi   = -(cfCos (cfPi - x))
         | otherwise = cfCos (x - (signum x)*2*cfPi)
cfCosIter n w | n > 1 = (termToBound 0):(termToBound 1):((4*n*(2*n-1)-5)%5, ratInfinity):( arithCF_ (prod 1 (prod 0 (trigMat n))) w (cfCosIter (n+1) w) )
              | otherwise =(-1%4, 1%1 ):( arithCF_  (trigMat 1) w (cfCosIter 2 w) ) 

cfSin x = cfCos (x - cfPi/2)
cfTan x = (cfSin x)/(cfCos x)

-- helpful for debugging infinite loops and slow computations
debug n (MakeCF_  cf) = take n cf
debugView n cf = MakeCF_ (debug n cf)
findTerms n (MakeCF_ cf) = [ (k, (numerator.fst) (cf!!k)) | k <- [1..n], isTerm (cf!!k) ]

-- arcsin(x)/x
-- asinMat n = [[(2n+1)^2,0,0,2*n+2],[0,0,0,(2*n+1)*(2*n+2)]] -- 1/(2n+1) + wy(2n+1)/(2n+2) where w = x^2
-- cfAsin x = x * (MakeCF_ (cfAsinIter 0 (getCF_ (x^2))))
