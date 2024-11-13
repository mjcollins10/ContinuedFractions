import Data.Ratio -- get (%) operator for rational approximation

{-
 - Gosper's algorithm for arithmetic on CFs
 -}

epsilon = 1 % 2^32 -- default threshold for 'equality'
infinity :: Integer
infinity = 999999999999999999
nobound = (1%1, infinity%1)

-- range_ is min,max of *integer part* of bihomomorphic matrix (axy + bx +cy + d)/(exy + fx + gy + h)
-- as x,y vary independently from zero to infinity
-- ratRange is min,max of bihomomorphic matrix
mightBeInf (n,d) = d==0 && n/=0
allZero curMatrix = all (all (==0)) curMatrix
openceil p r = (div p r) + if (mod p r) == 0 then -1 else 0 -- if asymptotic upper bound is k, integer part is <= k-1
range_ [numr,denr] | any (>0) denr && any (<0) denr && any (/= 0) numr = (-infinity,infinity) -- sign change in denominator
                   | any mightBeInf [ (n,d) | (n,d) <- zip numr denr ] = (-infinity,infinity) -- infinite upper bound
                   | allZero [numr,denr]                               = (-infinity,infinity) -- end of computation
                   | otherwise = ( fromIntegral (minimum [ (div n d)      | (n,d) <- zip numr denr , d /= 0]),
                                   fromIntegral (maximum [ (openceil n d) | (n,d) <- zip numr denr , d /= 0]) )

ratRange_ [numr,denr] | any (>0) denr && any (<0) denr && any (/= 0) numr = (-infinity%1,infinity%1) -- sign change in denominator
                      | any mightBeInf [ (n,d) | (n,d) <- zip numr denr ] = (-infinity%1,infinity%1) -- infinite upper bound
                      | allZero [numr,denr]                               = (-infinity%1,infinity%1) -- end of computation
                      | otherwise = ( minimum [ n%d | (n,d) <- zip numr denr , d /= 0],
                                     maximum [ n%d | (n,d) <- zip numr denr , d /= 0] )

-- after ingesting leading terms, can assume all terms >= 1
-- easier to  map xx, yy = x-1, y-1 and find range assuming xx,yy>0
shift [a,b,c,d] = [a, a+b, a+c, a+b+c+d]
-- apply bounds and get range of result
range (matrix, boundX, boundY) = range_ (map shift matrixWithBounds)
                              where matrixWithBounds = (substituteY boundY (substituteX boundX matrix))

ratRange (matrix, boundX, boundY) = ratRange_ (map shift matrixWithBounds)
                              where matrixWithBounds = (substituteY boundY (substituteX boundX matrix))

-- genuine term changes matrix; otherwise just update bounds
isTerm (lo,hi) = (denominator lo == 1) && (denominator hi == 1) && ((numerator hi == 1 + numerator lo) || (numerator hi == infinity))
ingestX termOrBound (matrix,boundX,boundY) | isTerm termOrBound = (substituteX termOrBound matrix , nobound, nobound)
                                           | otherwise          = (matrix, termOrBound, boundY)

ingestY termOrBound (matrix,boundX,boundY) | isTerm termOrBound = (substituteY termOrBound matrix , nobound, nobound)
                                           | otherwise          = (matrix, boundX, termOrBound)

-- transform bihomomorphic matrix (axy + bx +cy + d)/(exy + fx + gy + h)
-- by substitution x <- n/q + r/sx 
-- transfrom (lo,hi) to (lo, delta)==(lo,hi-lo)
-- ingesting ordinary term has q == r == s == 1
substituteX (lo,hi) [[a,b,c,d],[e,f,g,h]] | all (==0) [a,b,e,f] = [[0,0,c,d],[0,0,g,h]] -- no x terms in matrix
                                          | (lo,hi) == nobound  = [[a,b,c,d],[e,f,g,h]]
                                          | n == infinity       = [[0,0,a,b],[0,0,e,f]]
                                          | otherwise           = [[n*a*s + c*q*s, n*b*s + d*q*s, a*q*r, b*q*r],
                                                                   [n*e*s + g*q*s, n*f*s + h*q*s, e*q*r, f*q*r]]
                                              where  (n,q) = (numerator lo, denominator lo) 
                                                     (r,s) = (numerator (hi-lo), denominator (hi-lo))

substituteY (lo,hi) [[a,b,c,d],[e,f,g,h]] | all (==0) [a,c,e,g] = [[0,b,0,d],[0,f,0,h]] -- no y terms in matrix
                                          | (lo,hi) == nobound  = [[a,b,c,d],[e,f,g,h]]
                                          | n == infinity       = [[0,a,0,c],[0,e,0,g]]
                                          | otherwise           = [[n*a*s + b*q*s, a*q*r, n*c*s + d*q*s, c*q*r],
                                                                   [n*e*s + f*q*s, e*q*r, n*g*s + h*q*s, g*q*r]]
                                              where  (n,q) = (numerator lo, denominator lo)  
                                                     (r,s) = (numerator (hi-lo), denominator (hi-lo))

-- return (numerator/denominator - n)^{-1}
produce n [numerator, denominator] = ( [denominator, [j-n*k | (j,k) <- zip numerator denominator]], nobound, nobound )

-- finite CFs implicitly terminated by infinity
head_ [] = (infinity%1, infinity%1)
head_ xs = head xs
tail_ [] = []
tail_ xs = tail xs

-- one iteration of Gosper's algorithm:
-- produce the next term of output if we can,otherwise read both x and y and produce range
-- current state is ( (unread part of x, unread part of y),
--                    ((current bihomomorphic matrix, bound on x, bound on y), last output term) )
-- ingesting term changes matrix and sets bounds to [1,Inf]
-- ingesting range does nothing to matrix, just updates bounds
-- produce ignores ranges and returns matrix with ranges [1,Inf]
gosper ((x,y),(curM,_))  | allZero m         = ((x,y), (curM, (infinity%1,infinity%1))) -- stop on all-zero state
                         | all null [x,y]    = ((x,y), (curM, (infinity%1,infinity%1))) -- nothing more to do
                         | low == hi         = ((x,y), (produce hi m, (hi%1,(hi+1)%1))) -- produce another term of output
                         | otherwise         = ((tail_ x,tail_ y), (ingestY (head_ y) (ingestX (head_ x) curM), ratRange curM)) -- get next x,y
                             where (low,hi)  = range curM
                                   (m, _, _) = curM

-- start by unconditionally ingesting leading terms
arithCF_ x y initM = iterate gosper ((tail_ x, tail_ y), ( (ingestY (head_ y) (ingestX (head_ x) initM)) , ratRange initM)) 
-- finite CF is terminated by infinity
notInf (_, (_, bn)) = bn /= (infinity%1,infinity%1)
arithCF initialMatrix x y = map (snd.snd) (takeWhile notInf (arithCF_ x y initialMatrix) )

-- matrix initializations for arithmetic
addCF = arithCF ( [[0,1,1,0],[0,0,0,1]],  nobound, nobound )
subCF = arithCF ( [[0,1,-1,0],[0,0,0,1]], nobound, nobound )
mulCF = arithCF ( [[1,0,0,0],[0,0,0,1]],  nobound, nobound )
divCF = arithCF ( [[0,1,0,0],[0,0,1,0]],  nobound, nobound )

{-
 - turn continued fractions into a type with operator overloading
 -}
 
newtype CF = MakeCF_ { getCF_ :: [(Ratio Integer, Ratio Integer)] }
-- turn list of integers into list of bounds; the internal representation of a CF
makeCF terms = MakeCF_ [ (n%1, (n+1)%1) | n <- terms]

-- get CF from float
floatToCFterms x | x == floor_x   = [floor x]
                 | otherwise      = (floor x):(floatToCFterms (1/(x - floor_x)))
                    where floor_x = fromIntegral (floor x)
floatToCF x = makeCF (floatToCFterms x)

-- evaluate CF up to k^{th} term
evalCFterms k (a:[]) = fromIntegral a
evalCFterms k (a:as) | k > 1     = a_ + 1/(evalCFterms (k-1) as)
                     | otherwise = a_
                        where a_ = fromIntegral a
--TODO: evalCF k (makeCF terms) = evalCFterms k terms

-- convert CF to float (default accuracy)
--TODO: fromCF (makeCF terms) = evalCFterms 100 terms

instance Num CF where
  fromInteger n  = makeCF [n]
  x + y = MakeCF_ (addCF (getCF_ x) (getCF_ y))
  x - y = MakeCF_ (subCF (getCF_ x) (getCF_ y))
  x * y = MakeCF_ (mulCF (getCF_ x) (getCF_ y))
  {-TODO: get comparison/equality working
  abs x | x >= 0 = x
        | otherwise        = x * (makeCF [-1])
  signum x | x == 0    = 0
           | x > 0     = 1
           | otherwise = -1
               where terms = getCF x
  -}

instance Fractional CF where
  x / y          = MakeCF_ (divCF (getCF_ x) (getCF_ y))
  fromRational x = floatToCF x

{- instance Eq CF where
  x == y = and (take 100 compxy)
         where compxy = [xt==yt | (xt,yt) <- zip (getCF x) (getCF y)]

instance Ord CF where
  x <= y = xterms!!0 < yterms!!0 || (xterms!!0 == yterms!!0 && (makeCF (drop 1 xterms)) >= (makeCF (drop 1 yterms)))
           where xterms = getCF x
                 yterms = getCF y -}

--TODO: this is for debugging only; must extract terms to required accuracy
instance Show CF where
  show x = show (take 5 (getCF_ x))

showNterms n (MakeCF_ terms) = take n terms

-- rational approximation from CF
{- asRational k (makeCF terms) | null terms                   = infinity % 1 -- Rational cannot have zero denominator
                            | k<=1  || (null $ tail terms) = (terms!!0) % 1
                            | otherwise                    = ((terms!!0)*num+ den) % num 
                               where tailOfCF  = asRational (k-1) (makeCF $ tail terms)
                                     (num,den) = (numerator tailOfCF, denominator tailOfCF) -}

-- examples for testing
-- sqrt2 = makeCF (1:(cycle [2]))
-- "[0..]" has to be an Enum type
-- e = makeCF ([2, 1, 2] ++ (concat [ [1,1,4+2*k] | k <- (map fromIntegral [0..]) ]))
-- 'pi' is defined in standard prelude
-- piCF = floatToCF pi
-- phi = makeCF (cycle [1])
-- gamma = makeCF [0, 1, 1, 2, 1, 2, 1, 4, 3, 13, 5, 1, 1, 8, 1, 2, 4, 1, 1, 40, 1, 11, 3, 7, 1, 7, 1, 1, 5, 1, 49, 4, 1, 65, 1, 4, 7, 11, 1, 399, 2, 1, 3, 2, 1, 2, 1, 5, 3, 2, 1, 10, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 3, 6, 2, 1, 2, 1, 1, 1, 2, 1, 3, 16, 8, 1, 1, 2, 16, 6, 1, 2, 2, 1, 7, 2, 1, 1, 1, 3, 1, 2, 1, 2]

-- for debugging: make intermediate states printable
hist (_,_,h) = h
viewState (h,m) = (hist h, fst m, range (fst m), snd m)

