-- get CF from float
float2cf x | x == floor_x   = [floor x]
           | otherwise      = (floor x):(float2cf (1/(x - floor_x)))
               where floor_x = fromIntegral (floor x)

-- evaluate CF up to k^{th} term
evalCF k (a:[]) = a
evalCF k (a:as) | k > 0     = a + 1/(evalCF (k-1) as)
                | otherwise = a

{-
 - Gosper's algorithm for arithmetic on pairs of CFs
 -}

infinity = 999999999999999999
noOutput = -99999999999999999

-- range_ is min,max of integer part of homomorphic matrix (axy + bx +cy + d)/(exy + fx + gy + h)
-- as x,y vary independently from zero to infinity
mightBeInf (n,d) = d==0 && n/=0
allZero curMatrix = all (all (==0)) curMatrix
openceil p r = (div p r) + if (mod p r) == 0 then -1 else 0 -- if asymptotic upper bound is k, integer part is <= k-1
range_ [numr,denr] | any (>0) denr && any (<0) denr && any (/= 0) numr = (-999999999,999999999) -- sign change in denominator
                   | any mightBeInf [ (n,d) | (n,d) <- zip numr denr ] = (-999999999,999999999) -- infinite upper bound
                   | allZero [numr,denr]                               = (-999999999,999999999) -- end of computation
                   | otherwise = ( fromIntegral (minimum [ (div n d)      | (n,d) <- zip numr denr , d /= 0]),
                                   fromIntegral (maximum [ (openceil n d) | (n,d) <- zip numr denr , d /= 0]) )

-- after ingesting leading terms, can assume all terms >= 1
-- easier to  map xx, yy = x-1, y-1 and find range assuming xx,yy>0
shift [a,b,c,d] = [a, a+b, a+c, a+b+c+d]
range [num, den] = range_ [shift num , shift den]

-- transform homomorphic matrix (axy + bx +cy + d)/(exy + fx + gy + h)
-- by substitution x <- n + 1/x or y <- n + 1/y
ingestX n [[a,b,c,d],[e,f,g,h]] | all (==0) [a,b,e,f] = [[0,0,c,d],[0,0,g,h]] 
                                | n==infinity         = [[0,0,a,b],[0,0,e,f]]
                                | otherwise           = [[n*a+c, n*b+d, a, b], [n*e+g, n*f+h, e, f]]
ingestY n [[a,b,c,d],[e,f,g,h]] | all (==0) [a,c,e,g] = [[0,b,0,d],[0,f,0,h]]
                                | n==infinity         = [[0,a,0,c],[0,e,0,g]]
                                | otherwise           = [[n*a+b, a, n*c+d, c], [n*e+f, e, n*g+h, g]]

-- return (numerator/denominator - bn)^{-1}
produce bn [ numerator, denominator ] = [denominator, [j-bn*k | (j,k) <- zip numerator denominator]]

-- finite CFs implicitly terminated by infinity
head_ [] = infinity
head_ xs = head xs
tail_ [] = []
tail_ xs = tail xs

-- one iteration of Gosper's algorithm:
-- produce the next term of output if we can, otherwise read another term of input
-- current state is ( (unread part of x, unread part of y, history), (current homomorphic matrix, last output term) )
-- most recent history is at head of h
gosper ((x,y,h),(curM,bn))  | allZero curM      = ((x,y,h), (curM, infinity)) -- stop on all-zero state
                            | all null [x,y]    = ((x,y,h), (curM, infinity)) -- nothing more to do
                            | low == hi         = ((x,y,[h!!0]), (produce hi curM, hi)) -- produce another term of output
                            | length h > 100    = ((x,y,"x"), (produce hi curM, hi)) -- stuck in loop, truncate
                            | h!!0 == 'y'       = ((tail_ x,y,'x':h), (ingestX (head_ x) curM, noOutput)) -- get next x
                            | otherwise         = ((x,tail_ y,'y':h), (ingestY (head_ y) curM, noOutput)) -- get next y
                                  where (low,hi)  = range curM

-- start by unconditionally ingesting leading terms
arithCF_ x y initM = iterate gosper ((tail x, tail y, "yx"), ( (ingestY (y!!0) (ingestX (x!!0) initM)) , noOutput)) 
-- remove intermediate states, then pull output CF terms from production states
outputState (_, (curM, bn)) = bn /= noOutput
notInf      (_, (curM, bn)) = bn /= infinity
arithCF initialState x y = map (fromIntegral.snd.snd) (takeWhile notInf ( filter outputState (arithCF_ x y initialState) ))

-- matrix initializations for arithmetic
initAdd = [[0,1,1,0],[0,0,0,1]]
initSub = [[0,1,-1,0],[0,0,0,1]]
initMul = [[1,0,0,0],[0,0,0,1]]
initDiv = [[0,1,0,0],[0,0,1,0]]

addCF = arithCF initAdd
subCF = arithCF initSub
mulCF = arithCF initMul
divCF = arithCF initDiv

{-
 - turn continued fractions into a type with operator overloading
 -}

newtype CF = MakeCF [Integer]
fromCF :: CF -> [Integer]
fromCF (MakeCF terms) = terms

instance Num CF where
  fromInteger n  = MakeCF [n]
  x + y = MakeCF (addCF (fromCF x) (fromCF y))
  x - y = MakeCF (subCF (fromCF x) (fromCF y))
  x * y = MakeCF (mulCF (fromCF x) (fromCF y))
  -- abs is nontrivial !!
  abs x | (fromCF x)!!0 >= 0 = x
        |  otherwise         = x * (MakeCF [-1])
  signum (MakeCF terms ) | all (== 0) (take 100 terms)  = 0
                         | otherwise                       = signum (MakeCF [terms!!0])

instance Fractional CF where
  x / y  = MakeCF (divCF (fromCF x) (fromCF y))
  fromRational x = MakeCF (float2cf x)

instance Eq CF where
  x == y = and (take 100 compxy)
         where compxy = [xt==yt | (xt,yt) <- zip (fromCF x) (fromCF y)]

instance Ord CF where
  x <= y = xterms!!0 < yterms!!0 || (xterms!!0 == yterms!!0 && (MakeCF (drop 1 xterms)) >= (MakeCF (drop 1 yterms)))
           where xterms = fromCF x
                 yterms = fromCF y

instance Show CF where
  show x = show (take 8 (fromCF x))

showNterms n (MakeCF terms) = take n terms

-- examples for testing
sqrt2 = MakeCF (1:(cycle [2]))
-- "[0..]" has to be an Enum type
e = MakeCF ([2, 1, 2] ++ (concat [ [1,1,4+2*k] | k <- (map fromIntegral [0..]) ]))
-- 'pi' is defined in standard prelude
piCF = MakeCF (float2cf pi)
phi = MakeCF (cycle [1])
gamma = MakeCF [0, 1, 1, 2, 1, 2, 1, 4, 3, 13, 5, 1, 1, 8, 1, 2, 4, 1, 1, 40, 1, 11, 3, 7, 1, 7, 1, 1, 5, 1, 49, 4, 1, 65, 1, 4, 7, 11, 1, 399, 2, 1, 3, 2, 1, 2, 1, 5, 3, 2, 1, 10, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 3, 6, 2, 1, 2, 1, 1, 1, 2, 1, 3, 16, 8, 1, 1, 2, 16, 6, 1, 2, 2, 1, 7, 2, 1, 1, 1, 3, 1, 2, 1, 2]

-- for debugging: make intermediate states printable
hist (_,_,h) = h
viewState (h,m) = (hist h, fst m, range (fst m), snd m)

