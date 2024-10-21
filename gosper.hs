-- get CF from float
fleur x = fromIntegral (floor x)
float2cf  x | x == (fleur x) = [fleur x]
            | otherwise      = (fleur x):(float2cf (1/(x - fleur x)))

-- eval up to k^{th} term
evalCF k (a:[]) = a
evalCF k (a:as) | k > 0     = a + 1/(evalCF (k-1) as)
                | otherwise = a

-- exact CF of rational numbers
ratCF (_, 0) = []
ratCF (x, y) = map fromIntegral ((div x y):(ratCF (y, (x - y*(div x y)))))

-- Gosper's algorithm for rational function of one CF 
-- Don't really need this anymore
-- (except for range_, which is also used for arithmetic on two CFs)

divceil p r = (div p r) + if (mod p r) > 0 then 1 else 0 -- same as (ceiling (p/r)) but avoids non-integer division
openceil p r = (div p r) + if (mod p r) == 0 then -1 else 0 -- if asymptotic upper bound is k, integer part is <= k-1

-- will never call range on all-zero matrix
mightBeInf (n,d) = d==0 && n/=0
-- find range assuming only that x,y are positive
range_ [numr,denr] | any (>0) denr && any (<0) denr && any (/= 0) numr = (-999999999,999999999) -- sign change in denominator
                   | any mightBeInf [ (n,d) | (n,d) <- zip numr denr ] = (-999999999,999999999) -- infinite upper bound
                   | otherwise = ( fromIntegral (minimum [ (div n d)      | (n,d) <- zip numr denr , d /= 0 ]),
                                  fromIntegral (maximum [ (openceil n d) | (n,d) <- zip numr denr , d /= 0]) )

produce bn [ numerator, denominator ] = [denominator, [j-bn*k | (j,k) <- zip numerator denominator]]

ingest an [ [p,q] , [r,s] ] = [ [an*p + q, p] , [an*r + s, r] ]
-- when input is finite list, subsequent terms are infinite
ingestInfinity [ [p,q] , [r,s] ] = [ [0,p] , [0,r] ]

allZero curState = maximum (map maximum curState) == 0 && minimum (map minimum curState) == 0 

-- ? advance :: (Num a) => ([a], ([[a]], a)) -> ([a], ([[a]], a))
-- current state is ( "unread part of input CF", ("current holomorphic matrix", "output CF so far"))
-- TODO: even two-term case should use shifted range (rather than unshifted range_)
advance (a, ([[p,q],[r,s]], bn)) | low == hi   = (a, (produce hi curState, hi)) -- produce another term of output
                                 | allZero curState  = ([],(curState,9999999999)) -- stop on all-zero state
                                 | null a      = ([], (ingestInfinity curState, bn)) -- finite CF input
                                 | otherwise   = advance (tail a, ((ingest (head a) curState), bn)) -- get next term of a
                                    where (low,hi) = range_ curState
                                          curState = [[p,q],[r,s]]

-- map (snd.snd) pulls out the terms of the cf; then drop the initial empty state
computeCF a initialState  = map (fromIntegral.snd.snd) ( drop 1  (iterate advance (a, (initialState, -1))) )
-- for debugging; keep states
computeCFwithStates a initialState  = map snd (iterate advance (a, (initialState, -1))) 

-- basic ops on single cf
matIncrementBy :: Num a => a -> a -> [[a]]
matIncrementBy j k = [[k,j],[0,k]] -- i.e. x + j/k
matDivideBy :: Num a => a -> [[a]]
matDivideBy k = [[1,0],[0,k]] -- i.e. x/k
matMultiplyBy :: Num a => a -> [[a]]
matMultiplyBy k = [[k,0],[0,1]] -- i.e. k*x

{-
 - Gosper's algorithm for arithmetic on pairs of CFs
 -}

ingestY n [[a,b,c,d],[e,f,g,h]] = [[n*a+b, a, n*c+d, c], [n*e+f, e, n*g+h, g]]
ingestX n [[a,b,c,d],[e,f,g,h]] = [[n*a+c, n*b+d, a, b], [n*e+g, n*f+h, e, f]]

-- matrix initializations for arithmetic
initAdd :: Num a => [[a]]
initAdd = [[0,1,1,0],[0,0,0,1]]
initSub :: Num a => [[a]]
initSub = [[0,1,-1,0],[0,0,0,1]]
initMul :: Num a => [[a]]
initMul = [[1,0,0,0],[0,0,0,1]]
initDiv :: Num a => [[a]]
initDiv = [[0,1,0,0],[0,0,1,0]]

infinity :: Num a => a
infinity = 999999999
noOutput :: Num a => a
noOutput = -99999999

-- after ingesting leading terms, can assume all terms >= 1
-- easier to  map xx, yy = x-1, y-1 and find range assuming xx,yy>0
shift [a,b,c,d] = [a, a+b, a+c, a+b+c+d]
shift [a,b] = [a,a+b]
range [num, den] = range_ [shift num , shift den]
-- current state is ( (unread part of x, unread part of y, history), (current holomorphic matrix, last output) )
-- most recent history is at head of h
-- TODO: deal with only one input null; put low==hi after null checks; do we need allZero?
-- TODO: truncate based on equality tolerance
gosper ((x,y,h),(curM,bn))  | low == hi         = ((x,y,[h!!0]), (produce hi curM, hi)) -- produce another term of output
                            | allZero curM      = ((x,y,h), (curM, infinity)) -- stop on all-zero state
                            | null x && null y  = ((x,y,h), (curM, infinity)) -- stop on all-zero state
                            | length h > 100     = (([],[],"x"), (produce hi curM, hi)) -- stuck in loop, truncate
                            | h!!0 == 'y'       = ((tail x,y,'x':h), (ingestX (head x) curM, noOutput)) -- get next x
                            | otherwise         = ((x,tail y,'y':h), (ingestY (head y) curM, noOutput)) -- get next y
                                  where (low,hi)  = range curM

-- keep all intermediate states
-- start by unconditionally ingesting leading terms
arithCFdebug x y initM = iterate gosper ((tail x, tail y, "yx"), ( (ingestY (y!!0) (ingestX (x!!0) initM)) , noOutput)) 
-- remove intermediate states, then pull output CF terms from production states
outputState (_, (curM, bn)) = bn /= noOutput
-- TODO: drop artificial truncation, let equality operator take care of that
-- in fact this does not work for recursive equality!!!
arithCF initialState x y = map (fromIntegral.snd.snd) (take 100 ( filter outputState (arithCFdebug x y initialState) ))

-- for debugging: make intermediate states printable
hist (_,_,h) = h
viewState (h,m) = (hist h, fst m, range (fst m), snd m)

addCF :: (Integral a, Num b) => [a] -> [a] -> [b]
addCF = arithCF initAdd
subCF :: (Integral a, Num b) => [a] -> [a] -> [b]
subCF = arithCF initSub
mulCF :: (Integral a, Num b) => [a] -> [a] -> [b]
mulCF = arithCF initMul
divCF :: (Integral a, Num b) => [a] -> [a] -> [b]
divCF = arithCF initDiv

{-
 - turn continued fractions into a type
 -}

newtype CF = MakeCF [Integer]
fromCF :: CF -> [Integer]
fromCF (MakeCF terms) = terms

instance Num CF where
  fromInteger n = MakeCF [n]
  x + y = MakeCF (addCF (fromCF x) (fromCF y))
  x - y = MakeCF (subCF (fromCF x) (fromCF y))
  x * y = MakeCF (mulCF (fromCF x) (fromCF y))
  -- abs is nontrivial !!
  abs x | (fromCF x)!!0 >= 0 = x
        |  otherwise         = x * (MakeCF [-1])
  signum (MakeCF terms ) | all (== 0) (take 999999 terms)  = 0
                         | otherwise                       = signum (MakeCF [terms!!0])

instance Fractional CF where
  x / y  = MakeCF (divCF (fromCF x) (fromCF y))

instance Eq CF where
  x == y = and (take 5 compxy)
         where compxy = [xt==yt | (xt,yt) <- zip (fromCF x) (fromCF y)]

-- still needs work
instance Ord CF where
  x <= y = xterms!!0 < yterms!!0 || (xterms!!0 == yterms!!0 && (MakeCF (drop 1 xterms)) >= (MakeCF (drop 1 yterms)))
           where xterms = fromCF x
                 yterms = fromCF y

instance Show CF where
  show x = show (take 8 (fromCF x))

-- examples for testing
sqrt2 = MakeCF (1:(cycle [2]))
-- "[0..]" has to be an Enum type
e = MakeCF ([2, 1, 2] ++ (concat [ [1,1,4+2*k] | k <- (map fromIntegral [0..]) ]))
-- 'pi' is defined in standard prelude
piCF = MakeCF (float2cf pi)
phi = MakeCF (cycle [1])
gamma = MakeCF [0, 1, 1, 2, 1, 2, 1, 4, 3, 13, 5, 1, 1, 8, 1, 2, 4, 1, 1, 40, 1, 11, 3, 7, 1, 7, 1, 1, 5, 1, 49, 4, 1, 65, 1, 4, 7, 11, 1, 399, 2, 1, 3, 2, 1, 2, 1, 5, 3, 2, 1, 10, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 3, 6, 2, 1, 2, 1, 1, 1, 2, 1, 3, 16, 8, 1, 1, 2, 16, 6, 1, 2, 2, 1, 7, 2, 1, 1, 1, 3, 1, 2, 1, 2]

