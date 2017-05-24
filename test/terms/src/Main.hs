-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}

module Main (
    main
) where

-- This strang looking comment adds code only needed when running the
-- doctest tests embedded in the comments
-- $setup
-- >>> import Data.List (stripPrefix)

-- | Simple function to create a hello message.
-- prop> stripPrefix "Hello " (hello s) == Just s
import Text.Printf
--import Control.Exception
import System.CPUTime
import Data.List
import Data.String
import Control.Monad

type TermSym = String

foreach :: [a']->(a'->Bool)->Bool

takewhile l pred = case l of
    []   -> []
    x:ll -> if pred x then x:takewhile ll pred else []

foreach ll pred = foldr ((&&) . pred) True ll
--foreach [] pred = True
--foreach (x:ll) pred = pred x && foreach ll pred

primes = 2:[qq | qq <- [3,5..], foreach [3,5..floor(sqrt(fromIntegral qq))] (\pp -> qq `mod` pp>0)]
primes1 = 2:[qq | qq <- [3,5..], foreach (takewhile primes1 (<= floor(sqrt(fromIntegral qq)))) (\pp -> qq `mod` pp>0)]

twin = tw primes1
    where tw (p1:p2:qs) = if p2==p1+2 then p1: tw qs else tw (p2:qs)

twinpair = gd twin
    where gd (p1:p2:qs) = if p2==p1+6 then p1 : gd qs else gd (p2:qs)

sumf f l = case l of
    [] -> 0
    x:xs -> f x + sumf f xs

--data TermElement f v = Const f | Var v
--    deriving (Show, Eq, Ord)


data Term f v
    = Const f
    | Var v
    | Fun f [Term f v]
    | Empty
    deriving (Eq, Ord)

type STerm = Term TermSym TermSym

data TermReference f v = TRef [Term f v]
    deriving (Show, Eq, Ord)

type STermReference = TermReference TermSym TermSym

termRefList ref = case ref of TRef x -> x

data TermElement f v = TermVar v | TermSym f
    deriving (Show, Eq, Ord)

type STermElement = TermElement TermSym TermSym

class ITerm t where
    header :: t -> STermElement
    subterms :: t -> [STerm]
    subtermRefs :: t -> [STermReference]
    operands :: t -> [STerm]
    operandRefs :: t -> [STermReference]
    term :: t-> STerm
    termref :: t -> STermReference

instance ITerm STerm where
    subterms t = case t of
        Fun f l -> t : concatMap subterms l
        _ -> [t]
    header term = case term of
        Var v -> TermVar v
        Const c -> TermSym c
        Fun f l -> TermSym f
    operands term = case term of
        Fun f l -> l
        _ -> []
    operandRefs term = case term of
        Fun f l -> map (\x -> TRef [x,term]) l
        _ -> []
    subtermRefs t = subtermRefs (TRef [t])
    term t = t
    termref t = TRef [t]

instance ITerm STermReference where
    subterms (TRef (t:ts)) = subterms t
    subterms (TRef []) = []

    header (TRef (t:ts)) = header t
    operands (TRef (t:ts)) = operands t
    operandRefs (TRef ref) = case head ref of
        (Fun f l) -> map (\x -> TRef (x:ref)) l
        _ -> []
    subtermRefs = subrefs where
        subrefs ref = ref : concatMap subrefs (operandRefs ref)

    term (TRef (t:ts)) = t
    term (TRef []) = Empty
    termref t = t

parentRefs (TRef (t:s:ts)) = ts:parentRefs (TRef (s:ts))
parentRefs _ = []
parents (TRef (t:ts)) = ts

class (Show s) => LogSymbol s where
   str :: s -> String
   str = show

--instance LogSymbol Int where
--   str = show

instance LogSymbol Char where
   str c = [c]

instance LogSymbol String where
   str s = s

instance (LogSymbol f, LogSymbol v) => Show (Term f v) where
    --show :: Show f => Show v => (Term f v -> String)
    show (Var v) = str v
    show (Fun f l) = str f ++ "(" ++ sumstr [show x | x<-l] ++ ")"
         where
            sumstr [] = ""
            sumstr [a] = a
            sumstr (x:y:l) = x++","++sumstr (y:l)

class IConvertible a b where
    convert :: a -> b

instance IConvertible f (Term f v) where
    convert = Const

instance IConvertible STermReference STerm where
    convert = term

-- show
myFunction :: forall a. Ord a => [a] -> [(a, a)]
myFunction inputList = zip sortedList nubbedList
    where sortedList :: [a]
          sortedList = sort inputList
          nubbedList :: [a]
          nubbedList = nub inputList

-- /show--IConvertible x (Term f v)
infixr 5 &
(&) :: f -> [Term f v] -> Term f v
(&) = Fun

lengthf term = case term of
    Fun f l -> 1 + sumf lengthf l
    _ -> 1


refVal (TRef []) = Empty
refVal (TRef (x:xs)) = x


--refVal :: TermReference f v -> Term f v
--refVal (term,index) = case term of
--    Var v -> Var v
--    Const c -> Const c
--    Empty -> Empty
--    Fun f l -> if index == 0 then term else fnd l index
--        where
--            fnd ll index = case ll of
--                [] -> Empty
--                x:xs -> if lx <= index then fnd xs (index-lx) else refVal(x, index)
--                    where lx = lengthf x

-- returns list of operands of given term
--operands :: Term f v -> [Term f v]
--operands term = case term of
--    Fun f l -> l
--    _ -> []


-- returns head of term (symbol or variable)
--header :: Term f v -> TermElement f v
--header term = case term of
--    Var v -> TermVar v
--    Const c -> TermSym c
--    Fun f l -> TermSym f

-- returns list of subterms of current term
--subterms :: Term f v -> [Term f v]
--subterms t = case t of
--    Fun f l -> t : concatMap subterms l
--    _ -> [t]

-- replaces subterms from list s by corresponding subterms of list t
replaceTerms x s t = case elemIndex x s of
    Just i -> t!!i
    Nothing -> case x of
        Fun f l -> Fun f (map (\y -> replaceTerms y s t) l)
        _ -> x

repl t 0 = t
repl t n = replaceTerms (repl t (n-1)) ["g"&[Var "x"], Var "y"]  ["f"&[Var "y", "g"&[Var "x"]], "g"&[Var "x"]]

time :: IO t -> IO t
time a = do
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    let diff = fromIntegral (end - start) / (10^12)
    printf "Computation time: %0.3f sec\n" (diff :: Double)
    return v

-- sorts list and removes duplicates
rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort


hasMatch :: (Ord f, Ord v, Ord v1) => Term f v -> Term f v1 -> Maybe [(v1, Term f v)]

hasMatch trm patt = case r of
    (True, l) -> if isMapping sl then Just sl else Nothing where sl = rmdups l
    (False, _) -> Nothing
    where
        --conc :: [(Bool, [(String, Term Char Char)])] -> (Bool, [(String, Term Char Char)])
        conc = foldr (\(b1,l1) (b2,l2) -> (b1 && b2, l1 ++ l2)) (True,[])
        --unify :: Term Char Char-> Term Char String -> (Bool, [(String, Term Char Char)])
        unify x (Var v) = (True, [(v, x)])
        unify (Fun g1 l) (Fun g2 v) = if (g1==g2) && (length l == length v) then conc $ zipWith unify l v else (False, [])
        unify _ _ = (False, [])
        --r::(Bool,[(String, Term Char Char)])
        r = unify trm patt
        isMapping ((x1,y1):(x2,y2):xs) = (x1/=x2 || y1==y2) && isMapping ((x2,y2):xs)
        isMapping _ = True

findMatches :: STerm -> STerm -> [(STerm, [(TermSym, STerm)])]
findMatches trm patt = concatMap m (subterms trm)
    where
        m x = case hasMatch x patt of
            Nothing -> []
            Just l -> [(x,l)]

class ScanState st where
    level :: st -> Int
    new :: st -> Bool

class Problem p where
    premises :: p -> [STerm]
    conditions :: p -> [STerm]
    goals :: p -> [STerm]

solvePls :: (ScanState st, Problem p) => (st, p) -> STermReference-> Int -> Int -> Bool -> (st, p)
zamenavhozhdeniya :: (ScanState st, Problem p) => st->p->STermReference-> Int -> Int ->STerm->[[STerm]]->(st,p)

zamenavhozhdeniya s p x2 x3 x4 x5 u = (s,p)

internal :: TermReference f v -> Bool
internal (TRef [a]) = True
internal _ = False

solvePls (state, x1) x2 x3 x4 x5 =
    head (res ++ [(state,x1)])
    where
        res = do
            guard (internal x2)
            guard (level state == 0)
            guard (new state)
            do
                x6 <- operandRefs x2
                do
                    x7 <- operandRefs x2
                    guard (x6 /= x7)
                    guard (term x6 == term x7)
                    let x8 = [term x9 | x9 <- operandRefs x2, x9/=x6, x9/=x7]
                    let u = [["priem"&[], "pls"&[], "list"&["1"&[],"2"&[]], "secondsubterm"&[]]]
                    return (zamenavhozhdeniya state x1 x2 x3 x4 ("pls" & (x8++["0"&[]])) u)
            ++
            do
                x6 <- operandRefs x2
                do
                    x7 <- operandRefs x2
                    guard (x6 /= x7)
                    guard (term x6 == term x7)
                    let x8 = [term x9 | x9 <- operandRefs x2, x9/=x6, x9/=x7]
                    let u = [["priem"&[], "pls"&[], "list"&["1"&[],"2"&[]], "secondsubterm"&[]]]
                    return (zamenavhozhdeniya state x1 x2 x3 x4 ("pls" & (x8++["0"&[]])) u)


test n =
    do
        x1 <- [1..n]
        return (x1*x1)
    ++
    do
        x1 <- [1..n]
        return (x1^3)


main = do
    print $ test 10
    time (print $ lengthf (repl ("f"&[Var "y", "g"&[Var "x"]]) 15))
    print $ findMatches (repl ("f"&[Var "y", "g"&[Var "x"]]) 3) (repl ("f"&[Var "y", "g"&[Var "x"]]) 1)
    --start <- currentTime
    --print $ toStr (replaceTerms (Fun "f" [Var "x", Fun "g" [Var "x"]]) [(Fun "g" [Var "x"])] [(Fun "h" [Var "y"])])
    --time (print (take 100 twinpair))
    --stop <- currentTime
    --print $ "time = " (diffUTCTime stop start)
    --print $ (take 2 (nseq 1))
    --print $ (io 1 1)
    --print $ [binm 1 i | i <- [0..30]]
    --print $ [binm 2 i | i <- [0..30]]
    --print $ [binm 3 i | i <- [0..30]]
    --print $ [binm 4 i | i <- [0..30]]
    --print $ [binm 5 i | i <- [0..30]]

    --print $ [b 1 i | i <- [0..30]]
    --print $ [b 2 i | i <- [0..30]]
    --print $ [b 3 i | i <- [0..30]]
    --print $ [b 4 i | i <- [0..30]]
    --print $ [b 5 i | i <- [0..30]]

