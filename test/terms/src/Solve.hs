{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Solve (

) where

import Text.Printf
import System.CPUTime
import Data.List
import Data.String

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

data TermReference f v = TRef [Term f v]

termRefList ref = case ref of TRef x -> x

data TermElement f v = TermVar v | TermSym f
    deriving (Show, Eq, Ord)

class ITerm t f v where
    header :: t -> TermElement f v
    subterms :: t -> [Term f v]
    subtermRefs :: t -> [TermReference f v]
    operands :: t -> [Term f v]
    operandRefs :: t -> [TermReference f v]
    term :: t-> Term f v
    termref :: t -> TermReference f v
    internal :: t -> Bool

instance ITerm (Term f v) f v where
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
    internal t = False

instance ITerm (TermReference f v) f v where
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

    internal [t] = False
    internal _ = True

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



(&) :: f -> [Term f v] -> Term f v
(&) = Fun

lengthf term = case term of
    Fun f l -> 1 + sumf lengthf l
    _ -> 1


refVal (TRef []) = Empty
refVal (TRef (x:xs)) = x

-- replaces subterms from list s by corresponding subterms of list t
replaceTerms x s t = case elemIndex x s of
    Just i -> t!!i
    Nothing -> case x of
        Fun f l -> Fun f (map (\y -> replaceTerms y s t) l)
        _ -> x

repl t 0 = t
repl t n = replaceTerms (repl t (n-1)) ['g'&[Var 'x'], Var 'y']  ['f'&[Var 'y', 'g'&[Var 'x']], 'g'&[Var 'x']]

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

findMatches :: (Ord f, Ord v, Ord v1) => Term f v -> Term f v1 -> [(Term f v, [(v1, Term f v)])]
findMatches trm patt = concatMap m (subterms trm)
    where
        m x = case hasMatch x patt of
            Nothing -> []
            Just l -> [(x,l)]

class ScanState st where
    level :: st -> Int
    new :: st -> Bool

class Problem p where
    premises :: p -> [Term String Int]
    conditions :: p -> [Term String Int]
    goals :: p -> [Term String Int]

solvePls :: (ScanState st, Problem p) => (st, p) -> TermReference String Int-> Int -> Bool -> (st, p)
zamenavhozhdeniya :: (ScanState st,Problem p) => st->p->TermReference String Int-> Int -> Bool->[[Term Int Int]]-> (st, p)


solvePls (state, x1) x2 x3 x4 x5 = case res of
    [] -> (state, x1)
    x:xs -> x
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
                    return zamenavhozhdeniya st x1 x2 x3 x4 ("pls" & x8++["0"&[]]) [["priem"&[], "pls"&[], "list"&["1"&[],"2"&[]], "secondsubterm"&[]]]

--solve pls(x1, x2, x3, x4, x5){
--	internal(x2);
--	branch {
--		level(0d);
--		novij;
--		branch {
--			operand(x2, x6);
--			branch {
--				operand(x2, x7);
--				x7 != x6;
--				ravnietermi(x6, x7);
--				x8 = listof(subterm(x9) where x9 : operand(x2, x9), x9 != x6, x9 != x7);
--				kontrolpriema(pls, 12d, secondsubterm);
--				zamenavkhozhdeniya(x2, x3, x4, x1, unisborka(pls, append(x8, 0d)), [[priem, pls, 12d, secondsubterm]]);
--				rescan;
--			}
--			branch {
--				kontrolpriema(pls, 5d, spuskoperandov);
--				simvol(x6, pls);
--				zamenavkhozhdeniya(x2, x3, x4, x1, spuskoperandov(x2, x6), [[priem, pls, 5d, spuskoperandov]]);
--				rescan;
--			}
--			branch {
--				simvol(x6, 0d);
--				x7 = listof(subterm(x8) where x8 : operand(x2, x8), x8 != x6);
--				kontrolpriema(pls, 10d, secondsubterm);
--				zamenavkhozhdeniya(x2, x3, x4, x1, unisborka(pls, x7), [[priem, pls, 10d, secondsubterm]]);
--				rescan;
--			}
--			kontrolpriema(pls, 20d, secondsubterm);
--			simvol(x6, otr);
--			operand(x2, x7);
--			x7 != x6;
--			simvol(x7, otr);
--			x8 = listof(subterm(x9) where x9 : operand(x2, x9), x9 != x6, x9 != x7);
--			zamenavkhozhdeniya(x2, x3, x4, x1, unisborka(pls, x8 :: [firstsubterm(x6), firstsubterm(x7)]), [[priem, pls, 20d, secondsubterm]]);
--			rescan;
--		}
--		branch {
--			operand(x6, x2);
--			simvol(x6, kn);
--			if_false {
--				branch {
--					simvol(x6, dn);
--					operand(x6, x7) & x7 != x2 & x8 = subterm(x7) | operand(x2, x7) & simvol(x7, dn) & x8 = subterm(x7);
--					x9 = listof(subterm(x9) where x9 : operand(x6, x9), x9 != x2);
--					subset(naborchlenov(dn, x8), x9);
--					x10 = naborchlenov(pls, x8);
--					x11 = operands(x2);
--					subset(x10, x11);
--					x12 = listMinus(x11, x10);
--					x12 != emptylist;
--					kontrolpriema(pls, 19d, secondsubterm);
--					zamenavkhozhdeniya(x2, x3, x4, x1, unisborka(pls, x12), [[priem, pls, 19d, secondsubterm], [vivodimo, back([vivodimo, emptylist])], [korrekciyaposilok, emptylist], [termRoot, x6]]);
--					rescan;
--				}
--				branch {
--					kontrolpriema(pls, 18d, secondsubterm);
--					simvol(x6, imp);
--					x2 = firstoperand(x6);
--					x7 = secondsubterm(x6);
--					x8 = (secondsubtermheader(x6, pls) ? operands(secondoperand(x6)) : [x7]);
--					x9 = operands(x2);
--					subset(x8, x9);
--					x10 = listMinus(x9, x8);
--					x10 != emptylist;
--					x11 = [vivodimo, emptylist];
--					zamenavkhozhdeniya(x6, x3, x4, x1, normimp(imp[<unisborka(pls, x10), x7>], oblvkhozhd(x6, x3, x4, x1), [x11]), [[priem, pls, 18d, secondsubterm], [vivodimo, back(x11)], [korrekciyaposilok, emptylist]]);
--					rescan;
--				}
--				kontrolpriema(pls, 34d, secondsubterm);
--				simvol(x6, ravno);
--				operand(x6, x7);
--				x7 != x2;
--				x8 = operands(x2);
--				x9 = (simvol(x7, pls) ? operands(x7) : [subterm(x7)]);
--				x10 = listIntersection(x8, x9);
--				x10 != emptylist;
--				x11 = listMinus(x8, x10);
--				x11 != emptylist;
--				x12 = unisborka(pls, x11);
--				x13 = unisborka(pls, listMinus(x9, x10));
--				zamenavkhozhdeniya(x6, x3, x4, x1, ravno[<x12, x13>], [[priem, pls, 34d, secondsubterm], [perem, unisborka(pls, x10), x12, x13]]);
--				rescan;
--			}
--			branch {
--				operand(x2, x7);
--				simvol(x7, kn);
--				x8 = listof(subterm(x8) where x8 : operand(x6, x8), x8 != x2);
--				x9 = operands(x7);
--				x10 = listIntersection(x8, x9);
--				x10 != emptylist;
--				x11 = listMinus(x9, x10);
--				x11 != emptylist;
--				kontrolpriema(pls, 17d, secondsubterm);
--				zamenavkhozhdeniya(x7, x3, x4, x1, unisborka(kn, x11), [[priem, pls, 17d, secondsubterm], [vivodimo, back([vivodimo, emptylist])], [korrekciyaposilok, emptylist], [termRoot, x6]]);
--				rescan;
--			}
--			operand(x6, x7);
--			x7 != x2;
--			x8 = operands(x2);
--			x9 = naborchlenov(pls, simvol(x7, otr) ? firstsubterm(x7) : otr[<subterm(x7)>]);
--			subset(x9, x8);
--			x10 = listMinus(x8, x9);
--			x10 != emptylist;
--			kontrolpriema(pls, 16d, secondsubterm);
--			zamenavkhozhdeniya(x2, x3, x4, x1, unisborka(pls, x10), [[priem, pls, 16d, secondsubterm], [vivodimo, back([vivodimo, emptylist])], [korrekciyaposilok, emptylist], [termRoot, x6]]);
--			rescan;
--		}
--		kontrolpriema(pls, 9d, secondsubterm);
--		x4 = 1d;
--		problemtype(x1, opisat);
--		operand(x6, x2);
--		simvol(x6, ravno);
--		termRoot(x6);
--		operand(x2, x7);
--		simvol(x7, x8);
--		neizvestnaya(x8, x1);
--		x9 = listof(subterm(x10) where x10 : operand(x2, x10), x10 != x7);
--		forall(x10 if x10  in  x9 then izvestno(x10, x1));
--		operand(x6, x10);
--		x10 != x2;
--		x11 = subterm(x10);
--		izvestno(x11, x1);
--		x12 = [vivodimo, emptylist];
--		zamenavkhozhdeniya(x6, x3, x4, x1, ravno[<x8, normpls(unisborka(pls, append(x9, x11)), oblvkhozhd(x6, x3, x4, x1), [x12])>], [[priem, pls, 9d, secondsubterm], [vivodimo, back(x12)], [korrekciyaposilok, emptylist], [perem, unisborka(pls, x9), x10, [x8]]]);
--		rescan;
--	}
--	level(0d, 3d);
--	if_false {
--		level(1d);
--		if_false {
--			level(2d);
--			if_false {
--				level(4d);
--				novij;
--				x4 = 1d;
--				problemtype(x1, preobrazovat);
--				branch {
--					!goal(x1, zagolovokpriema) | goal(x1, standartizaciya);
--					goal(x1, dlina);
--					branch {
--						operand(x6, x2);
--						simvol(x6, ekv);
--						x7 = listof(subterm(x8) where x8 : operand(x6, x8), x8 != x2);
--						forall(x8 if x8  in  x7 then izvestno(x8, x1));
--						operand(x2, x8);
--						x9 = listof(subterm(x10) where x10 : operand(x2, x10), x10 != x8);
--						x10 = [vivodimo, emptylist];
--						x11 = oblvkhozhd(x6, x3, x4, x1);
--						x12 = [x10];
--						branch {
--							x13 = standuporyadochenie(normekv(ekv[<subterm(x8), normpls(unisborka(pls, prepend(unisborka(ekv, x7), x9)), x11, x12)>], x11, x12));
--							standartizaciya(x1, x6, x3, x4, x13);
--							branch {
--								kontrolpriema(pls, 30d, secondsubterm);
--								zamenavkhozhdeniya(x6, x3, x4, x1, x13, [[priem, pls, 30d, secondsubterm], [vivodimo, back(x10)], [korrekciyaposilok, emptylist]]);
--								rescan;
--							}
--							kontrolpriema(pls, 31d, firstsubterm);
--							zamenavkhozhdeniya(x6, x3, x4, x1, x13, [[priem, pls, 31d, firstsubterm], [vivodimo, back(x10)], [korrekciyaposilok, emptylist]]);
--							rescan;
--						}
--						x13 = standuporyadochenie(normpls(unisborka(pls, append(x9, normekv(unisborka(ekv, append(x7, subterm(x8))), x11, x12))), x11, x12));
--						standartizaciya(x1, x6, x3, x4, x13);
--						kontrolpriema(ekv, 33d, firstsubterm);
--						zamenavkhozhdeniya(x6, x3, x4, x1, x13, [[priem, ekv, 33d, firstsubterm], [vivodimo, back(x10)], [korrekciyaposilok, emptylist]]);
--						rescan;
--					}
--					operand(x2, x6);
--					simvol(x6, ekv);
--					x7 = listof(subterm(x8) where x8 : operand(x2, x8), x8 != x6);
--					forall(x8 if x8  in  x7 then izvestno(x8, x1));
--					operand(x6, x8);
--					x9 = listof(subterm(x10) where x10 : operand(x6, x10), x10 != x8);
--					x10 = [vivodimo, emptylist];
--					x11 = oblvkhozhd(x2, x3, x4, x1);
--					x12 = [x10];
--					x13 = standuporyadochenie(normekv(ekv[<subterm(x8), normpls(unisborka(pls, prepend(unisborka(ekv, x9), x7)), x11, x12)>], x11, x12));
--					standartizaciya(x1, x2, x3, x4, x13);
--					kontrolpriema(ekv, 32d, secondsubterm);
--					zamenavkhozhdeniya(x2, x3, x4, x1, x13, [[priem, ekv, 32d, secondsubterm], [vivodimo, back(x10)], [korrekciyaposilok, emptylist]]);
--					rescan;
--				}
--				goal(x1, standartizaciya);
--				goal(x1, reducirovanie);
--				goal(x1, uprostit);
--				!goal(x1, bikluch);
--				izvestno(*x3, x1);
--				operand(x6, x2);
--				simvol(x6, dn);
--				operand(x6, x7);
--				x7 != x2;
--				simvol(x7, kn);
--				operand(x7, x8);
--				simvol(x8, otr);
--				x9 = firstoperand(x8);
--				if(simvol(x9, kn))
--					operand(x9, x10);
--				else x10 = x9;
--				x11 = subterm(x10);
--				x12 = (simvol(x10, otr) ? firstsubterm(x10) : otr[<x11>]);
--				x13 = operands(x2);
--				x14 = naborchlenov(pls, x12);
--				subset(x14, x13);
--				x15 = listMinus(x13, x14);
--				dlinateksta(x15, 1d);
--				x16  in  x15;
--				x17 = naborchlenov(kn, x16);
--				x18 = (simvol(x9, kn) ? listof(subterm(x19) where x19 : operand(x9, x19), x19 != x10) : emptylist);
--				subset(x18, x17);
--				x19 = listMinus(x17, x18);
--				dlinateksta(x19, 1d);
--				x20  in  x19;
--				x21 = naborchlenov(kn, header(x20, otr) ? firstsubterm(x20) : otr[<x20>]);
--				x22 = listof(subterm(x23) where x23 : operand(x7, x23), x23 != x8);
--				equal_length(x21, x22);
--				subset(x21, x22);
--				x23 = [vivodimo, emptylist];
--				x24 = unisborka(kn, x18);
--				x25 = oblvkhozhd(x6, x3, x4, x1);
--				x26 = [x23];
--				x27 = unisborka(kn, x22);
--				x28 = normotr(otr[<x27>], x25, x26);
--				x29 = normotr(x11, x25, x26);
--				x30 = listof(subterm(x31) where x31 : operand(x6, x31), x31 != x7, x31 != x2);
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				branch {
--					continue;
--				}
--				continue;
--			}
--			novij;
--			branch {
--				x4 = 0d;
--				if_false {
--					x4 = 1d;
--					problemtype(x1, preobrazovat);
--					branch {
--						kontrolpriema(dn, 71d, secondsubterm);
--						goal(x1, standpls);
--						termRoot(x2);
--						komment(x1, standpls);
--						zamechanie(x1, standpls);
--						x6 = firstoperand(x2);
--						x7 = [vivodimo, emptylist];
--						x8 = standpls(subterm(x2), oblvkhozhd(x2, x3, x4, x1), [x7]);
--						zamenavkhozhdeniya(x2, x3, x4, x1, x8, [[priem, dn, 71d, secondsubterm], [vivodimo, back(x7)], [korrekciyaposilok, emptylist], [perem, x8, x6, isklyuchenieoperanda(x2, x6)]]);
--						rescan;
--					}
--					kontrolpriema(dn, 80d, secondsubterm);
--					goal(x1, sokraschdnf);
--					termRoot(x2);
--					komment(x1, sokraschdnf);
--					zamechanie(x1, sokraschdnf);
--					x6 = firstoperand(x2);
--					x7 = [vivodimo, emptylist];
--					x8 = sokraschdnf(subterm(x2), oblvkhozhd(x2, x3, x4, x1), [x7]);
--					zamenavkhozhdeniya(x2, x3, x4, x1, x8, [[priem, dn, 80d, secondsubterm], [vivodimo, back(x7)], [korrekciyaposilok, emptylist], [perem, x8, x6, isklyuchenieoperanda(x2, x6)]]);
--					rescan;
--				}
--				kontrolpriema(pls, 38d, secondsubterm);
--				operand(x6, x2);
--				simvol(x6, ravno);
--				termRoot(x6);
--				operand(x6, x7);
--				x7 != x2;
--				obl(x2, x3, x4, x1, x8);
--				header(x8, ravno);
--				x9 = begin(x8);
--				operand(x9, x10);
--				simvol(x10, pls);
--				operand(x9, x11);
--				x11 != x10;
--				ravnietermi(x11, x7);
--				x12 = operands(x2);
--				x13 = operands(x10);
--				x14 = listIntersection(x12, x13);
--				x14 != emptylist;
--				spisokperemennikh(unisborka(pls, x14)) != emptylist;
--				x15 = listMinus(x13, x14);
--				x15 != emptylist;
--				x16 = listMinus(x12, x14);
--				x16 != emptylist;
--				zamenavkhozhdeniya(x6, x3, x4, x1, ravno[<unisborka(pls, x15), unisborka(pls, x16)>], [[priem, pls, 38d, secondsubterm], [vivodimo, [x8]]]);
--				rescan;
--			}
--			kontrolpriema(dn, 94d, secondsubterm);
--			problemtype(x1, opisat);
--			goal(x1, normalizator);
--			operand(x6, x2);
--			simvol(x6, ravno);
--			termRoot(x6);
--			operand(x6, x7);
--			x7 != x2;
--			operand(x2, x8);
--			x9 = listof(subterm(x10) where x10 : operand(x2, x10), x10 != x8);
--			x10 = subterm(x8);
--			x11 = unisborka(pls, x9);
--			x12 = subterm(x7);
--			!exists(x13 : x13  in  params(*x3) & !exists(x14, x15, x16 : (x14 = x10 | x14 = x11 | x14 = x12) & x15 = begin(x14) & (header(x14, pls) ? operand(x15, x16) : x16 = x15) & !exists(x17 : (simvol(x16, kn) ? operand(x16, x17) : x17 = x16) & simvol(x17, x13))));
--			novayaperemennaya(taskvariables(x1), x13);
--			zamechanie(x1, novparam, x13);
--			x14 = oblvkhozhd(x6, x3, x4, x1);
--			x15 = [vivodimo, emptylist];
--			x16 = [x15];
--			zamenavkhozhdeniya(x6, x3, x4, x1, ravno[<normpls(pls[<normkn(kn[<x10, x13>], x14, x16), normkn(kn[<x11, x13>], x14, x16)>], x14, x16), normkn(kn[<x12, x13>], x14, x16)>], [[priem, dn, 94d, secondsubterm], [vivodimo, back(x15)], [korrekciyaposilok, emptylist], [vivod, dvoichnoe[<x13>], 0d, emptylist], [perem, x8, x11, x7, [x13]]]);
--			rescan;
--		}
--		branch {
--			novij;
--			branch {
--				x4 = 1d;
--				branch {
--					kontrolpriema(pls, 24d, secondsubterm);
--					!problemtype(x1, preobrazovat) | !goal(x1, standpls);
--					operand(x2, x6);
--					simvol(x6, 1d);
--					x7 = listof(subterm(x8) where x8 : operand(x2, x8), x8 != x6);
--					x8 = [vivodimo, emptylist];
--					zamenavkhozhdeniya(x2, x3, x4, x1, normotr(otr[<unisborka(pls, x7)>], oblvkhozhd(x2, x3, x4, x1), [x8]), [[priem, pls, 24d, secondsubterm], [vivodimo, back(x8)], [korrekciyaposilok, emptylist]]);
--					rescan;
--				}
--				kontrolpriema(ekv, 28d, secondsubterm);
--				problemtype(x1, preobrazovat);
--				goal(x1, reducirovanie);
--				operand(x2, x6);
--				simvol(x6, otr);
--				x7 = listof(subterm(x8) where x8 : operand(x2, x8), x8 != x6);
--				x8 = [vivodimo, emptylist];
--				zamenavkhozhdeniya(x2, x3, x4, x1, normekv(ekv[<firstsubterm(x6), unisborka(pls, x7)>], oblvkhozhd(x2, x3, x4, x1), [x8]), [[priem, ekv, 28d, secondsubterm], [vivodimo, back(x8)], [korrekciyaposilok, emptylist]]);
--				rescan;
--			}
--			branch {
--				operand(x6, x2);
--				simvol(x6, ravno);
--				operand(x6, x7);
--				x7 != x2;
--				simvol(x7, 0d);
--				if_false {
--					kontrolpriema(pls, 49d, secondsubterm);
--					simvol(x7, 1d);
--					operand(x2, x8);
--					simvol(x8, otr);
--					x9 = listof(subterm(x10) where x10 : operand(x2, x10), x10 != x8);
--					x10 = unisborka(pls, x9);
--					zamenavkhozhdeniya(x6, x3, x4, x1, ravno[<firstsubterm(x8), x10>], [[priem, pls, 49d, secondsubterm], [perem, firstoperand(x8), x10]]);
--					rescan;
--				}
--				kontrolpriema(pls, 39d, secondsubterm);
--				operand(x2, x8);
--				x9 = listof(subterm(x10) where x10 : operand(x2, x10), x10 != x8);
--				x10 = subterm(x8);
--				!subset(params(x10), params(x9));
--				zamenavkhozhdeniya(x6, x3, x4, x1, ravno[<x10, unisborka(pls, x9)>], [[priem, pls, 39d, secondsubterm]]);
--				rescan;
--			}
--			branch {
--				kontrolpriema(pls, 37d, secondsubterm);
--				!problemtype(x1, dokazat) | x4 = 0d;
--				operand(x6, x2);
--				simvol(x6, ravno);
--				operand(x7, x6);
--				simvol(x7, forall);
--				x8 = lastoperand(x7);
--				x6 != x8;
--				!lastsubtermheader(x7, ravno) | simvol(x8, ravno) & exists(x9, x10 : operand(x8, x9) & simvol(x9, 1d) & operand(x8, x10) & x10 != x9 & simvol(x10, pls));
--				operand(x6, x9);
--				x9 != x2;
--				simvol(x9, 1d);
--				x10 = operands(x2);
--				x11  in  x10;
--				x12 = listMinus(x10, [x11]);
--				x12 != emptylist;
--				x13 = unisborka(pls, x12);
--				x14 = listMinus(naborantecedentov(x7), [subterm(x6)]);
--				zamenavkhozhdeniya(x7, x3, x4, x1, Implikaciya(svyazpristavka(x7), x14 :: [not[<lastsubterm(x7)>]], ravno[<x11, x13>]), [[priem, pls, 37d, secondsubterm], [perem, x11, x13, unisborka(and, x14), x8]]);
--				rescan;
--			}
--			kontrolpriema(pls, 53d, secondsubterm);
--			operand(x2, x6);
--			simvol(x6, vichet);
--			secondsubtermheader(x6, 2d);
--			operand(x2, x7);
--			x7 != x6;
--			simvol(x7, vichet);
--			secondsubtermheader(x7, 2d);
--			x8 = [korrekciyaposilok, emptylist];
--			x9 = plus[<firstsubterm(x6), firstsubterm(x7)>];
--			preobrazovanie(x1, x9, oblvkhozhd(x2, x3, x4, x1), [[urovenobrascheniya, 4d], uprostit, [kommentarij, x8]], x10, x11, x12);
--			x10 != otkaz;
--			shorter(x10, x9);
--			x13 = listof(subterm(x14) where x14 : operand(x2, x14), x14 != x6, x14 != x7);
--			x14 = [vivodimo, emptylist];
--			zamenavkhozhdeniya(x2, x3, x4, x1, unisborka(pls, append(x13, vichet[<x10, 2d>])), [[priem, pls, 53d, secondsubterm], [vivodimo, back(x14)], [vivodimo, x11], [zadacha, x12], x8, [perem, firstoperand(x6), firstoperand(x7), x10]]);
--			rescan;
--		}
--		kontrolpriema(pls, 21d, podborznachenij);
--		x4 = 1d;
--		problemtype(x1, opisat);
--		goal(x1, primer);
--		operand(x6, x2);
--		simvol(x6, ravno);
--		termRoot(x6);
--		operand(x2, x7);
--		simvol(x7, x8);
--		neizvestnaya(x8, x1);
--		x9 = listof(subterm(x10) where x10 : operand(x2, x10), x10 != x7);
--		forall(x10 if x10  in  x9 then izvestno(x10, x1));
--		operand(x6, x10);
--		x10 != x2;
--		simvol(x10, 0d);
--		!exists(x11, x12 : uslovie(x11, x12, x1) & x12 != x3 & x8  in  x11 & (!header(x11, dvoichnoe) | !firstsubtermheader(x11, x8)));
--		popitkaspuska(x1, x3, ravno[<x8, unisborka(pls, x9)>], [[priem, pls, 21d, podborznachenij]]);
--		rescan;
--	}
--	novij;
--	branch {
--		kontrolpriema(pls, 5d, leksuporyadochenie);
--		if(x4 = 0d)
--			x5 = 0d;
--		else x5 = 3d;
--		leksuporyadochenie(operands(x2), x6);
--		x6 != 1d;
--		zamenavkhozhdeniya(x2, x3, x4, x1, sborka(pls, x6), [[priem, pls, 5d, leksuporyadochenie]]);
--		rescan;
--	}
--	level(3d);
--	x4 = 1d;
--	problemtype(x1, preobrazovat);
--	branch {
--		kontrolpriema(standdn, 49d, secondsubterm);
--		goal(x1, standdn);
--		x6 = [vivodimo, emptylist];
--		x7 = standdn(subterm(x2), oblvkhozhd(x2, x3, x4, x1), [x6]);
--		x8 = firstoperand(x2);
--		zamenavkhozhdeniya(x2, x3, x4, x1, x7, [[priem, standdn, 49d, secondsubterm], [vivodimo, back(x6)], [korrekciyaposilok, emptylist], [perem, x8, isklyuchenieoperanda(x2, x8), x7]]);
--		rescan;
--	}
--	kontrolpriema(standdn, 31d, secondsubterm);
--	goal(x1, uprostit);
--	!goal(x1, reducirovanie);
--	!goal(x1, standdn);
--	!exists(x6 : operand(x6, x2) & (simvol(x6, imp) | simvol(x6, pls) | simvol(x6, ekv) | simvol(x6, otr) | simvol(x6, dn) | simvol(x6, kn) | simvol(x6, otr)));
--	x6 = subterm(x2);
--	popitka(x1, [standdn, x6], x7);
--	x8 = oblvkhozhd(x2, x3, x4, x1);
--	x9 = [vivodimo, emptylist];
--	x10 = standdn(x6, x8, [x9, [bufer, 0d]]);
--	x11 = [x9];
--	x12 = svertka(!goal(x1, teorvivod) ? dvgruppirovki(x10, x8, x11) : x10, x8, x11);
--	x13 = standuporyadochenie(x12);
--	if(goal(x1, teorvivod))
--		standartizaciya(x1, x2, x3, x4, x13);
--	else shorter(x13, x6);
--	x14 = firstoperand(x2);
--	zamenavkhozhdeniya(x2, x3, x4, x1, x13, [[priem, standdn, 31d, secondsubterm], [vivodimo, back(x9)], [korrekciyaposilok, emptylist], [perem, x14, isklyuchenieoperanda(x2, x14), x12], [zamechanie, [standdn, standuporyadochenie(x13)]]]);
--	rescan;
--}


