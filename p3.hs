{--

author: Luke Dercher
student_id: l446d901
class: EECS 662

--}


{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad
import Data.Maybe

-- CFAE AST and Type Definitions

data CFAE where
  Num :: Int -> CFAE
  Plus :: CFAE -> CFAE -> CFAE
  Minus :: CFAE -> CFAE -> CFAE
  Lambda :: String -> CFAE -> CFAE
  App :: CFAE -> CFAE -> CFAE
  Id :: String -> CFAE
  If0 :: CFAE -> CFAE -> CFAE -> CFAE
  deriving (Show,Eq)

type Env = [(String,CFAE)]


evalDynCFAE :: Env -> CFAE -> (Maybe CFAE)
evalDynCFAE e (Num x) = (Just (Num x))
evalDynCFAE e (Plus l r) = do { (Num r') <- (evalDynCFAE e r);
                                (Num l') <- (evalDynCFAE e l);
                                return (Num (l' + r'))}
evalDynCFAE e (Minus l r) = do { (Num r') <- (evalDynCFAE e r);
                                 (Num l') <- (evalDynCFAE e l);
                                 return (Num (l' - r'))}
evalDynCFAE e (Lambda i b) = return (Lambda i b)
evalDynCFAE e (App f a) = do { (Lambda i b) <- (evalDynCFAE e f);
                                a' <- (evalDynCFAE e a);
                                evalDynCFAE ((i,a'):e) b}
evalDynCFAE e (Id i) = lookup i e
evalDynCFAE e (If0 c t1 t2) = do { (Num c') <- (evalDynCFAE e c);
                                    if (c' == 0) then (evalDynCFAE e t1) else (evalDynCFAE e t2)}


data CFAEValue where
  NumV :: Int -> CFAEValue
  ClosureV :: String -> CFAE -> Env' -> CFAEValue
  deriving (Show,Eq)

type Env' = [(String,CFAEValue)]

evalStatCFAE :: Env' -> CFAE -> (Maybe CFAEValue)
evalStatCFAE e (Num x) = (Just (NumV x))
evalStatCFAE e (Plus l r) = do { (NumV l') <- (evalStatCFAE e l);
                                 (NumV r') <- (evalStatCFAE e r);
                                 return (NumV (l' + r'))}
evalStatCFAE e (Minus l r) = do { (NumV l') <- (evalStatCFAE e l);
                                 (NumV r') <- (evalStatCFAE e r);
                                 return (NumV (l' - r'))}
evalStatCFAE e (Lambda i b) = (Just (ClosureV i b e))
evalStatCFAE e (App f a) = do { (ClosureV i b e') <- (evalStatCFAE e f);
                                  a' <- (evalStatCFAE e a);
                                  (evalStatCFAE ((i,a'):e') b)}
evalStatCFAE e (Id i) = lookup i e
evalStatCFAE e (If0 c t t2) = do { (NumV c') <- (evalStatCFAE e c);
                                  if (c' == 0) then (evalStatCFAE e t) else (evalStatCFAE e t2)}





data CFBAE where
  Num' :: Int -> CFBAE
  Plus' :: CFBAE -> CFBAE -> CFBAE
  Minus' :: CFBAE -> CFBAE -> CFBAE
  Lambda' :: String -> CFBAE -> CFBAE
  App' :: CFBAE -> CFBAE -> CFBAE
  Bind' :: String -> CFBAE -> CFBAE -> CFBAE
  Id' :: String -> CFBAE
  If0' :: CFBAE -> CFBAE -> CFBAE -> CFBAE
  deriving (Show,Eq)

-- prime types are types in our new lang 

elabCFBAE :: CFBAE -> CFAE
elabCFBAE (Num' x) = (Num x) -- this is called a catamorphism
elabCFBAE (Plus' l r) =(Plus (elabCFBAE l)(elabCFBAE r))
elabCFBAE (Minus' l r) =(Minus (elabCFBAE l)(elabCFBAE r))
elabCFBAE (Lambda' i b) = ( Lambda i (elabCFBAE b))
elabCFBAE (App' f a) = (App (elabCFBAE f)(elabCFBAE a))
elabCFBAE (Bind' i v b) = (App (Lambda i (elabCFBAE b)) (elabCFBAE v))
elabCFBAE (Id' i) = (Id i)
elabCFBAE (If0' c t1 t2) = (If0 (elabCFBAE c)(elabCFBAE t1)(elabCFBAE t2))

--- core lang is subset of lang (easier to prove or verify)
-- translation from lang to subset of lang is fairly error prone free
-- can make a larger language from core language 
-- can make lists, booleans from this smaller language

evalCFBAE :: Env' -> CFBAE -> (Maybe CFAEValue)
evalCFBAE e x = evalStatCFAE e (elabCFBAE x)

--last prob elaborator and other thing 

-- Test Cases

-- Note that these can be loaded separately using p3-test.hs if you do not
-- want to copy/paste into your project solution.

-- Tests for evalDynCFAE and evalDynCFAE.  test2 and test3 should demonstrate
-- the difference between static and dynamic scoping.  If you get the same
-- results with both interpreters, you've got problems.

test0=(App (Lambda "inc" (Id "inc")) (Lambda "x" (Plus (Id "x") (Num 1))))
test1=(App (Lambda "inc" (App (Id "inc") (Num 3))) (Lambda "x" (Plus (Id "x") (Num 1))))
test2=(App (Lambda "n" (App (Lambda "inc" (App (Lambda "n" (App (Id "inc") (Num 3))) (Num 3))) (Lambda "x" (Plus (Id "x") (Id "n"))))) (Num 1))
test3=(App (Lambda "Sum" (App (Id "Sum") (Num 3))) (Lambda "x" (If0 (Id "x") (Num 0) (Plus (Id "x") (App (Id "Sum") (Minus (Id "x") (Num 1)))))))

-- List of tests if you would like to use map for testing

testsStat = map (evalStatCFAE []) [test0,test1,test2,test3]

testsDyn = map (evalDynCFAE []) [test0,test1,test2,test3]

-- Tests for evalCFBAE and evalDynCFAE.  These are the same tests as above
-- using Bind.  You should get the same results from evalCFBAE that you
-- get from evalStateCFAE.

test0'= (Bind' "inc" (Lambda' "x" (Plus' (Id' "x") (Num' 1))) (Id' "inc"))
test1' = (Bind' "inc" (Lambda' "x" (Plus' (Id' "x") (Num' 1))) (App' (Id' "inc") (Num' 3)))
test2' = (Bind' "n" (Num' 1) (Bind' "inc" (Lambda' "x" (Plus' (Id' "x") (Id' "n"))) (Bind' "n" (Num' 3) (App' (Id' "inc") (Num' 3)))))
test3' = (Bind' "Sum" (Lambda' "x" (If0' (Id' "x") (Num' 0) (Plus' (Id' "x") (App' (Id' "Sum") (Minus' (Id' "x") (Num' 1)))))) (App' (Id' "Sum") (Num' 3)))

-- List of tests if you would like to use map for testing

tests' = map elabCFBAE [test0',test1',test2',test3']