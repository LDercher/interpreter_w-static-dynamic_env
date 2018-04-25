{--

author: Luke Dercher
student_id: l446d901
class: EECS 662

--}


{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad
import Test.HUnit
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

evalDynCFAETests =
  TestList [ "evalDynCFAE (Num 1) = 1" ~: fromJust (evalDynCFAE [] (Num 1)) ~?= (Num 1)
           , "evalDynCFAE (Plus(Num 1)(Num 1)) = 2" ~: fromJust (evalDynCFAE [] (Plus(Num 1)(Num 1)))  ~?= (Num 2)
           , "evalDynCFAE (Minus(Num 1)(Num 1)) = 0" ~: fromJust (evalDynCFAE [] (Minus(Num 1)(Num 1))) ~?= (Num 0)
           , "evalDynCFAE (App (Lambda x in x + x) 1)) = 2" ~: fromJust (evalDynCFAE [] (App (Lambda "x" (Plus x x )) (Num 1))) ~?= (Num 2)
           ]

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


allTests = TestList [evalDynCFAETests]

check = runTestTT allTests