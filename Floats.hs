{-# OPTIONS_GHC -Wall -fno-warn-unticked-promoted-constructors #-}
{-# LANGUAGE RankNTypes,
             TypeSynonymInstances,
             FlexibleInstances,
             StandaloneDeriving,
             DataKinds,
             KindSignatures,
             TypeOperators,
             GADTs,
             TypeFamilies,
             PatternSynonyms,
             ViewPatterns
  #-}
-- ----------------------------------------------------------------------------
-- Imports
-- ----------------------------------------------------------------------------

import Control.Monad.State
import Control.Monad.Cont
import Data.List

-- ----------------------------------------------------------------------------
-- Normal Forms
-- ----------------------------------------------------------------------------

{-
x     variable
R     rational numbers
L,M,N ::= x | R | M + N | M - N | M * N | M / N | signum M
        | if0 L then M else N
P     ::= \ x . P | N
-}

data Exp v
  = Var v
  | Lit Rational
  | Add (Exp v) (Exp v)
  | Sub (Exp v) (Exp v)
  | Mul (Exp v) (Exp v)
  | Div (Exp v) (Exp v)
  | Sig (Exp v)
  | If0 (Exp v) (Exp v) (Exp v)

type Expr = forall v. Exp v

data Prg v
  = Bdy (Exp v)
  | Abs (v -> Prg v)

type Prog = forall v. Prg v

-- ----------------------------------------------------------------------------
-- Compiler
-- ----------------------------------------------------------------------------

compile :: Prog -> C

-- ----------------------------------------------------------------------------
-- examples
-- ----------------------------------------------------------------------------

oneP :: Expr
oneP = Lit 1.0

squareP :: Prog
squareP = Abs (\ x -> Bdy (Mul (Var x) (Var x)))

inc :: Prog
inc = Abs (\ x -> Bdy (Add (Var x) oneP))

-- ----------------------------------------------------------------------------
-- Embedding Exp
-- ----------------------------------------------------------------------------

instance Num (Exp v) where
  fromInteger  = Lit . fromInteger
  (+)          = Add
  (-)          = Sub
  (*)          = Mul
  abs          = \ m -> Sig m * m
  signum       = Sig

instance Fractional (Exp v) where
  (/)          = Div
  fromRational = Lit

abs1 :: (Exp v -> Exp v) -> Prg v
abs1 f = Abs (Bdy . f . Var)

abs2 :: (Exp v -> Exp v -> Exp v) -> Prg v
abs2 f = Abs (\ x -> abs1 (f (Var x)))

-- ----------------------------------------------------------------------------
-- Example programs
-- ----------------------------------------------------------------------------

oneP' :: Expr
oneP' = 1.0

squareP' :: Prog
squareP' = abs1 (\ x -> x * x)

inc' :: Prog
inc' = abs1 (\ x -> x + oneP)

inc'' :: Prog
inc'' = abs1 (+ oneP)

idP :: Prog
idP = abs1 id

halfP :: Prog
halfP = abs1 (flip (/) 2)

averageP :: Prog
averageP = abs2 (\ x y -> (x + y) / 2)

average :: Fractional a => a -> a -> a
average x y = (x + y) / 2

averageP' :: Prog
averageP' = abs2 average

averageOE :: Exp v -> Exp v -> Exp v
averageOE x y = If0 (x - y) x (average x y)

averageOP :: Prog
averageOP = abs2 averageOE

-- ----------------------------------------------------------------------------
-- Problem I
-- ----------------------------------------------------------------------------

averageOE' :: (Eq a, Fractional a) => a -> a -> a
averageOE' x y = if x == y then x else average x y

averageOP' :: Prog
averageOP' = abs2 averageOE'

instance Eq (Exp v) where
 (==) = undefined
        -- what to write above?
        -- candidate:
        --   \ x y -> If0 (x - y) True False
        -- but impossible since body of If0 is not term


-- back to slides














































-- ----------------------------------------------------------------------------
-- Solution I
-- ----------------------------------------------------------------------------

is0M :: Exp v -> ContM v Bool
is0M x = shift (\ k -> If0 x (k True) (k False))

equalM :: Exp v -> Exp v -> ContM v Bool
equalM x y = is0M (x - y)

averageME :: Exp v -> Exp v -> ContM v (Exp v)
averageME x y = do b <- equalM x y
                   return (if b then x else average x y)

averageMP :: Prog
averageMP = abs2 (\ x y -> reset (averageME x y))

-- https://github.com/shayan-najd/SPLS-Oct2017












































-- ----------------------------------------------------------------------------
-- Problem II
-- ----------------------------------------------------------------------------

power :: Num a => Nat -> a -> a
power Zero     _ = 1
power (Succ n) x = x * (power n x)

powerP :: Nat -> Prog
powerP n = Abs (Bdy . power n . Var)

powerP3 :: String
powerP3 = showP (powerP (Succ (Succ (Succ Zero))))

{- "Abs1 (\\ x0 ->  Mul (x0) (Mul (x0) (Mul (x0) (Lit 1 % 1))))" -}

powerP3C :: IO ()
powerP3C  = putStrLn (compile (powerP (Succ (Succ (Succ Zero)))))

{-
double main (double x0)
  {
    return ((x0) * ((x0) * ((x0) * (1.0))));
  }
-}

-- ----------------------------------------------------------------------------
-- Solution II
-- ----------------------------------------------------------------------------

data RatS v
  = Sta Rational
  | Dyn (Exp v)

instance Num (RatS v) where
  fromInteger r       = Sta (fromInteger r)

  (Sta r1) + (Sta r2) = Sta (r1 + r2)
  (Sta 0)  + (Dyn n)  = Dyn n
  (Sta r1) + (Dyn n)  = Dyn (Lit r1 + n)
  (Dyn m)  + (Sta 0)  = Dyn m
  (Dyn m)  + (Sta r2) = Dyn (m + Lit r2)
  (Dyn m)  + (Dyn n)  = Dyn (m + n)

  (Sta r1) - (Sta r2) = Sta (r1 - r2)
  (Sta 0)  - (Dyn n)  = Dyn (negate n)
  (Sta r1) - (Dyn n)  = Dyn (Lit r1 - n)
  (Dyn m)  - (Sta 0)  = Dyn m
  (Dyn m)  - (Sta r2) = Dyn (m - Lit r2)
  (Dyn m)  - (Dyn n)  = Dyn (m - n)

  (Sta r1) * (Sta r2) = Sta (r1 * r2)
  (Sta 1)  * (Dyn n)  = Dyn n
  (Sta r1) * (Dyn n)  = Dyn (Lit r1 * n)
  (Dyn m)  * (Sta 1)  = Dyn m
  (Dyn m)  * (Sta r2) = Dyn (m * Lit r2)
  (Dyn m)  * (Dyn n)  = Dyn (m * n)

  abs (Sta r)         = Sta (abs r)
  abs (Dyn m)         = Dyn (abs m)

  signum (Sta r)      = Sta (signum r)
  signum (Dyn m)      = Dyn (signum m)

instance Fractional (RatS v) where
  fromRational r      = Sta r

  (Sta r1) / (Sta r2) = Sta (r1 / r2)
  (Sta r1) / (Dyn n)  = Dyn (Lit r1 / n)
  (Dyn m)  / (Sta 1)  = Dyn m
  (Dyn m)  / (Sta r2) = Dyn (m / Lit r2)
  (Dyn m)  / (Dyn n)  = Dyn (m / n)

ratSU :: Exp v -> RatS v
ratSU = Dyn

ratSD :: RatS v -> Exp v
ratSD (Sta r) = Lit r
ratSD (Dyn m) = m

powerSP :: Nat -> Prog
powerSP n = Abs (Bdy . ratSD . power n . ratSU . Var)

powerSP3 :: String
powerSP3 = showP (powerSP (Succ (Succ (Succ Zero))))

{- "Abs1 (\\ x0 -> Mul (x0) (Mul (x0) (x0)))" -}

powerSP3C :: IO ()
powerSP3C  = putStrLn (compile (powerSP (Succ (Succ (Succ Zero)))))

{-
double main (double x0)
  {
    return ((x0) * ((x0) * (x0)));
  }
-}





-- ----------------------------------------------------------------------------
-- Show Instances
-- ----------------------------------------------------------------------------

instance Show (Exp String) where
  show (Var x)     = x
  show (Lit r)     = "Lit " ++ show r
  show (Add m n)   = "Add (" ++ show m ++ ") (" ++ show n ++ ")"
  show (Sub m n)   = "Sub (" ++ show m ++ ") (" ++ show n ++ ")"
  show (Mul m n)   = "Mul (" ++ show m ++ ") (" ++ show n ++ ")"
  show (Div m n)   = "Div (" ++ show m ++ ") (" ++ show n ++ ")"
  show (Sig m)     = "Sig (" ++ show m ++ ")"
  show (If0 l m n) = "If0 (" ++ show l ++ ")"
                      ++ "(" ++ show m ++ ") (" ++ show n ++ ")"

type NameM a = State Int a

newName :: NameM String
newName = do i <- get
             put (succ i)
             return ("x" ++ show i)

instance Show (Prg String) where
  show m = evalState (showM m) 0
    where
      showM (Bdy n) = return ("Bdy " ++ show n)
      showM (Abs f) = do x <- newName
                         w <- showM (f x)
                         return ("Abs (\\ " ++ x ++ " -> " ++ w ++ ")")

showP :: Prog -> String
showP m = show (m :: Prg String)

-- ----------------------------------------------------------------------------
-- Compiler
-- ----------------------------------------------------------------------------

type Var = String
type C   = String

compileExp :: Exp Var -> C
compileExp (Var x)     = x
compileExp (Lit r)     = show (fromRational r :: Double)
                         -- ToDo: don't show too large literals!
compileExp (Add m n)   = "(" ++ compileExp m ++ ") + (" ++ compileExp n ++ ")"
compileExp (Sub m n)   = "(" ++ compileExp m ++ ") - (" ++ compileExp n ++ ")"
compileExp (Mul m n)   = "(" ++ compileExp m ++ ") * (" ++ compileExp n ++ ")"
compileExp (Div m n)   = "(" ++ compileExp m ++ ") / (" ++ compileExp n ++ ")"
                         -- ToDo: division by zero?!
compileExp (Sig m)     = "sig (" ++ compileExp m ++ ")"
compileExp (If0 l m n) = "(" ++ compileExp l ++ ") == 0 ? " ++
                         "(" ++ compileExp m ++ ") : (" ++ compileExp n ++ ")"

type VarM a = State ([Var], Int) a

newVar :: VarM Var
newVar = do (xs, i) <- get
            let x = "x" ++ show i
            put (xs ++ [x], succ i)
            return x

compile m = let (c, (xs, _)) = runState (compile' m) ([], 0)
            in "double main (" ++ intercalate ", " [ "double " ++ x | x <- xs ]
                               ++ ")\n  {\n    return (" ++ c ++ ");\n  }"
  where
    compile' :: Prg Var -> VarM C
    compile' (Bdy n) = return (compileExp n)
    compile' (Abs f) = do x <- newVar
                          compile' (f x)


-- ----------------------------------------------------------------------------
-- Useful definitions
-- ----------------------------------------------------------------------------

data Nat
  = Zero
  | Succ Nat

type ContM v a = Cont (Exp v) a

shift :: ((a -> Exp v) -> Exp v) -> ContM v a
shift = cont

reset :: ContM v (Exp v) -> Exp v
reset = flip runCont id
