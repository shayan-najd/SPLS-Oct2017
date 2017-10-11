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

import Prelude
  hiding (div)
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
P     ::= \ x . P | \ x . N
-}

data Exp a
  = Var a
  | Lit Rational
  | Add (Exp a) (Exp a)
  | Sub (Exp a) (Exp a)
  | Mul (Exp a) (Exp a)
  | Div (Exp a) (Exp a)
  | Sig (Exp a)
  | If0 (Exp a) (Exp a) (Exp a)

type Expr = forall a. Exp a

data Prg a
  = Abs1 (a -> Exp a)
  | AbsN (a -> Prg a)

type Prog = forall a. Prg a

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
squareP = Abs1 (\ x -> Mul (Var x) (Var x))

inc :: Prog
inc = Abs1 (\ x -> Add (Var x) oneP)

-- ----------------------------------------------------------------------------
-- Embedding Exp
-- ----------------------------------------------------------------------------

instance Num (Exp a) where
  fromInteger  = Lit . fromInteger
  (+)          = Add
  (-)          = Sub
  (*)          = Mul
  abs          = \ m -> Sig m * m
  signum       = Sig

instance Fractional (Exp a) where
  (/)          = Div
  fromRational = Lit

-- ----------------------------------------------------------------------------
-- Example programs
-- ----------------------------------------------------------------------------

oneP' :: Expr
oneP' = 1.0

squareP' :: Prog
squareP' = Abs1 (\ x -> Var x * Var x)

inc' :: Prog
inc' = Abs1 (\ x -> Var x + oneP)

idP :: Prog
idP = Abs1 (id . Var)

halfP :: Prog
halfP = Abs1 (flip (/) 2 . Var)

averageP :: Prog
averageP = AbsN (\ x -> Abs1 (\ y -> (Var x + Var y) / 2))

average :: Fractional a => a -> a -> a
average x y = (x + y) / 2

averageP' :: Prog
averageP' = AbsN (\ x -> Abs1 (\ y -> average (Var x) (Var y)))

averageOE :: Exp a -> Exp a -> Exp a
averageOE x y = If0 (x - y) x (average x y)

averageOP :: Prog
averageOP = AbsN (\ x -> Abs1 (\ y -> averageOE (Var x) (Var y)))

-- ----------------------------------------------------------------------------
-- Problem I
-- ----------------------------------------------------------------------------

averageOE' :: (Eq a, Fractional a) => a -> a -> a
averageOE' x y = if x == y then x else average x y

averageOP' :: Prog
averageOP' = AbsN (\ x -> Abs1 (\ y -> averageOE' (Var x) (Var y)))



instance Eq (Exp a) where
 (==) = undefined
        -- what to write above?
        -- candidate:
        --   \ x y -> If0 (x - y) True False
        -- but impossible since body of If0 is not term


-- back to slides














































-- ----------------------------------------------------------------------------
-- Solution I
-- ----------------------------------------------------------------------------

is0M :: Exp a -> ContM a Bool
is0M x = shift (\ k -> If0 x (k True) (k False))

equalM :: Exp a -> Exp a -> ContM a Bool
equalM x y = is0M (x - y)

averageME :: Exp a -> Exp a -> ContM a (Exp a)
averageME x y = do b <- equalM x y
                   return (if b then x else average x y)
averageMP :: Prog
averageMP = AbsN (\ x -> Abs1 (\ y -> reset (averageME (Var x) (Var y))))














































-- ----------------------------------------------------------------------------
-- Problem II
-- ----------------------------------------------------------------------------

power :: Num a => Nat -> a -> a
power Zero     _ = 1
power (Succ n) x = x * (power n x)

powerP :: Nat -> Prog
powerP n = Abs1 (power n . Var)

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

data RatS a
  = Sta Rational
  | Dyn (Exp a)

instance Num (RatS a) where
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

instance Fractional (RatS a) where
  fromRational r      = Sta r

  (Sta r1) / (Sta r2) = Sta (r1 / r2)
  (Sta r1) / (Dyn n)  = Dyn (Lit r1 / n)
  (Dyn m)  / (Sta 1)  = Dyn m
  (Dyn m)  / (Sta r2) = Dyn (m / Lit r2)
  (Dyn m)  / (Dyn n)  = Dyn (m / n)

ratSU :: Exp a -> RatS a
ratSU = Dyn

ratSD :: RatS a -> Exp a
ratSD (Sta r) = Lit r
ratSD (Dyn m) = m

powerSP :: Nat -> Prog
powerSP n = Abs1 (ratSD . power n . ratSU . Var)

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
      showM (Abs1 f) = do x <- newName
                          let w = show (f x)
                          return ("Abs1 (\\ " ++ x ++ " -> " ++ w ++ ")")
      showM (AbsN f) = do x <- newName
                          w <- showM (f x)
                          return ("AbsN (\\ " ++ x ++ " -> " ++ w ++ ")")

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
    compile' (Abs1 f) = do x <- newVar
                           return (compileExp (f x))
    compile' (AbsN f) = do x <- newVar
                           compile' (f x)


-- ----------------------------------------------------------------------------
-- Useful definitions
-- ----------------------------------------------------------------------------

data Nat
  = Zero
  | Succ Nat

type ContM a b = Cont (Exp a) b

shift :: ((b -> Exp a) -> Exp a) -> ContM a b
shift = cont

reset :: ContM a (Exp a) -> Exp a
reset = flip runCont id
