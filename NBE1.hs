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
             ViewPatterns,
             ScopedTypeVariables
  #-}
-- ----------------------------------------------------------------------------
-- Imports
-- ----------------------------------------------------------------------------

import Prelude
  hiding (div)
import Control.Monad.State
import Control.Applicative

-- ----------------------------------------------------------------------------
-- Terms (Syntactic Domain & Normal Forms)
-- ----------------------------------------------------------------------------

{-
A,B ::= Rational | A -> B
-}

data Typ
  = Rat
  | Typ :-> Typ

infixr 0 :->

{-
x     variable
r     rational numbers
L,M,N ::= x | r | _+_ | _-_ | _*_ | _/_ | signum
        | \ x . N | L M
-}

data Syn var a where
  Var :: var a -> Syn var a
  Lit :: Rational -> Syn var Rat

  Add :: Syn var (Rat :-> Rat :-> Rat)
  Sub :: Syn var (Rat :-> Rat :-> Rat)
  Mul :: Syn var (Rat :-> Rat :-> Rat)
  Div :: Syn var (Rat :-> Rat :-> Rat)
  Sig :: Syn var (Rat :-> Rat)

  Abs :: (var a -> Syn var b) -> Syn var (a :-> b)
  App :: Syn var (a :-> b) -> Syn var a -> Syn var b

type Synt a = forall var. Syn var a

-- ----------------------------------------------------------------------------
-- Semantic Domain
-- ----------------------------------------------------------------------------

type family Sem (var :: Typ -> *) (a :: Typ) :: * where
  Sem var Rat       = Syn var Rat
  Sem var (a :-> b) = Sem var a -> Sem var b

newtype Val var a = Val {unVal :: Sem var a}

-- ----------------------------------------------------------------------------
-- Semuation
-- ----------------------------------------------------------------------------

eval :: Syn (Val var) a -> Sem var a

eval (Var x)     = unVal x
eval (Lit r)     = Lit r

eval Add         = \ x y -> Add `App` x `App` y
eval Sub         = \ x y -> Sub `App` x `App` y
eval Mul         = \ x y -> Mul `App` x `App` y
eval Div         = \ x y -> Div `App` x `App` y
eval Sig         = \ x   -> Sig `App` x

eval (Abs f)     = \ x -> eval (f (Val x))
eval (App l m)   = (eval l) (eval m)

-- ----------------------------------------------------------------------------
-- Reification
-- ----------------------------------------------------------------------------

reify :: STyp a -> Sem var a -> Syn var a
reify SRat       m = m
reify (SFun a b) f = Abs (\ x -> reify b (f (reflect a (Var x))))

reflect :: STyp a ->  Syn var a -> Sem var a
reflect SRat       m = m
reflect (SFun a b) l = (\ x -> reflect b (l `App` (reify a x)))

data STyp :: Typ -> * where
  SRat :: STyp Rat
  SFun :: STyp a -> STyp b -> STyp (a :-> b)

-- ----------------------------------------------------------------------------
-- Normalisation (NBE)
-- ----------------------------------------------------------------------------

norm :: forall a var. STyp a -> Synt a -> Syn var a
norm a m = reify a (eval (m :: Syn (Val var) a))

-- ----------------------------------------------------------------------------
-- Continuation (Condensity) Monad
-- ----------------------------------------------------------------------------

type CodM var a = Cnt (Syn var) a

data Cnt c b where
  Cnt :: (forall (a :: Typ). (b -> c a) -> c a) -> Cnt c b

runCnt :: Cnt c b -> (forall a. (b -> c a) -> c a)
runCnt (Cnt k) = k

shiftC :: (forall a. (b -> c a) -> c a) -> Cnt c b
shiftC k = Cnt k

resetC :: Cnt trm (trm c) -> trm c
resetC m = runCnt m id

instance Monad (Cnt trm) where
  return x = Cnt (\ k -> k x)
  m >>= f  = Cnt (\ k -> runCnt m (\ x -> runCnt (f x) k))

instance Functor (Cnt trm) where
  fmap  = liftA

instance Applicative (Cnt trm) where
  pure  = return
  (<*>) = ap
