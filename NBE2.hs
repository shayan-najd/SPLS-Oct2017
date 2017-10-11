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
import Control.Applicative

-- ----------------------------------------------------------------------------
-- Terms (Syntactic Domain & Normal Forms)
-- ----------------------------------------------------------------------------

{-
A,B ::= Rational | A -> B | Bool
-}

data Typ
  = Rat
  | Typ :-> Typ
  | Bol


infixr 0 :->

{-
x     variable
r     rational numbers
L,M,N ::= x | r | _+_ | _-_ | _*_ | _/_ | signum
        | \ x . N | L M
        | is0
        | True | False | if L then M else N
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

  Is0 :: Syn var (Rat :-> Bol)

  Tru :: Syn var Bol
  Fal :: Syn var Bol
  If_ :: Syn var Bol -> Syn var a -> Syn var a -> Syn var a

type Synt a = forall var. Syn var a

-- ----------------------------------------------------------------------------
-- Semantic Domain
-- ----------------------------------------------------------------------------

type family Sem (var :: Typ -> *) (a :: Typ) :: * where
  Sem var Rat       = Syn var Rat
  Sem var Bol       = Bool
  Sem var (a :-> b) = Sem var a -> CodM var (Sem var b)

type SemC var a = CodM var (Sem var a)

-- ----------------------------------------------------------------------------
-- Evaluation
-- ----------------------------------------------------------------------------

newtype Val var a = Val {unVal :: Sem var a}

eval :: Syn (Val var) a -> SemC var a
eval (Var x)     = return (unVal x)
eval (Lit r)     = return (Lit r)

eval Add         = return (\ x -> return (\ y -> return (Add `App` x `App` y)))
eval Sub         = return (\ x -> return (\ y -> return (Sub `App` x `App` y)))
eval Mul         = return (\ x -> return (\ y -> return (Mul `App` x `App` y)))
eval Div         = return (\ x -> return (\ y -> return (Div `App` x `App` y)))
eval Sig         = return (\ x -> return (Sig `App` x))
eval Is0         = return (\ x -> reflect SBol (Is0 `App` x))

eval (Abs f)     = return (\ x -> eval (f (Val x)))
eval (App l m)   = do u <- eval l
                      v <- eval m
                      u v

eval Tru         = return True
eval Fal         = return False
eval (If_ l m n) = do u <- eval l
                      v <- eval m
                      w <- eval n
                      return (if u then v else w)

-- ----------------------------------------------------------------------------
-- Reificaion
-- ----------------------------------------------------------------------------

reify :: STyp a -> Sem var a -> Syn var a
reify SRat       m = m
reify (SFun a b) f = Abs (\ x -> reifyC b (do v <- reflect a (Var x)
                                              f v))
reify SBol       m = if m then Tru else Fal

reifyC :: STyp a -> SemC var a -> Syn var a
reifyC a c = reset (do v <- c
                       return (reify a v))

reflect :: STyp a ->  Syn var a -> CodM var (Sem var a)
reflect SRat       m = return m
reflect (SFun a b) l = return (\ x -> reflect b (l `App` (reify a x)))
reflect SBol       m = shift  (\ k -> If_ m (k True) (k False))

data STyp :: Typ -> * where
  SRat :: STyp Rat
  SBol :: STyp Bol
  SFun :: STyp a -> STyp b -> STyp (a :-> b)

-- ----------------------------------------------------------------------------
-- Normalisation
-- ----------------------------------------------------------------------------

norm :: STyp a -> Synt a -> Synt a
norm a = reifyC a . eval

-- ----------------------------------------------------------------------------
-- Continuation (Condensity) Monad
-- ----------------------------------------------------------------------------

type CodM var a = Cnt (Syn var) a

data Cnt c b where
  Cnt :: (forall (a :: Typ). (b -> c a) -> c a) -> Cnt c b

runCnt :: Cnt c b -> (forall a. (b -> c a) -> c a)
runCnt (Cnt k) = k

shift :: (forall a. (b -> c a) -> c a) -> Cnt c b
shift k = Cnt k

reset :: Cnt trm (trm c) -> trm c
reset m = runCnt m id

instance Monad (Cnt trm) where
  return x = Cnt (\ k -> k x)
  m >>= f  = Cnt (\ k -> runCnt m (\ x -> runCnt (f x) k))

instance Functor (Cnt trm) where
  fmap  = liftA

instance Applicative (Cnt trm) where
  pure  = return
  (<*>) = ap
