module TT where

type Color = String
data CVal = CVar String | Zero
  deriving (Show,Eq)
type Name = String

data Term = TU
          | TPi Term Term
          | TLam Name Term
          | TApp Term Term
          | TVar Name
{-

    Γ ⊢ a : T0     Γ ⊢ p : <i>T ∋ a
--------------------------------------
     Γ ⊢ (a,p) : [i]T

-}
          | TCPair Term Term
{-
  Γ ⊢{I} t : [i]A
------------------------
  Γ ⊢{I,i} ti : A
-}
          | TCApp Term CVal
{-
  Γ ⊢{I,i} t : A
------------------------
  Γ ⊢{I} <i>t : [i]A
-}
          | TCLam Color Term
          | TCPi Term -- [i]A = Π<i>A
{-
  Γ ⊢ u:A0  Γ ⊢ A:[i]U
------------------------
  Γ ⊢ A ∋ u : U
-}
          | TNi Term Term
{-

    Γ ⊢ P : A -> U
------------------------
  Γ ⊢ Ψ P : <i>U ∋ A

-}
          | TPsi Term
{-

    Γ ⊢ g : (x:[i]A) -> B[xi/x] ∋ f(x0)
--------------------------------------
     Γ ⊢ φ g : <i>(x:A) -> B ∋ f

-}

          | TPhi Term
          | TParam Term
--     Γ,(x:[i]A) ⊢{I,i} t : B
-- --------------------------------------
--      Γ ⊢{I,i} : λ{i}x. t : (x:A) -> B

          | TILam Color Name Term
  deriving Show

-- It's tempting to try to define φg:
-- (f,φg)i a = (f a(i0), g (<i>a))i
-- (f,φg)i = λx. (f x(i0), g (<i>x))i -- but: not valid
-- (f,φg) = <i> (λx. (f x(i0), g (<i>x))i)
-- φg = <i> (λx. (f x(i0), g (<i>x))i)!

-- It should probably be so: if one abstracts over A[i], one can get instead [i]A:

--     Γ,(x:[J]A) ⊢{I,J} t : B
-- --------------------------------------
--      Γ ⊢{I,J} : λ{J}x. t : (x:A) -> B

-- Then:
-- φg = <i> (λ{i}x. (f x0, g x)i)!


tphi :: Term -> Term -> Term
tphi f g = TParam (TCLam "i" $ TILam "i" "x" $ TCPair (f `TApp` (TVar "x" `TCApp` Zero)) (g `TApp` TVar "x"))


-- Natural numbers example:
-- (<i> f ((A,ΨP)i) ((z,z')i) (λ{i}x. (s x0, s x0 x!)i))!

-- An alternative is a way to transform variables of A[i] to [i]A:
-- Γ ⊢{I,i} A  x:A ∈ Γ
-- --------------------
-- Γ ⊢{I} x/i:[i]A

type Env = [(String,Val)]

data Val = Var String
         | Pi Val Val
         | App Val Val
         | U
         | Lam (Val -> Val)
         | CPair Val Val
         | CApp Val CVal
         | Param Val
         | CLam (CVal -> Val)
         | CPi Val
         | Phi Val
         | Psi Val
         | Ni Val Val

eval :: Term -> Env -> Val
eval t0 rho =
  let ev t = eval t rho
  in case t0 of
  TU -> U
  TPi a b -> Pi (ev a) (ev b)
  TLam x a -> Lam (\v -> eval a ((x,v):rho))
  TApp a b -> app (ev a) (ev b)
  TVar x -> Var x
  TCPair a b -> cpair (ev a) (ev b)
  TCApp f i -> capp (ev f) i
  TCLam xi a -> clam xi (ev a)
  TCPi a -> CPi (ev a)
  TNi a b -> ni (ev a) (ev b)
  TPsi a -> Psi (ev a)
  TPhi a -> Phi (ev a)
  TParam a -> param (ev a)
  TILam i x a -> Lam (\v -> eval a ((x,CLam $ \j -> ceval i j v):rho))

clam' :: (CVal -> Val) -> Val
clam' f | (CApp a (CVar "__RESERVED__")) <- f (CVar "__RESERVED__") = a
   -- eta contraction (no need for occurs check!)

clam :: Color -> Val -> Val
clam xi t = clam' (\i -> ceval xi i t)

cpair :: Val -> Val -> Val
cpair _ (Param t) = t
cpair a b = CPair a b

ceval :: Color -> CVal -> Val -> Val
ceval i p = ceval' (\j -> if i==j then p else CVar j)

ceval' :: (Color -> CVal) -> Val -> Val
ceval' s v0 =
  let ev = ceval' s in
  case v0 of
    Pi a b -> Pi (ev a) (ev b)
    App a b -> app (ev a) (ev b)
    U -> U
    Lam f -> Lam (ev . f)
    CPair a b -> cpair (ev a) (ev b)
    CApp a Zero -> capp (ev a) Zero
    CApp a (CVar i) -> capp (ev a) (s i)
    CPair a b -> cpair (ev a) (ev b)
    CLam f -> clam' (ev . f)
    CPi x -> CPi (ev x)
    Phi a -> Phi (ev a)
    Psi a -> Psi (ev a)
    Ni a b -> ni (ev a) (ev b)
    Param a -> param (ev a)

param :: Val -> Val
param (CPair _ p) = p
param x = Param x

proj :: Color -> Val -> Val
proj i = ceval i Zero

app :: Val -> Val -> Val
app (Lam f) a = f a
app (CApp (CPair f (Phi g)) (CVar i)) a = CPair (f `app` proj i a) (g `app` CLam (\j -> ceval i j a)) `capp` CVar i
app f a = App f a

face :: Val -> Val
face x = capp x Zero

capp :: Val -> CVal -> Val
capp (CLam f) x = f x
capp (CPair a _) Zero = a
capp f (CVar a) = CApp f (CVar a)

ni :: Val -> Val -> Val
ni (CPair _ (Psi p)) a = app p a
ni a b = Ni a b

conv :: [String] -> Val -> Val -> Bool
conv (n:ns) t0 t'0 = eq t0 t'0 where
  (===) = conv (n:ns)
  eq (Var x) (Var y) = x == y
  eq (Pi a b) (Pi a' b') = a === a' && b === b'
  eq (Lam f) (Lam f') = conv ns (f (Var n)) (f' (Var n))
  eq (Lam f) t = conv ns (f (Var n)) (app t (Var n))
  eq t (Lam f) = conv ns (f (Var n)) (app t (Var n))
  eq (App a b) (App a' b') = a === a' && b === b'
  eq U U = True
  eq (Param a) (Param a') = a === a'
  eq (CPair a b) (CPair a' b') =  a === a' && b === b'
  eq (CApp a b) (CApp a' b') = a === a' && b == b'
  eq (CLam f) (CLam f') = conv ns (f (CVar n)) (f' (CVar n))
  eq (CLam f) t = conv ns (f (CVar n)) (capp t (CVar n))
  eq t (CLam f) = conv ns (f (CVar n)) (capp t (CVar n))
  eq (CPi a) (CPi a') = a === a'
  eq (Psi a) (Psi a') = a === a'
  eq (Ni a b)(Ni a' b') =  a === a' && b === b'
  eq _ _ = False
