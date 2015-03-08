module New where

type Color = String
data CVal = CVar String | Zero
  deriving Show
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
-- φg = <i> (λ{i}x. (f x0, g x))i)!


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
         | CApp Val Color
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

clam' f | (CApp a "_") <- f (CVar "_") = a
   -- eta contraction (no need for occurs check!)

clam xi t = clam' (\i -> ceval t xi i)

cpair _ (Param t) = t
cpair a b = CPair a b

ceval :: Val -> Color -> CVal -> Val
ceval v0 i e =
  let ev v = ceval v i e in
  case v0 of
    Pi a b -> Pi (ev a) (ev b)
    App a b -> app (ev a) (ev b)
    U -> U
    Lam f -> Lam (ev . f)
    CPair a b -> cpair (ev a) (ev b)
    CApp a b -> capp (ev a) (CVar b)
    CPair a b -> cpair (ev a) (ev b)
    CLam f -> clam' (ev . f)
    CPi x -> CPi (ev x)
    Phi a -> Phi (ev a)
    Psi a -> Psi (ev a)
    Ni a b -> ni (ev a) (ev b)
    Param a -> param (ev a)

param (CPair _ p) = p
param x = Param x

proj i a = ceval a i Zero

app (Lam f) a = f a
app (CApp (CPair f (Phi g)) i) a = CPair (f `app` proj i a) (g `app` CLam (\j -> ceval a i j)) `capp` CVar i
app f a = App f a

capp (CLam f) x = f x
capp (CPair a _) Zero = a
capp f (CVar a) = CApp f a

ni (CPair _ (Psi p)) a = app p a
ni a b = Ni a b
