module New where

type Color = String
data CVal = CVar String | Zero | Param
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
     Γ ⊢ (a,p) : <i>T

-}
          | TCPair Term Term
          | TCApp Term CVal
          | TCLam Color Term
          | TCPi Term
          | TNi Term Term
          | TPsi Term
{-

    Γ ⊢ g : (x:[i]A) -> B[xi/x] ∋ f(x0)
--------------------------------------
     Γ ⊢ phi g : <i>(x:A) -> B ∋ f

-}
            
          | TPhi Term
  deriving Show

type Env = [(String,Val)]

data Val = Var String
         | Pi Val Val
         | App Val Val
         | U
         | Lam (Val -> Val)
         | CPair Val Val
         | CApp Val CVal
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
  TCLam xi a -> CLam (\i -> ceval (ev a) xi i)
  TCPi a -> CPi (ev a)
  TNi a b -> ni (ev a) (ev b)
  TPsi a -> Psi (ev a)
  TPhi a -> Phi (ev a)

cpair _ (CApp t Param) = t
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
    CApp a (CVar j) | i==j -> capp a e -- i is not in scope in a
    CApp a b -> capp (ev a) b
    CPair a b -> cpair (ev a) (ev b)
    CLam f -> CLam (ev . f)
    CPi x -> CPi (ev x)
    Phi a -> Phi (ev a)
    Psi a -> Psi (ev a)
    Ni a b -> ni (ev a) (ev b)

proj i a = ceval a i Zero
param i a = ceval a i Param

app (Lam f) a = f a
app (CApp (CPair f (Phi g)) (CVar i)) a = CPair (f `app` proj i a) (g `app` CLam (\j -> ceval a i j))
app f a = App f a

capp (CLam f) x = f x
capp (CPair a _) Zero = a
capp (CPair _ b) Param = b
capp f a = CApp f a

ni (Psi p) a = app p a
ni a b = Ni a b
