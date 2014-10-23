{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module Cubes3 where

import Data.Maybe
import Data.List

type Cub a b = [a] -> b
type Color = String
type Cube a = Cub Color a
type SubCube {-n-} a = Cube a


-- sublists' xs0 = case xs0 of
--   [] -> []
--   x:xs -> [x] : do
--     s <- sublists' xs
--     [s,x:s]

-- sublists xs0 = []:sublists' xs0

strictSublists = init . sublists

-- -- set xs = border xs U

sublists [] = [[]]
sublists (x:xs) = sublists xs ++ map (x:) (sublists xs)

type Env = [(String,Cub String Val)]

data Term = TU | TPi String Term Term | TLam String Term | TApp Term Term | TVar String | TParam Color Term | TPair Color Term Term | TParamIn Color Term Term
  deriving Show

class Nominal a where
  swap :: a -> (Color,Color) -> a
  support :: a -> [Color]

fresh :: Nominal a => a -> Color
fresh = gensym . support

freshs :: Nominal a => a -> [Color]
freshs = gensyms . support

gensym :: [Color] -> Color
gensym xs = head $ (map show [(0::Integer)..]) \\ xs

gensyms :: [Color] -> [Color]
gensyms d = let x = gensym d in x : gensyms (x : d)

instance Nominal Color where
  swap k (i,j) | k == i = j
               | k == j = i
               | otherwise = k

  support i = [i]

instance Nominal Term where
  swap u ij =
    let sw t = swap t ij
    in case u of
      TU -> TU
      TPi x a b -> TPi x (sw a) (sw b)
      TLam x b -> TLam x (sw b)
      TApp f a -> TApp (sw f) (sw a)
      TVar x -> TVar x
      TParam k t -> TParam (sw k) (sw t)
      TPair k a p -> TPair (sw k) (sw a) (sw p)

apps :: Val -> [Val] -> Val
apps f as = foldl App f as

lkCub :: (Show a1, Eq a1) => a1 -> [(a1, a)] -> a
lkCub pos cub = case lookup pos cub of
  Just x -> x
  Nothing -> error $ "ColorSet not found: " ++ show pos

mkCub :: [([Color],a)] -> Cube a
mkCub = flip lkCub

interior :: Color -> Cube x -> Cube x
interior i q is = q (i:is)

predic :: Value -> [(Excl)] -> Val
predic typ xss = multiPi typ [] xss $ \_ -> U

multiPi :: Value -> [(Excl,Val)] -> [(Excl)] -> (Value -> Val) -> Val
multiPi _typ vars [] k = k (\xs -> lkCub xs vars)
multiPi typ vars (xs:xss) k = Pi (typ xs `apps` [lkCub x vars | x <- strictSublists xs]) $
                              Lam $ \v -> multiPi typ ((xs,v):vars) xss k

multiLam :: [(Excl,Val)] -> [(Excl)] -> (Value -> Val) -> Val
multiLam vars [] k = k (mkCub vars)
multiLam vars (xs:xss) k = Lam $ \v -> multiLam ((xs,v):vars) xss k


type Natural = Integer
type Value = Cube Val
data Val = Var String | Pi Val Val | App Val Val | Lam (Val -> Val) | U

showCols = intercalate ","

vars xs = [[x] | x <- xs] ++ [x:ys | x <- xs, ys <- vars xs] 

freshVars = vars "xyzwstuv"

showValue :: Base -> Value -> String
showValue b v = vcat $ [ showCols is ++" ↦ "++showVal freshVars (v is) | is <- sublists b]

showVals su = hcat . map (showVal1 su)
hcat = foldr (<+>) " "
vcat = foldr (</>) ""


parens x = "("++x++")"
showVal1 :: [String] -> Val -> String
showVal1 _ U          = "U"
showVal1 _ (Var x)     = x
showVal1 su u           = parens $ showVal su u

x <+> y = x ++ " " ++ y
x </> y = x ++ "\n" ++ y
showVal :: [String] -> Val -> String
showVal _ U           = "U"
showVal (s:su) (Lam e)  = '\\' : showVal su x <+> "->" <+> showVal su (e x)
  where x = Var s
showVal su (Pi a f)    = "Pi" <+> showVals su [a,f]
showVal su (App u v)   = showVal su u <+> showVal1 su v
showVal su (Var x)     = x

apply :: [a] -> Val -> Cub a Val -> Val
apply base f u = f `apps` map u (sublists base)

sat :: [a] -> Val -> Cub a Val -> Val
sat base f u = f `apps` map u (strictSublists base)

appCub :: [a] -> Cub a Val -> Cub a Val -> Cub a Val
appCub base f u is = apply base (f is) u

-- satisfy :: Eq a => [a] -> [a] -> Cub a Val -> Cub a Val -> Cub a Val
-- satisfy base excl typ u xs = typ xs `apps` map u (sublists (base \\ excl))

type Base = [Color]
type Excl = [Color]

type FreshBase = (Int,Base)

rmCol :: Color -> FreshBase -> FreshBase
rmCol i (f,x:xs) = if i == x
                   then if f > 0 then (f-1,xs) else (f,xs)
                   else let (f',xs') = rmCol i (f-1,xs) in (f'+1,x:xs')

-- NOTE: The environment must provide enough "freshness" to interpret
-- parametricity (ie. very much).  The fresh colors in the base (after
-- the next index) MUST NOT clash with the free colors of the term NOR
-- with the colors of the returned value.

-- This last condition seems to indicate that the set of fresh colors
-- need to be split when interpreting the product type/intro/elim:

-- (f a)[fresh=θ++ι,ρ,χ] = f[θ,ρ(θ),χ] a[ι,ρ(ι),ψ] (for ψ ⊆ θ)

eval :: FreshBase -> Env -> Term -> Value
eval (next,base) env t0 is = let evalB = eval (next,base) in case t0 of
  TLam x b -> multiLam [] (sublists base) $ \x' -> evalB ((x,x'):env) b is
  TApp f u -> apply base (evalB env f is) (evalB env u)
  TVar x -> case lookup x env of
    Just x' -> x' is
  TParam i t -> eval (next+1,base) env (swap t (i,freshI)) (is++[freshI])
    where freshI = base !! next
  TPair i a p -> if i `elem` is
                 then eval (rmCol i (next,base)) env p (is \\ [i])
                 else eval (rmCol i (next,base)) env a is
  ty -> multiLam [] (strictSublists is) $ \v -> evalT next base env ty is v
        -- NOTE: we do not put the value bound ('v') in the environment; so it's ok if it is only partial.

evalT :: Int -> Base -> Env -> Term -> Excl -> Value -> Val
evalT next base env t0 excl v =
  let evalB = eval (next,base)
      evalTB = evalT next base
  in case t0 of
  TU -> predic v (strictSublists excl)
  TPi x a b -> multiPi (evalB env a) [] (sublists base) (\x' -> evalTB ((x,x'):env) b excl (appCub base v x'))
  TParamIn i t arg ->
      evalT (next+1) base env (swap t (i,freshI)) (excl++[freshI]) (\cs -> if freshI `elem` cs then v (cs \\ [freshI]) else evalB env arg cs)
      -- apply excl (evalB env (TParam i t) excl) (\cs -> if i `elem` cs then v (cs \\ [i]) else evalB env arg cs)
    where freshI = base !! next
  _ -> sat excl (evalB env t0 excl) v

--------------------------
-- Testing

absCub :: String -> Value
absCub x js = Var $ x ++ "["++showCols js ++"]"

swapExTm :: Term
swapExTm = TParam "j" (TPair "i" (TVar "a") (TVar "p") )

swapExEnv = [("a",absCub "a"),("p",absCub "p"),("A",absCub "A")]

freshBase n = take n $ vars "αβγδε"

swapEx = showValue base $ eval (0,base) swapExEnv swapExTm
   where base = freshBase 2

exU = putStrLn $ showValue boundBase $ eval base swapExEnv $ TU
   where base = (length boundBase, boundBase ++ freshBase 1)
         boundBase = ["i","j"]

exTy = putStrLn $ showValue boundBase $ eval base swapExEnv $
       (TParamIn "i" (TVar "A")  (TVar "a"))
       -- TParam "i" (TVar "A")
   where base = (length boundBase, boundBase ++ freshBase 1)
         boundBase = ["j"]

ex = putStrLn $ showValue boundBase $ eval base swapExEnv $ (TParam "j" $ TPair "i" (TVar "a") (TVar "p"))
   where base = (length boundBase, boundBase ++ freshBase 2)
         boundBase = ["i","k"]
