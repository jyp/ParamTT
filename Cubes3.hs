{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module Cubes3 where

import Data.Maybe
import Data.List

type Cub a b = [a] -> b
type Color = String
type Cube a = Cub Color a
type SubCube {-n-} a = Cube a


sublists' xs0 = case xs0 of
  [] -> []
  x:xs -> [x] : do
    s <- sublists' xs
    [s,x:s]

sublists xs0 = []:sublists' xs0

strictSublists = init . sublists

-- set xs = border xs U

type Env = [(String,Cub String Val)]

data Term = TU | TPi String Term Term | TLam String Term | TApp Term Term | TVar String | TParam Color Term | TPair Color Term Term

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

lkCub :: Eq a1 => a1 -> [(a1, a)] -> a
lkCub pos cub = fromJust $ lookup pos cub 

mkCub :: [([Color],a)] -> Cube a
mkCub = flip lkCub

interior :: Color -> Cube x -> Cube x
interior i q is = q (i:is)

predic :: Value -> [(Excl,Val)] -> [(Excl)] -> Val
predic _typ _vars [] = U
predic typ vars (xs:xss) = Pi (typ xs `apps` [lkCub x vars | x <- strictSublists xs]) $
                           Lam $ \v -> predic typ ((xs,v):vars) xss

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

apply :: [a] -> Cub a Val -> Cub a Val -> Cub a Val
apply base f u xs = f xs `apps` map u (sublists base)

satisfy :: Eq a => [a] -> [a] -> Cub a Val -> Cub a Val -> Cub a Val
satisfy base excl typ u xs = typ xs `apps` map u (sublists (base \\ excl))

type Base = [Color]
type Excl = [Color]

type FreshBase = (Int,Base)

rmCol :: Color -> FreshBase -> FreshBase
rmCol i (f,x:xs) = if i == x
                   then if f > 0 then (f-1,xs) else (f,xs)
                   else let (f',xs') = rmCol i (f-1,xs) in (f'+1,x:xs')

eval :: FreshBase -> Env -> Term -> Value
eval (next,base) env t0 is = let evalB = eval (next,base) in case t0 of
  TLam x b -> multiLam [] (sublists base) $ \x' -> evalB ((x,x'):env) b is
  TApp f u -> apply base (evalB env f) (evalB env u) is
  TVar x -> case lookup x env of
    Just x' -> x' is
  TParam i t -> evalB env (swap t (i,freshI)) (is++[freshI])
    where freshI = base !! next
  TPair i a p -> if i `elem` is
                 then eval (rmCol i (next,base)) env p (is \\ [i])
                 else eval (rmCol i (next,base)) env a is
  ty -> multiLam [] (strictSublists (base \\ is)) $ \v -> evalT next base env ty is v

evalT :: Int -> Base -> Env -> Term -> Excl -> Value -> Val
evalT next base env t0 excl v =
  let evalB = eval (next,base)
      evalTB = evalT next base
  in case t0 of
  TU -> predic v [] (strictSublists (base \\ excl))
  TPi x a b -> multiPi (evalB env a) [] (sublists base) (\x' -> evalTB ((x,x'):env) b excl (apply base v x'))
  _ -> satisfy base excl (evalB env t0) v excl

--------------------------
-- Testing
  
absCub :: String -> Value
absCub x js = Var $ x ++ concat js
