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

lkCub :: Eq a1 => a1 -> [(a1, a)] -> a
lkCub pos cub = fromJust $ lookup pos cub 

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

freshVars = vars "xyzwαβγδ"

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

-- NOTE: The environment must provide enough "freshness" to interpret
-- parametricity (ie. infinitely much).  The fresh colors in the
-- base (after the next index) MUST NOT clash with the free colors of
-- the term NOR with the colors of the returned value.

eval :: FreshBase -> Env -> Term -> Value
eval (next,base) env t0 is = let evalB = eval (next,base) in case t0 of
  TLam x b -> multiLam [] (sublists base) $ \x' -> evalB ((x,x'):env) b is
  TApp f u -> apply base (evalB env f) (evalB env u) is
  TVar x -> case lookup x env of
    Just x' -> x' is
  TParam i t -> eval (next+1,base) env (swap t (i,freshI)) (is++[freshI])
    where freshI = base !! next
  TPair i a p -> if i `elem` is
                 then eval (rmCol i (next,base)) env p (is \\ [i])
                 else eval (rmCol i (next,base)) env a is
  ty -> multiLam [] (strictSublists (base \\ is)) $ \v -> evalT next base env ty is v
        -- NOTE: we do not put the value bound ('v') in the environment; so it's ok if it is only partial.

evalT :: Int -> Base -> Env -> Term -> Excl -> Value -> Val
evalT next base env t0 excl v =
  let evalB = eval (next,base)
      evalTB = evalT next base
  in case t0 of
  TU -> predic v (strictSublists (base \\ excl))
  TPi x a b -> multiPi (evalB env a) [] (sublists base) (\x' -> evalTB ((x,x'):env) b excl (apply base v x'))
  _ -> satisfy base excl (evalB env t0) v excl

--------------------------
-- Testing

absCub :: String -> Value
absCub x js = Var $ x ++ "["++showCols js ++"]"

swapExTm :: Term
swapExTm = TParam "j" (TPair "i" (TVar "a") (TVar "p") )

swapExEnv = [("a",absCub "a"),("p",absCub "p")]

freshBase n = take n $ vars "ijkl"

swapEx = showValue base $ eval (0,base) swapExEnv swapExTm
   where base = freshBase 2

ex = putStrLn $ showValue ["z"] $ eval (0,base) swapExEnv $ (TParam "w" $ TPair "z" (TVar "a") (TVar "p"))
   where base = freshBase 2
