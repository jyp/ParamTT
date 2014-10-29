{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module Cubes4 where

import Data.List
import Data.Monoid

type Cub a b = [a] -> b
type Color = String
type Cube a = Cub Color a

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

cart :: [[a]] -> [[a]] -> [[a]]
cart xs ys = do
  x <- xs
  y <- ys
  return (x++y)

type Env = [(String,Cub String Val)]

data Term = TU | TPi String Term Term | TLam String Term | TApp Term Term | TVar String | TParam Color Term | TPair Color Term Term
          | PApp Term Term
  deriving Show

class Nominal a where
  swap :: a -> (Color,Color) -> a
  support :: a -> [Color]

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

app (Lam f) x = f x
app n x = App n x

apps :: Val -> [Val] -> Val
apps f as = foldl app f as

lkCub :: (Show a1, Eq a1) => a1 -> [(a1, a)] -> a
lkCub pos cub = case lookup pos cub of
  Just x -> x
  Nothing -> error $ "ColorSet not found: " ++ show pos ++ "\n" ++
                     "Have: " ++ show (map fst cub)

mkCub :: [([Color],a)] -> Cube a
mkCub = flip lkCub

interior :: Color -> Cube x -> Cube x
interior i q is = q (i:is)

predic :: Colors -> Value -> [(Colors)] -> Val
predic base typ xss = multiPi base typ [] xss $ \_ -> U

prime f fresh excl = f (excl ++ fresh) excl

multiPi :: Colors -> Value -> [(Colors,Val)] -> [(Colors)] -> (Value -> Val) -> Val
multiPi base _typ vars [] k = k (mkCub vars)
multiPi base typ vars (xs:xss) k = Pi (typ xs `apps` [lkCub x vars | x <- strictSublists xs]) $
                                   Lam $ \v -> multiPi base typ ((xs,v):vars) xss k

multiLam :: [(Colors,Val)] -> [(Colors)] -> (Value -> Val) -> Val
multiLam vars [] k = k (mkCub vars)
multiLam vars (xs:xss) k = Lam $ \v -> multiLam ((xs,v):vars) xss k

type Natural = Integer
type Value = Cube Val
data Val = Var String | Pi Val Val | App Val Val | Lam (Val -> Val) | U

apply :: [a] -> Val -> Cub a Val -> Val
apply base f u = f `apps` map u (sublists base)

-- appCub :: [a] -> [a] -> Cub a Val -> Cub a Val -> Cub a Val
appCub base excl f u is = sat base excl (f is) u


sat base excl pred v = pred `apps` map v (sublistsExcl base excl)

type Colors = [Color]

-- NOTE: The environment must provide enough "freshness" to interpret
-- parametricity (ie. very much).  The fresh colors in the base (after
-- the next index) MUST NOT clash with the free colors of the term NOR
-- with the colors of the returned value.

xs `contains` ys = null (ys \\ xs)

sublistsExcl :: Eq a => [a] -> [a] -> [[a]]
-- sublistsExcl base excl = filter (not . (`contains` excl)) $ sublists base
sublistsExcl base excl = cart (strictSublists excl) (sublists base)


splitSupply [] = ([],[])
splitSupply [x] = ([x],[])
splitSupply (x1:x2:xs) = (x1:xs1,x2:xs2)
  where (xs1,xs2) = splitSupply xs

eval :: Colors -> Env -> Term -> Value
eval fresh env t0 is =
  let (fresh1,fresh2) = splitSupply fresh
      (fresh0:freshs) = fresh
  in case t0 of
  TLam x b -> multiLam [] (sublists fresh2) $ \x' -> eval fresh2 ((x,x'):env) b is
  TApp f u -> apply (is++fresh2) (eval fresh2 env f is) (eval fresh1 env u)
  PApp p a -> prime sat fresh2 is (eval fresh2 env p is) (eval fresh1 env a)
  TVar x -> case lookup x env of
    Just x' -> x' is
  TParam i t -> eval freshs env (swap t (i,fresh0)) (is++[fresh0])
  TPair i a p -> if i `elem` is
                 then eval fresh env p (is \\ [i])
                 else eval fresh env a is
  ty -> multiLam [] (prime sublistsExcl fresh is) $ \v -> evalT fresh env ty is v
        -- NOTE: we do not put the value bound ('v') in the environment; so it's ok if it is only partial.

evalT :: Colors -> Env -> Term -> Colors -> Value -> Val
evalT fresh env t0 excl v =
  let evalB = eval fresh
      (fresh1,fresh2) = splitSupply fresh
  in case t0 of
  TU -> predic (excl ++ fresh) v (prime sublistsExcl fresh excl)
  TPi x a b -> multiPi (excl ++ fresh2) (eval fresh1 env a) [] (sublists (excl ++ fresh2)) $ \x' ->
                       evalT fresh2 ((x,x'):env) b excl (prime appCub fresh2 excl v x')
  -- TParamIn i t arg ->
  --     evalT (next+1) base env (swap t (i,freshI)) (excl++[freshI]) (\cs -> if freshI `elem` cs then v (cs \\ [freshI]) else evalB env arg cs)
    -- where freshI = base !! next
  _ -> sat fresh excl (evalB env t0 excl) v


-------------------------
-- Pretty

showCols = intercalate ","

vars xs = [[x] ++ (if i > 0 then show i else "") | i <- [0..], x <- xs] 

freshVars = vars "xyzwstuv"

showValue :: Colors -> Value -> String
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
showVal (s:su) (Pi a f)    = "Π(" <> s <+> ":" <+> showVal su a <> ")." <+> showVal su (app f x)
  where x = Var s
showVal su (App u v)   = showVal su u <+> showVal1 su v
showVal su (Var x)     = x

--------------------------
-- Testing

test b fb env term = putStrLn $ showValue b $ eval fb env term

absCub :: String -> Value
absCub x js = Var $ x ++ "["++showCols js ++"]"

swapExTm :: Term
swapExTm = TParam "j" (TPair "i" (TVar "a") (TVar "p") )

swapExEnv = [("a",absCub "a"),("p",absCub "p"),("A",absCub "A"),("x",absCub "x"),("P", absCub "P")]

freshBase n = take n $ map (:[]) "αβγδε"

swapEx = test base fb swapExEnv swapExTm
   where fb = freshBase 2
         base = ["i"]

exU = test boundBase fb swapExEnv TU
   where fb = freshBase 0
         boundBase = ["i","j"]

exApp = test boundBase fb swapExEnv (PApp (TVar "P") (TVar "x"))
   where fb = freshBase 2
         boundBase = ["i","j"]

exUi = test boundBase fb swapExEnv (TParam "i" TU)
   where fb = freshBase 1
         boundBase = ["j"]

exPredFun = test boundBase fb swapExEnv (TPi "x" (TVar "A") $ TU)
   where fb = freshBase 2
         boundBase = ["j"]

exPredParam = test boundBase fb swapExEnv (TParam "i" TU `PApp` TVar "A")
   where fb = freshBase 2
         boundBase = ["j"]

exTy = test boundBase fb swapExEnv $
       TParam "i" (TVar "A")
   where fb = freshBase 1
         boundBase = ["j","k"]

ex = test boundBase fb swapExEnv $ (TParam "j" $ TPair "i" (TVar "a") (TVar "p"))
   where fb = freshBase 2
         boundBase = ["i","k"]
