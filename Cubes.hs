

module Cubes where

import Control.Monad
import Data.Maybe

data Bit = Zero | One
  deriving (Eq)

type Natural = Integer


data Val = Var String | Pi Val Val | App Val Val | Lam (Val -> Val) | U
type Nat = Integer

type Cube x = [Nat] -> x
type Value = Cube Val

sublists' xs0 = case xs0 of
  [] -> []
  x:xs -> [x] : do
    s <- sublists' xs
    [s,x:s]

sublists xs0 = []:sublists' xs0

-- set xs = border xs U

type Env = [(String,Cube Val)]

data Term = TU

data Tele = Nil Val | Cons Val (Val -> Val)

apps f as = foldl App f as

lkCub pos cub = fromJust $ lookup pos cub 
predic _preds _vars [] = U
predic preds vars (xs:xss) = Pi (lkCub xs preds `apps` [lkCub x vars | x <- sublists xs]) $
                       Lam $ \v -> predic preds ((xs,v):vars) xss

lamPred preds [] k = k preds
lamPred preds (xs:xss) k = Lam $ \t -> lamPred ((xs,t):preds) xss k


set :: Value
set xs = lamPred [] (sublists xs) $ \preds -> predic preds [] (sublists xs)

eval env t = case t of
  TU -> set
