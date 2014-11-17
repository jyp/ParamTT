{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts, OverloadedStrings #-}
import Data.List

import Text.PrettyPrint.Compact
-- import Data.Monoid

type Color = String
type Colors = [Color]

type Cube a = Colors -> a

data Term = TU | TPi String Term Term | TLam String Term | TApp Term Term | TVar String | TParam Color Term | TPair Color Term Term
          | TPsi Color Term {- Domain -} Term {- Predicate -} -- Ψ i (A:U) (P:A->U)
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

type Env = [(String,Cube Val)]

data Dim = Incl [Colors] | Excl [Colors] [Colors]

incl is fresh = Incl (is ++ fresh)

data Val = Var String | Pi Dim (Cube Val) Val | App Dim Val (Cube Val) | Lam Dim (Cube Val -> Val) | Set

interior :: Color -> Cube x -> Cube x
interior i q is = q (i:is) -- FIXME: this is not correctly inserted (sort?)

face :: Color -> Cube x -> Cube x
face i q is = q (is \\ [i])

appCub :: Cube Val -> Cube Val -> Cube Val
appCub f u is = app (Incl is) (f is) u

app χ (Lam _ f) x = f x
app χ n x = App χ n x

splitSupply [] = ([],[])
splitSupply [x] = ([x],[])
splitSupply (x1:x2:xs) = (x1:xs1,x2:xs2)
  where (xs1,xs2) = splitSupply xs

π dim typ f = Pi dim typ $ Lam dim f

eval :: Colors -> Env -> Term -> Cube Val
eval fresh env t0 is =
  let (fresh1,fresh2) = splitSupply fresh
      (fresh0:freshs) = fresh
  in case t0 of
  TLam x b -> Lam (incl is fresh) $ \x' -> eval fresh2 ((x,x'):env) b is
  TApp f u -> app (incl is fresh) (eval fresh2 env f is) (eval fresh1 env u)
  TVar x -> case lookup x env of
    Just x' -> x' is
  TParam i t -> eval freshs env (swap t (i,fresh0)) (is++[fresh0])
  TPair i a p -> if i `elem` is
                 then eval fresh env p (is \\ [i])
                 else eval fresh env a is
  ty -> Lam (Excl is fresh) $ \v -> evalT fresh env ty is v
        -- NOTE: we do not put the value bound ('v') in the environment; so it's ok if it is only partial.

evalT :: Colors -> Env -> Term -> Colors -> Cube Val -> Val
evalT fresh env t0 excl v =
  let evalB = eval fresh
      (fresh1,fresh2) = splitSupply fresh
  in case t0 of
  TU -> π (Excl excl fresh) v $ \_ -> Set
  -- TPsi i a p -> if i `elem` excl
  --               then appCub (Face [i]) (appCub (Face [i]) (eval fresh env p) (face i v)) (interior i v) (excl \\ [i])
  --               else evalT fresh env a excl v -- Fixme: freshness

  TPi x a b -> π (incl excl fresh2) (eval fresh1 env a) $ \x' ->
               evalT fresh2 ((x,x'):env) b excl (appCub v x')
  _ -> app (Excl excl fresh) (evalB env t0 excl) v

-------------------------
-- Pretty

strictSublists = init . sublists

sublists [] = [[]]
sublists (x:xs) = sublists xs ++ map (x:) (sublists xs)

showCols [] = "∅"
showCols xs = hcat . map text $ xs

showColss = parens . align . hcat . punctuate ";" . map showCols

vars xs = [[x] ++ (if i > 0 then show i else "") | i <- [0..], x <- xs] 

freshVars = vars "xyzwstuv"

False ==> _ = True
_ ==> False = False

cart :: [[a]] -> [[a]] -> [[a]]
cart xs ys = do
  x <- xs
  y <- ys
  return (x++y)

dimLists (Incl xs) = sublists xs
dimLists (Excl is xs) = cart (strictSublists is) (sublists xs)

showCube dim su v = parens $ align $ cat $ punctuate ";" $
  [showCols is <+> "↦" <+> showVal su (v is) | is <- dimLists dim ]


-- showVals su = hcat . map (showVal1 su)

showVal1 :: [String] -> Val -> Doc
showVal1 _ Set          = "Set"
showVal1 _ (Var x)      = text x
showVal1 su u           = parens $ showVal su u

emptyCub = absCub "◆"
xs `contains` ys = null (ys \\ xs)

showVal :: [String] -> Val -> Doc
showVal _ Set           = "Set"
showVal (s:su) (Lam excl e)
  -- | null base =  showVal base su (e emptyCub)
  | otherwise = "\\" <> text s <> showColss (limit base excl) <+> "->" <+> showVal base su (e x)
  where x = absCub s
showVal base (s:su) (Pi excl a f)
  -- | null base =  showVal base su (app excl f emptyCub)
  | otherwise =  "Π(" <> text s <+> ":" <+> showPartialCube base excl su a <> ")." <+> showVal1 base su (app excl f x)
  where x = absCub s
showVal base su (App excl u v)
  -- | null base =  showVal base su u
  | otherwise = showVal base su u <+> showPartialCube base excl su v
showVal base su (Var x)     = text x

--------------------------
-- Testing

test b fb env term = putStrLn $ show $ showCube (sublists $ b ++ fb) freshVars $ eval fb env term

absCub :: String -> Cube Val
absCub x js = Var $ x ++ show (showCols js)

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

exApp = test boundBase fb swapExEnv (TApp (TVar "P") (TVar "x"))
   where fb = freshBase 2
         boundBase = ["i","j"]

exUi = test boundBase fb swapExEnv (TParam "k" TU)
   where fb = freshBase 1
         boundBase = ["i","j"]

exPredFun = test boundBase fb swapExEnv (TPi "x" (TVar "A") $ TU)
   where fb = freshBase 0
         boundBase = ["i","j"]

exPsi = test boundBase fb swapExEnv (TPsi "i" (TVar "A") (TVar "P"))
   where fb = freshBase 0
         boundBase = ["i","j"]

exPredParam = test boundBase fb swapExEnv (TParam "k" TU `TApp` TVar "A")
   where fb = freshBase 0
         boundBase = ["i","j"]

exTy = test boundBase fb swapExEnv $
       TParam "i" (TVar "A")
   where fb = freshBase 1
         boundBase = ["j","k"]

ex = test boundBase fb swapExEnv $ (-- TParam "j" $
                                    TPair "i" (TVar "a") (TVar "p"))
   where fb = freshBase 1
         boundBase = ["i","k"]

main = ex
