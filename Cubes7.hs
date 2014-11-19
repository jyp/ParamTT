{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts, OverloadedStrings #-}
import Data.List

import Text.PrettyPrint.Compact
-- import Data.Monoid

type Color = String
type Colors = [Color]

type Cube a = Colors -> a

data Term = TU | TPi String Term Term | TLam String Term | TApp Term Term | TVar String | TParam Color Term | TPair Color Term Term
          | TPsi Color Term {- Domain -} Term {- Predicate -} -- Ψ i (A:U) (P:A->U)
          | TInParam String Term Term
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
      TPsi k a p -> TPsi (sw k) (sw a) (sw p)

type Env = [(String,Cube Val)]

data Dim = Incl Colors | Excl Colors Colors

strictSublists = init . sublists

sublists [] = [[]]
sublists (x:xs) = sublists xs ++ map (x:) (sublists xs)

cart :: [[a]] -> [[a]] -> [[a]]
cart xs ys = do
  x <- xs
  y <- ys
  return (x++y)
dimLists :: Dim -> [[Color]]
dimLists (Incl xs) = sublists xs
dimLists (Excl is xs) = cart (strictSublists is) (sublists xs)

incl is fresh = Incl (is ++ fresh)

data Val = Var String | Pi Dim (Cube Val) Val | App Dim Val (Cube Val) | Lam Dim (Cube Val -> Val) | Set

interior :: Color -> Cube x -> Cube x
interior i q is = q (i:is) -- FIXME: this is not correctly inserted (sort?)
  -- Invariant: i ∉ is

face :: Color -> Cube x -> Cube x
face i q is = q (is \\ [i])

app χ (Lam χ' f) x = f x -- invariant χ=χ' (or at least dimLists χ ⊆ dimLists χ')
app χ n x = App χ n x

appCub :: Cube Val -> Cube Val -> Cube Val
appCub f u is = app (Incl is) (f is) u  -- implicit injection on u

splitSupply [] = ([],[])
splitSupply [x] = ([x],[])
splitSupply (x1:x2:xs) = (x1:xs1,x2:xs2)
  where (xs1,xs2) = splitSupply xs

π :: Dim -> Cube Val -> (Cube Val -> Val) -> Val
π dim typ f = Pi dim typ $ Lam dim f

eval :: Colors -> Env -> Term -> Cube Val
eval φ ρ t0 χ =
  let (φ1,φ2) = splitSupply φ
      (φ0:φs) = φ
  in case t0 of
  TLam x b -> Lam (incl χ φ2) $ \x' -> eval φ2 ((x,x'):ρ) b χ
  TApp f u -> app (incl χ φ2) (eval φ2 ρ f χ) (eval φ1 ρ u)
  TVar x -> case lookup x ρ of
    Just x' -> x' χ
  TParam i t -> eval φs ρ (swap t (i,φ0)) (χ++[φ0])
  TPair i a p -> if i `elem` χ
                 then eval φ ρ p (χ \\ [i])
                 else eval φ ρ a χ
  ty -> Lam (Excl χ φ) $ \v -> evalT φ ρ ty χ v
        -- NOTE: we do not put the value bound ('v') in the environment; so it's ok if it is only partial.

evalT :: Colors -> Env -> Term -> Colors -> Cube Val -> Val
evalT φ ρ t0 χ v =
  let (φ1,φ2) = splitSupply φ
      (φ0:φs) = φ
  in case t0 of
  TU -> π (Excl χ φ) v $ \_ -> Set
  TPsi i a p -> if i `elem` χ
                then app (Excl xi φ1) (app (incl xi φ1) (eval φ1 ρ p xi) (face i v)) (interior i v) -- FIXME: φ
                else evalT φ2 ρ a χ v -- Fixme: freshness
    where xi = χ \\ [i]
  TPi x a b -> π (incl χ φ2) (eval φ1 ρ a) $ \x' ->
               evalT φ2 ((x,x'):ρ) b χ (appCub v x')
  TInParam i p a -> evalT φs ρ (swap p (i,φ0)) (χ++[φ0])
                    (\xi -> if φ0 `elem` xi
                            then v (xi \\ [φ0])
                            else eval φ ρ a xi)
  _ -> app (Excl χ φ) (eval φ ρ t0 χ) v

-------------------------
-- Pretty

showCols :: [Color] -> Doc
showCols [] = "∅"
showCols xs = hcat . map text $ xs

showColss = parens . align . hcat . punctuate ";" . map showCols

vars xs = [[x] ++ (if i > 0 then show i else "") | i <- [0..], x <- xs] 

freshVars = vars "xyzwstuv"

showDim (Incl xs) = braces $ align $ showCols xs
showDim (Excl is xs) = braces $ align $ (showCols is <> "/" <> showCols xs)


showCube dim su v = parens $ align $ cat $ punctuate ";" $
  [showCols is <+> "↦" <+> showVal su (v is) | is <- dimLists dim ]


-- showVals su = hcat . map (showVal1 su)

showVal1 :: [String] -> Val -> Doc
showVal1 _ Set          = "Set"
showVal1 _ (Var x)      = text x
showVal1 su u           = parens $ showVal su u

emptyCub = absCub "◆"
xs `contains` ys = null (ys \\ xs)

noShowNull = True
showVal :: [String] -> Val -> Doc
showVal _ Set           = "Set"
showVal (s:su) (Lam dim e)
  | noShowNull, null (dimLists dim) =  showVal su (e emptyCub)
  | otherwise = "\\" <> text s <> showDim dim <+> "->" <+> showVal su (e x)
  where x = absCub s
showVal (s:su) (Pi dim a f)
  | noShowNull, null (dimLists dim) =  showVal su (app dim f emptyCub)
  | otherwise =  "Π(" <> text s <+> ":" <+> showCube dim su a <> ")." <+> showVal1 su (app dim f x)
  where x = absCub s
showVal su (App dim u v)
  | noShowNull, null (dimLists dim) =  showVal su u
  | otherwise = showVal su u <+> showCube dim su v
showVal su (Var x)     = text x

--------------------------
-- Testing

test :: Colors -> Colors -> Env -> Term -> IO ()
test b fb env term = putStrLn $ show $ showCube (Incl b) freshVars $ eval fb env term

absCub :: String -> Cube Val
absCub x js = Var $ x ++ show (showCols js)

absEnv = [("a",absCub "a"),("p",absCub "p"),("A",absCub "A"),("x",absCub "x"),("P", absCub "P")]

freshBase n = take n $ map (:[]) "αβγδε"

exSwap = test base fb absEnv $ TParam "j" (TPair "i" (TVar "a") (TVar "p") )
   where fb = freshBase 2
         base = ["i","k"]

exU = test boundBase fb absEnv TU
   where fb = freshBase 0
         boundBase = ["i","j"]

exApp = test boundBase fb absEnv (TApp (TVar "P") (TVar "x"))
   where fb = freshBase 0
         boundBase = ["i","j"]
exIn = test boundBase fb absEnv $ TInParam "i" (TVar "P") (TVar "x")
   where fb = freshBase 2
         boundBase = ["j"]

exxi = test boundBase fb absEnv (TParam "k" $ TVar "x")
   where fb = freshBase 1
         boundBase = ["i","j"]

exUi = test boundBase fb absEnv (TParam "k" TU)
   where fb = freshBase 1
         boundBase = ["i","j"]

exPredFun = test boundBase fb absEnv (TPi "x" (TVar "A") $ TU)
   where fb = freshBase 0
         boundBase = ["i","j"]

exPsi = test boundBase fb absEnv (TPsi "i" (TVar "A") (TVar "P"))
   where fb = freshBase 0
         boundBase = ["i","j"]

exPsiInv = test boundBase fb absEnv $ TInParam "i" (TPsi "i" (TVar "A") (TVar "P")) (TVar "x")
   where fb = freshBase 1
         boundBase = ["j"]

-- We should have :: (Ψi A P).i ∋ x = P x

exPredParam = test boundBase fb absEnv (TParam "k" TU `TApp` TVar "A")
   where fb = freshBase 2
         boundBase = ["i","j"]

exTy = test boundBase fb absEnv $
       TParam "i" (TVar "A")
   where fb = freshBase 1
         boundBase = ["j","k"]

exPair = test boundBase fb absEnv $ (-- TParam "j" $
                                    TPair "i" (TVar "a") (TVar "p"))
   where fb = freshBase 1
         boundBase = ["i","k"]

main = exPair
