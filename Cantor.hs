module Cantor where

data Bit = Zero | One
  deriving (Eq)

type Natural = Integer

type Cantor = Natural -> Bit

(#) :: Bit -> Cantor -> Cantor
x # a = \i -> if i == 0 then x else a(i-1)
-- x # a = (x:a)

ctail :: Cantor -> Cantor
ctail a x = a (x+1)

cview :: Cantor -> (Bit,Cantor)
cview xs = (xs 0,ctail xs)

insertCantor :: Integer -> Bit -> Cantor -> Cantor
insertCantor i b xs j = case compare j i of
  LT -> xs j
  EQ -> b
  GT -> xs (j-1)

forsome, forevery :: (Cantor -> Bool) -> Bool
find :: (Cantor -> Bool) -> Cantor

find = find_viii

forsome p = p(find(\a -> p a))
forevery p = not(forsome(\a -> not(p a)))

find_i :: (Cantor -> Bool) -> Cantor
find_i p = if forsome(\a -> p(Zero # a))
           then Zero # find_i(\a -> p(Zero # a))
           else One  # find_i(\a -> p(One  # a))

find_iii :: (Cantor -> Bool) -> Cantor
find_iii p = h # find_iii(\a -> p(h # a))
       where h = if p(Zero # find_iii(\a -> p(Zero # a))) then Zero else One

find_v :: (Cantor -> Bool) -> Cantor
find_v p = \n ->  if q n (find_v(q n)) then Zero else One
 where q n a = p(\i -> if i < n then find_v p i else if i == n then Zero else a(i-n-1))

search :: (Cantor -> Bool) -> Maybe Cantor
search p = if forsome(\a -> p a) then Just(find(\a -> p a)) else Nothing

type Cube x = Cantor -> x

equal :: Eq y => Cube y -> Cube y -> Bool
equal f g = forevery(\a -> f a == g a)

find_vii :: (Cantor -> Bool) -> Cantor
find_vii p = b
 where b = id'(\n -> if q n (find_vii(q n)) then Zero else One)
       q n a = p(\i -> if i < n then b i else if i == n then Zero else a(i-n-1))

findBit :: (Bit -> Bool) -> Bit
findBit p = if p Zero then Zero else One

branch :: Bit -> Cantor -> Cantor -> Cantor
branch x l r n | n == 0 = x
               | odd n = l ((n-1) `div` 2)
               | otherwise = r ((n-2) `div` 2)
find_viii :: (Cantor -> Bool) -> Cantor
find_viii p = branch x l r
  where x = findBit(\x -> forsome(\l -> forsome(\r -> p(branch x l r))))
        l = find_viii(\l -> forsome(\r -> p(branch x l r)))
        r = find_viii(\r -> p(branch x l r))

data T x = B x (T x) (T x)

code :: (Natural -> x) -> T x
code f = B (f 0) (code(\n -> f(2*n+1)))
                 (code(\n -> f(2*n+2)))

decode :: T x -> (Natural -> x)
decode (B x l r) n |  n == 0    = x
                   |  odd n     = decode l ((n-1) `div` 2)
                   |  otherwise = decode r ((n-2) `div` 2)

id' :: (Natural -> x) -> (Natural -> x)
id' = decode.code
