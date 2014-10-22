

module Cubes where

import Cantor


-- A sub-part of a cube.
-- The function is undefined at all prefixes starting with n times One.
type SubCube {-n-} x = Cube x

access :: Natural -> Bit -> Cube x -> Cube x
access i b q xs = q (insertCantor i b xs)

-- | The face of a cube in dimension i.
face1 :: Natural -> Cube x -> Cube x
face1 i = access i Zero


-- | The interior of a cube in dimension i
interior1 :: Natural -> Cube x -> Cube x
interior1 i = access i One

face0 = face1 0
interior0 = interior1 0

-- | Apply a functional cube to its argument
-- (f,g) @ (a,p) = (f a, g a p)
apply :: Cube x -> Cube x -> Cube x
apply h u xs = case cview xs of
  (Zero,xs') -> apply (face0 h) (face0 u) xs'
  (One,xs')  -> ((interior0 h) @@  (face0 u) @@ (interior0 u)) xs'

(@@) = apply

-- | Take a Cube TYPE of order N; a subcube of order n, and return a satisfaction cube.
-- [ P R ]  [p  ]  =   [P a  R a q p]
-- [ A Q ]  [a q]      [     Q a    ]
sat1 :: {-n:-} Natural -> Cube x -> SubCube {-n-} x -> Cube x
sat1 0 t _ xs = t xs
sat1 n r q xs = case cview xs of
  (Zero,xs') -> sat1 (n-1) (face0 r) (face0 q) xs'
  (One,xs') -> sat1 (n-1)  ((interior0 r) @@ face0 q) (interior0 q) xs'



set :: Cube x
set xs =



pi as bs fs is = pi as $ 
