U = Set

record _×_ A  (P : A -> U) : U where
  constructor _,_
  field
    fst : A
    snd : P fst
open _×_

Square : 
  (A : U)
  (P Q : A -> U)
  (R : (x : A) -> P x -> Q x -> U)
  -> U
Square A P Q R =  (A × P) × (λ x → Q (fst x) × R (fst x) (snd x))


square :
  (A : U)
  (P Q : A -> U)
  (R : (x : A) -> P x -> Q x -> U)
  (a : A)
  (p : P a)
  (q : Q a)
  (r : R a p q)
  -> Square A P Q R
square _ _ _ _ a p q r = (a , p) , (q , r)

postulate
  A : U
  P Q : A -> U
  R : (x : A) -> P x -> Q x -> U
swR = λ x y z → R x z y

T  = Square A P Q R
swT = Square A Q P swR

postulate
  a : A
  p : P a
  q : Q a
  r : R a p q

t : T
t = square A P Q R a p q r

swt : swT
swt = square _ _ _ _ a q p r

