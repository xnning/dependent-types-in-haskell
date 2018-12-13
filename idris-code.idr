%hide Nat  -- hiding Prelude.Nat

data Nat = Zero | Succ Nat

infixr 5 :>
data Vec :  Type -> Nat -> Type where
  Nil  : Vec a Zero
  (:>) : (x : a) -> Vec a k -> Vec a (Succ k)


eg0 : Vec Integer (Succ (Succ (Succ Zero)))
    -- Idris requires a top-level type annotation for every function
eg0 = (1:>2:>3:>Nil)


hd : Vec a (Succ k) -> a
hd (h :> t) = h

plus : Nat -> Nat -> Nat
plus Zero y     = y
plus (Succ x) y = Succ (plus x y)

append : Vec a m -> Vec a n -> Vec a (plus m n)
append Nil ys = ys
append (x :> xs) ys = x :> (append xs ys)

eg1 : Vec Integer (Succ (Succ (Succ (Succ (Succ Zero)))))
  -- Idris requires a top-level type annotation for every function
eg1 = append (1:>2:>Nil) (3:>4:>5:>Nil)

data Lt : Nat -> Nat -> Type where
  Base : Lt Zero (Succ n)
  Ind  : Lt n m -> Lt (Succ n) (Succ m)

-- nth : (m:Nat) -> Vec a n -> (prf : Lt m n) -> a
-- nth Zero     (x :> xs) prf = x
-- nth (Succ n) (x :> xs) prf = ?rhs

nth : (m:Nat) -> Vec a n -> (prf : Lt m n) -> a
nth Zero     (x :> xs) prf       = x
nth (Succ n) (x :> xs) (Ind prf) = nth n xs prf

eg2 : Integer
eg2 = nth Zero eg1 Base

eg3 : Integer
eg3 = nth (Succ Zero) eg1 (Ind Base)

nth_auto : (m:Nat) -> Vec a n -> {auto prf : Lt m n} -> a
nth_auto m xs {prf} = nth m xs prf

eg2' : Integer
eg2' = nth_auto Zero eg1

eg3' : Integer
eg3' = nth_auto (Succ Zero) eg1
