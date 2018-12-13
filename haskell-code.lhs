1. Let's get started with length-indexed vector

> {-# LANGUAGE
>   DataKinds        -- data type promotion
> , KindSignatures   -- enables explicit kind signature
> , GADTs            -- generalised algebraic data types
> , TypeFamilies     -- type-level programming
> #-}
> import Data.Kind (Type)


2. A length-index vector records its length in its type by GADTs.

> data Nat = Zero | Succ Nat deriving Show
>
> infixr 5 :>
> data Vec :: Type    -- type of vector
>          -> Nat     -- length of vector
>          -> Type where
>   Nil  :: Vec a 'Zero
>   (:>) :: a -> Vec a n -> Vec a ('Succ n)
>
> instance Show a => Show (Vec a n) where
>   show Nil = "nil"
>   show (a :> as) = show a ++ "::" ++ show as

An integer vector of length 3:

> eg0 :: Vec Int (Succ (Succ (Succ Zero)))
> eg0 = (1:>2:>3:>Nil)


3. `head` of lists in GHC is not safe -- there could be runtime errors.

> err = head []
> -- runtime *** Exception: Prelude.head: empty list


`hd` is always safe -- applying it to empty vectors won't type-check.

> hd :: Vec a ('Succ n) -> a
> hd (h :> t) = h


4. Let's define addition operator for Nats.

> plus :: Nat -> Nat -> Nat
> plus Zero y     = y
> plus (Succ x) y = Succ (plus x y)



When we append a vector of length m with another vector of length n,
we should get a vector of length (plus m n).

-- > append :: Vec a n -> Vec a m -> Vec a (plus n m)
-- > append Nil ys = ys
-- > append (x :> xs) ys = x :> (append xs ys)


5. What's wrong?

    • Couldn't match type ‘'Succ’ with ‘plus ('Succ n1)’
      Expected type: Vec a (plus n m)
        Actual type: Vec a ('Succ (plus0 n1 m))

`plus` is a term-level function, `plus n m` represents the result
of a term-level function, which GHC will not know at compile-time; it's not
type-level computation.



6. For type-level computation, we need type families:

> type family Plus (x::Nat) (y::Nat) where
>   Plus Zero y = y
>   Plus (Succ x) y = Succ (Plus x y)

> append :: Vec a n -> Vec a m -> Vec a (Plus n m)
> append Nil ys = ys
> append (x :> xs) ys = x :> (append xs ys)

Try an example:

> eg1 = append (1:>2:>Nil) (3:>4:>5:>Nil)


7. Similar as Lists, we would like to define a `nth` function, which gets the nth
element of the vector. E.g.

  nth 0 (1:>2:>3:>Nil)    ==  1
  nth 1 (1:>2:>3:>Nil)    ==  2


> nth1 :: Nat -> Vec a n -> a
> nth1 Zero (x :> xs) = x
> nth1 (Succ n) (x :> xs) = nth1 n xs

Try some examples:

> eg2 = nth1 Zero eg1
> eg3 = nth1 (Succ Zero) eg1


8. So far so good. But how about

> eg4 = nth1 Zero Nil



*** Exception:
    Non-exhaustive patterns in function nth1


Oops. It's like what happens when we type `head []` in GHCi.
We are not type-safe any more!


9.

> nth2 :: Nat -> Vec a n -> a
> nth2 Zero (x :> xs) = x
> nth2 (Succ n) (x :> xs) = nth1 n xs
> nth2 n Nil = undefined -- what to put here???


10. Recall the type signature for `hd`:

  hd :: Vec a ('Succ n) -> a
  hd (h :> t) = h

We guaranteed that `hd` can only be applied to non-empty vectors.
We need to have a similar guarantee for `nth`:

  nth m (Vec a n)   ==>    m < n

We first define `Less Than (<)` for Nats:

> data Lt :: Nat -> Nat -> Type where
>   Base :: Lt Zero (Succ n)
>   Ind  :: Lt n m -> Lt (Succ n) (Succ m)


11. Let's try again:

-- > nth3 :: Nat -> Vec a n -> a
-- > nth3 m v = undefined

GHC interprets `m` as the type, and `Nat` as the kind of `m`.
This is not what we want!



12. We need singleton types!

> data SNat :: Nat -> Type where
>   SZero :: SNat 'Zero
>   SSucc :: SNat n -> SNat ('Succ n)

The only role of `SNat` is to do similar thing as (m:Nat) in Idris.

We call `SNat` a singleton type: types with only one non-bottom value.

  SZero is the only inhabitant of the type SNat 'Zero;
  (SSucc n) is the only inhabitant of the type 'Succ n.

  data SNat :: Nat -> Type where
       ---     ---
        |       |
        - iso.. -

    SZero :: SNat 'Zero
    -----          ----
      |             |
      |             |
      -- isomorphic -

    SSucc :: SNat n -> SNat ('Succ n)
    ---------------         ---------
      |                          |
      |                          |
      -------- isomorphic --------


13.

> nth4 :: SNat m -> Vec a n -> Lt m n -> a
> nth4 SZero (x :> xs) prf = x
> nth4 (SSucc m) (x :> xs) (Ind prf) = nth4 m xs prf




Rewrite the examples:

> eg2' = nth4 SZero eg1 Base
> eg3' = nth4 (SSucc SZero) eg1 (Ind Base)



We can never construct a proof for eg4

  eg4 = nth4 (Succ Zero) Nil ?prf


14. However, providing proofs can be tiresome.

In Haskell, we can implement `LT` as a constraint and let GHC solve it:

> type family Lt'  (m::Nat) (n::Nat) :: Bool
> type instance Lt' Zero (Succ n) = 'True
> type instance Lt' m    Zero     = 'False
> type instance Lt' ('Succ m) ('Succ n) = Lt' m n



> nth :: (Lt' m n ~ 'True) => SNat m -> Vec a n -> a
> nth SZero   (x :> xs) = x
> nth (SSucc m) (x :> xs) = nth m xs


Rewrite the examples again:

> eg2'' = nth SZero eg1
> eg3'' = nth (SSucc SZero) eg1



15. Any problem so far?


16. We have two definition of `plus` for Nat:

  plus :: Nat -> Nat -> Nat
  plus Zero y     = y
  plus (Succ x) y = Succ (plus x y)

  type family Plus (x::Nat) (y::Nat) where
    Plus Zero y = y
    Plus (Succ x) y = Succ (Plus x y)

We have `Nat` and `SNat`

  data Nat = Zero | Succ Nat deriving Show

  data SNat :: Nat -> Type where
    SZero :: SNat 'Zero
    SSucc :: SNat n -> SNat ('Succ n)

We are repeating everything! Why?


17. Because GHC enforces a phase separation between runtime values and
compile-time types.

In order to express the dependency between one runtime argument and one
compile-time type, we define type-families and singleton types by repeating
original term-level definitions to add type-level supports.

Can we do better?

18. Yes we can.

The *Singletons* library is introduced in Dependently Typed Programming with
Singletons (Haskell'12) By Eisenberg and Weirich.
The library uses Template Haskell to:

- automatically generate singleton types
- automatically lift functions to the type level
- automatically refine functions with rich types


Template Haskell: a GHC extension to Haskell that adds compile-time
metaprogramming facilities.
