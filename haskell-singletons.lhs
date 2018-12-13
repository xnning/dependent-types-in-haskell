> {-# LANGUAGE
>   DataKinds        -- data type promotion
> , KindSignatures   -- enables explicit kind signature
> , GADTs            -- generalised algebraic data types
> , TypeFamilies     -- type-level programming
> , TemplateHaskell          -- for singletons
> , ScopedTypeVariables
> , UndecidableInstances
> , InstanceSigs
> #-}
>
> import Data.Kind (Type)
> import Data.Singletons.TH

$(...)     -- Template Haskell splice
[d| ... |] -- for declaration

> $(singletons [d|
>   data Nat = Zero | Succ Nat deriving Show
>
>   plus :: Nat -> Nat -> Nat
>   plus Zero y     = y
>   plus (Succ x) y = Succ (plus x y)
>
>   lt' :: Nat -> Nat -> Bool
>   lt' Zero (Succ n) = True
>   lt' m Zero        = False
>   lt' (Succ m) (Succ n) = lt' m n
>  |])

generates singleton types:

  data SNat :: Nat -> Type where
    SZero :: SNat 'Zero
    SSucc :: SNat n -> SNat ('Succ n)

lifting functions to type-level computations:

  type family Plus (x::Nat) (y::Nat) where
    Plus Zero y = y
    Plus (Succ x) y = Succ (Plus x y)

  type family Lt'  (m::Nat) (n::Nat) :: Bool
  type instance Lt' Zero (Succ n) = 'True
  type instance Lt' m    Zero     = 'False
  type instance Lt' ('Succ m) ('Succ n) = Lt' m n

> infixr 5 :>
> data Vec :: Type -> Nat -> Type where
>     Nil  :: Vec a 'Zero
>     (:>) :: a -> Vec a n -> Vec a ('Succ n)

> instance Show a => Show (Vec a n) where
>   show Nil = "nil"
>   show (a :> as) = show a ++ "::" ++ show as

> append :: Vec a n -> Vec a m -> Vec a (Plus n m)
> append Nil ys = ys
> append (x :> xs) ys = x :> (append xs ys)

> nth :: (Lt' m n ~ 'True) => SNat m -> Vec a n -> a
> nth SZero     (x :> xs) = x
> nth (SSucc m) (x :> xs) = nth m xs


Lessons we learnt:

  Singletons library is useful for writing dependent type programs. It generates
  boilerplate code for you, which enables us to write programs similar in other
  dependent type languages, e.g. Idris.

Any problem so far?
