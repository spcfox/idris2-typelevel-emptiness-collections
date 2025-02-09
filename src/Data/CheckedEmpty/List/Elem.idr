-- Despite the significant difference in the types, idea and function names taken from
-- https://github.com/idris-lang/Idris2/blob/4e8847b70372d2dffadfe31dbb540eec2280c9e1/libs/base/Data/List/Elem.idr

module Data.CheckedEmpty.List.Elem

import Data.CheckedEmpty.List

import Data.Singleton
import Decidable.Equality
import Control.Function

%default total

--------------------------------------------------------------------------------
-- List membership proof
--------------------------------------------------------------------------------

||| A proof that some element is found in a list.
public export
data Elem : a -> Lst ne a -> Type where
     ||| A proof that the element is at the head of the list
     Here : {0 u0 : _} -> {0 u1 : _} -> {0 xs : Lst _ _} ->
            Elem x $ (x :: xs) {ne} @{u0} @{u1}
     ||| A proof that the element is in the tail of the list
     There : {0 u0 : _} -> {0 u1 : _} -> {0 xs : Lst _ _} ->
             Elem x xs -> Elem x $ (y :: xs) @{u0} @{u1}

export
Uninhabited (Here {u0} {u1} {x} {xs} = There {u0=u0'} {u1=u1'} {x=x'} {y} {xs=xs'} e) where
  uninhabited Refl impossible

export
Uninhabited (There {u0} {u1} {x} {y} {xs} e = Here {u0=u0'} {u1=u1'} {x=x'} {xs=xs'}) where
  uninhabited Refl impossible

export
Injective (There {u0} {u1} {x} {y} {xs}) where
  injective Refl = Refl

export
DecEq (Elem x xs) where
  decEq Here          Here         = Yes Refl
  decEq (There this) (There that)  = decEqCong $ decEq this that
  decEq Here         (There later) = No absurd
  decEq (There later) Here         = No absurd

export
Uninhabited (Elem x []) where
  uninhabited $ Here     impossible
  uninhabited $ There p impossible

export
Uninhabited (x = z) => Uninhabited (Elem z xs) =>
Uninhabited (Elem z $ (x :: xs) @{u0} @{u1}) where
  uninhabited Here @{xz} = uninhabited Refl @{xz}
  uninhabited $ There y  = uninhabited y

||| An item not in the head and not in the tail is not in the list at all.
export
neitherHereNorThere : {0 xs : Lst ne a} ->
                      Not (x = y) -> Not (Elem x xs) ->
                      Not (Elem x $ (y :: xs) @{u0} @{u1})
neitherHereNorThere xny _    $ Here      = xny Refl
neitherHereNorThere _   xnxs $ There xxs = xnxs xxs

||| Check whether the given element is a member of the given list.
public export
isElem : DecEq a => (x : a) -> (xs : Lst ne a) -> Dec (Elem x xs)
isElem x $ [] = No absurd
isElem x $ y :: xs with (decEq x y)
  isElem x $ x :: xs | Yes Refl = Yes Here
  isElem x $ y :: xs | No xny with (isElem x xs)
    isElem x $ y :: xs | No xny | Yes xxs = Yes $ There xxs
    isElem x $ y :: xs | No xny | No xnxs = No $ neitherHereNorThere xny xnxs

||| Get the element at the given position.
public export
get : (xs : Lst ne a) -> (p : Elem x xs) -> a
get (x :: _)  $ Here    = x
get (_ :: xs) $ There p = get xs p

||| Get the element at the given position, with proof that it is the desired element.
public export
lookup : (xs : Lst ne a) -> (p : Elem x xs) -> Singleton x
lookup (x :: _)    Here    = Val x
lookup (_ :: xs) $ There p = lookup xs p

||| Remove the element at the given position.
public export
dropElem : (xs : Lst ne a) -> (p : Elem x xs) -> Lst0 a
dropElem (_ :: ys) $ Here    = relaxF ys
dropElem (x :: ys) $ There p = x :: dropElem ys p

||| Erase the indices, returning the numeric position of the element
public export
elemToNat : Elem x xs -> Nat
elemToNat  Here     = Z
elemToNat (There p) = S $ elemToNat p

||| Find the element with a proof at a given position, if it is valid
public export
indexElem : Nat -> (xs : Lst ne a) -> Maybe (x ** Elem x xs)
indexElem  _    []        = Nothing
indexElem  Z    (y :: _)  = Just (y ** Here)
indexElem (S n) (_ :: ys) = indexElem n ys <&> \(x ** p) => (x ** There p)

||| Lift the membership proof to a mapped list
export
elemMap : {0 xs : Lst ne a} -> (0 f : a -> b) ->
          Elem x xs -> Elem (f x) (map f xs)
elemMap f $ Here    = Here
elemMap f $ There e = There $ elemMap f e
