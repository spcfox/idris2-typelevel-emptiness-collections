-- Despite the significant difference in the types, idea and function names taken from
-- https://github.com/idris-lang/Idris2/blob/7972c6acbd7276a53e00e038a09607fc4edad006/libs/base/Data/List/Quantifiers.idr

module Data.CheckedEmpty.List.Lazy.Quantifiers

import Data.CheckedEmpty.List.Lazy
import Data.CheckedEmpty.List.Lazy.Elem

import Data.DPair
import Data.Fin

%default total

namespace Any

  public export
  data Any : (0 p : a -> Type) -> LazyLst ne a -> Type where

    Here  : {0 u0 : _} -> {0 u1 : _} ->
            {0 xs : Lazy (LazyLst _ _)} ->
            p x -> Any p $ (x :: xs) @{u0} @{u1}

    There : {0 u0 : _} -> {0 u1 : _} ->
            {0 xs : Lazy (LazyLst _ _)} ->
            Lazy (Any p xs) -> Any p $ (x :: xs) @{u0} @{u1}

  export
  Uninhabited (Any p Nil) where
    uninhabited (Here _) impossible
    uninhabited (There _) impossible

  export
  {0 p : a -> Type} -> {0 u0 : _} -> {0 u1 : _} ->
  Uninhabited (p x) => Uninhabited (Any p xs) => Uninhabited (Any p $ (x::xs) @{u0} @{u1}) where
    uninhabited $ Here  y = uninhabited y
    uninhabited $ There y = uninhabited y

  public export
  mapProperty : (f : {0 x : a} -> p x -> q x) -> Any p l -> Any q l
  mapProperty f $ Here p  = Here  $ f p
  mapProperty f $ There p = There $ mapProperty f p

  export
  any : ((x : a) -> Dec $ p x) -> (xs : LazyLst ne a) -> Dec $ Any p xs
  any _ Nil = No uninhabited
  any p $ x::xs with (p x)
    any p $ _::_  | Yes px = Yes $ Here px
    any p $ x::xs | No npx = case any p xs of
      Yes pxs => Yes $ There pxs
      No npxs => No $ \case
        Here  px  => npx px
        There pxs => npxs pxs

  public export
  toExists : Any p xs -> Exists p
  toExists $ Here  prf = Evidence _ prf
  toExists $ There prf = toExists prf

namespace All

  public export
  data All : (0 p : a -> Type) -> LazyLst ne a -> Type where
    Nil  : All p Nil
    (::) : {0 u0 : _} -> {0 u1 : _} ->
           p x -> Lazy (All p xs) -> All p $ (x :: xs) @{u0} @{u1}

  export
  {0 u0 : _} -> {0 u1 : _} ->
  Either (Uninhabited $ p x) (Uninhabited $ All p xs) => Uninhabited (All p $ (x::xs) @{u0} @{u1}) where
    uninhabited @{Left  _} (px::pxs) = uninhabited px
    uninhabited @{Right _} (px::pxs) = uninhabited pxs

  public export
  mapProperty : (f : {0 x : a} -> p x -> q x) -> All p l -> All q l
  mapProperty f []      = []
  mapProperty f (p::ps) = f p :: mapProperty f ps

  public export
  zipPropertyWith : ({0 x : a} -> p x -> q x -> r x) ->
                    All p xs -> All q xs -> All r xs
  zipPropertyWith f []        []        = []
  zipPropertyWith f (px::pxs) (qx::qxs) = f px qx :: zipPropertyWith f pxs qxs

  public export %inline
  imapProperty : (0 i : a -> Type) ->
                 (f : {0 x : _} -> i x => p x -> q x) ->
                 All i xs => All p xs -> All q xs
  imapProperty _ f @{ps} = zipPropertyWith (\_ => f) ps

  public export
  forget : All {ne} (const a) b -> LazyLst ne a
  forget []      = []
  forget (x::xs) = x :: forget xs

  public export
  all : ((x : a) -> Dec $ p x) -> (xs : LazyLst _ a) -> Dec $ All p xs
  all _ Nil = Yes Nil
  all p $ x::lxs with (p x)
    all p $ _::_        | No npx = No $ \(px::_) => npx px
    all p $ x::Delay xs | Yes px = case all p xs of
      Yes pxs => Yes $ px :: pxs
      No npxs => No $ \(_::pxs) => npxs pxs

  public export
  index : (idx : Fin xs.length) -> All p xs -> p (index idx xs)
  index FZ     (p::_  ) = p
  index (FS n) ( _::ps) = index n ps

----------------------------------------------------------
--- Relationships between `All`, `Any` and other stuff ---
----------------------------------------------------------

--- Relations throught `Not` ---

export
negAnyAll : {xs : LazyLst ne a} -> Not (Any p xs) -> All (Not . p) xs
negAnyAll {xs=[]}         _ = []
negAnyAll {xs=_::Delay _} f = (f . Here) :: negAnyAll (f . There . delay)

export
anyNegAll : Any (Not . p) xs -> Not (All p xs)
anyNegAll (Here nnp) (p::_)  = nnp p
anyNegAll (There np) (_::ps) = anyNegAll np ps

export
allNegAny : All (Not . p) xs -> Not (Any p xs)
allNegAny []         p         = absurd p
allNegAny (np::npxs) (Here p)  = absurd $ np p
allNegAny (np::npxs) (There p) = allNegAny npxs p

public export
indexAll : Elem x xs -> All p xs -> p x
indexAll  Here     $ p :: _  = p
indexAll (There e) $ _ :: ps = indexAll e ps

--- Relations between listwise `All` and elementwise `Subset` ---

-- The function below is commented out due to https://github.com/idris-lang/Idris2/issues/2910

--public export
--pushIn : (xs : LazyLst ne a) -> (0 _ : All p xs) -> LazyLst ne $ Subset a p
--pushIn []            []      = []
--pushIn (x::Delay xs) (p::ps) = Element x p :: pushIn xs ps

public export
pullOut : (xs : LazyLst ne $ Subset a p) -> Subset (LazyLst ne a) (All p)
pullOut []                  = Element [] []
pullOut (Element x p :: xs) = let Element ss ps = pullOut xs in Element (x::ss) (p::ps)

{-

export
pushInOutInverse : (xs : LazyLst ne a) -> (0 prf : All p xs) -> pullOut (pushIn xs prf) = Element xs prf
pushInOutInverse []      []      = Refl
pushInOutInverse (x::xs) (p::ps) = rewrite pushInOutInverse xs ps in Refl

export
pushOutInInverse : (xs : LazyLst ne $ Subset a p) -> uncurry Quantifiers.pushIn (pullOut xs) = xs
pushOutInInverse [] = Refl
pushOutInInverse (Element x p :: xs) with (pushOutInInverse xs)
  pushOutInInverse (Element x p :: xs) | subprf with (pullOut xs)
    pushOutInInverse (Element x p :: xs) | subprf | Element ss ps = rewrite subprf in Refl
