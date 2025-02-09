module Data.CheckedEmpty.List.Lazy.Properties.Map

import Data.Maybe

import Data.CheckedEmpty.List.Lazy
import Data.CheckedEmpty.List.Lazy.Elem
import Data.CheckedEmpty.List.Lazy.Quantifiers

%default total

export
mapId : (xs : LazyLst ne a) -> map Prelude.id xs === xs
mapId $ []            = Refl
mapId $ x :: Delay xs = cong (x ::) $ mapId xs

export
allMapMaybeJust : {f : a -> Maybe b} ->
                  {xs : LazyLst ne a} ->
                  ((x : a) -> (0 _ : IsJust $ f x) -> p $ fromJust (f x)) ->
                  All p $ mapMaybe f xs
allMapMaybeJust {xs=[]}      h = []
allMapMaybeJust {xs=x :: xs} h with (f x) proof 0 prf
  _ | Nothing = allMapMaybeJust h
  _ | Just y  = do
    let yIsJust : IsJust (f x) = rewrite prf in ItIsJust
    let Refl : y === fromJust (f x) = rewrite prf in Refl
    h x yIsJust :: allMapMaybeJust h
