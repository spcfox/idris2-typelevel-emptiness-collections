
module Data.CheckedEmpty.List.Lazy.Properties.Quantifiers

import Data.CheckedEmpty.List.Lazy
import Data.CheckedEmpty.List.Lazy.Elem
import Data.CheckedEmpty.List.Lazy.Properties.Map
import Data.CheckedEmpty.List.Lazy.Quantifiers

%default total

export
allMapForall : {0 f : a -> b} -> {xs : LazyLst ne a} ->
               ({x : a} -> (0 _ : Elem x xs) -> p (f x)) ->
               All p $ map f xs
allMapForall {xs=[]}      _ = []
allMapForall {xs=x :: xs} h = h Here :: allMapForall (\e => h $ There e)

export
allElem : {xs : LazyLst ne a} -> ({x : a} -> (0 _ : Elem x xs) -> p x) -> All p xs
allElem h = rewrite sym $ mapId {xs} in allMapForall h

export
allTrue : {xs : LazyLst ne a} -> ({x : a} -> p x) -> All p xs
allTrue h = allElem $ \_ => h

export
allMap : {0 xs : LazyLst ne a} -> {0 f : a -> b} ->
         All (p . f) xs -> All p $ map f xs
allMap $ []      = []
allMap $ h :: hs = h :: allMap hs
