
module Data.CheckedEmpty.List.Properties.Quantifiers

import Data.CheckedEmpty.List
import Data.CheckedEmpty.List.Elem
import Data.CheckedEmpty.List.Properties.Map
import Data.CheckedEmpty.List.Quantifiers

%default total

export
allMapForall : {0 f : a -> b} -> {xs : Lst ne a} ->
               ({x : a} -> (0 _ : Elem x xs) -> p (f x)) ->
               All p $ map f xs
allMapForall {xs=[]}      _ = []
allMapForall {xs=x :: xs} h = h Here :: allMapForall (\e => h $ There e)

export
allElem : {xs : Lst ne a} -> ({x : a} -> (0 _ : Elem x xs) -> p x) -> All p xs
allElem h = rewrite sym $ mapId {xs} in allMapForall h

export
allTrue : {xs : Lst ne a} -> ({x : a} -> p x) -> All p xs
allTrue h = allElem $ \_ => h

export
allMap : {0 xs : Lst ne a} -> {0 f : a -> b} ->
         All (p . f) xs -> All p $ map f xs
allMap $ []      = []
allMap $ h :: hs = h :: allMap hs
