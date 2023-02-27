module Data.CheckedEmpty.List.Lazy

import Data.Bool
import Data.List.Lazy

import public Language.Implicits.IfUnsolved

%default total

--- Types definitions ---

public export
data LazyL'st : (definitelyNotEmpty : Bool) -> Type -> Type where
  Nil  : LazyL'st False a
  (::) : (0 _ : True `IfUnsolved` ine) => (0 _ : True `IfUnsolved` ne) =>
         a -> Lazy (LazyL'st ine a) -> LazyL'st ne a

%name LazyL'st xs, ys, zs

||| An alias for a list that definitely may be empty.
||| Don't use this if you can be polymorphic on the boolean type argument.
public export %inline
LazyL'st0 : Type -> Type
LazyL'st0 = LazyL'st False

public export %inline
LazyL'st1 : Type -> Type
LazyL'st1 = LazyL'st True

--- Basic functions ---

public export
length : LazyL'st ne a -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
(++) : LazyL'st nel a -> Lazy (LazyL'st ner a) -> LazyL'st (nel || ner) a
[]      ++ ys = ys
(x::xs) ++ ys = x :: xs ++ ys

public export
Semigroup (LazyL'st ne a) where
  xs <+> ys = rewrite sym $ orSameNeutral ne in xs ++ ys

public export
Monoid (LazyL'st0 a) where
  neutral = []

--- Creation ---

public export
iterateN : (n : Nat) -> (a -> a) -> a -> LazyL'st (n /= 0) a
iterateN Z     _ x = []
iterateN (S n) f x = x :: iterateN n f (f x)

public export
replicate : (n : Nat) -> a -> LazyL'st (n /= 0) a
replicate Z     _ = []
replicate (S k) x = x :: replicate k x

covering
public export
iterate : (a -> Maybe a) -> a -> LazyL'st0 a
iterate f x = x :: case f x of
  Nothing => []
  Just y  => iterate f y

covering
public export
unfoldr : (b -> Maybe (a, b)) -> b -> LazyL'st0 a
unfoldr f c = case f c of
  Nothing     => []
  Just (a, n) => a :: unfoldr f n

--- Internal conversions ---

-- Relaxation --

public export
relaxF : LazyL'st ne a -> LazyL'st0 a
relaxF []      = []
relaxF (x::xs) = x::xs

public export %inline
relaxT : LazyL'st1 a -> LazyL'st ne a
relaxT (x::xs) = x::xs

public export
relaxAnd : LazyL'st ne a -> LazyL'st (ne && nx) a
relaxAnd []      = []
relaxAnd (x::xs) = x::xs

%transform "relaxF=id"   relaxF   {ne} {a} = believe_me (\x => the (LazyL'st ne a) x)
%transform "relaxT=id"   relaxT   {ne} {a} = believe_me (\x => the (LazyL'st ne a) x)
%transform "relaxAnd=id" relaxAnd {ne} {a} = believe_me (\x => the (LazyL'st ne a) x)

-- Strengthening --

public export
strengthen : LazyL'st ne a -> Maybe $ LazyL'st1 a
strengthen []      = Nothing
strengthen (x::xs) = Just $ x::xs

--- Functor ---

public export
Functor (LazyL'st ne) where
  map f []      = []
  map f (x::xs) = f x :: map f xs

namespace NEHeteroOps

  export
  bind : LazyL'st nel a -> (a -> LazyL'st ner b) -> LazyL'st (nel && ner) b
  bind [] _ = []
  bind wh@(x::xs) f = do
    rewrite andCommutative nel ner
    let Just nxs = strengthen xs
      | Nothing => relaxAnd $ f x
    rewrite sym $ orSameNeutral ner
    relaxAnd $ f x ++ (assert_smaller wh nxs `bind` f)

  export %inline
  bind' : LazyL'st nel a -> LazyL'st ner b -> LazyL'st (nel && ner) b
  bind' xs ys = xs `bind` \_ => ys

  export %inline
  join' : LazyL'st nel (LazyL'st ner a) -> LazyL'st (nel && ner) a
  join' xs = xs `bind` id

  export %inline
  ap : LazyL'st nel (a -> b) -> LazyL'st ner a -> LazyL'st (nel && ner) b
  ap xs ys = xs `bind` (<$> ys)

public export %inline
Applicative (LazyL'st ne) where
  pure x = [x]
  xs <*> ys = rewrite sym $ andSameNeutral ne in xs `ap` ys

public export %inline
Alternative LazyL'st0 where
  empty = []
  (<|>) = (++)

public export %inline
Monad (LazyL'st ne) where
  xs >>= f = rewrite sym $ andSameNeutral ne in xs `bind` f

--- Picking ---

public export
head : LazyL'st1 a -> a
head (x::_) = x

public export
head' : LazyL'st ne a -> Maybe a
head' = map head . strengthen

public export
tail : LazyL'st1 a -> LazyL'st0 a
tail (_::xs) = relaxF xs

public export
tail' : LazyL'st ne a -> Maybe $ LazyL'st0 a
tail' = map tail . strengthen

public export
last : LazyL'st1 a -> a
last [x]     = x
last wh@(_::(y::ys)) = last $ assert_smaller wh $ y::ys

public export
last' : LazyL'st ne a -> Maybe a
last' = map last . strengthen

public export
init : LazyL'st1 a -> LazyL'st0 a
init [x] = []
init wh@(x::(y::ys)) = x :: init (assert_smaller wh $ y::ys)

public export
init' : LazyL'st ne a -> Maybe $ LazyL'st0 a
init' = map init . strengthen

--- Sublisting ---

public export
take : (n : Nat) -> LazyL'st ne a -> LazyL'st (ne && n /= 0) a
take Z     _       = rewrite andFalseFalse ne in []
take _     []      = []
take (S k) (x::xs) = x :: take k xs

public export
drop : (n : Nat) -> LazyL'st ne a -> LazyL'st0 a
drop Z     xs      = relaxF xs
drop (S _) []      = []
drop (S n) (_::xs) = drop n $ relaxF xs

public export
takeWhile : (a -> Bool) -> LazyL'st ne a -> LazyL'st0 a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

public export
dropWhile : (a -> Bool) -> LazyL'st ne a -> LazyL'st0 a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

--- Folds ---

public export
foldrLazy : (op : a -> Lazy b -> b) -> (init : Lazy b) -> LazyL'st ne a -> b
foldrLazy _  init []      = init
foldrLazy op init (x::xs) = x `op` foldrLazy op init xs

export
Foldable (LazyL'st ne) where
  foldr c n []      = n
  foldr c n (x::xs) = c x (foldr c n xs)

  foldl f q []      = q
  foldl f q (x::xs) = foldl f (f q x) xs

  null []     = True
  null (_::_) = False

  foldlM op init []      = pure init
  foldlM op init (x::xs) = op init x >>= \next => foldlM op next xs

  toList []      = []
  toList (x::xs) = x :: toList xs

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

export
foldl1 : (a -> a -> a) -> LazyL'st1 a -> a
foldl1 f (x::xs) = foldl f x xs

export
foldr1 : (a -> Lazy a -> a) -> LazyL'st1 a -> a
foldr1 op [x] = x
foldr1 op (x::xs@(y::ys)) = op x $ foldr1 op $ assert_smaller xs (y::ys)

public export
traverse_ : Monad m => (a -> m b) -> LazyL'st ne a -> m Unit
traverse_ f = foldrLazy ((>>) . ignore . f) (pure ())

public export %inline
for_ : Monad m => LazyL'st ne a -> (a -> m b) -> m Unit
for_ = flip Lazy.traverse_

public export %inline
sequence_ : Monad m => LazyL'st ne (m a) -> m Unit
sequence_ = Lazy.traverse_ id

--- Filtering ---

export
filter : (a -> Bool) -> LazyL'st ne a -> LazyL'st0 a
filter _ []      = []
filter f (x::xs) = if f x then x :: filter f xs else filter f xs

export
mapMaybe : (a -> Maybe b) -> LazyL'st ne a -> LazyL'st0 b
mapMaybe _ [] = []
mapMaybe f (x::xs) = case f x of
                       Just y  => y :: mapMaybe f xs
                       Nothing => mapMaybe f xs

--- External conversions ---

-- List --

public export
fromList : (xs : List a) -> LazyL'st (not $ null xs) a
fromList []      = []
fromList (x::xs) = x :: fromList xs

public export
Cast (List a) (LazyL'st0 a) where
  cast xs = relaxF $ fromList xs

-- LazyList --

public export
fromLazyList : (xs : LazyList a) -> LazyL'st (not $ null xs) a
fromLazyList []      = []
fromLazyList (x::xs) = x :: fromLazyList xs

public export
Cast (LazyList a) (LazyL'st0 a) where
  cast xs = relaxF $ fromLazyList xs

public export
toLazyList : LazyL'st ne a -> LazyList a
toLazyList []      = []
toLazyList (x::xs) = x :: toLazyList xs

public export
Cast (LazyL'st ne a) (LazyList a) where
  cast = toLazyList

--- Showing ---

export
Show a => Show (LazyL'st ne a) where
  show = show . toList

export
[DoNotEval] Show a => Show (LazyL'st ne a) where
  show []     = "[]"
  show (x::_) = "\{show x} :: <lazy>"

--- Properties ---

export
mapFusion : (g : b -> c) -> (f : a -> b) -> (xs : LazyL'st ne a) -> map g (map f xs) = map (g . f) xs
mapFusion g f []      = Refl
mapFusion g f (x::xs) = rewrite mapFusion g f xs in Refl

export
mapExt : (xs : LazyL'st ne _) -> ((x : _) -> f x = g x) -> map f xs = map g xs
mapExt []      _  = Refl
mapExt (x::xs) fg = rewrite fg x in cong (g x ::) $ mapExt _ fg
