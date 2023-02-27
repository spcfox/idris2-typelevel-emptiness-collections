module Data.CheckedEmpty.List

import Data.Bool
import Data.List1
import Data.Vect

import public Language.Implicits.IfUnsolved

%default total

--- Types definitions ---

public export
data L'st : (definitelyNotEmpty : Bool) -> Type -> Type where
  Nil  : L'st False a
  (::) : (0 _ : True `IfUnsolved` ine) => (0 _ : True `IfUnsolved` ne) =>
         a -> L'st ine a -> L'st ne a

%name L'st xs, ys, zs

||| An alias for a list that definitely may be empty.
||| Don't use this if you can be polymorphic on the boolean type argument.
public export %inline
L'st0 : Type -> Type
L'st0 = L'st False

public export %inline
L'st1 : Type -> Type
L'st1 = L'st True

--- Basic functions ---

public export
length : L'st ne a -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
(++) : L'st nel a -> L'st ner a -> L'st (nel || ner) a
[]      ++ ys = ys
(x::xs) ++ ys = x :: xs ++ ys

public export
Semigroup (L'st ne a) where
  xs <+> ys = rewrite sym $ orSameNeutral ne in xs ++ ys

public export
Monoid (L'st0 a) where
  neutral = []

--- Creation ---

public export
iterateN : (n : Nat) -> (a -> a) -> a -> L'st (n /= 0) a
iterateN Z     _ x = []
iterateN (S n) f x = x :: iterateN n f x

public export
replicate : (n : Nat) -> a -> L'st (n /= 0) a
replicate Z     _ = []
replicate (S k) x = x :: replicate k x

covering
public export
iterate : (a -> Maybe a) -> a -> L'st0 a
iterate f x = x :: case f x of
  Nothing => []
  Just y  => iterate f y

covering
public export
unfoldr : (b -> Maybe (a, b)) -> b -> L'st0 a
unfoldr f c = case f c of
  Nothing     => []
  Just (a, n) => a :: unfoldr f n

--- Internal conversions ---

-- Relaxation --

public export
relaxF : L'st ne a -> L'st0 a
relaxF []      = []
relaxF (x::xs) = x::xs

public export %inline
relaxT : L'st1 a -> L'st ne a
relaxT (x::xs) = x::xs

public export
relaxAnd : L'st ne a -> L'st (ne && nx) a
relaxAnd []      = []
relaxAnd (x::xs) = x::xs

%transform "relaxF=id"   relaxF   {ne} {a} = believe_me (\x => the (L'st ne a) x)
%transform "relaxT=id"   relaxT   {ne} {a} = believe_me (\x => the (L'st ne a) x)
%transform "relaxAnd=id" relaxAnd {ne} {a} = believe_me (\x => the (L'st ne a) x)

-- Strengthening --

public export
strengthen : L'st ne a -> Maybe $ L'st1 a
strengthen []      = Nothing
strengthen (x::xs) = Just $ x::xs

--- Functor ---

public export
Functor (L'st ne) where
  map f []      = []
  map f (x::xs) = f x :: map f xs

namespace NEHeteroOps

  export
  bind : L'st nel a -> (a -> L'st ner b) -> L'st (nel && ner) b
  bind [] _ = []
  bind wh@(x::xs) f = do
    rewrite andCommutative nel ner
    let Just nxs = strengthen xs
      | Nothing => relaxAnd $ f x
    rewrite sym $ orSameNeutral ner
    relaxAnd $ f x ++ (assert_smaller wh nxs `bind` f)

  export %inline
  bind' : L'st nel a -> L'st ner b -> L'st (nel && ner) b
  bind' xs ys = xs `bind` \_ => ys

  export %inline
  join' : L'st nel (L'st ner a) -> L'st (nel && ner) a
  join' xs = xs `bind` id

  export %inline
  ap : L'st nel (a -> b) -> L'st ner a -> L'st (nel && ner) b
  ap xs ys = xs `bind` (<$> ys)

public export %inline
Applicative (L'st ne) where
  pure x = [x]
  xs <*> ys = rewrite sym $ andSameNeutral ne in xs `ap` ys

public export %inline
Alternative L'st0 where
  empty = []
  xs <|> ys = xs ++ ys

public export %inline
Monad (L'st ne) where
  xs >>= f = rewrite sym $ andSameNeutral ne in xs `bind` f

--- Picking ---

public export
head : L'st1 a -> a
head (x::_) = x

public export
head' : L'st ne a -> Maybe a
head' = map head . strengthen

public export
tail : L'st1 a -> L'st0 a
tail (_::xs) = relaxF xs

public export
tail' : L'st ne a -> Maybe $ L'st0 a
tail' = map tail . strengthen

public export
last : L'st1 a -> a
last [x]     = x
last wh@(_::(y::ys)) = last $ assert_smaller wh $ y::ys

public export
last' : L'st ne a -> Maybe a
last' = map last . strengthen

public export
init : L'st1 a -> L'st0 a
init [x] = []
init wh@(x::(y::ys)) = x :: init (assert_smaller wh $ y::ys)

public export
init' : L'st ne a -> Maybe $ L'st0 a
init' = map init . strengthen

--- Sublisting ---

public export
take : (n : Nat) -> L'st ne a -> L'st (ne && n /= 0) a
take Z     _       = rewrite andFalseFalse ne in []
take _     []      = []
take (S k) (x::xs) = x :: take k xs

public export
drop : (n : Nat) -> L'st ne a -> L'st0 a
drop Z     xs      = relaxF xs
drop (S _) []      = []
drop (S n) (_::xs) = drop n $ relaxF xs

public export
takeWhile : (a -> Bool) -> L'st ne a -> L'st0 a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

public export
dropWhile : (a -> Bool) -> L'st ne a -> L'st0 a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

--- Folds ---

export
Foldable (L'st ne) where
  foldr c n []      = n
  foldr c n (x::xs) = c x (foldr c n xs)

  foldl f q []      = q
  foldl f q (x::xs) = foldl f (f q x) xs

  null []     = True
  null (_::_) = False

  toList []      = []
  toList (x::xs) = x :: toList xs

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

export
foldl1 : (a -> a -> a) -> L'st1 a -> a
foldl1 f (x::xs) = foldl f x xs

export
Traversable (L'st ne) where
  traverse f []      = pure []
  traverse f (x::xs) = [| f x :: traverse f xs |]

--- Filtering ---

export
filter : (a -> Bool) -> L'st ne a -> L'st0 a
filter _ []      = []
filter f (x::xs) = if f x then x :: filter f xs else filter f xs

export
mapMaybe : (a -> Maybe b) -> L'st ne a -> L'st0 b
mapMaybe _ [] = []
mapMaybe f (x::xs) = case f x of
                       Just y  => y :: mapMaybe f xs
                       Nothing => mapMaybe f xs

--- External conversions ---

-- List --

public export
fromList : (xs : List a) -> L'st (not $ null xs) a
fromList []      = []
fromList (x::xs) = x :: fromList xs

public export
Cast (List a) (L'st0 a) where
  cast xs = relaxF $ fromList xs

-- List1 --

public export
fromList1 : List1 a -> L'st1 a
fromList1 $ x:::xs = x :: fromList xs

public export
toList1 : L'st1 a -> List1 a
toList1 $ x::xs = x ::: toList xs

public export
Cast (List1 a) (L'st True a) where
  cast = fromList1

public export
Cast (L'st True a) (List1 a) where
  cast = toList1

-- Vect --

public export
fromVect : Vect n a -> L'st (n /= Z) a
fromVect []      = []
fromVect (x::xs) = x :: fromVect xs

public export
Cast (Vect n a) (L'st (n /= Z) a) where
  cast = fromVect

--- Showing ---

export
Show a => Show (L'st ne a) where
  show = show . toList

--- Reversing ---

public export
reverse : L'st ne a -> L'st ne a
reverse []      = []
reverse (x::xs) = foldl (flip (::)) [x] xs

--- Properties ---

export
mapFusion : (g : b -> c) -> (f : a -> b) -> (xs : L'st ne a) -> map g (map f xs) = map (g . f) xs
mapFusion g f []      = Refl
mapFusion g f (x::xs) = rewrite mapFusion g f xs in Refl

export
mapExt : (xs : L'st ne _) -> ((x : _) -> f x = g x) -> map f xs = map g xs
mapExt []      _  = Refl
mapExt (x::xs) fg = rewrite fg x in cong (g x ::) $ mapExt _ fg
