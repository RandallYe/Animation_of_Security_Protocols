{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Set(Set(..), image, insert, member, remove, bot_set, inf_set, sup_set,
       less_eq_set, equal_set, uminus_set)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified List;

data Set a = Set [a] | Coset [a] deriving (Prelude.Read, Prelude.Show);

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (List.removeAll x xs);
insert x (Set xs) = Set (List.insert x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (List.member xs x);
member x (Set xs) = List.member xs x;

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (List.insert x xs);
remove x (Set xs) = Set (List.removeAll x xs);

bot_set :: forall a. Set a;
bot_set = Set [];

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = List.fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = List.fold insert xs a;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

}
