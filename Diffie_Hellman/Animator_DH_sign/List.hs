{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  List(nth, fold, member, insert, union, remdups, removeAll, gen_length,
        map_filter, size_list, sort_key, insort_key)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified Multiset;
import qualified Product_Type;
import qualified HOL;
import qualified Orderings;
import qualified Option;
import qualified Arith;

nth :: forall a. [a] -> Arith.Nat -> a;
nth (x : xs) n =
  (if Arith.equal_nat n Arith.zero_nat then x
    else nth xs (Arith.minus_nat n Arith.one_nat));

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

member :: forall a. (Eq a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = x == y || member xs y;

insert :: forall a. (Eq a) => a -> [a] -> [a];
insert x xs = (if member xs x then xs else x : xs);

union :: forall a. (Eq a) => [a] -> [a] -> [a];
union = fold insert;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if member xs x then remdups xs else x : remdups xs);

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

gen_length :: forall a. Arith.Nat -> [a] -> Arith.Nat;
gen_length n (x : xs) = gen_length (Arith.suc n) xs;
gen_length n [] = n;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

size_list :: forall a. [a] -> Arith.Nat;
size_list = gen_length Arith.zero_nat;

sort_key :: forall a b. (Orderings.Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs =
  (case xs of {
    [] -> [];
    [_] -> xs;
    [x, y] -> (if Orderings.less_eq (f x) (f y) then xs else [y, x]);
    _ : _ : _ : _ ->
      (case Multiset.part f
              (f (nth xs
                   (Arith.divide_nat (size_list xs)
                     (Arith.nat_of_integer (2 :: Integer)))))
              xs
        of {
        (lts, (eqs, gts)) -> sort_key f lts ++ eqs ++ sort_key f gts;
      });
  });

insort_key :: forall a b. (Orderings.Linorder b) => (a -> b) -> a -> [a] -> [a];
insort_key f x [] = [x];
insort_key f x (y : ys) =
  (if Orderings.less_eq (f x) (f y) then x : y : ys else y : insort_key f x ys);

}
