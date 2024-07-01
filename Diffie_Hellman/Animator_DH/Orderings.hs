{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Orderings(Ord(..), Preorder(..), Order(..), Linorder(..), max) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

class (Order a) => Linorder a where {
};

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

}
