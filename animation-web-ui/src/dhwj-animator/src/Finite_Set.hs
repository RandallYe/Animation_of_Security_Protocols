{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Finite_Set(Finite(..), card) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Rational;
import qualified List;
import qualified Set;
import qualified Arith;
import qualified Countable;

class (Countable.Countable a) => Finite a where {
};

card :: forall a. (Eq a) => Set.Set a -> Arith.Nat;
card (Set.Set xs) = List.size_list (List.remdups xs);

}
