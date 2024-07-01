{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Relation_Extra(rel_domres) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified AList;
import qualified Set;

rel_domres ::
  forall a b. (Eq a) => Set.Set a -> Set.Set (a, b) -> Set.Set (a, b);
rel_domres a (Set.Set xs) = Set.Set (AList.restrict a xs);

}
