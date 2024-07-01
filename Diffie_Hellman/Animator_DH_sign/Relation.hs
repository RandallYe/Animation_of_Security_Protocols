{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Relation(converse) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified Product_Type;
import qualified Set;

converse :: forall a b. Set.Set (a, b) -> Set.Set (b, a);
converse (Set.Set xs) = Set.Set (map (\ (x, y) -> (y, x)) xs);
converse r = Set.image (\ (x, y) -> (y, x)) r;

}
