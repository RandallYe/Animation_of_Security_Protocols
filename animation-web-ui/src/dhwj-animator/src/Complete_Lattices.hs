{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Complete_Lattices(sup_set) where {

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

sup_set :: forall a. (Eq a) => Set.Set (Set.Set a) -> Set.Set a;
sup_set (Set.Set xs) = List.fold Set.sup_set xs Set.bot_set;

}
