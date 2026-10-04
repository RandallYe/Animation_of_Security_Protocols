{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Typerep(Typerepa(..), Typerep(..)) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Rational;
import qualified HOL;

data Typerepa = Typerep String [Typerepa] deriving (Prelude.Read, Prelude.Show);

class Typerep a where {
  typerep :: HOL.Itself a -> Typerepa;
};

}
