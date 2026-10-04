{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Numeral_Type(Bit0(..), typerep_bit0, Bit1(..), typerep_bit1, Num1(..),
                typerep_num1)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Rational;
import qualified Arith;
import qualified Finite_Set;
import qualified HOL;
import qualified Typerep;

newtype Bit0 a = Abs_bit0 Arith.Int deriving (Prelude.Read, Prelude.Show);

typerep_bit0 ::
  forall a. (Typerep.Typerep a) => HOL.Itself (Bit0 a) -> Typerep.Typerepa;
typerep_bit0 t =
  Typerep.Typerep "Numeral_Type.bit0"
    [(Typerep.typerep :: HOL.Itself a -> Typerep.Typerepa) HOL.Type];

instance (Typerep.Typerep a) => Typerep.Typerep (Bit0 a) where {
  typerep = typerep_bit0;
};

newtype Bit1 a = Abs_bit1 Arith.Int deriving (Prelude.Read, Prelude.Show);

typerep_bit1 ::
  forall a. (Typerep.Typerep a) => HOL.Itself (Bit1 a) -> Typerep.Typerepa;
typerep_bit1 t =
  Typerep.Typerep "Numeral_Type.bit1"
    [(Typerep.typerep :: HOL.Itself a -> Typerep.Typerepa) HOL.Type];

instance (Typerep.Typerep a) => Typerep.Typerep (Bit1 a) where {
  typerep = typerep_bit1;
};

data Num1 = One_num1 deriving (Prelude.Read, Prelude.Show);

typerep_num1 :: HOL.Itself Num1 -> Typerep.Typerepa;
typerep_num1 t = Typerep.Typerep "Numeral_Type.num1" [];

instance Typerep.Typerep Num1 where {
  typerep = typerep_num1;
};

}
