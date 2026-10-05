{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Type_Length(Len0(..), len_of_bit0, Len(..), len_of_bit1, len_of_num1)
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
import qualified Numeral_Type;
import qualified Arith;
import qualified HOL;

class Len0 a where {
  len_of :: HOL.Itself a -> Arith.Nat;
};

len_of_bit0 ::
  forall a. (Len0 a) => HOL.Itself (Numeral_Type.Bit0 a) -> Arith.Nat;
len_of_bit0 uu =
  Arith.times_nat (Arith.nat_of_integer (2 :: Integer))
    ((len_of :: HOL.Itself a -> Arith.Nat) HOL.Type);

class (Len0 a) => Len a where {
};

instance (Len0 a) => Len0 (Numeral_Type.Bit0 a) where {
  len_of = len_of_bit0;
};

instance (Len a) => Len (Numeral_Type.Bit0 a) where {
};

len_of_bit1 ::
  forall a. (Len0 a) => HOL.Itself (Numeral_Type.Bit1 a) -> Arith.Nat;
len_of_bit1 uu =
  Arith.plus_nat
    (Arith.times_nat (Arith.nat_of_integer (2 :: Integer))
      ((len_of :: HOL.Itself a -> Arith.Nat) HOL.Type))
    Arith.one_nat;

instance (Len0 a) => Len0 (Numeral_Type.Bit1 a) where {
  len_of = len_of_bit1;
};

instance (Len0 a) => Len (Numeral_Type.Bit1 a) where {
};

len_of_num1 :: HOL.Itself Numeral_Type.Num1 -> Arith.Nat;
len_of_num1 uu = Arith.one_nat;

instance Len0 Numeral_Type.Num1 where {
  len_of = len_of_num1;
};

instance Len Numeral_Type.Num1 where {
};

}
