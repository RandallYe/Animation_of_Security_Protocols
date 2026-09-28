{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module FSNat(Fsnat(..), nat_of_fsnat, equal_fsnat, less_eq_fsnat) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified HOL;
import qualified Arith;
import qualified Type_Length;

newtype Fsnat a = Nmk Arith.Nat deriving (Prelude.Read, Prelude.Show);

nat_of_fsnat :: forall a. (Type_Length.Len a) => Fsnat a -> Arith.Nat;
nat_of_fsnat (Nmk x) =
  Arith.modulo_nat x
    ((Type_Length.len_of :: HOL.Itself a -> Arith.Nat) HOL.Type);

equal_fsnat :: forall a. (Type_Length.Len a) => Fsnat a -> Fsnat a -> Bool;
equal_fsnat = (\ k l -> Arith.equal_nat (nat_of_fsnat k) (nat_of_fsnat l));

instance (Type_Length.Len a) => Eq (Fsnat a) where {
  a == b = equal_fsnat a b;
};

less_eq_fsnat :: forall a. (Type_Length.Len a) => Fsnat a -> Fsnat a -> Bool;
less_eq_fsnat x y = Arith.less_eq_nat (nat_of_fsnat x) (nat_of_fsnat y);

}
