{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ITree_Choice(genchoice) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Rational;
import qualified Product_Type;
import qualified Interaction_Trees;

genchoice ::
  forall a b.
    (Eq b) => (Interaction_Trees.Pfun a (Interaction_Trees.Itree a b) ->
                Interaction_Trees.Pfun a (Interaction_Trees.Itree a b) ->
                  Interaction_Trees.Pfun a (Interaction_Trees.Itree a b)) ->
                Interaction_Trees.Itree a b ->
                  Interaction_Trees.Itree a b -> Interaction_Trees.Itree a b;
genchoice m p q =
  (case (p, q) of {
    (Interaction_Trees.Ret r, Interaction_Trees.Ret y) ->
      (if r == y then Interaction_Trees.Ret r
        else Interaction_Trees.Vis Interaction_Trees.bot_pfun);
    (Interaction_Trees.Ret _, Interaction_Trees.Sil qa) ->
      Interaction_Trees.Sil (genchoice m p qa);
    (Interaction_Trees.Ret r, Interaction_Trees.Vis _) ->
      Interaction_Trees.Ret r;
    (Interaction_Trees.Sil pa, _) -> Interaction_Trees.Sil (genchoice m pa q);
    (Interaction_Trees.Vis _, Interaction_Trees.Ret a) ->
      Interaction_Trees.Ret a;
    (Interaction_Trees.Vis _, Interaction_Trees.Sil qa) ->
      Interaction_Trees.Sil (genchoice m p qa);
    (Interaction_Trees.Vis f, Interaction_Trees.Vis g) ->
      Interaction_Trees.Vis (m f g);
  });

}
