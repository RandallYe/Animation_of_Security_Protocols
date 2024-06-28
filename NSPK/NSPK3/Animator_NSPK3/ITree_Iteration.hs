{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ITree_Iteration(iterate) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified Interaction_Trees;

iterate ::
  forall a b.
    (a -> Bool) ->
      (a -> Interaction_Trees.Itree b a) -> a -> Interaction_Trees.Itree b a;
iterate b p s =
  (if b s
    then Interaction_Trees.bind_itree (p s)
           (Interaction_Trees.Sil . iterate b p)
    else Interaction_Trees.Ret s);

}
