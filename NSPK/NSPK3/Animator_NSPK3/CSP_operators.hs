{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSP_operators(inter_csp_list, indexed_inter_csp_list) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified ITree_CSP;
import qualified Interaction_Trees;
import qualified Set;

inter_csp_list ::
  forall a b.
    (Eq a) => [Interaction_Trees.Itree a b] -> Interaction_Trees.Itree a ();
inter_csp_list [] = ITree_CSP.skip;
inter_csp_list (p : ps) =
  ITree_CSP.gpar_csp (Interaction_Trees.bind_itree p (\ _ -> ITree_CSP.skip))
    Set.bot_set (inter_csp_list ps);

indexed_inter_csp_list ::
  forall a b c.
    (Eq b) => [a] ->
                (a -> Interaction_Trees.Itree b c) ->
                  Interaction_Trees.Itree b ();
indexed_inter_csp_list a px = inter_csp_list (map px a);

}
