{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSP_operators(seq_csp_list, inter_csp_list, indexed_seq_csp_list,
                 indexed_inter_csp_list)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified ITree_CSP;
import qualified Set;
import qualified Interaction_Trees;

seq_csp_list ::
  forall a b.
    [a -> Interaction_Trees.Itree b a] -> a -> Interaction_Trees.Itree b a;
seq_csp_list [] s = Interaction_Trees.Ret s;
seq_csp_list (p : ps) s = Interaction_Trees.bind_itree (p s) (seq_csp_list ps);

inter_csp_list ::
  forall a b.
    (Eq a) => [Interaction_Trees.Itree a b] -> Interaction_Trees.Itree a ();
inter_csp_list [] = ITree_CSP.skip;
inter_csp_list (p : ps) =
  ITree_CSP.gpar_csp (Interaction_Trees.bind_itree p (\ _ -> ITree_CSP.skip))
    Set.bot_set (inter_csp_list ps);

indexed_seq_csp_list ::
  forall a b c.
    [a] ->
      (a -> b -> Interaction_Trees.Itree c b) ->
        b -> Interaction_Trees.Itree c b;
indexed_seq_csp_list a ps s = seq_csp_list (map ps a) s;

indexed_inter_csp_list ::
  forall a b c.
    (Eq b) => [a] ->
                (a -> Interaction_Trees.Itree b c) ->
                  Interaction_Trees.Itree b ();
indexed_inter_csp_list a px = inter_csp_list (map px a);

}
