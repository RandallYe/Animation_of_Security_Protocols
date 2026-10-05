{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSP_operators(hidep, par_hidep, list_inter, inter_csp_list,
                 outp_choice_from_list, indexed_inter_csp_list)
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
import qualified Prisms;
import qualified ITree_CSP;
import qualified List;
import qualified Interaction_Trees;
import qualified Set;

hidep ::
  forall a b.
    (Eq a) => Interaction_Trees.Itree a b -> [a] -> Interaction_Trees.Itree a b;
hidep p es =
  List.foldl (\ q e -> ITree_CSP.hide q (Set.insert e Set.bot_set)) p es;

par_hidep ::
  forall a.
    (Eq a) => Interaction_Trees.Itree a () ->
                [a] ->
                  Interaction_Trees.Itree a () -> Interaction_Trees.Itree a ();
par_hidep p s q = hidep (ITree_CSP.gpar_csp p (Set.Set s) q) s;

list_inter :: forall a. (Eq a) => [a] -> [a] -> [a];
list_inter [] ys = [];
list_inter (x : xs) ys =
  (if List.member ys x then x : list_inter xs ys else list_inter xs ys);

inter_csp_list ::
  forall a b.
    (Eq a) => [Interaction_Trees.Itree a b] -> Interaction_Trees.Itree a ();
inter_csp_list [] = ITree_CSP.skip;
inter_csp_list (p : ps) =
  ITree_CSP.gpar_csp (Interaction_Trees.bind_itree p (\ _ -> ITree_CSP.skip))
    Set.bot_set (inter_csp_list ps);

outp_choice_from_list ::
  forall a b c.
    Prisms.Prism_ext a b () ->
      (a -> Interaction_Trees.Itree b c) -> [a] -> Interaction_Trees.Itree b c;
outp_choice_from_list c p a =
  Interaction_Trees.Vis
    (Interaction_Trees.Pfun_of_alist
      (map (\ x -> (Prisms.prism_build c x, p x)) a));

indexed_inter_csp_list ::
  forall a b c.
    (Eq b) => [a] ->
                (a -> Interaction_Trees.Itree b c) ->
                  Interaction_Trees.Itree b ();
indexed_inter_csp_list a px = inter_csp_list (map px a);

}
