{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  ITree_CSP(hide, outp, skip, guard, emerge, gpar_csp, exception, excl_comb,
             inp_list_where, extchoice_itree)
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
import qualified ITree_Choice;
import qualified List;
import qualified Option;
import qualified AList;
import qualified Map;
import qualified Product_Type;
import qualified ITree_Parallel;
import qualified Prisms;
import qualified Finite_Set;
import qualified Interaction_Trees;
import qualified Set;
import qualified Arith;

hide ::
  forall a b.
    (Eq a) => Interaction_Trees.Itree a b ->
                Set.Set a -> Interaction_Trees.Itree a b;
hide p a =
  (case p of {
    Interaction_Trees.Ret aa -> Interaction_Trees.Ret aa;
    Interaction_Trees.Sil pa -> Interaction_Trees.Sil (hide pa a);
    Interaction_Trees.Vis f ->
      (if Arith.equal_nat
            (Finite_Set.card (Set.inf_set a (Interaction_Trees.pdom f)))
            Arith.one_nat
        then Interaction_Trees.Sil
               (hide (Interaction_Trees.pfun_app f
                       (Set.the_elem
                         (Set.inf_set a (Interaction_Trees.pdom f))))
                 a)
        else (if Set.is_empty (Set.inf_set a (Interaction_Trees.pdom f))
               then Interaction_Trees.Vis
                      (Interaction_Trees.map_pfun (\ x -> hide x a) f)
               else Interaction_Trees.Vis Interaction_Trees.bot_pfun));
  });

outp ::
  forall a b. Prisms.Prism_ext a b () -> a -> Interaction_Trees.Itree b ();
outp c v =
  Interaction_Trees.Vis
    (Interaction_Trees.Pfun_of_alist
      [(Prisms.prism_build c v, Interaction_Trees.Ret ())]);

skip :: forall a. Interaction_Trees.Itree a ();
skip = Interaction_Trees.Ret ();

guard :: forall a. Bool -> Interaction_Trees.Itree a ();
guard b =
  (if b then Interaction_Trees.Ret ()
    else Interaction_Trees.Vis Interaction_Trees.bot_pfun);

emerge ::
  forall a b c.
    (Eq a) => Interaction_Trees.Pfun a b ->
                Set.Set a ->
                  Interaction_Trees.Pfun a c ->
                    Interaction_Trees.Pfun a (ITree_Parallel.Andor b c);
emerge f a g =
  Interaction_Trees.oplus_pfun
    (Interaction_Trees.oplus_pfun
      (Interaction_Trees.map_pfun ITree_Parallel.Both
        (Interaction_Trees.pdom_res a (Interaction_Trees.pfuse f g)))
      (Interaction_Trees.map_pfun ITree_Parallel.Left
        (Interaction_Trees.pdom_res
          (Set.uminus_set (Set.sup_set a (Interaction_Trees.pdom g))) f)))
    (Interaction_Trees.map_pfun ITree_Parallel.Right
      (Interaction_Trees.pdom_res
        (Set.uminus_set (Set.sup_set a (Interaction_Trees.pdom f))) g));

gpar_csp ::
  forall a b c.
    (Eq a) => Interaction_Trees.Itree a b ->
                Set.Set a ->
                  Interaction_Trees.Itree a c -> Interaction_Trees.Itree a ();
gpar_csp p cs q =
  Interaction_Trees.bind_itree (ITree_Parallel.genpar emerge p cs q)
    (\ (_, _) -> Interaction_Trees.Ret ());

exception ::
  forall a b.
    (Eq a) => Interaction_Trees.Itree a b ->
                Set.Set a ->
                  Interaction_Trees.Itree a b -> Interaction_Trees.Itree a b;
exception p a q =
  (case p of {
    Interaction_Trees.Ret aa -> Interaction_Trees.Ret aa;
    Interaction_Trees.Sil pa -> Interaction_Trees.Sil (exception pa a q);
    Interaction_Trees.Vis f ->
      Interaction_Trees.Vis
        (Interaction_Trees.map_pfun
          (\ b -> (case b of {
                    ITree_Parallel.Left pa -> exception pa a q;
                    ITree_Parallel.Right qa -> qa;
                  }))
          (emerge (Interaction_Trees.pdom_res (Set.uminus_set a) f) Set.bot_set
            (Interaction_Trees.Pfun_entries
              (Set.inf_set a (Interaction_Trees.pdom f)) (\ _ -> q))));
  });

excl_comb ::
  forall a b.
    (Eq a) => Interaction_Trees.Pfun a b ->
                Interaction_Trees.Pfun a b -> Interaction_Trees.Pfun a b;
excl_comb p (Interaction_Trees.Pfun_of_alist []) = p;
excl_comb (Interaction_Trees.Pfun_of_alist []) p = p;
excl_comb (Interaction_Trees.Pfun_of_alist xs) (Interaction_Trees.Pfun_of_map p)
  = Interaction_Trees.Pfun_of_map (\ x -> (case Map.map_of xs x of {
    Nothing -> (case p x of {
                 Nothing -> Nothing;
                 Just a -> Just a;
               });
    Just xa -> (case p x of {
                 Nothing -> Just xa;
                 Just _ -> Nothing;
               });
  }));
excl_comb (Interaction_Trees.Pfun_of_map f) (Interaction_Trees.Pfun_of_alist xs)
  = Interaction_Trees.Pfun_of_map
      (\ x -> (case f x of {
                Nothing -> (case Map.map_of xs x of {
                             Nothing -> Nothing;
                             Just a -> Just a;
                           });
                Just xa -> (case Map.map_of xs x of {
                             Nothing -> Just xa;
                             Just _ -> Nothing;
                           });
              }));
excl_comb (Interaction_Trees.Pfun_of_alist xs)
  (Interaction_Trees.Pfun_of_alist ys) =
  Interaction_Trees.Pfun_of_alist
    (AList.restrict (Set.uminus_set (Set.image fst (Set.Set xs))) ys ++
      AList.restrict (Set.uminus_set (Set.image fst (Set.Set ys))) xs);
excl_comb (Interaction_Trees.Pfun_of_map f) (Interaction_Trees.Pfun_of_map g) =
  Interaction_Trees.Pfun_of_map (\ x -> (case (f x, g x) of {
  (Nothing, Nothing) -> Nothing;
  (Nothing, Just a) -> Just a;
  (Just xa, Nothing) -> Just xa;
  (Just _, Just _) -> Nothing;
}));

inp_list_where ::
  forall a b.
    Prisms.Prism_ext a b () ->
      [a] -> (a -> Bool) -> Interaction_Trees.Itree b a;
inp_list_where c b p =
  Interaction_Trees.Vis
    (Interaction_Trees.Pfun_of_alist
      (List.map_filter
        (\ x ->
          (if p x then Just (Prisms.prism_build c x, Interaction_Trees.Ret x)
            else Nothing))
        b));

extchoice_itree ::
  forall a b.
    (Eq a,
      Eq b) => Interaction_Trees.Itree a b ->
                 Interaction_Trees.Itree a b -> Interaction_Trees.Itree a b;
extchoice_itree = ITree_Choice.genchoice excl_comb;

}
