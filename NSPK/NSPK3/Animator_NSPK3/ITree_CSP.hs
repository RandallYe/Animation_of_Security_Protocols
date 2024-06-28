{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  ITree_CSP(Andor(..), outp, skip, guard, emerge, genpar, rename, gpar_csp,
             map_prod, exception, genchoice, inp_list_where, extchoice_itree)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified List;
import qualified Option;
import qualified AList;
import qualified Map;
import qualified Relation_Extra;
import qualified Relation;
import qualified Product_Type;
import qualified Set;
import qualified Prisms;
import qualified Interaction_Trees;

data Andor a b = Left a | Right b | Both (a, b)
  deriving (Prelude.Read, Prelude.Show);

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
                    Interaction_Trees.Pfun a (Andor b c);
emerge f a g =
  Interaction_Trees.oplus_pfun
    (Interaction_Trees.oplus_pfun
      (Interaction_Trees.map_pfun Both
        (Interaction_Trees.pdom_res a (Interaction_Trees.pfuse f g)))
      (Interaction_Trees.map_pfun Left
        (Interaction_Trees.pdom_res
          (Set.uminus_set (Set.sup_set a (Interaction_Trees.pdom g))) f)))
    (Interaction_Trees.map_pfun Right
      (Interaction_Trees.pdom_res
        (Set.uminus_set (Set.sup_set a (Interaction_Trees.pdom f))) g));

genpar ::
  forall a b c.
    (Eq a) => (Interaction_Trees.Pfun a (Interaction_Trees.Itree a b) ->
                Set.Set a ->
                  Interaction_Trees.Pfun a (Interaction_Trees.Itree a c) ->
                    Interaction_Trees.Pfun a
                      (Andor (Interaction_Trees.Itree a b)
                        (Interaction_Trees.Itree a c))) ->
                Interaction_Trees.Itree a b ->
                  Set.Set a ->
                    Interaction_Trees.Itree a c ->
                      Interaction_Trees.Itree a (b, c);
genpar m p a q =
  (case (p, q) of {
    (Interaction_Trees.Ret r, Interaction_Trees.Ret y) ->
      Interaction_Trees.Ret (r, y);
    (Interaction_Trees.Ret _, Interaction_Trees.Sil qa) ->
      Interaction_Trees.Sil (genpar m p a qa);
    (Interaction_Trees.Ret r, Interaction_Trees.Vis g) ->
      Interaction_Trees.Vis
        (Interaction_Trees.map_pfun (genpar m (Interaction_Trees.Ret r) a)
          (Interaction_Trees.pdom_res (Set.uminus_set a) g));
    (Interaction_Trees.Sil pa, _) -> Interaction_Trees.Sil (genpar m pa a q);
    (Interaction_Trees.Vis pfun, Interaction_Trees.Ret v) ->
      Interaction_Trees.Vis
        (Interaction_Trees.map_pfun
          (\ pa -> genpar m pa a (Interaction_Trees.Ret v))
          (Interaction_Trees.pdom_res (Set.uminus_set a) pfun));
    (Interaction_Trees.Vis _, Interaction_Trees.Sil qa) ->
      Interaction_Trees.Sil (genpar m p a qa);
    (Interaction_Trees.Vis pfun, Interaction_Trees.Vis g) ->
      Interaction_Trees.Vis
        (Interaction_Trees.map_pfun
          (\ b -> (case b of {
                    Left pa -> genpar m pa a q;
                    Right ba -> genpar m p a ba;
                    Both (pa, ba) -> genpar m pa a ba;
                  }))
          (m pfun a g));
  });

rename ::
  forall a b c.
    (Eq a,
      Eq b) => Set.Set (a, b) ->
                 Interaction_Trees.Itree a c -> Interaction_Trees.Itree b c;
rename rho p =
  (case p of {
    Interaction_Trees.Ret a -> Interaction_Trees.Ret a;
    Interaction_Trees.Sil pa -> Interaction_Trees.Sil (rename rho pa);
    Interaction_Trees.Vis f ->
      Interaction_Trees.Vis
        (Interaction_Trees.map_pfun (rename rho)
          (Interaction_Trees.pfun_comp f
            (Interaction_Trees.graph_pfun
              (Relation.converse
                (Relation_Extra.rel_domres (Interaction_Trees.pdom f) rho)))));
  });

gpar_csp ::
  forall a b c.
    (Eq a) => Interaction_Trees.Itree a b ->
                Set.Set a ->
                  Interaction_Trees.Itree a c -> Interaction_Trees.Itree a ();
gpar_csp p cs q =
  Interaction_Trees.bind_itree (genpar emerge p cs q)
    (\ (_, _) -> Interaction_Trees.Ret ());

map_prod ::
  forall a b.
    (Eq a) => Interaction_Trees.Pfun a b ->
                Interaction_Trees.Pfun a b -> Interaction_Trees.Pfun a b;
map_prod p (Interaction_Trees.Pfun_of_alist []) = p;
map_prod (Interaction_Trees.Pfun_of_alist []) p = p;
map_prod (Interaction_Trees.Pfun_of_alist xs) (Interaction_Trees.Pfun_of_map p)
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
map_prod (Interaction_Trees.Pfun_of_map f) (Interaction_Trees.Pfun_of_alist xs)
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
map_prod (Interaction_Trees.Pfun_of_alist xs)
  (Interaction_Trees.Pfun_of_alist ys) =
  Interaction_Trees.Pfun_of_alist
    (AList.restrict (Set.uminus_set (Set.image fst (Set.Set xs))) ys ++
      AList.restrict (Set.uminus_set (Set.image fst (Set.Set ys))) xs);
map_prod (Interaction_Trees.Pfun_of_map f) (Interaction_Trees.Pfun_of_map g) =
  Interaction_Trees.Pfun_of_map (\ x -> (case (f x, g x) of {
  (Nothing, Nothing) -> Nothing;
  (Nothing, Just a) -> Just a;
  (Just xa, Nothing) -> Just xa;
  (Just _, Just _) -> Nothing;
}));

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
        (Interaction_Trees.map_pfun (\ b -> (case b of {
      Left pa -> exception pa a q;
      Right qa -> qa;
    }))
          (emerge (Interaction_Trees.pdom_res (Set.uminus_set a) f) Set.bot_set
            (Interaction_Trees.Pfun_entries
              (Set.inf_set a (Interaction_Trees.pdom f)) (\ _ -> q))));
  });

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
extchoice_itree = genchoice map_prod;

}
