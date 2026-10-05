{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ITree_Parallel(Andor(..), genpar) where {

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
import qualified Set;

data Andor a b = Left a | Right b | Both (a, b)
  deriving (Prelude.Read, Prelude.Show);

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

}
