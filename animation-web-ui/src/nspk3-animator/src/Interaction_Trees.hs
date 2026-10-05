{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Interaction_Trees(Pfun(..), Itree(..), pdom, pfun_app, pfuse_alist, pfuse,
                     pdom_res, pfun_upd, pfun_comp, graph_pfun, map_pfun,
                     bind_itree, bot_pfun, oplus_pfun)
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
import qualified Product_Type;
import qualified Arith;
import qualified Map;
import qualified List;
import qualified Option;
import qualified AList;
import qualified Set;

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b)
  | Pfun_entries (Set.Set a) (a -> b);

data Itree a b = Ret b | Sil (Itree a b) | Vis (Pfun a (Itree a b));

pdom :: forall a b. Pfun a b -> Set.Set a;
pdom (Pfun_entries a f) = a;
pdom (Pfun_of_alist xs) = Set.Set (map fst xs);

pfun_app :: forall a b. (Eq a) => Pfun a b -> a -> b;
pfun_app (Pfun_entries a f) x =
  (if Set.member x a then f x else error "undefined");
pfun_app (Pfun_of_map f) x = Option.the (f x);
pfun_app (Pfun_of_alist xs) k =
  (if List.member (map fst xs) k then Option.the (Map.map_of xs k)
    else error "undefined");

pfuse_alist :: forall a b c. (Eq a) => [(a, b)] -> Pfun a c -> [(a, (b, c))];
pfuse_alist [] f = [];
pfuse_alist ((k, v) : ps) f =
  (if Set.member k (pdom f) then (k, (v, pfun_app f k)) : pfuse_alist ps f
    else pfuse_alist ps f);

pfuse :: forall a b c. (Eq a) => Pfun a b -> Pfun a c -> Pfun a (b, c);
pfuse (Pfun_of_alist xs) g = Pfun_of_alist (pfuse_alist (AList.clearjunk xs) g);

pdom_res :: forall a b. (Eq a) => Set.Set a -> Pfun a b -> Pfun a b;
pdom_res a (Pfun_entries (Set.Set bs) f) =
  Pfun_of_alist
    (List.map_filter
      (\ x -> (if Set.member x a then Just (x, f x) else Nothing)) bs);
pdom_res (Set.Set xs) (Pfun_of_map m) =
  Pfun_of_alist
    (List.map_filter
      (\ x ->
        (if not (Option.is_none (m x)) then Just (x, Option.the (m x))
          else Nothing))
      xs);
pdom_res a (Pfun_of_alist m) = Pfun_of_alist (AList.restrict a m);

pfun_upd :: forall a b. (Eq a) => Pfun a b -> a -> b -> Pfun a b;
pfun_upd (Pfun_of_alist xs) k v = Pfun_of_alist (AList.update k v xs);

pfun_comp :: forall a b c. (Eq a, Eq c) => Pfun a b -> Pfun c a -> Pfun c b;
pfun_comp (Pfun_of_alist ys) (Pfun_of_alist xs) =
  Pfun_of_alist (AList.compose xs ys);

graph_pfun :: forall a b. (Eq a, Eq b) => Set.Set (a, b) -> Pfun a b;
graph_pfun (Set.Set xs) =
  Pfun_of_alist
    (filter
      (\ (x, _) ->
        Arith.equal_nat
          (List.size_list
            (List.remdups
              (map snd (AList.restrict (Set.insert x Set.bot_set) xs))))
          Arith.one_nat)
      xs);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_map g) = Pfun_of_map (\ x -> Option.map_option f (g x));
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = k v;

bot_pfun :: forall a b. Pfun a b;
bot_pfun = Pfun_of_alist [];

oplus_pfun :: forall a b. (Eq a) => Pfun a b -> Pfun a b -> Pfun a b;
oplus_pfun (Pfun_of_map f) (Pfun_of_alist xs) =
  Pfun_of_map
    (\ k -> (if List.member (map fst xs) k then Map.map_of xs k else f k));
oplus_pfun (Pfun_of_alist xs) (Pfun_of_map f) =
  Pfun_of_map (\ k -> (case f k of {
                        Nothing -> Map.map_of xs k;
                        Just a -> Just a;
                      }));
oplus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

}
