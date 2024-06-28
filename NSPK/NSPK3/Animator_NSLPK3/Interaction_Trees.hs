{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Interaction_Trees(Pfun(..), Itree(..), pdom, pfun_app, pfuse, pdom_res,
                     pfun_comp, graph_pfun, map_pfun, bind_itree, bot_pfun,
                     oplus_pfun)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
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
pfun_app (Pfun_of_alist xs) k =
  (if List.member (map fst xs) k then Option.the (Map.map_of xs k)
    else error "undefined");

pfuse :: forall a b c. (Eq a) => Pfun a b -> Pfun a c -> Pfun a (b, c);
pfuse f g =
  Pfun_entries (Set.inf_set (pdom f) (pdom g))
    (\ x -> (pfun_app f x, pfun_app g x));

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

oplus_pfun :: forall a b. Pfun a b -> Pfun a b -> Pfun a b;
oplus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

}
