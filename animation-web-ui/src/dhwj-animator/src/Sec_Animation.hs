{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Sec_Animation(Skind(..), explore, checks, is_end, is_sig, is_leak, reaches,
                 feasible, is_start, check_sig, is_honest, stop_kind,
                 budget_hit, check_corr, check_leak, follow_fuel, state_kind,
                 is_terminate, is_end_honest, matches_start, check_leak_msg,
                 check_terminate, check_auth_violation, check_authenticity,
                 check_corr_violation)
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
import qualified List;
import qualified Complete_Lattices;
import qualified Sec_Messages;
import qualified FSNat;
import qualified Typerep;
import qualified Type_Length;
import qualified Interaction_Trees;
import qualified Set;
import qualified Arith;

data Skind = SContinues | STerminated | SDeadlocked | SDivergent
  deriving (Prelude.Read, Prelude.Show);

explore ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat ->
                  Arith.Nat -> Interaction_Trees.Itree a b -> Set.Set [a];
explore n mx t (Interaction_Trees.Vis f) =
  (if Arith.equal_nat n Arith.zero_nat then Set.insert [] Set.bot_set
    else Set.sup_set (Set.insert [] Set.bot_set)
           (Complete_Lattices.sup_set
             (Set.image
               (\ e ->
                 Set.image (\ a -> e : a)
                   (explore (Arith.minus_nat n Arith.one_nat) mx mx
                     (Interaction_Trees.pfun_app f e)))
               (Interaction_Trees.pdom f))));
explore n mx t (Interaction_Trees.Sil q) =
  (if Arith.equal_nat n Arith.zero_nat then Set.insert [] Set.bot_set
    else (if Arith.equal_nat t Arith.zero_nat then Set.insert [] Set.bot_set
           else explore n mx (Arith.minus_nat t Arith.one_nat) q));
explore n mx t (Interaction_Trees.Ret x) = Set.insert [] Set.bot_set;

checks ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat ->
                  Interaction_Trees.Itree a b -> ([a] -> Bool) -> Set.Set [a];
checks n mx p pred = Set.filtera pred (explore n mx mx p);

is_end ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Sec_Messages.Chan a b c d e f g -> Bool;
is_end e = (case e of {
             Sec_Messages.Env_C _ -> False;
             Sec_Messages.Send_C _ -> False;
             Sec_Messages.Cjam_C _ -> False;
             Sec_Messages.Cdejam_C _ -> False;
             Sec_Messages.Recv_C _ -> False;
             Sec_Messages.Leak_C _ -> False;
             Sec_Messages.Sig_C (Sec_Messages.ClaimSecret _ _ _) -> False;
             Sec_Messages.Sig_C (Sec_Messages.StartProt _ _ _ _) -> False;
             Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _) -> True;
             Sec_Messages.Terminate_C _ -> False;
           });

is_sig ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Sec_Messages.Chan a b c d e f g -> Bool;
is_sig e = (case e of {
             Sec_Messages.Env_C _ -> False;
             Sec_Messages.Send_C _ -> False;
             Sec_Messages.Cjam_C _ -> False;
             Sec_Messages.Cdejam_C _ -> False;
             Sec_Messages.Recv_C _ -> False;
             Sec_Messages.Leak_C _ -> False;
             Sec_Messages.Sig_C _ -> True;
             Sec_Messages.Terminate_C _ -> False;
           });

is_leak ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Sec_Messages.Chan a b c d e f g -> Bool;
is_leak e = (case e of {
              Sec_Messages.Env_C _ -> False;
              Sec_Messages.Send_C _ -> False;
              Sec_Messages.Cjam_C _ -> False;
              Sec_Messages.Cdejam_C _ -> False;
              Sec_Messages.Recv_C _ -> False;
              Sec_Messages.Leak_C _ -> True;
              Sec_Messages.Sig_C _ -> False;
              Sec_Messages.Terminate_C _ -> False;
            });

reaches ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat -> Interaction_Trees.Itree a b -> [a] -> [a] -> Bool;
reaches n mx p re me =
  not (Set.equal_set
        (Set.filtera
          (\ tr ->
            any (List.member tr) re && (null me || any (List.member tr) me))
          (explore n mx mx p))
        Set.bot_set);

feasible ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat -> Interaction_Trees.Itree a b -> [a] -> Bool;
feasible n mx p tr = Set.member tr (explore n mx mx p);

is_start ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Sec_Messages.Chan a b c d e f g -> Bool;
is_start e = (case e of {
               Sec_Messages.Env_C _ -> False;
               Sec_Messages.Send_C _ -> False;
               Sec_Messages.Cjam_C _ -> False;
               Sec_Messages.Cdejam_C _ -> False;
               Sec_Messages.Recv_C _ -> False;
               Sec_Messages.Leak_C _ -> False;
               Sec_Messages.Sig_C (Sec_Messages.ClaimSecret _ _ _) -> False;
               Sec_Messages.Sig_C (Sec_Messages.StartProt _ _ _ _) -> True;
               Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _) -> False;
               Sec_Messages.Terminate_C _ -> False;
             });

check_sig ::
  forall a b c d e f g h.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Arith.Nat ->
                              Arith.Nat ->
                                Interaction_Trees.Itree
                                  (Sec_Messages.Chan a b c d e f g) h ->
                                  Set.Set [Sec_Messages.Chan a b c d e f g];
check_sig n mx p = checks n mx p (any is_sig);

is_honest ::
  forall a.
    (Type_Length.Len a, Typerep.Typerep a) => Sec_Messages.Dagent a -> Bool;
is_honest a = (case a of {
                Sec_Messages.Agent _ -> True;
                Sec_Messages.Intruder -> False;
                Sec_Messages.Server -> True;
              });

stop_kind :: forall a b. Arith.Nat -> Interaction_Trees.Itree a b -> Skind;
stop_kind t p =
  (case p of {
    Interaction_Trees.Ret _ -> STerminated;
    Interaction_Trees.Sil q ->
      (if Arith.equal_nat t Arith.zero_nat then SDivergent
        else stop_kind (Arith.minus_nat t Arith.one_nat) q);
    Interaction_Trees.Vis f ->
      (if Set.is_empty (Interaction_Trees.pdom f) then SDeadlocked
        else SContinues);
  });

budget_hit ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat -> Arith.Nat -> Interaction_Trees.Itree a b -> Bool;
budget_hit n mx t (Interaction_Trees.Vis f) =
  (if Arith.equal_nat n Arith.zero_nat then False
    else Set.bex (Interaction_Trees.pdom f)
           (\ e ->
             budget_hit (Arith.minus_nat n Arith.one_nat) mx mx
               (Interaction_Trees.pfun_app f e)));
budget_hit n mx t (Interaction_Trees.Sil q) =
  (if Arith.equal_nat n Arith.zero_nat then False
    else (if Arith.equal_nat t Arith.zero_nat then True
           else budget_hit n mx (Arith.minus_nat t Arith.one_nat) q));
budget_hit n mx t (Interaction_Trees.Ret x) = False;

check_corr ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat ->
                  Interaction_Trees.Itree a b ->
                    (a -> Bool) -> (a -> Bool) -> Set.Set [a];
check_corr n mx p mon re =
  checks n mx p
    (\ tr -> not (null tr) && re (List.last tr) && any mon (List.butlast tr));

check_leak ::
  forall a b c d e f g h.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Arith.Nat ->
                              Arith.Nat ->
                                Interaction_Trees.Itree
                                  (Sec_Messages.Chan a b c d e f g) h ->
                                  Set.Set [Sec_Messages.Chan a b c d e f g];
check_leak n mx p = checks n mx p (any is_leak);

follow_fuel ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat ->
                  Arith.Nat ->
                    Interaction_Trees.Itree a b ->
                      [a] -> Interaction_Trees.Itree a b;
follow_fuel f mx t p tr =
  (if Arith.equal_nat f Arith.zero_nat then p
    else (case p of {
           Interaction_Trees.Ret a -> Interaction_Trees.Ret a;
           Interaction_Trees.Sil q ->
             (if Arith.equal_nat t Arith.zero_nat then Interaction_Trees.Sil q
               else follow_fuel (Arith.minus_nat f Arith.one_nat) mx
                      (Arith.minus_nat t Arith.one_nat) q tr);
           Interaction_Trees.Vis fa ->
             (case tr of {
               [] -> Interaction_Trees.Vis fa;
               e : tra ->
                 (if Set.member e (Interaction_Trees.pdom fa)
                   then follow_fuel (Arith.minus_nat f Arith.one_nat) mx mx
                          (Interaction_Trees.pfun_app fa e) tra
                   else Interaction_Trees.Vis fa);
             });
         }));

state_kind ::
  forall a b.
    (Eq a) => Arith.Nat -> Interaction_Trees.Itree a b -> [a] -> Skind;
state_kind mx p tr =
  stop_kind mx
    (follow_fuel
      (Arith.times_nat (Arith.plus_nat (List.size_list tr) Arith.one_nat)
        (Arith.plus_nat mx Arith.one_nat))
      mx mx p tr);

is_terminate ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Sec_Messages.Chan a b c d e f g -> Bool;
is_terminate e = (case e of {
                   Sec_Messages.Env_C _ -> False;
                   Sec_Messages.Send_C _ -> False;
                   Sec_Messages.Cjam_C _ -> False;
                   Sec_Messages.Cdejam_C _ -> False;
                   Sec_Messages.Recv_C _ -> False;
                   Sec_Messages.Leak_C _ -> False;
                   Sec_Messages.Sig_C _ -> False;
                   Sec_Messages.Terminate_C () -> True;
                 });

is_end_honest ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Sec_Messages.Chan a b c d e f g -> Bool;
is_end_honest e =
  (case e of {
    Sec_Messages.Env_C _ -> False;
    Sec_Messages.Send_C _ -> False;
    Sec_Messages.Cjam_C _ -> False;
    Sec_Messages.Cdejam_C _ -> False;
    Sec_Messages.Recv_C _ -> False;
    Sec_Messages.Leak_C _ -> False;
    Sec_Messages.Sig_C (Sec_Messages.ClaimSecret _ _ _) -> False;
    Sec_Messages.Sig_C (Sec_Messages.StartProt _ _ _ _) -> False;
    Sec_Messages.Sig_C (Sec_Messages.EndProt s d _ _) ->
      is_honest s && is_honest d;
    Sec_Messages.Terminate_C _ -> False;
  });

matches_start ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Sec_Messages.Chan a b c d e f g ->
                              Sec_Messages.Chan a b c d e f g -> Bool;
matches_start e_end e_start =
  (case (e_end, e_start) of {
    (Sec_Messages.Env_C _, _) -> False;
    (Sec_Messages.Send_C _, _) -> False;
    (Sec_Messages.Cjam_C _, _) -> False;
    (Sec_Messages.Cdejam_C _, _) -> False;
    (Sec_Messages.Recv_C _, _) -> False;
    (Sec_Messages.Leak_C _, _) -> False;
    (Sec_Messages.Sig_C (Sec_Messages.ClaimSecret _ _ _), _) -> False;
    (Sec_Messages.Sig_C (Sec_Messages.StartProt _ _ _ _), _) -> False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _), Sec_Messages.Env_C _) ->
      False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _), Sec_Messages.Send_C _)
      -> False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _), Sec_Messages.Cjam_C _)
      -> False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _), Sec_Messages.Cdejam_C _)
      -> False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _), Sec_Messages.Recv_C _)
      -> False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _), Sec_Messages.Leak_C _)
      -> False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _),
      Sec_Messages.Sig_C (Sec_Messages.ClaimSecret _ _ _))
      -> False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt s d ns nd),
      Sec_Messages.Sig_C (Sec_Messages.StartProt sa da nsa nda))
      -> Sec_Messages.equal_dagent sa d &&
           Sec_Messages.equal_dagent da s &&
             FSNat.equal_fsnat nsa ns && FSNat.equal_fsnat nda nd;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _),
      Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _))
      -> False;
    (Sec_Messages.Sig_C (Sec_Messages.EndProt _ _ _ _),
      Sec_Messages.Terminate_C _)
      -> False;
    (Sec_Messages.Terminate_C _, _) -> False;
  });

check_leak_msg ::
  forall a b c d e f g h.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Arith.Nat ->
                              Arith.Nat ->
                                Interaction_Trees.Itree
                                  (Sec_Messages.Chan a b c d e f g) h ->
                                  Sec_Messages.Dmsg a b c d e f g ->
                                    Set.Set [Sec_Messages.Chan a b c d e f g];
check_leak_msg n mx p m =
  checks n mx p
    (any (\ a -> (case a of {
                   Sec_Messages.Env_C _ -> False;
                   Sec_Messages.Send_C _ -> False;
                   Sec_Messages.Cjam_C _ -> False;
                   Sec_Messages.Cdejam_C _ -> False;
                   Sec_Messages.Recv_C _ -> False;
                   Sec_Messages.Leak_C ma -> Sec_Messages.equal_dmsg ma m;
                   Sec_Messages.Sig_C _ -> False;
                   Sec_Messages.Terminate_C _ -> False;
                 })));

check_terminate ::
  forall a b c d e f g h.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Arith.Nat ->
                              Arith.Nat ->
                                Interaction_Trees.Itree
                                  (Sec_Messages.Chan a b c d e f g) h ->
                                  Set.Set [Sec_Messages.Chan a b c d e f g];
check_terminate n mx p = checks n mx p (any is_terminate);

check_auth_violation ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat ->
                  Interaction_Trees.Itree a b ->
                    (a -> a -> Bool) -> (a -> Bool) -> Set.Set [a];
check_auth_violation n mx p rel re =
  checks n mx p
    (\ tr ->
      not (null tr) &&
        re (List.last tr) && not (any (rel (List.last tr)) (List.butlast tr)));

check_authenticity ::
  forall a b c d e f g h.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Arith.Nat ->
                              Arith.Nat ->
                                Interaction_Trees.Itree
                                  (Sec_Messages.Chan a b c d e f g) h ->
                                  Set.Set [Sec_Messages.Chan a b c d e f g];
check_authenticity n mx p =
  check_auth_violation n mx p matches_start is_end_honest;

check_corr_violation ::
  forall a b.
    (Eq a) => Arith.Nat ->
                Arith.Nat ->
                  Interaction_Trees.Itree a b ->
                    (a -> Bool) -> (a -> Bool) -> Set.Set [a];
check_corr_violation n mx p mon re =
  checks n mx p
    (\ tr ->
      not (null tr) && re (List.last tr) && not (any mon (List.butlast tr)));

}
