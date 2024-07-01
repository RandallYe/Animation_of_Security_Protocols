{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  DH_sign(pBob, pAlice, terminate_event, b_I_snd_msg, b_I_snd_event,
           b_I_rcv_msg, b_I_rcv_event, a_I_snd_msg, a_I_snd_event, a_I_rcv_msg,
           a_I_rcv_event, events_A_B_I, pLeakOnlyOnce, pIntruder0, pIntruder1,
           allSecrets, initKnows, rename_leak, rename_I, pIntruder, dH_sign)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified CSP_operators;
import qualified ITree_Iteration;
import qualified Set;
import qualified Product_Type;
import qualified ITree_CSP;
import qualified List;
import qualified HOL;
import qualified Interaction_Trees;
import qualified Prisms;
import qualified DH_message;

pBob ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      DH_message.Dagent -> Interaction_Trees.Itree DH_message.Chan ();
pBob b nb a =
  Interaction_Trees.bind_itree
    (ITree_CSP.inp_list_where DH_message.recv
      (concatMap
        (\ na ->
          (if not (DH_message.equal_dnonce na (DH_message.N DH_message.Server))
            then concatMap
                   (\ skA ->
                     map (\ pkA ->
                           (DH_message.Intruder,
                             (b, DH_message.msort
                                   (DH_message.MCmp
                                     (DH_message.MSig
                                       (DH_message.MModExp DH_message.MExpg na)
                                       skA)
                                     pkA))))
                       (List.removeAll (DH_message.MKp (DH_message.PK b))
                         DH_message.allPKsLst))
                   (List.removeAll (DH_message.SK b) DH_message.allSKs)
            else []))
        (List.removeAll nb DH_message.allNonces))
      (\ _ -> True))
    (\ (_, (_, m)) ->
      let {
        pkA = DH_message.mc1 m;
        m1 = DH_message.mc2 m;
        g_na = DH_message.msd m1;
      } in (if DH_message.equal_dskey (DH_message.inv_p (DH_message.mkp pkA))
                 (DH_message.msk m1)
             then Interaction_Trees.bind_itree
                    (ITree_CSP.outp DH_message.send
                      (b, (DH_message.Intruder,
                            DH_message.MSig
                              (DH_message.MModExp DH_message.MExpg nb)
                              (DH_message.SK b))))
                    (\ _ ->
                      Interaction_Trees.bind_itree
                        (ITree_CSP.inp_list_where DH_message.recv
                          (concatMap
                            (\ s ->
                              (if not (DH_message.equal_dmsg s
(DH_message.MNon (DH_message.N DH_message.Server)))
                                then (if not
   (DH_message.equal_dmsg s (DH_message.MNon nb))
                                       then concatMap
      (\ na ->
        (if not (DH_message.equal_dnonce na (DH_message.N DH_message.Server))
          then [(DH_message.Intruder,
                  (b, DH_message.msort
                        (DH_message.MSEnc s
                          (DH_message.MModExp
                            (DH_message.MModExp DH_message.MExpg nb) na))))]
          else []))
      (List.removeAll nb DH_message.allNonces)
                                       else [])
                                else []))
                            DH_message.allNoncesLst)
                          (\ _ -> True))
                        (\ (_, (_, m2)) ->
                          (if List.member
                                (DH_message.breakm
                                  [DH_message.MNon nb, DH_message.MAg b,
                                    DH_message.MModExp DH_message.MExpg nb,
                                    g_na, m2])
                                (DH_message.MNon (DH_message.N a))
                            then ITree_CSP.outp DH_message.terminate ()
                            else Interaction_Trees.Ret ())))
             else Interaction_Trees.Ret ()));

pAlice ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      DH_message.Dagent -> Interaction_Trees.Itree DH_message.Chan ();
pAlice a na b =
  Interaction_Trees.bind_itree
    (ITree_CSP.outp DH_message.send
      (a, (DH_message.Intruder,
            DH_message.msort
              (DH_message.MCmp
                (DH_message.MSig (DH_message.MModExp DH_message.MExpg na)
                  (DH_message.SK a))
                (DH_message.MKp (DH_message.PK a))))))
    (\ _ ->
      Interaction_Trees.bind_itree
        (ITree_CSP.inp_list_where DH_message.recv
          (concatMap
            (\ nb ->
              (if not (DH_message.equal_dnonce nb
                        (DH_message.N DH_message.Server))
                then [(DH_message.Intruder,
                        (a, DH_message.MSig
                              (DH_message.MModExp DH_message.MExpg nb)
                              (DH_message.SK b)))]
                else []))
            (List.removeAll na DH_message.allNonces))
          (\ _ -> True))
        (\ (_, (_, m)) ->
          let {
            g_nb = DH_message.msd m;
          } in Interaction_Trees.bind_itree
                 (ITree_CSP.outp DH_message.send
                   (a, (DH_message.Intruder,
                         DH_message.MSEnc (DH_message.MNon (DH_message.N a))
                           (DH_message.MModExp g_nb na))))
                 (\ _ -> ITree_CSP.outp DH_message.terminate ())));

terminate_event :: [DH_message.Chan];
terminate_event = [DH_message.Terminate_C ()];

b_I_snd_msg ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      [(DH_message.Dagent, (DH_message.Dagent, DH_message.Dmsg))];
b_I_snd_msg b nb =
  [(b, (DH_message.Intruder,
         DH_message.MSig (DH_message.MModExp DH_message.MExpg nb)
           (DH_message.SK b)))];

b_I_snd_event :: DH_message.Dagent -> DH_message.Dnonce -> [DH_message.Chan];
b_I_snd_event b nb = map DH_message.Send_C (b_I_snd_msg b nb);

b_I_rcv_msg ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      [(DH_message.Dagent, (DH_message.Dagent, DH_message.Dmsg))];
b_I_rcv_msg b nb =
  concatMap
    (\ na ->
      (if not (DH_message.equal_dnonce na (DH_message.N DH_message.Server))
        then concatMap
               (\ skA ->
                 map (\ pkA ->
                       (DH_message.Intruder,
                         (b, DH_message.msort
                               (DH_message.MCmp
                                 (DH_message.MSig
                                   (DH_message.MModExp DH_message.MExpg na) skA)
                                 pkA))))
                   (List.removeAll (DH_message.MKp (DH_message.PK b))
                     DH_message.allPKsLst))
               (List.removeAll (DH_message.SK b) DH_message.allSKs)
        else []))
    (List.removeAll nb DH_message.allNonces) ++
    concatMap
      (\ s ->
        (if not (DH_message.equal_dmsg s
                  (DH_message.MNon (DH_message.N DH_message.Server)))
          then (if not (DH_message.equal_dmsg s (DH_message.MNon nb))
                 then concatMap
                        (\ na ->
                          (if not (DH_message.equal_dnonce na
                                    (DH_message.N DH_message.Server))
                            then [(DH_message.Intruder,
                                    (b, DH_message.msort
  (DH_message.MSEnc s
    (DH_message.MModExp (DH_message.MModExp DH_message.MExpg nb) na))))]
                            else []))
                        (List.removeAll nb DH_message.allNonces)
                 else [])
          else []))
      DH_message.allNoncesLst;

b_I_rcv_event :: DH_message.Dagent -> DH_message.Dnonce -> [DH_message.Chan];
b_I_rcv_event b nb = map DH_message.Recv_C (b_I_rcv_msg b nb);

a_I_snd_msg ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      [(DH_message.Dagent, (DH_message.Dagent, DH_message.Dmsg))];
a_I_snd_msg a na =
  [(a, (DH_message.Intruder,
         DH_message.msort
           (DH_message.MCmp
             (DH_message.MSig (DH_message.MModExp DH_message.MExpg na)
               (DH_message.SK a))
             (DH_message.MKp (DH_message.PK a)))))] ++
    concatMap
      (\ nb ->
        (if not (DH_message.equal_dnonce nb (DH_message.N DH_message.Server))
          then [(a, (DH_message.Intruder,
                      DH_message.MSEnc (DH_message.MNon (DH_message.N a))
                        (DH_message.MModExp
                          (DH_message.MModExp DH_message.MExpg nb) na)))]
          else []))
      (List.removeAll na DH_message.allNonces);

a_I_snd_event :: DH_message.Dagent -> DH_message.Dnonce -> [DH_message.Chan];
a_I_snd_event a na = map DH_message.Send_C (a_I_snd_msg a na);

a_I_rcv_msg ::
  forall a.
    a -> DH_message.Dnonce ->
           DH_message.Dagent -> [(DH_message.Dagent, (a, DH_message.Dmsg))];
a_I_rcv_msg a na b =
  concatMap
    (\ nb ->
      (if not (DH_message.equal_dnonce nb (DH_message.N DH_message.Server))
        then [(DH_message.Intruder,
                (a, DH_message.MSig (DH_message.MModExp DH_message.MExpg nb)
                      (DH_message.SK b)))]
        else []))
    (List.removeAll na DH_message.allNonces);

a_I_rcv_event ::
  DH_message.Dagent ->
    DH_message.Dnonce -> DH_message.Dagent -> [DH_message.Chan];
a_I_rcv_event a na b = map DH_message.Recv_C (a_I_rcv_msg a na b);

events_A_B_I :: Set.Set DH_message.Chan;
events_A_B_I =
  Set.Set
    ((a_I_snd_event DH_message.Alice (DH_message.N DH_message.Alice) ++
       a_I_rcv_event DH_message.Alice (DH_message.N DH_message.Alice)
         DH_message.Bob) ++
      (b_I_snd_event DH_message.Bob (DH_message.N DH_message.Bob) ++
        b_I_rcv_event DH_message.Bob (DH_message.N DH_message.Bob)) ++
        terminate_event);

pLeakOnlyOnce ::
  [DH_message.Dmsg] -> Interaction_Trees.Itree DH_message.Chan ();
pLeakOnlyOnce secrects =
  CSP_operators.indexed_inter_csp_list secrects
    (ITree_CSP.outp DH_message.leak);

pIntruder0 ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      [DH_message.Dmsg] ->
        [DH_message.Dmsg] -> Interaction_Trees.Itree DH_message.Chan ();
pIntruder0 i ni k s =
  Interaction_Trees.bind_itree (Interaction_Trees.Ret (True, (k, s)))
    (\ ret ->
      Interaction_Trees.bind_itree
        (ITree_Iteration.iterate (\ (con, (_, _)) -> con)
          (\ (_, (knows, sec)) ->
            ITree_CSP.extchoice_itree
              (ITree_CSP.extchoice_itree
                (ITree_CSP.extchoice_itree
                  (Interaction_Trees.bind_itree
                    (ITree_CSP.inp_list_where DH_message.hear
                      (a_I_snd_msg DH_message.Alice
                         (DH_message.N DH_message.Alice) ++
                        b_I_snd_msg DH_message.Bob
                          (DH_message.N DH_message.Bob))
                      (\ _ -> True))
                    (\ (_, (_, m)) ->
                      Interaction_Trees.Ret
                        (True, (DH_message.breakm (List.insert m knows), sec))))
                  (Interaction_Trees.bind_itree
                    (ITree_CSP.inp_list_where DH_message.fake
                      (concatMap
                        (\ a ->
                          concatMap
                            (\ b ->
                              (if not (DH_message.equal_dagent b
DH_message.Server)
                                then map (\ m -> (a, (b, m)))
                                       (DH_message.build1_n_2 knows)
                                else []))
                            (List.removeAll i DH_message.allAgents))
                        [i])
                      (\ _ -> True))
                    (\ _ -> Interaction_Trees.Ret (True, (knows, sec)))))
                (Interaction_Trees.bind_itree
                  (ITree_CSP.outp DH_message.terminate ())
                  (\ _ -> Interaction_Trees.Ret (False, (knows, sec)))))
              (let {
                 leaked = filter (List.member knows) sec;
               } in Interaction_Trees.bind_itree
                      (ITree_CSP.guard (not (null leaked)))
                      (\ _ ->
                        Interaction_Trees.bind_itree
                          (ITree_CSP.inp_list_where DH_message.leak leaked
                            (\ _ -> True))
                          (\ _ -> Interaction_Trees.Ret (True, (knows, sec))))))
          ret)
        (\ _ -> Interaction_Trees.Ret ()));

pIntruder1 ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      [DH_message.Dmsg] ->
        [DH_message.Dmsg] -> Interaction_Trees.Itree DH_message.Chan ();
pIntruder1 i ni k s =
  ITree_CSP.exception
    (ITree_CSP.gpar_csp (pIntruder0 i ni k s)
      (Set.Set (map DH_message.Leak_C s)) (pLeakOnlyOnce s))
    (Set.Set [DH_message.Terminate_C ()]) ITree_CSP.skip;

allSecrets :: [DH_message.Dmsg];
allSecrets =
  List.removeAll (DH_message.MNon (DH_message.N DH_message.Intruder))
    DH_message.allNoncesLst;

initKnows :: [DH_message.Dmsg];
initKnows =
  DH_message.allAgentsLst ++
    List.removeAll (DH_message.MKp (DH_message.PK DH_message.Server))
      DH_message.allPKsLst ++
      [DH_message.MExpg, DH_message.MNon (DH_message.N DH_message.Intruder),
        DH_message.MKs (DH_message.SK DH_message.Intruder)];

rename_leak :: [(DH_message.Chan, DH_message.Chan)];
rename_leak =
  map (\ x -> (DH_message.Leak_C x, DH_message.Leak_C x)) allSecrets;

rename_I :: [(DH_message.Chan, DH_message.Chan)];
rename_I =
  map (\ x -> (DH_message.Hear_C x, DH_message.Send_C x))
    (a_I_snd_msg DH_message.Alice (DH_message.N DH_message.Alice) ++
      b_I_snd_msg DH_message.Bob (DH_message.N DH_message.Bob)) ++
    map (\ x -> (DH_message.Fake_C x, DH_message.Recv_C x))
      (a_I_rcv_msg DH_message.Alice (DH_message.N DH_message.Alice)
         DH_message.Bob ++
        b_I_rcv_msg DH_message.Bob (DH_message.N DH_message.Bob)) ++
      [(DH_message.Terminate_C (), DH_message.Terminate_C ())] ++ rename_leak;

pIntruder :: Interaction_Trees.Itree DH_message.Chan ();
pIntruder =
  ITree_CSP.rename (Set.Set rename_I)
    (pIntruder1 DH_message.Intruder (DH_message.N DH_message.Intruder) initKnows
      allSecrets);

dH_sign :: Interaction_Trees.Itree DH_message.Chan ();
dH_sign =
  ITree_CSP.gpar_csp
    (ITree_CSP.gpar_csp
      (pAlice DH_message.Alice (DH_message.N DH_message.Alice) DH_message.Bob)
      (Set.Set terminate_event)
      (pBob DH_message.Bob (DH_message.N DH_message.Bob) DH_message.Alice))
    events_A_B_I pIntruder;

}
