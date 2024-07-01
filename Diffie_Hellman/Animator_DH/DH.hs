{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  DH(pBob, pAlice, allSecrets, rename_leak, b_I_snd_msg, b_I_rcv_msg,
      a_I_snd_msg, a_I_rcv_msg, rename_I, initKnows, pLeakOnlyOnce, pIntruder0,
      pIntruder1, pIntruder, terminate_event, b_I_snd_event, b_I_rcv_event,
      a_I_snd_event, a_I_rcv_event, events_A_B_I, dH_Original)
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
import qualified HOL;
import qualified Set;
import qualified Product_Type;
import qualified ITree_CSP;
import qualified List;
import qualified Interaction_Trees;
import qualified Prisms;
import qualified DH_message;

pBob ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      DH_message.Dagent -> Interaction_Trees.Itree DH_message.Chan ();
pBob b nb a =
  Interaction_Trees.bind_itree
    (ITree_CSP.outp DH_message.send
      (b, (DH_message.Intruder, DH_message.MModExp DH_message.MExpg nb)))
    (\ _ ->
      Interaction_Trees.bind_itree
        (ITree_CSP.inp_list_where DH_message.recv
          (concatMap
            (\ na ->
              (if not (DH_message.equal_dnonce na
                        (DH_message.N DH_message.Server))
                then [(DH_message.Intruder,
                        (b, DH_message.MModExp DH_message.MExpg na))]
                else []))
            (List.removeAll nb DH_message.allNonces))
          (\ _ -> True))
        (\ (_, (_, m)) ->
          Interaction_Trees.bind_itree
            (ITree_CSP.inp_list_where DH_message.recv
              (concatMap
                (\ s ->
                  concatMap
                    (\ na ->
                      (if not (DH_message.equal_dnonce na
                                (DH_message.N DH_message.Server))
                        then [(DH_message.Intruder,
                                (b, DH_message.MSEnc s
                                      (DH_message.MModExp
(DH_message.MModExp DH_message.MExpg nb) na)))]
                        else []))
                    (List.removeAll nb DH_message.allNonces))
                DH_message.allPKsLst)
              (\ _ -> True))
            (\ (_, (_, ma)) ->
              (if List.member
                    (DH_message.breakm
                      [DH_message.MNon nb, DH_message.MAg b,
                        DH_message.MModExp DH_message.MExpg nb, m, ma])
                    (DH_message.MKp (DH_message.PK a))
                then ITree_CSP.outp DH_message.terminate ()
                else Interaction_Trees.Ret ()))));

pAlice ::
  DH_message.Dagent ->
    DH_message.Dnonce -> Interaction_Trees.Itree DH_message.Chan ();
pAlice a na =
  Interaction_Trees.bind_itree
    (ITree_CSP.outp DH_message.send
      (a, (DH_message.Intruder, DH_message.MModExp DH_message.MExpg na)))
    (\ _ ->
      Interaction_Trees.bind_itree
        (ITree_CSP.inp_list_where DH_message.recv
          (concatMap
            (\ nb ->
              (if not (DH_message.equal_dnonce nb
                        (DH_message.N DH_message.Server))
                then [(DH_message.Intruder,
                        (a, DH_message.MModExp DH_message.MExpg nb))]
                else []))
            (List.removeAll na DH_message.allNonces))
          (\ _ -> True))
        (\ (_, (_, m)) ->
          Interaction_Trees.bind_itree
            (ITree_CSP.outp DH_message.send
              (a, (DH_message.Intruder,
                    DH_message.MSEnc (DH_message.MKp (DH_message.PK a))
                      (DH_message.MModExp m na))))
            (\ _ -> ITree_CSP.outp DH_message.terminate ())));

allSecrets :: [DH_message.Dmsg];
allSecrets =
  List.removeAll (DH_message.MNon (DH_message.N DH_message.Intruder))
    DH_message.allNoncesLst ++
    List.removeAll (DH_message.MKp (DH_message.PK DH_message.Intruder))
      DH_message.allPKsLst;

rename_leak :: [(DH_message.Chan, DH_message.Chan)];
rename_leak =
  map (\ x -> (DH_message.Leak_C x, DH_message.Leak_C x)) allSecrets;

b_I_snd_msg ::
  forall a.
    a -> DH_message.Dnonce -> [(a, (DH_message.Dagent, DH_message.Dmsg))];
b_I_snd_msg b nb =
  [(b, (DH_message.Intruder, DH_message.MModExp DH_message.MExpg nb))];

b_I_rcv_msg ::
  forall a.
    a -> DH_message.Dnonce -> [(DH_message.Dagent, (a, DH_message.Dmsg))];
b_I_rcv_msg b nb =
  concatMap
    (\ na ->
      (if not (DH_message.equal_dnonce na (DH_message.N DH_message.Server))
        then [(DH_message.Intruder,
                (b, DH_message.MModExp DH_message.MExpg na))]
        else []))
    (List.removeAll nb DH_message.allNonces) ++
    concatMap
      (\ s ->
        concatMap
          (\ na ->
            (if not (DH_message.equal_dnonce na
                      (DH_message.N DH_message.Server))
              then [(DH_message.Intruder,
                      (b, DH_message.MSEnc s
                            (DH_message.MModExp
                              (DH_message.MModExp DH_message.MExpg nb) na)))]
              else []))
          (List.removeAll nb DH_message.allNonces))
      DH_message.allPKsLst;

a_I_snd_msg ::
  DH_message.Dagent ->
    DH_message.Dnonce ->
      [(DH_message.Dagent, (DH_message.Dagent, DH_message.Dmsg))];
a_I_snd_msg a na =
  [(a, (DH_message.Intruder, DH_message.MModExp DH_message.MExpg na))] ++
    concatMap
      (\ nb ->
        (if not (DH_message.equal_dnonce nb (DH_message.N DH_message.Server))
          then [(a, (DH_message.Intruder,
                      DH_message.MSEnc (DH_message.MKp (DH_message.PK a))
                        (DH_message.MModExp
                          (DH_message.MModExp DH_message.MExpg nb) na)))]
          else []))
      (List.removeAll na DH_message.allNonces);

a_I_rcv_msg ::
  forall a.
    a -> DH_message.Dnonce -> [(DH_message.Dagent, (a, DH_message.Dmsg))];
a_I_rcv_msg a na =
  concatMap
    (\ nb ->
      (if not (DH_message.equal_dnonce nb (DH_message.N DH_message.Server))
        then [(DH_message.Intruder,
                (a, DH_message.MModExp DH_message.MExpg nb))]
        else []))
    (List.removeAll na DH_message.allNonces);

rename_I :: [(DH_message.Chan, DH_message.Chan)];
rename_I =
  map (\ x -> (DH_message.Hear_C x, DH_message.Send_C x))
    (a_I_snd_msg DH_message.Alice (DH_message.N DH_message.Alice) ++
      b_I_snd_msg DH_message.Bob (DH_message.N DH_message.Bob)) ++
    map (\ x -> (DH_message.Fake_C x, DH_message.Recv_C x))
      (a_I_rcv_msg DH_message.Alice (DH_message.N DH_message.Alice) ++
        b_I_rcv_msg DH_message.Bob (DH_message.N DH_message.Bob)) ++
      [(DH_message.Terminate_C (), DH_message.Terminate_C ())] ++ rename_leak;

initKnows :: [DH_message.Dmsg];
initKnows =
  DH_message.allAgentsLst ++
    [DH_message.MExpg, DH_message.MNon (DH_message.N DH_message.Intruder),
      DH_message.MKs (DH_message.SK DH_message.Intruder),
      DH_message.MKp (DH_message.PK DH_message.Intruder)];

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
                                       (DH_message.build1_n_0 knows)
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

pIntruder :: Interaction_Trees.Itree DH_message.Chan ();
pIntruder =
  ITree_CSP.rename (Set.Set rename_I)
    (pIntruder1 DH_message.Intruder (DH_message.N DH_message.Intruder) initKnows
      allSecrets);

terminate_event :: [DH_message.Chan];
terminate_event = [DH_message.Terminate_C ()];

b_I_snd_event :: DH_message.Dagent -> DH_message.Dnonce -> [DH_message.Chan];
b_I_snd_event b nb = map DH_message.Send_C (b_I_snd_msg b nb);

b_I_rcv_event :: DH_message.Dagent -> DH_message.Dnonce -> [DH_message.Chan];
b_I_rcv_event b nb = map DH_message.Recv_C (b_I_rcv_msg b nb);

a_I_snd_event :: DH_message.Dagent -> DH_message.Dnonce -> [DH_message.Chan];
a_I_snd_event a na = map DH_message.Send_C (a_I_snd_msg a na);

a_I_rcv_event :: DH_message.Dagent -> DH_message.Dnonce -> [DH_message.Chan];
a_I_rcv_event a na = map DH_message.Recv_C (a_I_rcv_msg a na);

events_A_B_I :: Set.Set DH_message.Chan;
events_A_B_I =
  Set.Set
    ((a_I_snd_event DH_message.Alice (DH_message.N DH_message.Alice) ++
       a_I_rcv_event DH_message.Alice (DH_message.N DH_message.Alice)) ++
      (b_I_snd_event DH_message.Bob (DH_message.N DH_message.Bob) ++
        b_I_rcv_event DH_message.Bob (DH_message.N DH_message.Bob)) ++
        terminate_event);

dH_Original :: Interaction_Trees.Itree DH_message.Chan ();
dH_Original =
  ITree_CSP.gpar_csp
    (ITree_CSP.gpar_csp
      (pAlice DH_message.Alice (DH_message.N DH_message.Alice))
      (Set.Set terminate_event)
      (pBob DH_message.Bob (DH_message.N DH_message.Bob) DH_message.Alice))
    events_A_B_I pIntruder;

}
