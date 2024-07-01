{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  NSPK7(responder, pBob, terminate_event, i_snd_msg_sec, i_snd_event_sec,
         i_rcv_msg_sec, i_rcv_event_sec, b_I_snd_msg, b_I_snd_event,
         b_I_rcv_msg, b_I_rcv_event, a_I_snd_msg, a_I_snd_event, a_I_rcv_msg,
         a_I_rcv_event, b_I_sig, a_I_sig, events_A_B_S_I, b_I_snd_msg_sec,
         b_I_snd_event_sec, b_I_rcv_msg_sec, b_I_rcv_event_sec, a_I_snd_msg_sec,
         a_I_snd_event_sec, a_I_rcv_msg_sec, a_I_rcv_event_sec, events_A_B_S,
         pLeakOnlyOnce, get_PK_agents, get_pk_agents, pIntruder0, pIntruder1,
         pIntruder2, allSecrets, initKnows, rename_leak, rename_sig, rename_I,
         pIntruder, rename_Server, pServer0, pServer1, pServer, initiator,
         pAlice, nSPK7)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified CSP_operators;
import qualified Product_Type;
import qualified ITree_Iteration;
import qualified HOL;
import qualified Prisms;
import qualified List;
import qualified ITree_CSP;
import qualified Set;
import qualified Interaction_Trees;
import qualified NSPK7_message;

responder ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce -> Interaction_Trees.Itree NSPK7_message.Chan ();
responder b nb =
  Interaction_Trees.bind_itree
    (ITree_CSP.inp_list_where NSPK7_message.recv
      (concatMap
        (\ a ->
          (if not (NSPK7_message.equal_dagent a NSPK7_message.Server)
            then concatMap
                   (\ na ->
                     (if not (NSPK7_message.equal_dnonce na
                               (NSPK7_message.N NSPK7_message.Server))
                       then [(NSPK7_message.Intruder,
                               (b, NSPK7_message.MEnc
                                     (NSPK7_message.MCmp (NSPK7_message.MNon na)
                                       (NSPK7_message.MAg a))
                                     (NSPK7_message.PK b)))]
                       else []))
                   (List.removeAll nb NSPK7_message.allNonces)
            else []))
        (List.removeAll b NSPK7_message.allAgents))
      (\ _ -> True))
    (\ (_, (_, m)) ->
      let {
        a = NSPK7_message.ma (NSPK7_message.mc2 (NSPK7_message.mem m));
        na = NSPK7_message.mn (NSPK7_message.mc1 (NSPK7_message.mem m));
      } in Interaction_Trees.bind_itree
             (ITree_CSP.outp NSPK7_message.send_s
               (b, (NSPK7_message.Server,
                     NSPK7_message.MCmp (NSPK7_message.MAg b)
                       (NSPK7_message.MAg a))))
             (\ _ ->
               Interaction_Trees.bind_itree
                 (ITree_CSP.inp_list_where NSPK7_message.recv_s
                   (map (\ pka ->
                          (NSPK7_message.Server,
                            (b, NSPK7_message.MSig
                                  (NSPK7_message.MCmp pka (NSPK7_message.MAg a))
                                  (NSPK7_message.SK NSPK7_message.Server))))
                     NSPK7_message.allPKsLst)
                   (\ _ -> True))
                 (\ (_, (_, ma)) ->
                   let {
                     pka = NSPK7_message.mkp
                             (NSPK7_message.mc1 (NSPK7_message.msd ma));
                   } in Interaction_Trees.bind_itree
                          (ITree_CSP.outp NSPK7_message.sig
                            (NSPK7_message.ClaimSecret b nb (Set.Set [a])))
                          (\ _ ->
                            Interaction_Trees.bind_itree
                              (ITree_CSP.outp NSPK7_message.sig
                                (NSPK7_message.StartProt b a na nb))
                              (\ _ ->
                                Interaction_Trees.bind_itree
                                  (ITree_CSP.outp NSPK7_message.send
                                    (b, (NSPK7_message.Intruder,
  NSPK7_message.MEnc
    (NSPK7_message.MCmp (NSPK7_message.MNon na) (NSPK7_message.MNon nb)) pka)))
                                  (\ _ ->
                                    Interaction_Trees.bind_itree
                                      (ITree_CSP.inp_list_where
NSPK7_message.recv
[(NSPK7_message.Intruder,
   (b, NSPK7_message.MEnc (NSPK7_message.MNon nb) (NSPK7_message.PK b)))]
(\ _ -> True))
                                      (\ _ ->
Interaction_Trees.bind_itree
  (ITree_CSP.outp NSPK7_message.sig (NSPK7_message.EndProt b a na nb))
  (\ _ -> ITree_CSP.outp NSPK7_message.terminate ()))))))));

pBob :: Interaction_Trees.Itree NSPK7_message.Chan ();
pBob = responder NSPK7_message.Bob (NSPK7_message.N NSPK7_message.Bob);

terminate_event :: [NSPK7_message.Chan];
terminate_event = [NSPK7_message.Terminate_C ()];

i_snd_msg_sec ::
  NSPK7_message.Dagent ->
    [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
i_snd_msg_sec i =
  let {
    a = filter
          (\ a ->
            not (NSPK7_message.equal_dagent a i) &&
              not (NSPK7_message.equal_dagent a NSPK7_message.Server))
          NSPK7_message.allAgents;
  } in map (\ b ->
             (i, (NSPK7_message.Server,
                   NSPK7_message.MCmp (NSPK7_message.MAg i)
                     (NSPK7_message.MAg b))))
         a;

i_snd_event_sec :: NSPK7_message.Dagent -> [NSPK7_message.Chan];
i_snd_event_sec i = map NSPK7_message.Send_s_C (i_snd_msg_sec i);

i_rcv_msg_sec ::
  NSPK7_message.Dagent ->
    [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
i_rcv_msg_sec i =
  let {
    a = filter
          (\ a ->
            not (NSPK7_message.equal_dagent a i) &&
              not (NSPK7_message.equal_dagent a NSPK7_message.Server))
          NSPK7_message.allAgents;
  } in concatMap
         (\ b ->
           map (\ pk ->
                 (NSPK7_message.Server,
                   (i, NSPK7_message.MSig
                         (NSPK7_message.MCmp pk (NSPK7_message.MAg b))
                         (NSPK7_message.SK NSPK7_message.Server))))
             NSPK7_message.allPKsLst)
         a;

i_rcv_event_sec :: NSPK7_message.Dagent -> [NSPK7_message.Chan];
i_rcv_event_sec i = map NSPK7_message.Recv_s_C (i_rcv_msg_sec i);

b_I_snd_msg ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce ->
      [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
b_I_snd_msg b nb =
  let {
    a = filter
          (\ a ->
            not (NSPK7_message.equal_dagent a b) &&
              not (NSPK7_message.equal_dagent a NSPK7_message.Server))
          NSPK7_message.allAgents;
  } in concatMap
         (\ aa ->
           List.map_filter
             (\ x ->
               (if not (NSPK7_message.equal_dnonce x nb) &&
                     not (NSPK7_message.equal_dnonce x
                           (NSPK7_message.N NSPK7_message.Server))
                 then Just (b, (NSPK7_message.Intruder,
                                 NSPK7_message.MEnc
                                   (NSPK7_message.MCmp (NSPK7_message.MNon x)
                                     (NSPK7_message.MNon (NSPK7_message.N b)))
                                   (NSPK7_message.PK aa)))
                 else Nothing))
             NSPK7_message.allNonces)
         a;

b_I_snd_event ::
  NSPK7_message.Dagent -> NSPK7_message.Dnonce -> [NSPK7_message.Chan];
b_I_snd_event b nb = map NSPK7_message.Send_C (b_I_snd_msg b nb);

b_I_rcv_msg ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce ->
      [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
b_I_rcv_msg b nb =
  let {
    asa = filter
            (\ a ->
              not (NSPK7_message.equal_dagent a b) &&
                not (NSPK7_message.equal_dagent a NSPK7_message.Server))
            NSPK7_message.allAgents;
  } in concatMap
         (\ a ->
           List.map_filter
             (\ x ->
               (if not (NSPK7_message.equal_dnonce x nb) &&
                     not (NSPK7_message.equal_dnonce x
                           (NSPK7_message.N NSPK7_message.Server))
                 then Just (NSPK7_message.Intruder,
                             (b, NSPK7_message.MEnc
                                   (NSPK7_message.MCmp (NSPK7_message.MNon x)
                                     (NSPK7_message.MAg a))
                                   (NSPK7_message.PK b)))
                 else Nothing))
             NSPK7_message.allNonces)
         asa ++
         [(NSPK7_message.Intruder,
            (b, NSPK7_message.MEnc (NSPK7_message.MNon nb)
                  (NSPK7_message.PK b)))];

b_I_rcv_event ::
  NSPK7_message.Dagent -> NSPK7_message.Dnonce -> [NSPK7_message.Chan];
b_I_rcv_event b nb = map NSPK7_message.Recv_C (b_I_rcv_msg b nb);

a_I_snd_msg ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce ->
      [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
a_I_snd_msg a na =
  let {
    bs = filter
           (\ aa ->
             not (NSPK7_message.equal_dagent aa a) &&
               not (NSPK7_message.equal_dagent aa NSPK7_message.Server))
           NSPK7_message.allAgents;
  } in map (\ b ->
             (a, (NSPK7_message.Intruder,
                   NSPK7_message.MEnc
                     (NSPK7_message.MCmp
                       (NSPK7_message.MNon (NSPK7_message.N a))
                       (NSPK7_message.MAg a))
                     (NSPK7_message.PK b))))
         bs ++
         concatMap
           (\ b ->
             List.map_filter
               (\ x ->
                 (if not (NSPK7_message.equal_dnonce x na) &&
                       not (NSPK7_message.equal_dnonce x
                             (NSPK7_message.N NSPK7_message.Server))
                   then Just (a, (NSPK7_message.Intruder,
                                   NSPK7_message.MEnc (NSPK7_message.MNon x)
                                     (NSPK7_message.PK b)))
                   else Nothing))
               NSPK7_message.allNonces)
           bs;

a_I_snd_event ::
  NSPK7_message.Dagent -> NSPK7_message.Dnonce -> [NSPK7_message.Chan];
a_I_snd_event a na = map NSPK7_message.Send_C (a_I_snd_msg a na);

a_I_rcv_msg ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce ->
      [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
a_I_rcv_msg a na =
  List.map_filter
    (\ x ->
      (if not (NSPK7_message.equal_dnonce x na) &&
            not (NSPK7_message.equal_dnonce x
                  (NSPK7_message.N NSPK7_message.Server))
        then Just (NSPK7_message.Intruder,
                    (a, NSPK7_message.MEnc
                          (NSPK7_message.MCmp (NSPK7_message.MNon na)
                            (NSPK7_message.MNon x))
                          (NSPK7_message.PK a)))
        else Nothing))
    NSPK7_message.allNonces;

a_I_rcv_event ::
  NSPK7_message.Dagent -> NSPK7_message.Dnonce -> [NSPK7_message.Chan];
a_I_rcv_event a na = map NSPK7_message.Recv_C (a_I_rcv_msg a na);

b_I_sig :: forall a. NSPK7_message.Dagent -> a -> [NSPK7_message.Chan];
b_I_sig b nb =
  concatMap
    (\ na ->
      List.map_filter
        (\ x ->
          (if not (NSPK7_message.equal_dagent x b) &&
                not (NSPK7_message.equal_dagent x NSPK7_message.Server)
            then Just (NSPK7_message.Sig_C
                        (NSPK7_message.ClaimSecret b na (Set.Set [x])))
            else Nothing))
        NSPK7_message.allAgents)
    (List.removeAll (NSPK7_message.N NSPK7_message.Server)
      NSPK7_message.allNonces);

a_I_sig :: forall a. NSPK7_message.Dagent -> a -> [NSPK7_message.Chan];
a_I_sig a na =
  concatMap
    (\ nb ->
      List.map_filter
        (\ x ->
          (if not (NSPK7_message.equal_dagent x a) &&
                not (NSPK7_message.equal_dagent x NSPK7_message.Server)
            then Just (NSPK7_message.Sig_C
                        (NSPK7_message.ClaimSecret a nb (Set.Set [x])))
            else Nothing))
        NSPK7_message.allAgents)
    (List.removeAll (NSPK7_message.N NSPK7_message.Server)
      NSPK7_message.allNonces);

events_A_B_S_I :: Set.Set NSPK7_message.Chan;
events_A_B_S_I =
  Set.Set
    ((a_I_snd_event NSPK7_message.Alice (NSPK7_message.N NSPK7_message.Alice) ++
       a_I_rcv_event NSPK7_message.Alice
         (NSPK7_message.N NSPK7_message.Alice) ++
         a_I_sig NSPK7_message.Alice (NSPK7_message.N NSPK7_message.Alice)) ++
      (b_I_snd_event NSPK7_message.Bob (NSPK7_message.N NSPK7_message.Bob) ++
        b_I_rcv_event NSPK7_message.Bob (NSPK7_message.N NSPK7_message.Bob) ++
          b_I_sig NSPK7_message.Bob (NSPK7_message.N NSPK7_message.Bob)) ++
        terminate_event ++
          i_snd_event_sec NSPK7_message.Intruder ++
            i_rcv_event_sec NSPK7_message.Intruder);

b_I_snd_msg_sec ::
  NSPK7_message.Dagent ->
    [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
b_I_snd_msg_sec b =
  let {
    a = filter
          (\ a ->
            not (NSPK7_message.equal_dagent a b) &&
              not (NSPK7_message.equal_dagent a NSPK7_message.Server))
          NSPK7_message.allAgents;
  } in map (\ aa ->
             (b, (NSPK7_message.Server,
                   NSPK7_message.MCmp (NSPK7_message.MAg b)
                     (NSPK7_message.MAg aa))))
         a;

b_I_snd_event_sec :: NSPK7_message.Dagent -> [NSPK7_message.Chan];
b_I_snd_event_sec b = map NSPK7_message.Send_s_C (b_I_snd_msg_sec b);

b_I_rcv_msg_sec ::
  NSPK7_message.Dagent ->
    [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
b_I_rcv_msg_sec b =
  let {
    a = filter
          (\ a ->
            not (NSPK7_message.equal_dagent a b) &&
              not (NSPK7_message.equal_dagent a NSPK7_message.Server))
          NSPK7_message.allAgents;
  } in concatMap
         (\ aa ->
           map (\ pk ->
                 (NSPK7_message.Server,
                   (b, NSPK7_message.MSig
                         (NSPK7_message.MCmp pk (NSPK7_message.MAg aa))
                         (NSPK7_message.SK NSPK7_message.Server))))
             NSPK7_message.allPKsLst)
         a;

b_I_rcv_event_sec :: NSPK7_message.Dagent -> [NSPK7_message.Chan];
b_I_rcv_event_sec b = map NSPK7_message.Recv_s_C (b_I_rcv_msg_sec b);

a_I_snd_msg_sec ::
  NSPK7_message.Dagent ->
    [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
a_I_snd_msg_sec a =
  let {
    b = filter
          (\ aa ->
            not (NSPK7_message.equal_dagent aa a) &&
              not (NSPK7_message.equal_dagent aa NSPK7_message.Server))
          NSPK7_message.allAgents;
  } in map (\ ba ->
             (a, (NSPK7_message.Server,
                   NSPK7_message.MCmp (NSPK7_message.MAg a)
                     (NSPK7_message.MAg ba))))
         b;

a_I_snd_event_sec :: NSPK7_message.Dagent -> [NSPK7_message.Chan];
a_I_snd_event_sec a = map NSPK7_message.Send_s_C (a_I_snd_msg_sec a);

a_I_rcv_msg_sec ::
  NSPK7_message.Dagent ->
    [(NSPK7_message.Dagent, (NSPK7_message.Dagent, NSPK7_message.Dmsg))];
a_I_rcv_msg_sec a =
  let {
    b = filter
          (\ aa ->
            not (NSPK7_message.equal_dagent aa a) &&
              not (NSPK7_message.equal_dagent aa NSPK7_message.Server))
          NSPK7_message.allAgents;
  } in concatMap
         (\ ba ->
           map (\ pk ->
                 (NSPK7_message.Server,
                   (a, NSPK7_message.MSig
                         (NSPK7_message.MCmp pk (NSPK7_message.MAg ba))
                         (NSPK7_message.SK NSPK7_message.Server))))
             NSPK7_message.allPKsLst)
         b;

a_I_rcv_event_sec :: NSPK7_message.Dagent -> [NSPK7_message.Chan];
a_I_rcv_event_sec a = map NSPK7_message.Recv_s_C (a_I_rcv_msg_sec a);

events_A_B_S :: Set.Set NSPK7_message.Chan;
events_A_B_S =
  Set.Set
    (a_I_snd_event_sec NSPK7_message.Alice ++
      a_I_rcv_event_sec NSPK7_message.Alice ++
        terminate_event ++
          b_I_snd_event_sec NSPK7_message.Bob ++
            b_I_rcv_event_sec NSPK7_message.Bob);

pLeakOnlyOnce ::
  [NSPK7_message.Dmsg] -> Interaction_Trees.Itree NSPK7_message.Chan ();
pLeakOnlyOnce secrects =
  CSP_operators.indexed_inter_csp_list secrects
    (ITree_CSP.outp NSPK7_message.leak);

get_PK_agents ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dagent ->
      [NSPK7_message.Dmsg] ->
        Interaction_Trees.Itree NSPK7_message.Chan [NSPK7_message.Dmsg];
get_PK_agents i a knows =
  Interaction_Trees.bind_itree
    (ITree_CSP.outp NSPK7_message.send_s
      (i, (NSPK7_message.Server,
            NSPK7_message.MCmp (NSPK7_message.MAg i) (NSPK7_message.MAg a))))
    (\ _ ->
      Interaction_Trees.bind_itree
        (ITree_CSP.inp_list_where NSPK7_message.recv_s
          (map (\ pk ->
                 (NSPK7_message.Server,
                   (i, NSPK7_message.MSig
                         (NSPK7_message.MCmp pk (NSPK7_message.MAg a))
                         (NSPK7_message.SK NSPK7_message.Server))))
            NSPK7_message.allPKsLst)
          (\ _ -> True))
        (\ (_, (_, m)) ->
          Interaction_Trees.Ret
            (List.insert
              (NSPK7_message.MKp
                (NSPK7_message.mkp (NSPK7_message.mc1 (NSPK7_message.msd m))))
              knows)));

get_pk_agents ::
  NSPK7_message.Dagent ->
    [NSPK7_message.Dmsg] ->
      Interaction_Trees.Itree NSPK7_message.Chan [NSPK7_message.Dmsg];
get_pk_agents i =
  CSP_operators.indexed_seq_csp_list
    (filter
      (\ a ->
        not (NSPK7_message.equal_dagent a i) &&
          not (NSPK7_message.equal_dagent a NSPK7_message.Server))
      NSPK7_message.allAgents)
    (get_PK_agents i);

pIntruder0 ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce ->
      [NSPK7_message.Dmsg] ->
        [NSPK7_message.Dmsg] -> Interaction_Trees.Itree NSPK7_message.Chan ();
pIntruder0 i ni k s =
  Interaction_Trees.bind_itree (Interaction_Trees.Ret (True, (k, s)))
    (\ ret ->
      Interaction_Trees.bind_itree
        (ITree_Iteration.iterate (\ (con, (_, _)) -> con)
          (\ (_, (knows, sec)) ->
            ITree_CSP.extchoice_itree
              (ITree_CSP.extchoice_itree
                (ITree_CSP.extchoice_itree
                  (ITree_CSP.extchoice_itree
                    (Interaction_Trees.bind_itree
                      (ITree_CSP.inp_list_where NSPK7_message.hear
                        (a_I_snd_msg NSPK7_message.Alice
                           (NSPK7_message.N NSPK7_message.Alice) ++
                          b_I_snd_msg NSPK7_message.Bob
                            (NSPK7_message.N NSPK7_message.Bob))
                        (\ _ -> True))
                      (\ (_, (_, m)) ->
                        Interaction_Trees.Ret
                          (True,
                            (NSPK7_message.breakm (List.insert m knows), sec))))
                    (Interaction_Trees.bind_itree
                      (ITree_CSP.inp_list_where NSPK7_message.fake
                        (concatMap
                          (\ a ->
                            concatMap
                              (\ b ->
                                (if not (NSPK7_message.equal_dagent b
  NSPK7_message.Server)
                                  then map (\ m -> (a, (b, m)))
 (NSPK7_message.build_n_1 knows)
                                  else []))
                              (List.removeAll i NSPK7_message.allAgents))
                          [i])
                        (\ _ -> True))
                      (\ _ -> Interaction_Trees.Ret (True, (knows, sec)))))
                  (Interaction_Trees.bind_itree
                    (ITree_CSP.outp NSPK7_message.terminate ())
                    (\ _ -> Interaction_Trees.Ret (False, (knows, sec)))))
                (Interaction_Trees.bind_itree
                  (ITree_CSP.inp_list_where NSPK7_message.sig
                    (concat
                      (List.map_filter
                        (\ x ->
                          (if not (NSPK7_message.equal_dagent x i) &&
                                not (NSPK7_message.equal_dagent x
                                      NSPK7_message.Server)
                            then Just (concat
(List.map_filter
  (\ xa ->
    (if not (NSPK7_message.equal_dnonce xa ni) &&
          not (NSPK7_message.equal_dnonce xa
                (NSPK7_message.N NSPK7_message.Server))
      then Just (map (\ b -> NSPK7_message.ClaimSecret x xa (Set.Set [b]))
                  (List.removeAll NSPK7_message.Server NSPK7_message.allAgents))
      else Nothing))
  NSPK7_message.allNonces))
                            else Nothing))
                        NSPK7_message.allAgents))
                    (\ _ -> True))
                  (\ c ->
                    (if Set.member i (NSPK7_message.sp c)
                      then Interaction_Trees.Ret
                             (True,
                               (knows,
                                 List.removeAll
                                   (NSPK7_message.MNon (NSPK7_message.sn c))
                                   sec))
                      else Interaction_Trees.Ret (True, (knows, sec))))))
              (let {
                 leaked = filter (List.member knows) sec;
               } in Interaction_Trees.bind_itree
                      (ITree_CSP.guard (not (null leaked)))
                      (\ _ ->
                        Interaction_Trees.bind_itree
                          (ITree_CSP.inp_list_where NSPK7_message.leak leaked
                            (\ _ -> True))
                          (\ _ -> Interaction_Trees.Ret (True, (knows, sec))))))
          ret)
        (\ _ -> Interaction_Trees.Ret ()));

pIntruder1 ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce ->
      [NSPK7_message.Dmsg] ->
        [NSPK7_message.Dmsg] -> Interaction_Trees.Itree NSPK7_message.Chan ();
pIntruder1 i ni k s =
  Interaction_Trees.bind_itree (get_pk_agents i k)
    (\ knows -> pIntruder0 i ni knows s);

pIntruder2 ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce ->
      [NSPK7_message.Dmsg] ->
        [NSPK7_message.Dmsg] -> Interaction_Trees.Itree NSPK7_message.Chan ();
pIntruder2 i ni k s =
  ITree_CSP.exception
    (ITree_CSP.gpar_csp (pIntruder1 i ni k s)
      (Set.Set (map NSPK7_message.Leak_C s)) (pLeakOnlyOnce s))
    (Set.Set [NSPK7_message.Terminate_C ()]) ITree_CSP.skip;

allSecrets :: [NSPK7_message.Dmsg];
allSecrets =
  List.removeAll (NSPK7_message.MNon (NSPK7_message.N NSPK7_message.Intruder))
    NSPK7_message.allNoncesLst;

initKnows :: [NSPK7_message.Dmsg];
initKnows =
  NSPK7_message.allAgentsLst ++
    [NSPK7_message.MNon (NSPK7_message.N NSPK7_message.Intruder),
      NSPK7_message.MKs (NSPK7_message.SK NSPK7_message.Intruder)];

rename_leak :: [(NSPK7_message.Chan, NSPK7_message.Chan)];
rename_leak =
  map (\ x -> (NSPK7_message.Leak_C x, NSPK7_message.Leak_C x)) allSecrets;

rename_sig ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce -> [(NSPK7_message.Chan, NSPK7_message.Chan)];
rename_sig i ni =
  concatMap
    (\ a ->
      concatMap
        (\ n ->
          concatMap
            (\ b ->
              (if not (NSPK7_message.equal_dagent a b)
                then (if not (NSPK7_message.equal_dagent a NSPK7_message.Server)
                       then (if not (NSPK7_message.equal_dagent b
                                      NSPK7_message.Server)
                              then [(NSPK7_message.Sig_C
                                       (NSPK7_message.ClaimSecret a n
 (Set.Set [b])),
                                      NSPK7_message.Sig_C
(NSPK7_message.ClaimSecret a n (Set.Set [b])))]
                              else [])
                       else [])
                else []))
            NSPK7_message.allAgents)
        (List.removeAll ni NSPK7_message.allNonces))
    (List.removeAll i NSPK7_message.allAgents);

rename_I :: [(NSPK7_message.Chan, NSPK7_message.Chan)];
rename_I =
  map (\ x -> (NSPK7_message.Hear_C x, NSPK7_message.Send_C x))
    (a_I_snd_msg NSPK7_message.Alice (NSPK7_message.N NSPK7_message.Alice) ++
      b_I_snd_msg NSPK7_message.Bob (NSPK7_message.N NSPK7_message.Bob)) ++
    map (\ x -> (NSPK7_message.Fake_C x, NSPK7_message.Recv_C x))
      (a_I_rcv_msg NSPK7_message.Alice (NSPK7_message.N NSPK7_message.Alice) ++
        b_I_rcv_msg NSPK7_message.Bob (NSPK7_message.N NSPK7_message.Bob)) ++
      [(NSPK7_message.Terminate_C (), NSPK7_message.Terminate_C ())] ++
        rename_leak ++
          rename_sig NSPK7_message.Intruder
            (NSPK7_message.N NSPK7_message.Intruder) ++
            map (\ x -> (NSPK7_message.Send_s_C x, NSPK7_message.Send_s_C x))
              (i_snd_msg_sec NSPK7_message.Intruder) ++
              map (\ x -> (NSPK7_message.Recv_s_C x, NSPK7_message.Recv_s_C x))
                (i_rcv_msg_sec NSPK7_message.Intruder);

pIntruder :: Interaction_Trees.Itree NSPK7_message.Chan ();
pIntruder =
  ITree_CSP.rename (Set.Set rename_I)
    (pIntruder2 NSPK7_message.Intruder (NSPK7_message.N NSPK7_message.Intruder)
      initKnows allSecrets);

rename_Server :: [(NSPK7_message.Chan, NSPK7_message.Chan)];
rename_Server =
  map (\ x -> (NSPK7_message.Recv_s_C x, NSPK7_message.Send_s_C x))
    (a_I_snd_msg_sec NSPK7_message.Alice ++
      b_I_snd_msg_sec NSPK7_message.Bob ++
        i_snd_msg_sec NSPK7_message.Intruder) ++
    map (\ x -> (NSPK7_message.Send_s_C x, NSPK7_message.Recv_s_C x))
      (a_I_rcv_msg_sec NSPK7_message.Alice ++
        b_I_rcv_msg_sec NSPK7_message.Bob ++
          i_rcv_msg_sec NSPK7_message.Intruder) ++
      [(NSPK7_message.Terminate_C (), NSPK7_message.Terminate_C ())];

pServer0 :: Interaction_Trees.Itree NSPK7_message.Chan ();
pServer0 =
  ITree_Iteration.iterate (\ _ -> True)
    (\ _ ->
      Interaction_Trees.bind_itree
        (ITree_CSP.inp_list_where NSPK7_message.recv_s
          (concatMap
            (\ a ->
              concatMap
                (\ b ->
                  (if not (NSPK7_message.equal_dagent b a)
                    then [(a, (NSPK7_message.Server,
                                NSPK7_message.MCmp (NSPK7_message.MAg a)
                                  (NSPK7_message.MAg b)))]
                    else []))
                (List.removeAll NSPK7_message.Server NSPK7_message.allAgents))
            (List.removeAll NSPK7_message.Server NSPK7_message.allAgents))
          (\ _ -> True))
        (\ (a, (_, m)) ->
          let {
            b = NSPK7_message.ma (NSPK7_message.mc2 m);
          } in ITree_CSP.outp NSPK7_message.send_s
                 (NSPK7_message.Server,
                   (a, NSPK7_message.MSig
                         (NSPK7_message.MCmp
                           (NSPK7_message.MKp (NSPK7_message.PK b))
                           (NSPK7_message.MAg b))
                         (NSPK7_message.SK NSPK7_message.Server)))))
    ();

pServer1 :: Interaction_Trees.Itree NSPK7_message.Chan ();
pServer1 =
  ITree_CSP.interrupt pServer0 (ITree_CSP.outp NSPK7_message.terminate ());

pServer :: Interaction_Trees.Itree NSPK7_message.Chan ();
pServer = ITree_CSP.rename (Set.Set rename_Server) pServer1;

initiator ::
  NSPK7_message.Dagent ->
    NSPK7_message.Dnonce -> Interaction_Trees.Itree NSPK7_message.Chan ();
initiator a na =
  Interaction_Trees.bind_itree
    (ITree_CSP.inp_list_where NSPK7_message.env
      (concatMap
        (\ c ->
          (if not (NSPK7_message.equal_dagent c a)
            then (if not (NSPK7_message.equal_dagent c NSPK7_message.Server)
                   then [(a, c)] else [])
            else []))
        NSPK7_message.allAgents)
      (\ _ -> True))
    (\ (_, b) ->
      Interaction_Trees.bind_itree
        (ITree_CSP.outp NSPK7_message.send_s
          (a, (NSPK7_message.Server,
                NSPK7_message.MCmp (NSPK7_message.MAg a)
                  (NSPK7_message.MAg b))))
        (\ _ ->
          Interaction_Trees.bind_itree
            (ITree_CSP.inp_list_where NSPK7_message.recv_s
              (map (\ pk ->
                     (NSPK7_message.Server,
                       (a, NSPK7_message.MSig
                             (NSPK7_message.MCmp pk (NSPK7_message.MAg b))
                             (NSPK7_message.SK NSPK7_message.Server))))
                NSPK7_message.allPKsLst)
              (\ _ -> True))
            (\ (_, (_, m)) ->
              let {
                pkb = NSPK7_message.mkp
                        (NSPK7_message.mc1 (NSPK7_message.msd m));
              } in Interaction_Trees.bind_itree
                     (ITree_CSP.outp NSPK7_message.sig
                       (NSPK7_message.ClaimSecret a na (Set.Set [b])))
                     (\ _ ->
                       Interaction_Trees.bind_itree
                         (ITree_CSP.outp NSPK7_message.send
                           (a, (NSPK7_message.Intruder,
                                 NSPK7_message.MEnc
                                   (NSPK7_message.MCmp
                                     (NSPK7_message.MNon (NSPK7_message.N a))
                                     (NSPK7_message.MAg a))
                                   pkb)))
                         (\ _ ->
                           Interaction_Trees.bind_itree
                             (ITree_CSP.inp_list_where NSPK7_message.recv
                               (concatMap
                                 (\ nb ->
                                   (if not
 (NSPK7_message.equal_dnonce nb (NSPK7_message.N NSPK7_message.Server))
                                     then [(NSPK7_message.Intruder,
     (a, NSPK7_message.MEnc
           (NSPK7_message.MCmp (NSPK7_message.MNon na) (NSPK7_message.MNon nb))
           (NSPK7_message.PK a)))]
                                     else []))
                                 (List.removeAll na NSPK7_message.allNonces))
                               (\ _ -> True))
                             (\ (_, (_, ma)) ->
                               let {
                                 nb = NSPK7_message.mn
(NSPK7_message.mc2 (NSPK7_message.mem ma));
                               } in Interaction_Trees.bind_itree
                                      (ITree_CSP.outp NSPK7_message.sig
(NSPK7_message.StartProt a b na nb))
                                      (\ _ ->
Interaction_Trees.bind_itree
  (ITree_CSP.outp NSPK7_message.send
    (a, (NSPK7_message.Intruder,
          NSPK7_message.MEnc (NSPK7_message.MNon nb) pkb)))
  (\ _ ->
    Interaction_Trees.bind_itree
      (ITree_CSP.outp NSPK7_message.sig (NSPK7_message.EndProt a b na nb))
      (\ _ -> ITree_CSP.outp NSPK7_message.terminate ())))))))));

pAlice :: Interaction_Trees.Itree NSPK7_message.Chan ();
pAlice = initiator NSPK7_message.Alice (NSPK7_message.N NSPK7_message.Alice);

nSPK7 :: Interaction_Trees.Itree NSPK7_message.Chan ();
nSPK7 =
  ITree_CSP.gpar_csp
    (ITree_CSP.gpar_csp
      (ITree_CSP.gpar_csp pAlice (Set.Set terminate_event) pBob) events_A_B_S
      pServer)
    events_A_B_S_I pIntruder;

}
