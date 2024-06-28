{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  NSPK3(lResponder, lPBob, a_I_sig, b_I_sig, lInitiator, lPAlice, initKnows,
         allSecrets, pLeakOnlyOnce, lB_I_snd_msg, lA_I_snd_msg, lPIntruder0,
         lPIntruder1, lB_I_rcv_msg, lA_I_rcv_msg, rename_leak, rename_sig,
         rename_I_L, lPIntruder, terminate_event, lB_I_snd_event,
         lB_I_rcv_event, a_I_snd_msg, lA_I_snd_event, lA_I_rcv_event,
         lEvents_A_B_I, nSPKP_Lowe)
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
import qualified Product_Type;
import qualified ITree_CSP;
import qualified HOL;
import qualified Prisms;
import qualified List;
import qualified Set;
import qualified Interaction_Trees;
import qualified NSPK3_message;

lResponder ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce -> Interaction_Trees.Itree NSPK3_message.Chan ();
lResponder b nb =
  Interaction_Trees.bind_itree
    (ITree_CSP.inp_list_where NSPK3_message.recv
      (concatMap
        (\ a ->
          map (\ na ->
                (NSPK3_message.Intruder,
                  (b, NSPK3_message.MEnc
                        (NSPK3_message.MCmp (NSPK3_message.MNon na)
                          (NSPK3_message.MAg a))
                        (NSPK3_message.PK b))))
            (List.removeAll nb NSPK3_message.allNonces))
        (List.removeAll b NSPK3_message.allAgents))
      (\ _ -> True))
    (\ (_, (_, m)) ->
      let {
        a = NSPK3_message.ma (NSPK3_message.mc2 (NSPK3_message.mem m));
        na = NSPK3_message.mn (NSPK3_message.mc1 (NSPK3_message.mem m));
      } in Interaction_Trees.bind_itree
             (ITree_CSP.outp NSPK3_message.sig
               (NSPK3_message.ClaimSecret b nb (Set.Set [a])))
             (\ _ ->
               Interaction_Trees.bind_itree
                 (ITree_CSP.outp NSPK3_message.sig
                   (NSPK3_message.StartProt b a na nb))
                 (\ _ ->
                   Interaction_Trees.bind_itree
                     (ITree_CSP.outp NSPK3_message.send
                       (b, (NSPK3_message.Intruder,
                             NSPK3_message.MEnc
                               (NSPK3_message.MCmp (NSPK3_message.MNon na)
                                 (NSPK3_message.MCmp (NSPK3_message.MNon nb)
                                   (NSPK3_message.MAg b)))
                               (NSPK3_message.PK a))))
                     (\ _ ->
                       Interaction_Trees.bind_itree
                         (ITree_CSP.inp_list_where NSPK3_message.recv
                           [(NSPK3_message.Intruder,
                              (b, NSPK3_message.MEnc (NSPK3_message.MNon nb)
                                    (NSPK3_message.PK b)))]
                           (\ _ -> True))
                         (\ _ ->
                           Interaction_Trees.bind_itree
                             (ITree_CSP.outp NSPK3_message.sig
                               (NSPK3_message.EndProt b a na nb))
                             (\ _ ->
                               ITree_CSP.outp NSPK3_message.terminate ()))))));

lPBob :: Interaction_Trees.Itree NSPK3_message.Chan ();
lPBob = lResponder NSPK3_message.Bob (NSPK3_message.N NSPK3_message.Bob);

a_I_sig :: forall a. NSPK3_message.Dagent -> a -> [NSPK3_message.Chan];
a_I_sig a na =
  concatMap
    (\ nb ->
      map (\ b ->
            NSPK3_message.Sig_C (NSPK3_message.ClaimSecret a nb (Set.Set [b])))
        (List.removeAll a NSPK3_message.allAgents))
    NSPK3_message.allNonces;

b_I_sig :: forall a. NSPK3_message.Dagent -> a -> [NSPK3_message.Chan];
b_I_sig b nb =
  concatMap
    (\ na ->
      map (\ a ->
            NSPK3_message.Sig_C (NSPK3_message.ClaimSecret b na (Set.Set [a])))
        (List.removeAll b NSPK3_message.allAgents))
    NSPK3_message.allNonces;

lInitiator ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce -> Interaction_Trees.Itree NSPK3_message.Chan ();
lInitiator a na =
  Interaction_Trees.bind_itree
    (ITree_CSP.inp_list_where NSPK3_message.env
      (concatMap
        (\ c -> (if not (NSPK3_message.equal_dagent c a) then [(a, c)] else []))
        NSPK3_message.allAgents)
      (\ _ -> True))
    (\ (_, b) ->
      Interaction_Trees.bind_itree
        (ITree_CSP.outp NSPK3_message.sig
          (NSPK3_message.ClaimSecret a na (Set.Set [b])))
        (\ _ ->
          Interaction_Trees.bind_itree
            (ITree_CSP.outp NSPK3_message.send
              (a, (NSPK3_message.Intruder,
                    NSPK3_message.MEnc
                      (NSPK3_message.MCmp
                        (NSPK3_message.MNon (NSPK3_message.N a))
                        (NSPK3_message.MAg a))
                      (NSPK3_message.PK b))))
            (\ _ ->
              Interaction_Trees.bind_itree
                (ITree_CSP.inp_list_where NSPK3_message.recv
                  (map (\ nb ->
                         (NSPK3_message.Intruder,
                           (a, NSPK3_message.MEnc
                                 (NSPK3_message.MCmp (NSPK3_message.MNon na)
                                   (NSPK3_message.MCmp (NSPK3_message.MNon nb)
                                     (NSPK3_message.MAg b)))
                                 (NSPK3_message.PK a))))
                    (List.removeAll na NSPK3_message.allNonces))
                  (\ _ -> True))
                (\ (_, (_, m)) ->
                  let {
                    nb = NSPK3_message.mn
                           (NSPK3_message.mc1
                             (NSPK3_message.mc2 (NSPK3_message.mem m)));
                  } in Interaction_Trees.bind_itree
                         (ITree_CSP.outp NSPK3_message.sig
                           (NSPK3_message.StartProt a b na nb))
                         (\ _ ->
                           Interaction_Trees.bind_itree
                             (ITree_CSP.outp NSPK3_message.send
                               (a, (NSPK3_message.Intruder,
                                     NSPK3_message.MEnc (NSPK3_message.MNon nb)
                                       (NSPK3_message.PK b))))
                             (\ _ ->
                               Interaction_Trees.bind_itree
                                 (ITree_CSP.outp NSPK3_message.sig
                                   (NSPK3_message.EndProt a b na nb))
                                 (\ _ ->
                                   ITree_CSP.outp NSPK3_message.terminate
                                     ())))))));

lPAlice :: Interaction_Trees.Itree NSPK3_message.Chan ();
lPAlice = lInitiator NSPK3_message.Alice (NSPK3_message.N NSPK3_message.Alice);

initKnows :: [NSPK3_message.Dmsg];
initKnows =
  NSPK3_message.allAgentsLst ++
    NSPK3_message.allPKsLst ++
      [NSPK3_message.MNon (NSPK3_message.N NSPK3_message.Intruder),
        NSPK3_message.MKs (NSPK3_message.SK NSPK3_message.Intruder)];

allSecrets :: [NSPK3_message.Dmsg];
allSecrets =
  List.removeAll (NSPK3_message.MNon (NSPK3_message.N NSPK3_message.Intruder))
    NSPK3_message.allNoncesLst;

pLeakOnlyOnce ::
  [NSPK3_message.Dmsg] -> Interaction_Trees.Itree NSPK3_message.Chan ();
pLeakOnlyOnce secrects =
  CSP_operators.indexed_inter_csp_list secrects
    (ITree_CSP.outp NSPK3_message.leak);

lB_I_snd_msg ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce ->
      [(NSPK3_message.Dagent, (NSPK3_message.Dagent, NSPK3_message.Dmsg))];
lB_I_snd_msg b nb =
  let {
    a = List.removeAll NSPK3_message.Bob NSPK3_message.allAgents;
  } in concatMap
         (\ aa ->
           map (\ na ->
                 (b, (NSPK3_message.Intruder,
                       NSPK3_message.MEnc
                         (NSPK3_message.MCmp (NSPK3_message.MNon na)
                           (NSPK3_message.MCmp
                             (NSPK3_message.MNon (NSPK3_message.N b))
                             (NSPK3_message.MAg b)))
                         (NSPK3_message.PK aa))))
             (List.removeAll nb NSPK3_message.allNonces))
         a;

lA_I_snd_msg ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce ->
      [(NSPK3_message.Dagent, (NSPK3_message.Dagent, NSPK3_message.Dmsg))];
lA_I_snd_msg a na =
  let {
    bs = List.removeAll a NSPK3_message.allAgents;
  } in map (\ b ->
             (a, (NSPK3_message.Intruder,
                   NSPK3_message.MEnc
                     (NSPK3_message.MCmp
                       (NSPK3_message.MNon (NSPK3_message.N a))
                       (NSPK3_message.MAg a))
                     (NSPK3_message.PK b))))
         bs ++
         concatMap
           (\ b ->
             map (\ nb ->
                   (a, (NSPK3_message.Intruder,
                         NSPK3_message.MEnc (NSPK3_message.MNon nb)
                           (NSPK3_message.PK b))))
               (List.removeAll na NSPK3_message.allNonces))
           bs;

lPIntruder0 ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce ->
      [NSPK3_message.Dmsg] ->
        [NSPK3_message.Dmsg] -> Interaction_Trees.Itree NSPK3_message.Chan ();
lPIntruder0 i ni k s =
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
                      (ITree_CSP.inp_list_where NSPK3_message.hear
                        (lA_I_snd_msg NSPK3_message.Alice
                           (NSPK3_message.N NSPK3_message.Alice) ++
                          lB_I_snd_msg NSPK3_message.Bob
                            (NSPK3_message.N NSPK3_message.Bob))
                        (\ _ -> True))
                      (\ (_, (_, m)) ->
                        Interaction_Trees.Ret
                          (True,
                            (NSPK3_message.breakm (List.insert m knows), sec))))
                    (Interaction_Trees.bind_itree
                      (ITree_CSP.inp_list_where NSPK3_message.fake
                        (concatMap
                          (\ a ->
                            concatMap
                              (\ b ->
                                map (\ m -> (a, (b, m)))
                                  (NSPK3_message.build_n_2 knows))
                              (List.removeAll i NSPK3_message.allAgents))
                          [i])
                        (\ _ -> True))
                      (\ _ -> Interaction_Trees.Ret (True, (knows, sec)))))
                  (Interaction_Trees.bind_itree
                    (ITree_CSP.outp NSPK3_message.terminate ())
                    (\ _ -> Interaction_Trees.Ret (False, (knows, sec)))))
                (Interaction_Trees.bind_itree
                  (ITree_CSP.inp_list_where NSPK3_message.sig
                    (concatMap
                      (\ a ->
                        concatMap
                          (\ n ->
                            map (\ b ->
                                  NSPK3_message.ClaimSecret a n (Set.Set [b]))
                              NSPK3_message.allAgents)
                          (List.removeAll ni NSPK3_message.allNonces))
                      (List.removeAll i NSPK3_message.allAgents))
                    (\ _ -> True))
                  (\ c ->
                    (if Set.member i (NSPK3_message.sp c)
                      then Interaction_Trees.Ret
                             (True,
                               (knows,
                                 List.removeAll
                                   (NSPK3_message.MNon (NSPK3_message.sn c))
                                   sec))
                      else Interaction_Trees.Ret (True, (knows, sec))))))
              (let {
                 leaked = filter (List.member knows) sec;
               } in Interaction_Trees.bind_itree
                      (ITree_CSP.guard (not (null leaked)))
                      (\ _ ->
                        Interaction_Trees.bind_itree
                          (ITree_CSP.inp_list_where NSPK3_message.leak leaked
                            (\ _ -> True))
                          (\ _ -> Interaction_Trees.Ret (True, (knows, sec))))))
          ret)
        (\ _ -> Interaction_Trees.Ret ()));

lPIntruder1 ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce ->
      [NSPK3_message.Dmsg] ->
        [NSPK3_message.Dmsg] -> Interaction_Trees.Itree NSPK3_message.Chan ();
lPIntruder1 i ni k s =
  ITree_CSP.exception
    (ITree_CSP.gpar_csp (lPIntruder0 i ni k s)
      (Set.Set (map NSPK3_message.Leak_C s)) (pLeakOnlyOnce s))
    (Set.Set [NSPK3_message.Terminate_C ()]) ITree_CSP.skip;

lB_I_rcv_msg ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce ->
      [(NSPK3_message.Dagent, (NSPK3_message.Dagent, NSPK3_message.Dmsg))];
lB_I_rcv_msg b nb =
  let {
    asa = List.removeAll b NSPK3_message.allAgents;
  } in concatMap
         (\ a ->
           map (\ na ->
                 (NSPK3_message.Intruder,
                   (b, NSPK3_message.MEnc
                         (NSPK3_message.MCmp (NSPK3_message.MNon na)
                           (NSPK3_message.MAg a))
                         (NSPK3_message.PK b))))
             (List.removeAll nb NSPK3_message.allNonces))
         asa ++
         [(NSPK3_message.Intruder,
            (b, NSPK3_message.MEnc (NSPK3_message.MNon nb)
                  (NSPK3_message.PK b)))];

lA_I_rcv_msg ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce ->
      [(NSPK3_message.Dagent, (NSPK3_message.Dagent, NSPK3_message.Dmsg))];
lA_I_rcv_msg a na =
  concatMap
    (\ nb ->
      map (\ b ->
            (NSPK3_message.Intruder,
              (a, NSPK3_message.MEnc
                    (NSPK3_message.MCmp (NSPK3_message.MNon na)
                      (NSPK3_message.MCmp (NSPK3_message.MNon nb)
                        (NSPK3_message.MAg b)))
                    (NSPK3_message.PK a))))
        (List.removeAll a NSPK3_message.allAgents))
    (List.removeAll na NSPK3_message.allNonces);

rename_leak :: [(NSPK3_message.Chan, NSPK3_message.Chan)];
rename_leak =
  map (\ x -> (NSPK3_message.Leak_C x, NSPK3_message.Leak_C x)) allSecrets;

rename_sig ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce -> [(NSPK3_message.Chan, NSPK3_message.Chan)];
rename_sig i ni =
  concatMap
    (\ a ->
      concatMap
        (\ n ->
          concatMap
            (\ b ->
              (if not (NSPK3_message.equal_dagent a b)
                then [(NSPK3_message.Sig_C
                         (NSPK3_message.ClaimSecret a n (Set.Set [b])),
                        NSPK3_message.Sig_C
                          (NSPK3_message.ClaimSecret a n (Set.Set [b])))]
                else []))
            NSPK3_message.allAgents)
        (List.removeAll ni NSPK3_message.allNonces))
    (List.removeAll i NSPK3_message.allAgents);

rename_I_L :: [(NSPK3_message.Chan, NSPK3_message.Chan)];
rename_I_L =
  map (\ x -> (NSPK3_message.Hear_C x, NSPK3_message.Send_C x))
    (lA_I_snd_msg NSPK3_message.Alice (NSPK3_message.N NSPK3_message.Alice) ++
      lB_I_snd_msg NSPK3_message.Bob (NSPK3_message.N NSPK3_message.Bob)) ++
    map (\ x -> (NSPK3_message.Fake_C x, NSPK3_message.Recv_C x))
      (lA_I_rcv_msg NSPK3_message.Alice (NSPK3_message.N NSPK3_message.Alice) ++
        lB_I_rcv_msg NSPK3_message.Bob (NSPK3_message.N NSPK3_message.Bob)) ++
      [(NSPK3_message.Terminate_C (), NSPK3_message.Terminate_C ())] ++
        rename_leak ++
          rename_sig NSPK3_message.Intruder
            (NSPK3_message.N NSPK3_message.Intruder);

lPIntruder :: Interaction_Trees.Itree NSPK3_message.Chan ();
lPIntruder =
  ITree_CSP.rename (Set.Set rename_I_L)
    (lPIntruder1 NSPK3_message.Intruder (NSPK3_message.N NSPK3_message.Intruder)
      initKnows allSecrets);

terminate_event :: [NSPK3_message.Chan];
terminate_event = [NSPK3_message.Terminate_C ()];

lB_I_snd_event ::
  NSPK3_message.Dagent -> NSPK3_message.Dnonce -> [NSPK3_message.Chan];
lB_I_snd_event b nb = map NSPK3_message.Send_C (lB_I_snd_msg b nb);

lB_I_rcv_event ::
  NSPK3_message.Dagent -> NSPK3_message.Dnonce -> [NSPK3_message.Chan];
lB_I_rcv_event b nb = map NSPK3_message.Recv_C (lB_I_rcv_msg b nb);

a_I_snd_msg ::
  NSPK3_message.Dagent ->
    NSPK3_message.Dnonce ->
      [(NSPK3_message.Dagent, (NSPK3_message.Dagent, NSPK3_message.Dmsg))];
a_I_snd_msg a na =
  let {
    bs = List.removeAll a NSPK3_message.allAgents;
  } in map (\ b ->
             (a, (NSPK3_message.Intruder,
                   NSPK3_message.MEnc
                     (NSPK3_message.MCmp
                       (NSPK3_message.MNon (NSPK3_message.N a))
                       (NSPK3_message.MAg a))
                     (NSPK3_message.PK b))))
         bs ++
         concatMap
           (\ b ->
             map (\ nb ->
                   (a, (NSPK3_message.Intruder,
                         NSPK3_message.MEnc (NSPK3_message.MNon nb)
                           (NSPK3_message.PK b))))
               (List.removeAll na NSPK3_message.allNonces))
           bs;

lA_I_snd_event ::
  NSPK3_message.Dagent -> NSPK3_message.Dnonce -> [NSPK3_message.Chan];
lA_I_snd_event a na = map NSPK3_message.Send_C (a_I_snd_msg a na);

lA_I_rcv_event ::
  NSPK3_message.Dagent -> NSPK3_message.Dnonce -> [NSPK3_message.Chan];
lA_I_rcv_event a na = map NSPK3_message.Recv_C (lA_I_rcv_msg a na);

lEvents_A_B_I :: Set.Set NSPK3_message.Chan;
lEvents_A_B_I =
  Set.Set
    ((lA_I_snd_event NSPK3_message.Alice
        (NSPK3_message.N NSPK3_message.Alice) ++
       lA_I_rcv_event NSPK3_message.Alice
         (NSPK3_message.N NSPK3_message.Alice) ++
         a_I_sig NSPK3_message.Alice (NSPK3_message.N NSPK3_message.Alice)) ++
      terminate_event ++
        lB_I_snd_event NSPK3_message.Bob (NSPK3_message.N NSPK3_message.Bob) ++
          lB_I_rcv_event NSPK3_message.Bob
            (NSPK3_message.N NSPK3_message.Bob) ++
            b_I_sig NSPK3_message.Bob (NSPK3_message.N NSPK3_message.Bob));

nSPKP_Lowe :: Interaction_Trees.Itree NSPK3_message.Chan ();
nSPKP_Lowe =
  ITree_CSP.gpar_csp
    (ITree_CSP.gpar_csp lPAlice (Set.Set terminate_event) lPBob) lEvents_A_B_I
    lPIntruder;

}
