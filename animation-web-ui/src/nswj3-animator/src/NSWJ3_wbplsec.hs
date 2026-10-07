{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  NSWJ3_wbplsec(msg3a, msg1a, msg1b, b_rcv_msgsa, bob_jamming_events, rcv_msg,
                 jamming, pBob_jamming, msg2b, responder, pBob, msg2a,
                 get_messages, a_rcv_msgs, alice_jamming_events, initiator,
                 pAlice, msg2ab, msg3ab, msgsab, a_I_sig, b_I_sig, msgsabj,
                 sublist, all_msgs, pLeakOnlyOnce, intruder_jamming_events,
                 jamming_intruder, b_rcv_msgs, allRecvMsgs,
                 allPossibleMsgsRecvByAgents, pIntruder0, pIntruder0a,
                 pIntruder1, pIntruder, a_snd_msgs, all_msgs_I, b_snd_msgs,
                 a_snd_events, b_snd_events, terminate_event, evt_msgs_recv,
                 b_recv_events, a_recv_events, evt_msgs_snd, events_A_B_I,
                 nSWJ3_active, nSWJ3_active_eve1, nSWJ3_active_eve2,
                 nSWJ3_active_eve3, nSWJ3_active_eve4)
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
import qualified Typerep;
import qualified HOL;
import qualified Product_Type;
import qualified ITree_Iteration;
import qualified Prisms;
import qualified List;
import qualified NSWJ3_config;
import qualified CSP_operators;
import qualified ITree_CSP;
import qualified Interaction_Trees;
import qualified FSNat;
import qualified Set;
import qualified Arith;
import qualified Sec_Messages;
import qualified Numeral_Type;
import qualified Type_Length;

msg3a ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1) ->
      Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
        (Numeral_Type.Bit0 Numeral_Type.Num1);
msg3a a nb = Sec_Messages.MWat nb (NSWJ3_config.mkbma a);

msg1a ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1);
msg1a a =
  Sec_Messages.MWat
    (Sec_Messages.MPair
      (Sec_Messages.MNon
        (Interaction_Trees.pfun_app
          (Interaction_Trees.pfun_upd
            (Interaction_Trees.pfun_upd
              (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                (FSNat.Nmk Arith.zero_nat))
              (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
              (FSNat.Nmk Arith.one_nat))
            Sec_Messages.Intruder
            (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
          a))
      (Sec_Messages.MAg a))
    (NSWJ3_config.mkbma a);

msg1b ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
msg1b b = map msg1a (NSWJ3_config.allOtherAgents b);

b_rcv_msgsa ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
b_rcv_msgsa b nb =
  let {
    asa = List.removeAll b
            [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
              Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
              Sec_Messages.Intruder];
  } in msg1b b ++ map (\ a -> msg3a a (Sec_Messages.MNon nb)) asa;

bob_jamming_events ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
bob_jamming_events b nb =
  concatMap
    (\ m ->
      map (\ ba -> Sec_Messages.Cjam_C (Sec_Messages.MJam m ba))
        [NSWJ3_config.mkbma b, Sec_Messages.MBitm Sec_Messages.Null])
    (b_rcv_msgsa b nb);

rcv_msg ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
      [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
             Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
               (Numeral_Type.Bit0 Numeral_Type.Num1))))];
rcv_msg a ms =
  concatMap
    (\ m ->
      map (\ b -> (b, (Sec_Messages.Intruder, (a, m))))
        (NSWJ3_config.allOtherAgentsa a))
    ms;

jamming ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
      Bool ->
        Interaction_Trees.Itree
          (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
            (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
            (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
            (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
            Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
            (Numeral_Type.Bit0 Numeral_Type.Num1))
          ();
jamming a ms inrange =
  ITree_Iteration.iterate (\ _ -> True)
    (\ _ ->
      Interaction_Trees.bind_itree
        (ITree_CSP.inp_list_where Sec_Messages.recv (rcv_msg a ms)
          (\ _ -> True))
        (\ (_, (_, (aa, m))) ->
          ITree_CSP.outp Sec_Messages.cjam
            (Sec_Messages.MJam m
              (if inrange then NSWJ3_config.mkbma aa
                else Sec_Messages.MBitm Sec_Messages.Null))))
    ();

pBob_jamming ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      Interaction_Trees.Itree
        (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
          (Numeral_Type.Bit0 Numeral_Type.Num1))
        ();
pBob_jamming b nb = jamming b (b_rcv_msgsa b nb) True;

msg2b ::
  forall a b c d e.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e) => Sec_Messages.Dagent
                              (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                              FSNat.Fsnat a ->
                                FSNat.Fsnat a ->
                                  Sec_Messages.Dmsg b a c d e
                                    (Numeral_Type.Bit1 Numeral_Type.Num1)
                                    (Numeral_Type.Bit0 Numeral_Type.Num1);
msg2b b na nb =
  Sec_Messages.MWat
    (Sec_Messages.MPair (Sec_Messages.MNon na) (Sec_Messages.MNon nb))
    (NSWJ3_config.mkbma b);

responder ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      Interaction_Trees.Itree
        (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
          (Numeral_Type.Bit0 Numeral_Type.Num1))
        ();
responder b nb =
  Interaction_Trees.bind_itree
    (ITree_CSP.inp_list_where Sec_Messages.cjam
      (map (\ m -> Sec_Messages.MJam m (NSWJ3_config.mkbma b)) (msg1b b))
      (\ _ -> True))
    (\ m ->
      let {
        m1 = Sec_Messages.mwm (Sec_Messages.mjm m);
        a = Sec_Messages.ma (Sec_Messages.mc2 m1);
        na = Sec_Messages.mn (Sec_Messages.mc1 m1);
      } in Interaction_Trees.bind_itree
             (ITree_CSP.outp Sec_Messages.sig
               (Sec_Messages.ClaimSecret b nb (Set.Set [a])))
             (\ _ ->
               Interaction_Trees.bind_itree
                 (ITree_CSP.outp Sec_Messages.sig
                   (Sec_Messages.StartProt b a na nb))
                 (\ _ ->
                   Interaction_Trees.bind_itree
                     (ITree_CSP.outp Sec_Messages.send
                       (b, (Sec_Messages.Intruder, (a, msg2b b na nb))))
                     (\ _ ->
                       Interaction_Trees.bind_itree
                         (ITree_CSP.inp_list_where Sec_Messages.cjam
                           (map (\ ma ->
                                  Sec_Messages.MJam ma (NSWJ3_config.mkbma b))
                             [msg3a a (Sec_Messages.MNon nb)])
                           (\ _ -> True))
                         (\ _ ->
                           Interaction_Trees.bind_itree
                             (ITree_CSP.outp Sec_Messages.sig
                               (Sec_Messages.EndProt b a na nb))
                             (\ _ ->
                               ITree_CSP.outp Sec_Messages.terminate ()))))));

pBob ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
pBob =
  ITree_CSP.exception
    (CSP_operators.par_hidep
      (responder (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
        ((Interaction_Trees.pfun_app ::
           Interaction_Trees.Pfun
             (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
             (FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
             Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
               FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
          ((Interaction_Trees.pfun_upd ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))))
            ((Interaction_Trees.pfun_upd ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))))
              ((Interaction_Trees.pfun_upd ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))))
                Interaction_Trees.bot_pfun
                (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                (FSNat.Nmk Arith.zero_nat))
              (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
              (FSNat.Nmk Arith.one_nat))
            Sec_Messages.Intruder
            (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))))
      (bob_jamming_events (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
        ((Interaction_Trees.pfun_app ::
           Interaction_Trees.Pfun
             (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
             (FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
             Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
               FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
          ((Interaction_Trees.pfun_upd ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))))
            ((Interaction_Trees.pfun_upd ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))))
              ((Interaction_Trees.pfun_upd ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))))
                Interaction_Trees.bot_pfun
                (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                (FSNat.Nmk Arith.zero_nat))
              (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
              (FSNat.Nmk Arith.one_nat))
            Sec_Messages.Intruder
            (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))))
      (pBob_jamming (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
        ((Interaction_Trees.pfun_app ::
           Interaction_Trees.Pfun
             (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
             (FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
             Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
               FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
          ((Interaction_Trees.pfun_upd ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))))
            ((Interaction_Trees.pfun_upd ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))))
              ((Interaction_Trees.pfun_upd ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))))
                Interaction_Trees.bot_pfun
                (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                (FSNat.Nmk Arith.zero_nat))
              (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
              (FSNat.Nmk Arith.one_nat))
            Sec_Messages.Intruder
            (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)))))
    (Set.Set [Sec_Messages.Terminate_C ()]) ITree_CSP.skip;

msg2a ::
  forall a b c d.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c,
      Type_Length.Len d) => Sec_Messages.Dagent
                              (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                              [Sec_Messages.Dmsg a
                                 (Numeral_Type.Bit0
                                   (Numeral_Type.Bit0 Numeral_Type.Num1))
                                 b c d (Numeral_Type.Bit1 Numeral_Type.Num1)
                                 (Numeral_Type.Bit0 Numeral_Type.Num1)];
msg2a a =
  map (\ b ->
        Sec_Messages.MWat
          (Sec_Messages.MPair
            (Sec_Messages.MNon
              (Interaction_Trees.pfun_app
                (Interaction_Trees.pfun_upd
                  (Interaction_Trees.pfun_upd
                    (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                      (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                      (FSNat.Nmk Arith.zero_nat))
                    (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                    (FSNat.Nmk Arith.one_nat))
                  Sec_Messages.Intruder
                  (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                a))
            (Sec_Messages.MNon
              (Interaction_Trees.pfun_app
                (Interaction_Trees.pfun_upd
                  (Interaction_Trees.pfun_upd
                    (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                      (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                      (FSNat.Nmk Arith.zero_nat))
                    (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                    (FSNat.Nmk Arith.one_nat))
                  Sec_Messages.Intruder
                  (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                b)))
          (NSWJ3_config.mkbma b))
    (NSWJ3_config.allOtherAgents a);

get_messages ::
  [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
       (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
           (Numeral_Type.Bit0 Numeral_Type.Num1))))] ->
    [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
get_messages ms = List.remdups (map Sec_Messages.last4 ms);

a_rcv_msgs ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
       (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
             Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
             (Numeral_Type.Bit0 Numeral_Type.Num1))))];
a_rcv_msgs a = rcv_msg a (msg2a a);

alice_jamming_events ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
alice_jamming_events a na =
  concatMap
    (\ m ->
      map (\ b -> Sec_Messages.Cjam_C (Sec_Messages.MJam m b))
        [NSWJ3_config.mkbma (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)),
          Sec_Messages.MBitm Sec_Messages.Null])
    (get_messages (a_rcv_msgs a));

initiator ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      Interaction_Trees.Itree
        (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
          (Numeral_Type.Bit0 Numeral_Type.Num1))
        ();
initiator a na =
  Interaction_Trees.bind_itree
    (ITree_CSP.inp_list_where Sec_Messages.env
      (concatMap
        (\ c -> (if not (Sec_Messages.equal_dagent c a) then [(a, c)] else []))
        [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
          Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder])
      (\ _ -> True))
    (\ (_, b) ->
      Interaction_Trees.bind_itree
        (ITree_CSP.outp Sec_Messages.sig
          (Sec_Messages.ClaimSecret a na (Set.Set [b])))
        (\ _ ->
          Interaction_Trees.bind_itree
            (ITree_CSP.outp Sec_Messages.send
              (a, (Sec_Messages.Intruder, (b, msg1a a))))
            (\ _ ->
              Interaction_Trees.bind_itree
                (ITree_CSP.inp_list_where Sec_Messages.cjam
                  (map (\ m -> Sec_Messages.MJam m (NSWJ3_config.mkbma a))
                    (msg2a a))
                  (\ _ -> True))
                (\ m ->
                  let {
                    m2 = Sec_Messages.mwm (Sec_Messages.mjm m);
                    nb = Sec_Messages.mn (Sec_Messages.mc2 m2);
                  } in Interaction_Trees.bind_itree
                         (ITree_CSP.outp Sec_Messages.sig
                           (Sec_Messages.StartProt a b na nb))
                         (\ _ ->
                           Interaction_Trees.bind_itree
                             (ITree_CSP.outp Sec_Messages.send
                               (a, (Sec_Messages.Intruder,
                                     (b, msg3a a (Sec_Messages.MNon nb)))))
                             (\ _ ->
                               Interaction_Trees.bind_itree
                                 (ITree_CSP.outp Sec_Messages.sig
                                   (Sec_Messages.EndProt a b na nb))
                                 (\ _ ->
                                   ITree_CSP.outp Sec_Messages.terminate
                                     ())))))));

pAlice ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
pAlice =
  ITree_CSP.exception
    (CSP_operators.par_hidep
      (initiator (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
        ((Interaction_Trees.pfun_app ::
           Interaction_Trees.Pfun
             (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
             (FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
             Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
               FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
          ((Interaction_Trees.pfun_upd ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))))
            ((Interaction_Trees.pfun_upd ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))))
              ((Interaction_Trees.pfun_upd ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))))
                Interaction_Trees.bot_pfun
                (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                (FSNat.Nmk Arith.zero_nat))
              (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
              (FSNat.Nmk Arith.one_nat))
            Sec_Messages.Intruder
            (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
          (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))))
      (alice_jamming_events (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
        ((Interaction_Trees.pfun_app ::
           Interaction_Trees.Pfun
             (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
             (FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
             Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
               FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
          ((Interaction_Trees.pfun_upd ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))))
            ((Interaction_Trees.pfun_upd ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))))
              ((Interaction_Trees.pfun_upd ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))))
                Interaction_Trees.bot_pfun
                (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                (FSNat.Nmk Arith.zero_nat))
              (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
              (FSNat.Nmk Arith.one_nat))
            Sec_Messages.Intruder
            (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
          (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))))
      (jamming (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
        (get_messages
          (a_rcv_msgs (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))))
        True))
    (Set.Set [Sec_Messages.Terminate_C ()]) ITree_CSP.skip;

msg2ab ::
  forall a b c d.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c,
      Type_Length.Len d) => Sec_Messages.Dagent
                              (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                              [Sec_Messages.Dmsg a
                                 (Numeral_Type.Bit0
                                   (Numeral_Type.Bit0 Numeral_Type.Num1))
                                 b c d (Numeral_Type.Bit1 Numeral_Type.Num1)
                                 (Numeral_Type.Bit0 Numeral_Type.Num1)];
msg2ab b =
  map (\ a ->
        msg2b b
          (Interaction_Trees.pfun_app
            (Interaction_Trees.pfun_upd
              (Interaction_Trees.pfun_upd
                (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                  (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                  (FSNat.Nmk Arith.zero_nat))
                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                (FSNat.Nmk Arith.one_nat))
              Sec_Messages.Intruder
              (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
            a)
          (Interaction_Trees.pfun_app
            (Interaction_Trees.pfun_upd
              (Interaction_Trees.pfun_upd
                (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                  (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                  (FSNat.Nmk Arith.zero_nat))
                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                (FSNat.Nmk Arith.one_nat))
              Sec_Messages.Intruder
              (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
            b))
    (NSWJ3_config.allOtherAgents b);

msg3ab ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
msg3ab a =
  concatMap
    (\ b ->
      (if not (Sec_Messages.equal_dagent a b)
        then [msg3a a
                (Sec_Messages.MNon
                  (Interaction_Trees.pfun_app
                    (Interaction_Trees.pfun_upd
                      (Interaction_Trees.pfun_upd
                        (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                          (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                          (FSNat.Nmk Arith.zero_nat))
                        (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                        (FSNat.Nmk Arith.one_nat))
                      Sec_Messages.Intruder
                      (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                    b))]
        else []))
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder];

msgsab ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
msgsab a = [msg1a a] ++ msg3ab a ++ msg2ab a;

a_I_sig ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
a_I_sig a na =
  concatMap
    (\ nb ->
      map (\ b ->
            Sec_Messages.Sig_C (Sec_Messages.ClaimSecret a nb (Set.Set [b])))
        (List.removeAll a
          [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
            Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
            Sec_Messages.Intruder]))
    [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
      FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))];

b_I_sig ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
b_I_sig b nb =
  concatMap
    (\ na ->
      map (\ a ->
            Sec_Messages.Sig_C (Sec_Messages.ClaimSecret b na (Set.Set [a])))
        (List.removeAll b
          [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
            Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
            Sec_Messages.Intruder]))
    [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
      FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))];

msgsabj ::
  NSWJ3_config.Deve ->
    [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
msgsabj eve =
  concatMap
    (\ (a, b) ->
      concatMap
        (\ m ->
          map (Sec_Messages.MJam m)
            [(if Interaction_Trees.pfun_app
                   (case eve of {
                     NSWJ3_config.Eve1 ->
                       Interaction_Trees.pfun_upd
                         (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                           (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)) True)
                         (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)) False;
                     NSWJ3_config.Eve2 ->
                       Interaction_Trees.pfun_upd
                         (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                           (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                           False)
                         (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)) True;
                     NSWJ3_config.Eve3 ->
                       Interaction_Trees.pfun_upd
                         (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                           (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)) True)
                         (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)) True;
                     NSWJ3_config.Eve4 ->
                       Interaction_Trees.pfun_upd
                         (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
                           (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                           False)
                         (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)) False;
                   })
                   b
               then NSWJ3_config.mkbma b
               else Sec_Messages.MBitm Sec_Messages.Null)])
        (msgsab a))
    NSWJ3_config.allCommsAgents;

sublist :: forall a. (Eq a) => [a] -> [a] -> [a];
sublist xs ys = filter (List.member ys) xs;

all_msgs ::
  [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
       (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
           (Numeral_Type.Bit0 Numeral_Type.Num1))))];
all_msgs =
  concatMap
    (\ a ->
      concatMap
        (\ b ->
          (if not (Sec_Messages.equal_dagent b a)
            then map (\ m -> (a, (Sec_Messages.Intruder, (b, m)))) (msgsab a)
            else []))
        [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
          Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder])
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder];

pLeakOnlyOnce ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => [Sec_Messages.Dmsg a b c d e f g] ->
                              Interaction_Trees.Itree
                                (Sec_Messages.Chan a b c d e f g) ();
pLeakOnlyOnce secrects =
  CSP_operators.indexed_inter_csp_list secrects
    (ITree_CSP.outp Sec_Messages.leak);

intruder_jamming_events ::
  NSWJ3_config.Deve ->
    [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
intruder_jamming_events eve = map Sec_Messages.Cjam_C (msgsabj eve);

jamming_intruder ::
  NSWJ3_config.Deve ->
    Interaction_Trees.Itree
      (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
        (Numeral_Type.Bit0 Numeral_Type.Num1))
      ();
jamming_intruder eve =
  ITree_Iteration.iterate (\ _ -> True)
    (\ _ ->
      Interaction_Trees.bind_itree
        (ITree_CSP.inp_list_where Sec_Messages.send
          (concatMap
            (\ (a, b) ->
              map (\ m -> (a, (Sec_Messages.Intruder, (b, m)))) (msgsab a))
            NSWJ3_config.allCommsAgents)
          (\ _ -> True))
        (\ (a, (_, (b, m))) ->
          ITree_CSP.gpar_csp
            (CSP_operators.outp_choice_from_list Sec_Messages.cjam
              (\ _ -> ITree_CSP.skip)
              (map (\ ba ->
                     Sec_Messages.MJam m
                       (if Interaction_Trees.pfun_app
                             (case eve of {
                               NSWJ3_config.Eve1 ->
                                 Interaction_Trees.pfun_upd
                                   (Interaction_Trees.pfun_upd
                                     Interaction_Trees.bot_pfun
                                     (Sec_Messages.Agent
                                       (FSNat.Nmk Arith.zero_nat))
                                     True)
                                   (Sec_Messages.Agent
                                     (FSNat.Nmk Arith.one_nat))
                                   False;
                               NSWJ3_config.Eve2 ->
                                 Interaction_Trees.pfun_upd
                                   (Interaction_Trees.pfun_upd
                                     Interaction_Trees.bot_pfun
                                     (Sec_Messages.Agent
                                       (FSNat.Nmk Arith.zero_nat))
                                     False)
                                   (Sec_Messages.Agent
                                     (FSNat.Nmk Arith.one_nat))
                                   True;
                               NSWJ3_config.Eve3 ->
                                 Interaction_Trees.pfun_upd
                                   (Interaction_Trees.pfun_upd
                                     Interaction_Trees.bot_pfun
                                     (Sec_Messages.Agent
                                       (FSNat.Nmk Arith.zero_nat))
                                     True)
                                   (Sec_Messages.Agent
                                     (FSNat.Nmk Arith.one_nat))
                                   True;
                               NSWJ3_config.Eve4 ->
                                 Interaction_Trees.pfun_upd
                                   (Interaction_Trees.pfun_upd
                                     Interaction_Trees.bot_pfun
                                     (Sec_Messages.Agent
                                       (FSNat.Nmk Arith.zero_nat))
                                     False)
                                   (Sec_Messages.Agent
                                     (FSNat.Nmk Arith.one_nat))
                                   False;
                             })
                             ba
                         then NSWJ3_config.mkbma ba
                         else Sec_Messages.MBitm Sec_Messages.Null))
                (NSWJ3_config.allOtherAgents a)))
            Set.bot_set
            (ITree_CSP.outp Sec_Messages.recv
              (a, (Sec_Messages.Intruder, (b, m))))))
    ();

b_rcv_msgs ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
             Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
               (Numeral_Type.Bit0 Numeral_Type.Num1))))];
b_rcv_msgs b nb = rcv_msg b (b_rcv_msgsa b nb);

allRecvMsgs ::
  [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
       (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
           (Numeral_Type.Bit0 Numeral_Type.Num1))))];
allRecvMsgs =
  a_rcv_msgs (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)) ++
    b_rcv_msgs (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
      ((Interaction_Trees.pfun_app ::
         Interaction_Trees.Pfun
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
           (FSNat.Fsnat
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
           Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
             FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
        ((Interaction_Trees.pfun_upd ::
           Interaction_Trees.Pfun
             (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
             (FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
             Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
               FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))))
          ((Interaction_Trees.pfun_upd ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))))
            ((Interaction_Trees.pfun_upd ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))))
              Interaction_Trees.bot_pfun
              (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
              (FSNat.Nmk Arith.zero_nat))
            (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
            (FSNat.Nmk Arith.one_nat))
          Sec_Messages.Intruder
          (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
        (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)));

allPossibleMsgsRecvByAgents ::
  [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) Numeral_Type.Num1
     (Numeral_Type.Bit1 Numeral_Type.Num1)
     (Numeral_Type.Bit0 Numeral_Type.Num1)];
allPossibleMsgsRecvByAgents = map Sec_Messages.last4 allRecvMsgs;

pIntruder0 ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
        [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
           (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
          NSWJ3_config.Deve ->
            Interaction_Trees.Itree
              (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
                (Numeral_Type.Bit0 Numeral_Type.Num1))
              ();
pIntruder0 i ni k s eve =
  Interaction_Trees.bind_itree (Interaction_Trees.Ret (True, (k, s)))
    (\ ret ->
      Interaction_Trees.bind_itree
        (ITree_Iteration.iterate (\ (con, (_, _)) -> con)
          (\ (_, (knows, sec)) ->
            ITree_CSP.extchoice_itree
              (Interaction_Trees.bind_itree
                (ITree_CSP.inp_list_where Sec_Messages.cjam (msgsabj eve)
                  (\ _ -> True))
                (\ m ->
                  Interaction_Trees.Ret
                    (True, (Sec_Messages.breakl (List.insert m knows), sec))))
              (ITree_CSP.extchoice_itree
                (Interaction_Trees.bind_itree
                  (ITree_CSP.inp_list_where Sec_Messages.recv
                    (sublist
                      (concatMap
                        (\ a ->
                          concatMap
                            (\ b ->
                              map (\ m -> (a, (i, (b, m))))
                                (Sec_Messages.filter_buildable
                                  allPossibleMsgsRecvByAgents (Set.Set knows)))
                            [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
                              Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)])
                        [i])
                      allRecvMsgs)
                    (\ _ -> True))
                  (\ _ -> Interaction_Trees.Ret (True, (knows, sec))))
                (ITree_CSP.extchoice_itree
                  (Interaction_Trees.bind_itree
                    (ITree_CSP.outp Sec_Messages.terminate ())
                    (\ _ -> Interaction_Trees.Ret (False, (knows, sec))))
                  (ITree_CSP.extchoice_itree
                    (Interaction_Trees.bind_itree
                      (ITree_CSP.inp_list_where Sec_Messages.sig
                        (concatMap
                          (\ a ->
                            concatMap
                              (\ n ->
                                concatMap
                                  (\ b ->
                                    (if not (Sec_Messages.equal_dagent a b)
                                      then [Sec_Messages.ClaimSecret a n
      (Set.Set [b])]
                                      else []))
                                  [Sec_Messages.Agent
                                     (FSNat.Nmk Arith.zero_nat),
                                    Sec_Messages.Agent
                                      (FSNat.Nmk Arith.one_nat),
                                    Sec_Messages.Intruder])
                              (List.removeAll ni
                                [FSNat.Nmk Arith.zero_nat,
                                  FSNat.Nmk Arith.one_nat,
                                  FSNat.Nmk
                                    (Arith.nat_of_integer (2 :: Integer))]))
                          [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
                            Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)])
                        (\ _ -> True))
                      (\ c ->
                        (if Set.member i (Sec_Messages.sp c)
                          then Interaction_Trees.Ret
                                 (True,
                                   (knows,
                                     List.removeAll
                                       (Sec_Messages.MNon (Sec_Messages.sn c))
                                       sec))
                          else Interaction_Trees.Ret (True, (knows, sec)))))
                    (let {
                       leaked = CSP_operators.list_inter knows sec;
                     } in Interaction_Trees.bind_itree
                            (ITree_CSP.guard (not (null leaked)))
                            (\ _ ->
                              Interaction_Trees.bind_itree
                                (ITree_CSP.inp_list_where Sec_Messages.leak
                                  leaked (\ _ -> True))
                                (\ _ ->
                                  Interaction_Trees.Ret
                                    (True, (knows, sec)))))))))
          ret)
        (\ _ -> Interaction_Trees.Ret ()));

pIntruder0a ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
        [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
           (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
          NSWJ3_config.Deve ->
            Interaction_Trees.Itree
              (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
                (Numeral_Type.Bit0 Numeral_Type.Num1))
              ();
pIntruder0a i ni k s eve =
  CSP_operators.par_hidep (pIntruder0 i ni k s eve)
    (intruder_jamming_events eve) (jamming_intruder eve);

pIntruder1 ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
        [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
           (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
          NSWJ3_config.Deve ->
            Interaction_Trees.Itree
              (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
                (Numeral_Type.Bit0 Numeral_Type.Num1))
              ();
pIntruder1 i ni k s eve =
  ITree_CSP.exception
    (ITree_CSP.gpar_csp (pIntruder0a i ni k s eve)
      (Set.Set (map Sec_Messages.Leak_C s)) (pLeakOnlyOnce s))
    (Set.Set [Sec_Messages.Terminate_C ()]) ITree_CSP.skip;

pIntruder ::
  NSWJ3_config.Deve ->
    Interaction_Trees.Itree
      (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
        (Numeral_Type.Bit0 Numeral_Type.Num1))
      ();
pIntruder eve =
  pIntruder1 Sec_Messages.Intruder
    ((Interaction_Trees.pfun_app ::
       Interaction_Trees.Pfun
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
         (FSNat.Fsnat
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
         Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
           FSNat.Fsnat
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
      ((Interaction_Trees.pfun_upd ::
         Interaction_Trees.Pfun
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
           (FSNat.Fsnat
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
           Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
             FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))))
        ((Interaction_Trees.pfun_upd ::
           Interaction_Trees.Pfun
             (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
             (FSNat.Fsnat
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
             Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
               FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))))
          ((Interaction_Trees.pfun_upd ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (FSNat.Fsnat
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))))
            Interaction_Trees.bot_pfun
            (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
            (FSNat.Nmk Arith.zero_nat))
          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
          (FSNat.Nmk Arith.one_nat))
        Sec_Messages.Intruder (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
      Sec_Messages.Intruder)
    NSWJ3_config.initKnows NSWJ3_config.allSecrets eve;

a_snd_msgs ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
       (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
             Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
             (Numeral_Type.Bit0 Numeral_Type.Num1))))];
a_snd_msgs a =
  let {
    bs = List.removeAll a
           [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
             Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
             Sec_Messages.Intruder];
  } in map (\ b -> (a, (Sec_Messages.Intruder, (b, msg1a a)))) bs ++
         map (\ b ->
               (a, (Sec_Messages.Intruder,
                     (b, msg3a a
                           (Sec_Messages.MNon
                             (Interaction_Trees.pfun_app
                               (Interaction_Trees.pfun_upd
                                 (Interaction_Trees.pfun_upd
                                   (Interaction_Trees.pfun_upd
                                     Interaction_Trees.bot_pfun
                                     (Sec_Messages.Agent
                                       (FSNat.Nmk Arith.zero_nat))
                                     (FSNat.Nmk Arith.zero_nat))
                                   (Sec_Messages.Agent
                                     (FSNat.Nmk Arith.one_nat))
                                   (FSNat.Nmk Arith.one_nat))
                                 Sec_Messages.Intruder
                                 (FSNat.Nmk
                                   (Arith.nat_of_integer (2 :: Integer))))
                               b))))))
           bs;

all_msgs_I ::
  [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
       (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
           (Numeral_Type.Bit0 Numeral_Type.Num1))))];
all_msgs_I =
  concatMap
    (\ a ->
      map (\ m -> (Sec_Messages.Intruder, (Sec_Messages.Intruder, (a, m))))
        (msgsab a))
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)];

b_snd_msgs ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
             Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
               (Numeral_Type.Bit0 Numeral_Type.Num1))))];
b_snd_msgs b nb =
  let {
    a = List.removeAll b
          [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
            Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
            Sec_Messages.Intruder];
  } in map (\ aa ->
             (b, (Sec_Messages.Intruder,
                   (aa, msg2b b
                          (Interaction_Trees.pfun_app
                            (Interaction_Trees.pfun_upd
                              (Interaction_Trees.pfun_upd
                                (Interaction_Trees.pfun_upd
                                  Interaction_Trees.bot_pfun
                                  (Sec_Messages.Agent
                                    (FSNat.Nmk Arith.zero_nat))
                                  (FSNat.Nmk Arith.zero_nat))
                                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                                (FSNat.Nmk Arith.one_nat))
                              Sec_Messages.Intruder
                              (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                            aa)
                          nb))))
         a;

a_snd_events ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
a_snd_events a = map Sec_Messages.Send_C (a_snd_msgs a);

b_snd_events ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
b_snd_events b nb = map Sec_Messages.Send_C (b_snd_msgs b nb);

terminate_event ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => [Sec_Messages.Chan a b c d e f g];
terminate_event = [Sec_Messages.Terminate_C ()];

evt_msgs_recv ::
  [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) Numeral_Type.Num1
     (Numeral_Type.Bit1 Numeral_Type.Num1)
     (Numeral_Type.Bit0 Numeral_Type.Num1)];
evt_msgs_recv = map Sec_Messages.Recv_C (List.union all_msgs all_msgs_I);

b_recv_events ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
b_recv_events b nb = map Sec_Messages.Recv_C (b_rcv_msgs b nb);

a_recv_events ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
a_recv_events a = map Sec_Messages.Recv_C (a_rcv_msgs a);

evt_msgs_snd ::
  [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) Numeral_Type.Num1
     (Numeral_Type.Bit1 Numeral_Type.Num1)
     (Numeral_Type.Bit0 Numeral_Type.Num1)];
evt_msgs_snd = map Sec_Messages.Send_C (List.union all_msgs all_msgs_I);

events_A_B_I ::
  Set.Set
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1));
events_A_B_I =
  Set.Set
    (List.remdups
      (a_snd_events (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)) ++
        a_recv_events (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)) ++
          b_snd_events (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
            ((Interaction_Trees.pfun_app ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (FSNat.Fsnat
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   FSNat.Fsnat
                     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
              ((Interaction_Trees.pfun_upd ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))))
                ((Interaction_Trees.pfun_upd ::
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                     Sec_Messages.Dagent
                       (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                       FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                         Interaction_Trees.Pfun
                           (Sec_Messages.Dagent
                             (Numeral_Type.Bit0 Numeral_Type.Num1))
                           (FSNat.Fsnat
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1))))
                  ((Interaction_Trees.pfun_upd ::
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                       Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                         FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                           Interaction_Trees.Pfun
                             (Sec_Messages.Dagent
                               (Numeral_Type.Bit0 Numeral_Type.Num1))
                             (FSNat.Fsnat
                               (Numeral_Type.Bit0
                                 (Numeral_Type.Bit0 Numeral_Type.Num1))))
                    Interaction_Trees.bot_pfun
                    (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                    (FSNat.Nmk Arith.zero_nat))
                  (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                  (FSNat.Nmk Arith.one_nat))
                Sec_Messages.Intruder
                (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
              (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))) ++
            b_recv_events (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
              ((Interaction_Trees.pfun_app ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (FSNat.Fsnat
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1)))
                ((Interaction_Trees.pfun_upd ::
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                     Sec_Messages.Dagent
                       (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                       FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                         Interaction_Trees.Pfun
                           (Sec_Messages.Dagent
                             (Numeral_Type.Bit0 Numeral_Type.Num1))
                           (FSNat.Fsnat
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1))))
                  ((Interaction_Trees.pfun_upd ::
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                       Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                         FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                           Interaction_Trees.Pfun
                             (Sec_Messages.Dagent
                               (Numeral_Type.Bit0 Numeral_Type.Num1))
                             (FSNat.Fsnat
                               (Numeral_Type.Bit0
                                 (Numeral_Type.Bit0 Numeral_Type.Num1))))
                    ((Interaction_Trees.pfun_upd ::
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                         Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                           FSNat.Fsnat
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                             Interaction_Trees.Pfun
                               (Sec_Messages.Dagent
                                 (Numeral_Type.Bit0 Numeral_Type.Num1))
                               (FSNat.Fsnat
                                 (Numeral_Type.Bit0
                                   (Numeral_Type.Bit0 Numeral_Type.Num1))))
                      Interaction_Trees.bot_pfun
                      (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                      (FSNat.Nmk Arith.zero_nat))
                    (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                    (FSNat.Nmk Arith.one_nat))
                  Sec_Messages.Intruder
                  (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))) ++
              a_I_sig (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                ((Interaction_Trees.pfun_app ::
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (FSNat.Fsnat
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                     Sec_Messages.Dagent
                       (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                       FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1)))
                  ((Interaction_Trees.pfun_upd ::
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (FSNat.Fsnat
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                       Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                         FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                           Interaction_Trees.Pfun
                             (Sec_Messages.Dagent
                               (Numeral_Type.Bit0 Numeral_Type.Num1))
                             (FSNat.Fsnat
                               (Numeral_Type.Bit0
                                 (Numeral_Type.Bit0 Numeral_Type.Num1))))
                    ((Interaction_Trees.pfun_upd ::
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                         Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                           FSNat.Fsnat
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                             Interaction_Trees.Pfun
                               (Sec_Messages.Dagent
                                 (Numeral_Type.Bit0 Numeral_Type.Num1))
                               (FSNat.Fsnat
                                 (Numeral_Type.Bit0
                                   (Numeral_Type.Bit0 Numeral_Type.Num1))))
                      ((Interaction_Trees.pfun_upd ::
                         Interaction_Trees.Pfun
                           (Sec_Messages.Dagent
                             (Numeral_Type.Bit0 Numeral_Type.Num1))
                           (FSNat.Fsnat
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                           Sec_Messages.Dagent
                             (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                             FSNat.Fsnat
                               (Numeral_Type.Bit0
                                 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                               Interaction_Trees.Pfun
                                 (Sec_Messages.Dagent
                                   (Numeral_Type.Bit0 Numeral_Type.Num1))
                                 (FSNat.Fsnat
                                   (Numeral_Type.Bit0
                                     (Numeral_Type.Bit0 Numeral_Type.Num1))))
                        Interaction_Trees.bot_pfun
                        (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                        (FSNat.Nmk Arith.zero_nat))
                      (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                      (FSNat.Nmk Arith.one_nat))
                    Sec_Messages.Intruder
                    (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                  (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))) ++
                terminate_event ++
                  b_I_sig (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                    ((Interaction_Trees.pfun_app ::
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (FSNat.Fsnat
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                         Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                           FSNat.Fsnat
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1)))
                      ((Interaction_Trees.pfun_upd ::
                         Interaction_Trees.Pfun
                           (Sec_Messages.Dagent
                             (Numeral_Type.Bit0 Numeral_Type.Num1))
                           (FSNat.Fsnat
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                           Sec_Messages.Dagent
                             (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                             FSNat.Fsnat
                               (Numeral_Type.Bit0
                                 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                               Interaction_Trees.Pfun
                                 (Sec_Messages.Dagent
                                   (Numeral_Type.Bit0 Numeral_Type.Num1))
                                 (FSNat.Fsnat
                                   (Numeral_Type.Bit0
                                     (Numeral_Type.Bit0 Numeral_Type.Num1))))
                        ((Interaction_Trees.pfun_upd ::
                           Interaction_Trees.Pfun
                             (Sec_Messages.Dagent
                               (Numeral_Type.Bit0 Numeral_Type.Num1))
                             (FSNat.Fsnat
                               (Numeral_Type.Bit0
                                 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                             Sec_Messages.Dagent
                               (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                               FSNat.Fsnat
                                 (Numeral_Type.Bit0
                                   (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                                 Interaction_Trees.Pfun
                                   (Sec_Messages.Dagent
                                     (Numeral_Type.Bit0 Numeral_Type.Num1))
                                   (FSNat.Fsnat
                                     (Numeral_Type.Bit0
                                       (Numeral_Type.Bit0 Numeral_Type.Num1))))
                          ((Interaction_Trees.pfun_upd ::
                             Interaction_Trees.Pfun
                               (Sec_Messages.Dagent
                                 (Numeral_Type.Bit0 Numeral_Type.Num1))
                               (FSNat.Fsnat
                                 (Numeral_Type.Bit0
                                   (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                               Sec_Messages.Dagent
                                 (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                                 FSNat.Fsnat
                                   (Numeral_Type.Bit0
                                     (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                                   Interaction_Trees.Pfun
                                     (Sec_Messages.Dagent
                                       (Numeral_Type.Bit0 Numeral_Type.Num1))
                                     (FSNat.Fsnat
                                       (Numeral_Type.Bit0
 (Numeral_Type.Bit0 Numeral_Type.Num1))))
                            Interaction_Trees.bot_pfun
                            (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                            (FSNat.Nmk Arith.zero_nat))
                          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                          (FSNat.Nmk Arith.one_nat))
                        Sec_Messages.Intruder
                        (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                      (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))) ++
                    evt_msgs_snd ++ evt_msgs_recv));

nSWJ3_active ::
  NSWJ3_config.Deve ->
    Interaction_Trees.Itree
      (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
        (Numeral_Type.Bit0 Numeral_Type.Num1))
      ();
nSWJ3_active eve =
  ITree_CSP.gpar_csp (ITree_CSP.gpar_csp pAlice (Set.Set terminate_event) pBob)
    events_A_B_I (pIntruder eve);

nSWJ3_active_eve1 ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
nSWJ3_active_eve1 =
  (if NSWJ3_config.equal_deve NSWJ3_config.Eve1 NSWJ3_config.Eve2
    then nSWJ3_active NSWJ3_config.Eve1 else nSWJ3_active NSWJ3_config.Eve1);

nSWJ3_active_eve2 ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
nSWJ3_active_eve2 =
  (if NSWJ3_config.equal_deve NSWJ3_config.Eve1 NSWJ3_config.Eve2
    then nSWJ3_active NSWJ3_config.Eve2 else nSWJ3_active NSWJ3_config.Eve2);

nSWJ3_active_eve3 ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
nSWJ3_active_eve3 =
  (if NSWJ3_config.equal_deve NSWJ3_config.Eve1 NSWJ3_config.Eve2
    then nSWJ3_active NSWJ3_config.Eve3 else nSWJ3_active NSWJ3_config.Eve3);

nSWJ3_active_eve4 ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
      (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
nSWJ3_active_eve4 =
  (if NSWJ3_config.equal_deve NSWJ3_config.Eve1 NSWJ3_config.Eve2
    then nSWJ3_active NSWJ3_config.Eve4 else nSWJ3_active NSWJ3_config.Eve4);

}
