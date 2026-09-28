{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  NSLPK3(lResponder, lPBob, terminate_event, lB_I_snd_msg, lB_I_snd_event,
          lB_I_rcv_msg, lB_I_rcv_event, lA_I_snd_msg, lA_I_snd_event,
          lA_I_rcv_msg, lA_I_rcv_event, b_I_sig, a_I_sig, lEvents_A_B_I,
          pLeakOnlyOnce, allPossibleMsgsRecvByAgents, lPIntruder0, lPIntruder1,
          rename_leak, rename_sig, rename_I_L, lPIntruder, lInitiator, lPAlice,
          nSLPK3)
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
import qualified NSPK3_config;
import qualified HOL;
import qualified Prisms;
import qualified Typerep;
import qualified List;
import qualified ITree_CSP;
import qualified Set;
import qualified Numeral_Type;
import qualified Interaction_Trees;
import qualified FSNat;
import qualified Arith;
import qualified Sec_Messages;
import qualified Type_Length;

lResponder ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      Interaction_Trees.Itree
        (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          Numeral_Type.Num1 Numeral_Type.Num1
          (Numeral_Type.Bit0 Numeral_Type.Num1))
        ();
lResponder b nb =
  Interaction_Trees.bind_itree
    (ITree_CSP.inp_list_where Sec_Messages.recv
      (concatMap
        (\ a ->
          map (\ na ->
                (Sec_Messages.Intruder,
                  (Sec_Messages.Intruder,
                    (b, Sec_Messages.MAEnc
                          (Sec_Messages.MPair (Sec_Messages.MNon na)
                            (Sec_Messages.MAg a))
                          (Sec_Messages.MK (NSPK3_config.pks b))))))
            (List.removeAll nb
              [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
                FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))]))
        (List.removeAll b
          [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
            Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
            Sec_Messages.Intruder]))
      (\ _ -> True))
    (\ (_, (_, (_, m))) ->
      let {
        a = Sec_Messages.ma (Sec_Messages.mc2 (Sec_Messages.mem m));
        na = Sec_Messages.mn (Sec_Messages.mc1 (Sec_Messages.mem m));
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
                       (b, (Sec_Messages.Intruder,
                             (a, Sec_Messages.MAEnc
                                   (Sec_Messages.MPair (Sec_Messages.MNon na)
                                     (Sec_Messages.MPair (Sec_Messages.MNon nb)
                                       (Sec_Messages.MAg b)))
                                   (Sec_Messages.MK (NSPK3_config.pks a))))))
                     (\ _ ->
                       Interaction_Trees.bind_itree
                         (ITree_CSP.inp_list_where Sec_Messages.recv
                           [(Sec_Messages.Intruder,
                              (Sec_Messages.Intruder,
                                (b, Sec_Messages.MAEnc (Sec_Messages.MNon nb)
                                      (Sec_Messages.MK (NSPK3_config.pks b)))))]
                           (\ _ -> True))
                         (\ _ ->
                           Interaction_Trees.bind_itree
                             (ITree_CSP.outp Sec_Messages.sig
                               (Sec_Messages.EndProt b a na nb))
                             (\ _ ->
                               ITree_CSP.outp Sec_Messages.terminate ()))))));

lPBob ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
lPBob =
  lResponder (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
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
      (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)));

terminate_event ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => [Sec_Messages.Chan a b c d e f g];
terminate_event = [Sec_Messages.Terminate_C ()];

lB_I_snd_msg ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
             Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               Numeral_Type.Num1 Numeral_Type.Num1
               (Numeral_Type.Bit0 Numeral_Type.Num1))))];
lB_I_snd_msg b nb =
  let {
    a = List.removeAll (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
          [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
            Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
            Sec_Messages.Intruder];
  } in concatMap
         (\ aa ->
           map (\ na ->
                 (b, (Sec_Messages.Intruder,
                       (aa, Sec_Messages.MAEnc
                              (Sec_Messages.MPair (Sec_Messages.MNon na)
                                (Sec_Messages.MPair (Sec_Messages.MNon nb)
                                  (Sec_Messages.MAg b)))
                              (Sec_Messages.MK (NSPK3_config.pks aa))))))
             (List.removeAll nb
               [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
                 FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))]))
         a;

lB_I_snd_event ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 Numeral_Type.Num1
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
lB_I_snd_event b nb = map Sec_Messages.Send_C (lB_I_snd_msg b nb);

lB_I_rcv_msg ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
             Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               Numeral_Type.Num1 Numeral_Type.Num1
               (Numeral_Type.Bit0 Numeral_Type.Num1))))];
lB_I_rcv_msg b nb =
  let {
    asa = List.removeAll b
            [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
              Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
              Sec_Messages.Intruder];
  } in concatMap
         (\ a ->
           map (\ na ->
                 (Sec_Messages.Intruder,
                   (Sec_Messages.Intruder,
                     (b, Sec_Messages.MAEnc
                           (Sec_Messages.MPair (Sec_Messages.MNon na)
                             (Sec_Messages.MAg a))
                           (Sec_Messages.MK (NSPK3_config.pks b))))))
             (List.removeAll nb
               [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
                 FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))]))
         asa ++
         [(Sec_Messages.Intruder,
            (Sec_Messages.Intruder,
              (b, Sec_Messages.MAEnc (Sec_Messages.MNon nb)
                    (Sec_Messages.MK (NSPK3_config.pks b)))))];

lB_I_rcv_event ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 Numeral_Type.Num1
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
lB_I_rcv_event b nb = map Sec_Messages.Recv_C (lB_I_rcv_msg b nb);

lA_I_snd_msg ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
             Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               Numeral_Type.Num1 Numeral_Type.Num1
               (Numeral_Type.Bit0 Numeral_Type.Num1))))];
lA_I_snd_msg a na =
  let {
    bs = List.removeAll a
           [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
             Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
             Sec_Messages.Intruder];
  } in map (\ b ->
             (a, (Sec_Messages.Intruder,
                   (b, Sec_Messages.MAEnc
                         (Sec_Messages.MPair (Sec_Messages.MNon na)
                           (Sec_Messages.MAg a))
                         (Sec_Messages.MK (NSPK3_config.pks b))))))
         bs ++
         concatMap
           (\ b ->
             map (\ nb ->
                   (a, (Sec_Messages.Intruder,
                         (b, Sec_Messages.MAEnc (Sec_Messages.MNon nb)
                               (Sec_Messages.MK (NSPK3_config.pks b))))))
               (List.removeAll na
                 [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
                   FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))]))
           bs;

lA_I_snd_event ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 Numeral_Type.Num1
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
lA_I_snd_event a na = map Sec_Messages.Send_C (lA_I_snd_msg a na);

lA_I_rcv_msg ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
             Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               Numeral_Type.Num1 Numeral_Type.Num1
               (Numeral_Type.Bit0 Numeral_Type.Num1))))];
lA_I_rcv_msg a na =
  concatMap
    (\ nb ->
      map (\ b ->
            (Sec_Messages.Intruder,
              (Sec_Messages.Intruder,
                (a, Sec_Messages.MAEnc
                      (Sec_Messages.MPair (Sec_Messages.MNon na)
                        (Sec_Messages.MPair (Sec_Messages.MNon nb)
                          (Sec_Messages.MAg b)))
                      (Sec_Messages.MK (NSPK3_config.pks a))))))
        (List.removeAll a
          [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
            Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
            Sec_Messages.Intruder]))
    (List.removeAll na
      [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
        FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))]);

lA_I_rcv_event ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 Numeral_Type.Num1
         (Numeral_Type.Bit0 Numeral_Type.Num1)];
lA_I_rcv_event a na = map Sec_Messages.Recv_C (lA_I_rcv_msg a na);

b_I_sig ::
  forall a b c d e f.
    (Type_Length.Len b, Typerep.Typerep b, Type_Length.Len c, Typerep.Typerep c,
      Type_Length.Len d, Typerep.Typerep d, Type_Length.Len e,
      Typerep.Typerep e, Type_Length.Len f,
      Typerep.Typerep f) => Sec_Messages.Dagent
                              (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                              a -> [Sec_Messages.Chan
                                      (Numeral_Type.Bit0 Numeral_Type.Num1)
                                      (Numeral_Type.Bit0
(Numeral_Type.Bit0 Numeral_Type.Num1))
                                      b c d e f];
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

a_I_sig ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 Numeral_Type.Num1
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

lEvents_A_B_I ::
  Set.Set
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 Numeral_Type.Num1
      (Numeral_Type.Bit0 Numeral_Type.Num1));
lEvents_A_B_I =
  Set.Set
    (List.remdups
      ((lA_I_snd_event (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
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
                  Interaction_Trees.bot_pfun
                  (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                  (FSNat.Nmk Arith.zero_nat))
                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                (FSNat.Nmk Arith.one_nat))
              Sec_Messages.Intruder
              (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
            (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))) ++
         lA_I_rcv_event (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
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
           a_I_sig (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
             ((Interaction_Trees.pfun_app ::
                Interaction_Trees.Pfun
                  (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                  (FSNat.Fsnat
                    (Numeral_Type.Bit0
                      (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
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
               (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)))) ++
        terminate_event ++
          lB_I_snd_event (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
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
            lB_I_rcv_event (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
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
              (b_I_sig ::
                Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                  FSNat.Fsnat
                    (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                    [Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
                       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                       Numeral_Type.Num1 Numeral_Type.Num1
                       (Numeral_Type.Bit0 Numeral_Type.Num1)])
                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
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
                  (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)))));

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

allPossibleMsgsRecvByAgents ::
  [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) Numeral_Type.Num1
     Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1)];
allPossibleMsgsRecvByAgents =
  map Sec_Messages.last4
    (lA_I_rcv_msg (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
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
                    (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
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
         (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))) ++
      lB_I_rcv_msg (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
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
          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))));

lPIntruder0 ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 Numeral_Type.Num1
         (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
        [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 Numeral_Type.Num1
           (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
          Interaction_Trees.Itree
            (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
              (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
              (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
              (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
              Numeral_Type.Num1 Numeral_Type.Num1
              (Numeral_Type.Bit0 Numeral_Type.Num1))
            ();
lPIntruder0 i ni k s =
  Interaction_Trees.bind_itree (Interaction_Trees.Ret (True, (k, s)))
    (\ ret ->
      Interaction_Trees.bind_itree
        (ITree_Iteration.iterate (\ (con, (_, _)) -> con)
          (\ (_, (knows, sec)) ->
            ITree_CSP.extchoice_itree
              (Interaction_Trees.bind_itree
                (ITree_CSP.inp_list_where Sec_Messages.send
                  (lA_I_snd_msg (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
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
(Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))))
                             Interaction_Trees.bot_pfun
                             (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                             (FSNat.Nmk Arith.zero_nat))
                           (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                           (FSNat.Nmk Arith.one_nat))
                         Sec_Messages.Intruder
                         (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                       (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))) ++
                    lB_I_snd_msg (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
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
 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))))
                              Interaction_Trees.bot_pfun
                              (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                              (FSNat.Nmk Arith.zero_nat))
                            (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                            (FSNat.Nmk Arith.one_nat))
                          Sec_Messages.Intruder
                          (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
                        (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))))
                  (\ _ -> True))
                (\ (_, (_, (_, m))) ->
                  Interaction_Trees.Ret
                    (True, (Sec_Messages.breakl (List.insert m knows), sec))))
              (ITree_CSP.extchoice_itree
                (Interaction_Trees.bind_itree
                  (ITree_CSP.inp_list_where Sec_Messages.recv
                    (concatMap
                      (\ a ->
                        concatMap
                          (\ b ->
                            map (\ m -> (a, (i, (b, m))))
                              (Sec_Messages.filter_buildable
                                allPossibleMsgsRecvByAgents (Set.Set knows)))
                          (List.removeAll i
                            [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
                              Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
                              Sec_Messages.Intruder]))
                      [i])
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
                                map (\ b ->
                                      Sec_Messages.ClaimSecret a n
(Set.Set [b]))
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
                          (List.removeAll i
                            [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
                              Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
                              Sec_Messages.Intruder]))
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
                       leaked = filter (List.member knows) sec;
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

lPIntruder1 ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
         Numeral_Type.Num1 Numeral_Type.Num1
         (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
        [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           Numeral_Type.Num1 Numeral_Type.Num1
           (Numeral_Type.Bit0 Numeral_Type.Num1)] ->
          Interaction_Trees.Itree
            (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
              (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
              (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
              (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
              Numeral_Type.Num1 Numeral_Type.Num1
              (Numeral_Type.Bit0 Numeral_Type.Num1))
            ();
lPIntruder1 i ni k s =
  ITree_CSP.exception
    (ITree_CSP.gpar_csp (lPIntruder0 i ni k s)
      (Set.Set (map Sec_Messages.Leak_C s)) (pLeakOnlyOnce s))
    (Set.Set [Sec_Messages.Terminate_C ()]) ITree_CSP.skip;

rename_leak ::
  [(Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1),
     Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 Numeral_Type.Num1
       (Numeral_Type.Bit0 Numeral_Type.Num1))];
rename_leak =
  map (\ x -> (Sec_Messages.Leak_C x, Sec_Messages.Leak_C x))
    NSPK3_config.allSecrets;

rename_sig ::
  forall a b c d e f g h i j.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g, Type_Length.Len h, Typerep.Typerep h,
      Type_Length.Len i, Typerep.Typerep i, Type_Length.Len j,
      Typerep.Typerep j) => Sec_Messages.Dagent
                              (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                              FSNat.Fsnat
                                (Numeral_Type.Bit0
                                  (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                                [(Sec_Messages.Chan
                                    (Numeral_Type.Bit0 Numeral_Type.Num1)
                                    (Numeral_Type.Bit0
                                      (Numeral_Type.Bit0 Numeral_Type.Num1))
                                    a b c d e,
                                   Sec_Messages.Chan
                                     (Numeral_Type.Bit0 Numeral_Type.Num1)
                                     (Numeral_Type.Bit0
                                       (Numeral_Type.Bit0 Numeral_Type.Num1))
                                     f g h i j)];
rename_sig i ni =
  concatMap
    (\ a ->
      concatMap
        (\ n ->
          concatMap
            (\ b ->
              (if not (Sec_Messages.equal_dagent a b)
                then [(Sec_Messages.Sig_C
                         (Sec_Messages.ClaimSecret a n (Set.Set [b])),
                        Sec_Messages.Sig_C
                          (Sec_Messages.ClaimSecret a n (Set.Set [b])))]
                else []))
            [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
              Sec_Messages.Agent (FSNat.Nmk Arith.one_nat),
              Sec_Messages.Intruder])
        (List.removeAll ni
          [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
            FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))]))
    (List.removeAll i
      [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
        Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder]);

rename_I_L ::
  [(Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1),
     Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 Numeral_Type.Num1
       (Numeral_Type.Bit0 Numeral_Type.Num1))];
rename_I_L =
  map (\ x -> (Sec_Messages.Send_C x, Sec_Messages.Send_C x))
    (lA_I_snd_msg (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
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
                    (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
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
         (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))) ++
      lB_I_snd_msg (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
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
          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)))) ++
    map (\ x -> (Sec_Messages.Recv_C x, Sec_Messages.Recv_C x))
      (lA_I_rcv_msg (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
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
           (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))) ++
        lB_I_rcv_msg (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
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
                  Interaction_Trees.bot_pfun
                  (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                  (FSNat.Nmk Arith.zero_nat))
                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                (FSNat.Nmk Arith.one_nat))
              Sec_Messages.Intruder
              (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))))
            (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)))) ++
      [(Sec_Messages.Terminate_C (), Sec_Messages.Terminate_C ())] ++
        rename_leak ++
          rename_sig Sec_Messages.Intruder
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
              Sec_Messages.Intruder);

lPIntruder ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
lPIntruder =
  ITree_CSP.rename (Set.Set rename_I_L)
    (lPIntruder1 Sec_Messages.Intruder
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
        Sec_Messages.Intruder)
      NSPK3_config.initKnows NSPK3_config.allSecrets);

lInitiator ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    FSNat.Fsnat (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      Interaction_Trees.Itree
        (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
          Numeral_Type.Num1 Numeral_Type.Num1
          (Numeral_Type.Bit0 Numeral_Type.Num1))
        ();
lInitiator a na =
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
              (a, (Sec_Messages.Intruder,
                    (b, Sec_Messages.MAEnc
                          (Sec_Messages.MPair (Sec_Messages.MNon na)
                            (Sec_Messages.MAg a))
                          (Sec_Messages.MK (NSPK3_config.pks b))))))
            (\ _ ->
              Interaction_Trees.bind_itree
                (ITree_CSP.inp_list_where Sec_Messages.recv
                  (map (\ nb ->
                         (Sec_Messages.Intruder,
                           (Sec_Messages.Intruder,
                             (a, Sec_Messages.MAEnc
                                   (Sec_Messages.MPair (Sec_Messages.MNon na)
                                     (Sec_Messages.MPair (Sec_Messages.MNon nb)
                                       (Sec_Messages.MAg b)))
                                   (Sec_Messages.MK (NSPK3_config.pks a))))))
                    (List.removeAll na
                      [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
                        FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))]))
                  (\ _ -> True))
                (\ (_, (_, (_, m))) ->
                  let {
                    nb = Sec_Messages.mn
                           (Sec_Messages.mc1
                             (Sec_Messages.mc2 (Sec_Messages.mem m)));
                  } in Interaction_Trees.bind_itree
                         (ITree_CSP.outp Sec_Messages.sig
                           (Sec_Messages.StartProt a b na nb))
                         (\ _ ->
                           Interaction_Trees.bind_itree
                             (ITree_CSP.outp Sec_Messages.send
                               (a, (Sec_Messages.Intruder,
                                     (b, Sec_Messages.MAEnc
   (Sec_Messages.MNon nb) (Sec_Messages.MK (NSPK3_config.pks b))))))
                             (\ _ ->
                               Interaction_Trees.bind_itree
                                 (ITree_CSP.outp Sec_Messages.sig
                                   (Sec_Messages.EndProt a b na nb))
                                 (\ _ ->
                                   ITree_CSP.outp Sec_Messages.terminate
                                     ())))))));

lPAlice ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
lPAlice =
  lInitiator (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
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
      (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)));

nSLPK3 ::
  Interaction_Trees.Itree
    (Sec_Messages.Chan (Numeral_Type.Bit0 Numeral_Type.Num1)
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      Numeral_Type.Num1 Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1))
    ();
nSLPK3 =
  ITree_CSP.gpar_csp
    (ITree_CSP.gpar_csp lPAlice (Set.Set terminate_event) lPBob) lEvents_A_B_I
    lPIntruder;

}
