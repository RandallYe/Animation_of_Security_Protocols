{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module NSPK3_config(pks, initKnows, allSecrets) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified List;
import qualified Numeral_Type;
import qualified Interaction_Trees;
import qualified FSNat;
import qualified Arith;
import qualified Sec_Messages;
import qualified Type_Length;

pks ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    Sec_Messages.Dkey (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1));
pks a =
  (Sec_Messages.pk_of_sk ::
    Sec_Messages.Dkey (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
      (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
      Sec_Messages.Dkey
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
        (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
    ((Interaction_Trees.pfun_app ::
       Interaction_Trees.Pfun
         (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
         (Sec_Messages.Dkey
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
         Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
           Sec_Messages.Dkey
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
      ((Interaction_Trees.pfun_upd ::
         Interaction_Trees.Pfun
           (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
           (Sec_Messages.Dkey
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
             (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
           Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
             Sec_Messages.Dkey
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (Sec_Messages.Dkey
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))))
        ((Interaction_Trees.pfun_upd ::
           Interaction_Trees.Pfun
             (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
             (Sec_Messages.Dkey
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
             Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
               Sec_Messages.Dkey
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (Sec_Messages.Dkey
                     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))))
          ((Interaction_Trees.pfun_upd ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Sec_Messages.Dkey
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 Sec_Messages.Dkey
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (Sec_Messages.Dkey
                       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))))
            Interaction_Trees.bot_pfun
            (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
            (Sec_Messages.Ks (FSNat.Nmk Arith.zero_nat)))
          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
          (Sec_Messages.Ks (FSNat.Nmk Arith.one_nat)))
        Sec_Messages.Intruder
        (Sec_Messages.Ks (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer)))))
      a);

initKnows ::
  [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) Numeral_Type.Num1
     Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1)];
initKnows =
  Sec_Messages.agentsLst
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder] ++
    Sec_Messages.pKsLst
      [Sec_Messages.Kp (FSNat.Nmk Arith.zero_nat),
        Sec_Messages.Kp (FSNat.Nmk Arith.one_nat),
        Sec_Messages.Kp (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer)))] ++
      [Sec_Messages.MNon
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
           Sec_Messages.Intruder),
        Sec_Messages.MK
          ((Interaction_Trees.pfun_app ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Sec_Messages.Dkey
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 Sec_Messages.Dkey
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))
            ((Interaction_Trees.pfun_upd ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (Sec_Messages.Dkey
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   Sec_Messages.Dkey
                     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (Sec_Messages.Dkey
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))))
              ((Interaction_Trees.pfun_upd ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (Sec_Messages.Dkey
                     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (Numeral_Type.Bit0
                       (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     Sec_Messages.Dkey
                       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (Sec_Messages.Dkey
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))
                           (Numeral_Type.Bit0
                             (Numeral_Type.Bit0 Numeral_Type.Num1))))
                ((Interaction_Trees.pfun_upd ::
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (Sec_Messages.Dkey
                       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (Numeral_Type.Bit0
                         (Numeral_Type.Bit0 Numeral_Type.Num1))) ->
                     Sec_Messages.Dagent
                       (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                       Sec_Messages.Dkey
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (Numeral_Type.Bit0
                           (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                         Interaction_Trees.Pfun
                           (Sec_Messages.Dagent
                             (Numeral_Type.Bit0 Numeral_Type.Num1))
                           (Sec_Messages.Dkey
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1))
                             (Numeral_Type.Bit0
                               (Numeral_Type.Bit0 Numeral_Type.Num1))))
                  Interaction_Trees.bot_pfun
                  (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                  (Sec_Messages.Ks (FSNat.Nmk Arith.zero_nat)))
                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                (Sec_Messages.Ks (FSNat.Nmk Arith.one_nat)))
              Sec_Messages.Intruder
              (Sec_Messages.Ks
                (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer)))))
            Sec_Messages.Intruder),
        Sec_Messages.MK (pks Sec_Messages.Intruder)];

allSecrets ::
  [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) Numeral_Type.Num1
     Numeral_Type.Num1 (Numeral_Type.Bit0 Numeral_Type.Num1)];
allSecrets =
  List.removeAll
    (Sec_Messages.MNon
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
        Sec_Messages.Intruder))
    (Sec_Messages.noncesLst
      [FSNat.Nmk Arith.zero_nat, FSNat.Nmk Arith.one_nat,
        FSNat.Nmk (Arith.nat_of_integer (2 :: Integer))]) ++
    List.removeAll
      (Sec_Messages.MK
        (Sec_Messages.Ks
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
            Sec_Messages.Intruder)))
      (Sec_Messages.sKsLst
        [Sec_Messages.Ks (FSNat.Nmk Arith.zero_nat),
          Sec_Messages.Ks (FSNat.Nmk Arith.one_nat),
          Sec_Messages.Ks (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer)))]);

}
