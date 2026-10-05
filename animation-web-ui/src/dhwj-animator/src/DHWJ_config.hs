{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  DHWJ_config(Deve(..), pks, mkbma, initKnows, allSecrets, allOtherPKs,
               allOtherAgents, allOtherAgentsButIntr, allCommsAgentsButIntr,
               equal_deve)
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
import qualified List;
import qualified Numeral_Type;
import qualified Interaction_Trees;
import qualified FSNat;
import qualified Arith;
import qualified Sec_Messages;
import qualified Type_Length;

data Deve = Eve1 | Eve2 | Eve3 | Eve4 deriving (Prelude.Read, Prelude.Show);

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

mkbma ::
  forall a b c d e.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e) => Sec_Messages.Dagent
                              (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                              Sec_Messages.Dmsg a b c d e
                                (Numeral_Type.Bit1 Numeral_Type.Num1)
                                (Numeral_Type.Bit0 Numeral_Type.Num1);
mkbma a =
  Sec_Messages.MBitm
    (Interaction_Trees.pfun_app
      (Interaction_Trees.pfun_upd
        (Interaction_Trees.pfun_upd
          (Interaction_Trees.pfun_upd Interaction_Trees.bot_pfun
            (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
            (Sec_Messages.Bm (FSNat.Nmk Arith.zero_nat)
              (FSNat.Nmk Arith.one_nat)))
          (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
          (Sec_Messages.Bm (FSNat.Nmk Arith.one_nat) (FSNat.Nmk Arith.one_nat)))
        Sec_Messages.Intruder
        (Sec_Messages.Bm (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer)))
          (FSNat.Nmk Arith.one_nat)))
      a);

initKnows ::
  [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) Numeral_Type.Num1
     (Numeral_Type.Bit1 Numeral_Type.Num1)
     (Numeral_Type.Bit0 Numeral_Type.Num1)];
initKnows =
  Sec_Messages.agentsLst
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder] ++
    Sec_Messages.expGLst Sec_Messages.allExpGs ++
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
        Sec_Messages.MBitm
          ((Interaction_Trees.pfun_app ::
             Interaction_Trees.Pfun
               (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
               (Sec_Messages.Dbitmask (Numeral_Type.Bit1 Numeral_Type.Num1)
                 (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
               Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                 Sec_Messages.Dbitmask (Numeral_Type.Bit1 Numeral_Type.Num1)
                   (Numeral_Type.Bit0 Numeral_Type.Num1))
            ((Interaction_Trees.pfun_upd ::
               Interaction_Trees.Pfun
                 (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                 (Sec_Messages.Dbitmask (Numeral_Type.Bit1 Numeral_Type.Num1)
                   (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                 Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                   Sec_Messages.Dbitmask (Numeral_Type.Bit1 Numeral_Type.Num1)
                     (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     Interaction_Trees.Pfun
                       (Sec_Messages.Dagent
                         (Numeral_Type.Bit0 Numeral_Type.Num1))
                       (Sec_Messages.Dbitmask
                         (Numeral_Type.Bit1 Numeral_Type.Num1)
                         (Numeral_Type.Bit0 Numeral_Type.Num1)))
              ((Interaction_Trees.pfun_upd ::
                 Interaction_Trees.Pfun
                   (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                   (Sec_Messages.Dbitmask (Numeral_Type.Bit1 Numeral_Type.Num1)
                     (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                   Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                     Sec_Messages.Dbitmask (Numeral_Type.Bit1 Numeral_Type.Num1)
                       (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                       Interaction_Trees.Pfun
                         (Sec_Messages.Dagent
                           (Numeral_Type.Bit0 Numeral_Type.Num1))
                         (Sec_Messages.Dbitmask
                           (Numeral_Type.Bit1 Numeral_Type.Num1)
                           (Numeral_Type.Bit0 Numeral_Type.Num1)))
                ((Interaction_Trees.pfun_upd ::
                   Interaction_Trees.Pfun
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
                     (Sec_Messages.Dbitmask
                       (Numeral_Type.Bit1 Numeral_Type.Num1)
                       (Numeral_Type.Bit0 Numeral_Type.Num1)) ->
                     Sec_Messages.Dagent
                       (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                       Sec_Messages.Dbitmask
                         (Numeral_Type.Bit1 Numeral_Type.Num1)
                         (Numeral_Type.Bit0 Numeral_Type.Num1) ->
                         Interaction_Trees.Pfun
                           (Sec_Messages.Dagent
                             (Numeral_Type.Bit0 Numeral_Type.Num1))
                           (Sec_Messages.Dbitmask
                             (Numeral_Type.Bit1 Numeral_Type.Num1)
                             (Numeral_Type.Bit0 Numeral_Type.Num1)))
                  Interaction_Trees.bot_pfun
                  (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat))
                  (Sec_Messages.Bm (FSNat.Nmk Arith.zero_nat)
                    (FSNat.Nmk Arith.one_nat)))
                (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))
                (Sec_Messages.Bm (FSNat.Nmk Arith.one_nat)
                  (FSNat.Nmk Arith.one_nat)))
              Sec_Messages.Intruder
              (Sec_Messages.Bm (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer)))
                (FSNat.Nmk Arith.one_nat)))
            Sec_Messages.Intruder)];

allSecrets ::
  [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
     (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)) Numeral_Type.Num1
     (Numeral_Type.Bit1 Numeral_Type.Num1)
     (Numeral_Type.Bit0 Numeral_Type.Num1)];
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
        (Sec_Messages.Kp
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
      (Sec_Messages.pKsLst
        [Sec_Messages.Kp (FSNat.Nmk Arith.zero_nat),
          Sec_Messages.Kp (FSNat.Nmk Arith.one_nat),
          Sec_Messages.Kp (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer)))]) ++
      [mkbma (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)),
        mkbma (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))];

allOtherPKs ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dmsg (Numeral_Type.Bit0 Numeral_Type.Num1)
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
       Numeral_Type.Num1 (Numeral_Type.Bit1 Numeral_Type.Num1)
       (Numeral_Type.Bit0 Numeral_Type.Num1)];
allOtherPKs a =
  List.removeAll (Sec_Messages.MK (pks a))
    (Sec_Messages.pKsLst
      [Sec_Messages.Kp (FSNat.Nmk Arith.zero_nat),
        Sec_Messages.Kp (FSNat.Nmk Arith.one_nat),
        Sec_Messages.Kp (FSNat.Nmk (Arith.nat_of_integer (2 :: Integer)))]);

allOtherAgents ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1)];
allOtherAgents a =
  concatMap (\ b -> (if not (Sec_Messages.equal_dagent b a) then [b] else []))
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder];

allOtherAgentsButIntr ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1)];
allOtherAgentsButIntr a =
  concatMap (\ b -> (if not (Sec_Messages.equal_dagent b a) then [b] else []))
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)];

allCommsAgentsButIntr ::
  [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
     Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))];
allCommsAgentsButIntr =
  concatMap (\ a -> map (\ b -> (a, b)) (allOtherAgentsButIntr a))
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)];

equal_deve :: Deve -> Deve -> Bool;
equal_deve Eve3 Eve4 = False;
equal_deve Eve4 Eve3 = False;
equal_deve Eve2 Eve4 = False;
equal_deve Eve4 Eve2 = False;
equal_deve Eve2 Eve3 = False;
equal_deve Eve3 Eve2 = False;
equal_deve Eve1 Eve4 = False;
equal_deve Eve4 Eve1 = False;
equal_deve Eve1 Eve3 = False;
equal_deve Eve3 Eve1 = False;
equal_deve Eve1 Eve2 = False;
equal_deve Eve2 Eve1 = False;
equal_deve Eve4 Eve4 = True;
equal_deve Eve3 Eve3 = True;
equal_deve Eve2 Eve2 = True;
equal_deve Eve1 Eve1 = True;

}
