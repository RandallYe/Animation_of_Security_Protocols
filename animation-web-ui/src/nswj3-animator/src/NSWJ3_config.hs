{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  NSWJ3_config(Deve(..), mkbma, initKnows, allSecrets, allOtherAgents,
                allCommsAgents, allOtherAgentsa, equal_deve)
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
                     (Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))
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
    [mkbma (Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat)),
      mkbma (Sec_Messages.Agent (FSNat.Nmk Arith.one_nat))];

allOtherAgents ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1)];
allOtherAgents a =
  concatMap (\ b -> (if not (Sec_Messages.equal_dagent b a) then [b] else []))
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)];

allCommsAgents ::
  [(Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1),
     Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1))];
allCommsAgents =
  concatMap (\ a -> map (\ b -> (a, b)) (allOtherAgents a))
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat)];

allOtherAgentsa ::
  Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1) ->
    [Sec_Messages.Dagent (Numeral_Type.Bit0 Numeral_Type.Num1)];
allOtherAgentsa a =
  concatMap (\ b -> (if not (Sec_Messages.equal_dagent b a) then [b] else []))
    [Sec_Messages.Agent (FSNat.Nmk Arith.zero_nat),
      Sec_Messages.Agent (FSNat.Nmk Arith.one_nat), Sec_Messages.Intruder];

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
