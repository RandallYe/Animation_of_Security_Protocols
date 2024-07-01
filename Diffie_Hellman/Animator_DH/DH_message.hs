{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  DH_message(Dagent(..), equal_dagent, Dnonce(..), equal_dnonce, Dsig(..),
              equal_dsig, Dskey(..), equal_dskey, Dpkey(..), equal_dpkey,
              Dmsg(..), equal_dmsg, Chan(..), equal_Chan, rec_dagent,
              less_dagent, rec_dnonce, less_dnonce, rec_dskey, less_dskey,
              rec_dpkey, less_dpkey, rec_dmsg, less_eq_dmsg, less_dmsg,
              insort_insert_key, atomic, dupl, mcmp_to_list, create_cmp, msort,
              is_MKs, length, pair2, enum_dagent, enum_dpkey, allPKs, break_lst,
              breakl, breakm, mn, mkp, mks, mod_exp1, mod_exp2, allAgents,
              enum_dnonce, allNonces, allPKsLst, un_fake_C, is_fake_C, fake,
              un_hear_C, is_hear_C, hear, un_leak_C, is_leak_C, leak, un_recv_C,
              is_recv_C, recv, un_send_C, is_send_C, send, is_MNon,
              extract_nonces, mod_exp1a, mod_exp2a, is_MKp, sig_1, allAgentsLst,
              allNoncesLst, senc_1, extract_dskey, sig_1a, is_MModExp, senc_1a,
              build_n, extract_dpkey, un_terminate_C, is_terminate_C, terminate,
              build1_n, build1_n_0)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified Channel_Type;
import qualified Prisms;
import qualified HOL;
import qualified Arith;
import qualified Option;
import qualified List;
import qualified Set;
import qualified Orderings;

data Dagent = Alice | Bob | Intruder | Server
  deriving (Prelude.Read, Prelude.Show);

equal_dagent :: Dagent -> Dagent -> Bool;
equal_dagent Intruder Server = False;
equal_dagent Server Intruder = False;
equal_dagent Bob Server = False;
equal_dagent Server Bob = False;
equal_dagent Bob Intruder = False;
equal_dagent Intruder Bob = False;
equal_dagent Alice Server = False;
equal_dagent Server Alice = False;
equal_dagent Alice Intruder = False;
equal_dagent Intruder Alice = False;
equal_dagent Alice Bob = False;
equal_dagent Bob Alice = False;
equal_dagent Server Server = True;
equal_dagent Intruder Intruder = True;
equal_dagent Bob Bob = True;
equal_dagent Alice Alice = True;

newtype Dnonce = N Dagent deriving (Prelude.Read, Prelude.Show);

equal_dnonce :: Dnonce -> Dnonce -> Bool;
equal_dnonce (N x) (N ya) = equal_dagent x ya;

data Dsig = ClaimSecret Dagent Dnonce (Set.Set Dagent)
  | StartProt Dagent Dagent Dnonce Dnonce | EndProt Dagent Dagent Dnonce Dnonce
  deriving (Prelude.Read, Prelude.Show);

instance Eq Dagent where {
  a == b = equal_dagent a b;
};

equal_dsig :: Dsig -> Dsig -> Bool;
equal_dsig (StartProt x21 x22 x23 x24) (EndProt x31 x32 x33 x34) = False;
equal_dsig (EndProt x31 x32 x33 x34) (StartProt x21 x22 x23 x24) = False;
equal_dsig (ClaimSecret x11 x12 x13) (EndProt x31 x32 x33 x34) = False;
equal_dsig (EndProt x31 x32 x33 x34) (ClaimSecret x11 x12 x13) = False;
equal_dsig (ClaimSecret x11 x12 x13) (StartProt x21 x22 x23 x24) = False;
equal_dsig (StartProt x21 x22 x23 x24) (ClaimSecret x11 x12 x13) = False;
equal_dsig (EndProt x31 x32 x33 x34) (EndProt y31 y32 y33 y34) =
  equal_dagent x31 y31 &&
    equal_dagent x32 y32 && equal_dnonce x33 y33 && equal_dnonce x34 y34;
equal_dsig (StartProt x21 x22 x23 x24) (StartProt y21 y22 y23 y24) =
  equal_dagent x21 y21 &&
    equal_dagent x22 y22 && equal_dnonce x23 y23 && equal_dnonce x24 y24;
equal_dsig (ClaimSecret x11 x12 x13) (ClaimSecret y11 y12 y13) =
  equal_dagent x11 y11 && equal_dnonce x12 y12 && Set.equal_set x13 y13;

newtype Dskey = SK Dagent deriving (Prelude.Read, Prelude.Show);

equal_dskey :: Dskey -> Dskey -> Bool;
equal_dskey (SK x) (SK ya) = equal_dagent x ya;

newtype Dpkey = PK Dagent deriving (Prelude.Read, Prelude.Show);

equal_dpkey :: Dpkey -> Dpkey -> Bool;
equal_dpkey (PK x) (PK ya) = equal_dagent x ya;

data Dmsg = MAg Dagent | MNon Dnonce | MKp Dpkey | MKs Dskey | MCmp Dmsg Dmsg
  | MEnc Dmsg Dpkey | MSig Dmsg Dskey | MSEnc Dmsg Dmsg | MExpg
  | MModExp Dmsg Dnonce deriving (Prelude.Read, Prelude.Show);

equal_dmsg :: Dmsg -> Dmsg -> Bool;
equal_dmsg MExpg (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) MExpg = False;
equal_dmsg (MSEnc x81 x82) (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) (MSEnc x81 x82) = False;
equal_dmsg (MSEnc x81 x82) MExpg = False;
equal_dmsg MExpg (MSEnc x81 x82) = False;
equal_dmsg (MSig x71 x72) (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) MExpg = False;
equal_dmsg MExpg (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MSEnc x81 x82) = False;
equal_dmsg (MSEnc x81 x82) (MSig x71 x72) = False;
equal_dmsg (MEnc x61 x62) (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) MExpg = False;
equal_dmsg MExpg (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MSEnc x81 x82) = False;
equal_dmsg (MSEnc x81 x82) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MEnc x61 x62) = False;
equal_dmsg (MCmp x51 x52) (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) MExpg = False;
equal_dmsg MExpg (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MSEnc x81 x82) = False;
equal_dmsg (MSEnc x81 x82) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MCmp x51 x52) = False;
equal_dmsg (MKs x4) (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) (MKs x4) = False;
equal_dmsg (MKs x4) MExpg = False;
equal_dmsg MExpg (MKs x4) = False;
equal_dmsg (MKs x4) (MSEnc x81 x82) = False;
equal_dmsg (MSEnc x81 x82) (MKs x4) = False;
equal_dmsg (MKs x4) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MKs x4) = False;
equal_dmsg (MKs x4) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MKs x4) = False;
equal_dmsg (MKs x4) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MKs x4) = False;
equal_dmsg (MKp x3) (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) (MKp x3) = False;
equal_dmsg (MKp x3) MExpg = False;
equal_dmsg MExpg (MKp x3) = False;
equal_dmsg (MKp x3) (MSEnc x81 x82) = False;
equal_dmsg (MSEnc x81 x82) (MKp x3) = False;
equal_dmsg (MKp x3) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MKp x3) = False;
equal_dmsg (MKp x3) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MKp x3) = False;
equal_dmsg (MKp x3) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MKp x3) = False;
equal_dmsg (MKp x3) (MKs x4) = False;
equal_dmsg (MKs x4) (MKp x3) = False;
equal_dmsg (MNon x2) (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) (MNon x2) = False;
equal_dmsg (MNon x2) MExpg = False;
equal_dmsg MExpg (MNon x2) = False;
equal_dmsg (MNon x2) (MSEnc x81 x82) = False;
equal_dmsg (MSEnc x81 x82) (MNon x2) = False;
equal_dmsg (MNon x2) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MNon x2) = False;
equal_dmsg (MNon x2) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MNon x2) = False;
equal_dmsg (MNon x2) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MNon x2) = False;
equal_dmsg (MNon x2) (MKs x4) = False;
equal_dmsg (MKs x4) (MNon x2) = False;
equal_dmsg (MNon x2) (MKp x3) = False;
equal_dmsg (MKp x3) (MNon x2) = False;
equal_dmsg (MAg x1) (MModExp x101 x102) = False;
equal_dmsg (MModExp x101 x102) (MAg x1) = False;
equal_dmsg (MAg x1) MExpg = False;
equal_dmsg MExpg (MAg x1) = False;
equal_dmsg (MAg x1) (MSEnc x81 x82) = False;
equal_dmsg (MSEnc x81 x82) (MAg x1) = False;
equal_dmsg (MAg x1) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MAg x1) = False;
equal_dmsg (MAg x1) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MAg x1) = False;
equal_dmsg (MAg x1) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MAg x1) = False;
equal_dmsg (MAg x1) (MKs x4) = False;
equal_dmsg (MKs x4) (MAg x1) = False;
equal_dmsg (MAg x1) (MKp x3) = False;
equal_dmsg (MKp x3) (MAg x1) = False;
equal_dmsg (MAg x1) (MNon x2) = False;
equal_dmsg (MNon x2) (MAg x1) = False;
equal_dmsg (MModExp x101 x102) (MModExp y101 y102) =
  equal_dmsg x101 y101 && equal_dnonce x102 y102;
equal_dmsg (MSEnc x81 x82) (MSEnc y81 y82) =
  equal_dmsg x81 y81 && equal_dmsg x82 y82;
equal_dmsg (MSig x71 x72) (MSig y71 y72) =
  equal_dmsg x71 y71 && equal_dskey x72 y72;
equal_dmsg (MEnc x61 x62) (MEnc y61 y62) =
  equal_dmsg x61 y61 && equal_dpkey x62 y62;
equal_dmsg (MCmp x51 x52) (MCmp y51 y52) =
  equal_dmsg x51 y51 && equal_dmsg x52 y52;
equal_dmsg (MKs x4) (MKs y4) = equal_dskey x4 y4;
equal_dmsg (MKp x3) (MKp y3) = equal_dpkey x3 y3;
equal_dmsg (MNon x2) (MNon y2) = equal_dnonce x2 y2;
equal_dmsg (MAg x1) (MAg y1) = equal_dagent x1 y1;
equal_dmsg MExpg MExpg = True;

data Chan = Env_C (Dagent, Dagent) | Send_C (Dagent, (Dagent, Dmsg))
  | Recv_C (Dagent, (Dagent, Dmsg)) | Hear_C (Dagent, (Dagent, Dmsg))
  | Fake_C (Dagent, (Dagent, Dmsg)) | Leak_C Dmsg | Sig_C Dsig | Terminate_C ()
  deriving (Prelude.Read, Prelude.Show);

instance Eq Dmsg where {
  a == b = equal_dmsg a b;
};

equal_Chan :: Chan -> Chan -> Bool;
equal_Chan (Sig_C x7) (Terminate_C x8) = False;
equal_Chan (Terminate_C x8) (Sig_C x7) = False;
equal_Chan (Leak_C x6) (Terminate_C x8) = False;
equal_Chan (Terminate_C x8) (Leak_C x6) = False;
equal_Chan (Leak_C x6) (Sig_C x7) = False;
equal_Chan (Sig_C x7) (Leak_C x6) = False;
equal_Chan (Fake_C x5) (Terminate_C x8) = False;
equal_Chan (Terminate_C x8) (Fake_C x5) = False;
equal_Chan (Fake_C x5) (Sig_C x7) = False;
equal_Chan (Sig_C x7) (Fake_C x5) = False;
equal_Chan (Fake_C x5) (Leak_C x6) = False;
equal_Chan (Leak_C x6) (Fake_C x5) = False;
equal_Chan (Hear_C x4) (Terminate_C x8) = False;
equal_Chan (Terminate_C x8) (Hear_C x4) = False;
equal_Chan (Hear_C x4) (Sig_C x7) = False;
equal_Chan (Sig_C x7) (Hear_C x4) = False;
equal_Chan (Hear_C x4) (Leak_C x6) = False;
equal_Chan (Leak_C x6) (Hear_C x4) = False;
equal_Chan (Hear_C x4) (Fake_C x5) = False;
equal_Chan (Fake_C x5) (Hear_C x4) = False;
equal_Chan (Recv_C x3) (Terminate_C x8) = False;
equal_Chan (Terminate_C x8) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Sig_C x7) = False;
equal_Chan (Sig_C x7) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Leak_C x6) = False;
equal_Chan (Leak_C x6) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Fake_C x5) = False;
equal_Chan (Fake_C x5) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Hear_C x4) = False;
equal_Chan (Hear_C x4) (Recv_C x3) = False;
equal_Chan (Send_C x2) (Terminate_C x8) = False;
equal_Chan (Terminate_C x8) (Send_C x2) = False;
equal_Chan (Send_C x2) (Sig_C x7) = False;
equal_Chan (Sig_C x7) (Send_C x2) = False;
equal_Chan (Send_C x2) (Leak_C x6) = False;
equal_Chan (Leak_C x6) (Send_C x2) = False;
equal_Chan (Send_C x2) (Fake_C x5) = False;
equal_Chan (Fake_C x5) (Send_C x2) = False;
equal_Chan (Send_C x2) (Hear_C x4) = False;
equal_Chan (Hear_C x4) (Send_C x2) = False;
equal_Chan (Send_C x2) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Send_C x2) = False;
equal_Chan (Env_C x1) (Terminate_C x8) = False;
equal_Chan (Terminate_C x8) (Env_C x1) = False;
equal_Chan (Env_C x1) (Sig_C x7) = False;
equal_Chan (Sig_C x7) (Env_C x1) = False;
equal_Chan (Env_C x1) (Leak_C x6) = False;
equal_Chan (Leak_C x6) (Env_C x1) = False;
equal_Chan (Env_C x1) (Fake_C x5) = False;
equal_Chan (Fake_C x5) (Env_C x1) = False;
equal_Chan (Env_C x1) (Hear_C x4) = False;
equal_Chan (Hear_C x4) (Env_C x1) = False;
equal_Chan (Env_C x1) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Env_C x1) = False;
equal_Chan (Env_C x1) (Send_C x2) = False;
equal_Chan (Send_C x2) (Env_C x1) = False;
equal_Chan (Terminate_C x8) (Terminate_C y8) = x8 == y8;
equal_Chan (Sig_C x7) (Sig_C y7) = equal_dsig x7 y7;
equal_Chan (Leak_C x6) (Leak_C y6) = equal_dmsg x6 y6;
equal_Chan (Fake_C x5) (Fake_C y5) = x5 == y5;
equal_Chan (Hear_C x4) (Hear_C y4) = x4 == y4;
equal_Chan (Recv_C x3) (Recv_C y3) = x3 == y3;
equal_Chan (Send_C x2) (Send_C y2) = x2 == y2;
equal_Chan (Env_C x1) (Env_C y1) = x1 == y1;

instance Eq Chan where {
  a == b = equal_Chan a b;
};

rec_dagent :: forall a. a -> a -> a -> a -> Dagent -> a;
rec_dagent f1 f2 f3 f4 Alice = f1;
rec_dagent f1 f2 f3 f4 Bob = f2;
rec_dagent f1 f2 f3 f4 Intruder = f3;
rec_dagent f1 f2 f3 f4 Server = f4;

less_dagent :: Dagent -> Dagent -> Bool;
less_dagent =
  rec_dagent (\ a -> (case a of {
                       Alice -> False;
                       Bob -> True;
                       Intruder -> True;
                       Server -> True;
                     }))
    (\ a -> (case a of {
              Alice -> False;
              Bob -> False;
              Intruder -> True;
              Server -> True;
            }))
    (\ a -> (case a of {
              Alice -> False;
              Bob -> False;
              Intruder -> False;
              Server -> True;
            }))
    (\ a -> (case a of {
              Alice -> False;
              Bob -> False;
              Intruder -> False;
              Server -> False;
            }));

rec_dnonce :: forall a. (Dagent -> a) -> Dnonce -> a;
rec_dnonce f (N x) = f x;

less_dnonce :: Dnonce -> Dnonce -> Bool;
less_dnonce = rec_dnonce (\ x_0 (N a) -> less_dagent x_0 a);

rec_dskey :: forall a. (Dagent -> a) -> Dskey -> a;
rec_dskey f (SK x) = f x;

less_dskey :: Dskey -> Dskey -> Bool;
less_dskey = rec_dskey (\ x_0 (SK a) -> less_dagent x_0 a);

rec_dpkey :: forall a. (Dagent -> a) -> Dpkey -> a;
rec_dpkey f (PK x) = f x;

less_dpkey :: Dpkey -> Dpkey -> Bool;
less_dpkey = rec_dpkey (\ x_0 (PK a) -> less_dagent x_0 a);

rec_dmsg ::
  forall a.
    (Dagent -> a) ->
      (Dnonce -> a) ->
        (Dpkey -> a) ->
          (Dskey -> a) ->
            (Dmsg -> Dmsg -> a -> a -> a) ->
              (Dmsg -> Dpkey -> a -> a) ->
                (Dmsg -> Dskey -> a -> a) ->
                  (Dmsg -> Dmsg -> a -> a -> a) ->
                    a -> (Dmsg -> Dnonce -> a -> a) -> Dmsg -> a;
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MAg x1) = f1 x1;
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MNon x2) = f2 x2;
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MKp x3) = f3 x3;
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MKs x4) = f4 x4;
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MCmp x51 x52) =
  f5 x51 x52 (rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 x51)
    (rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 x52);
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MEnc x61 x62) =
  f6 x61 x62 (rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 x61);
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MSig x71 x72) =
  f7 x71 x72 (rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 x71);
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MSEnc x81 x82) =
  f8 x81 x82 (rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 x81)
    (rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 x82);
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 MExpg = f9;
rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (MModExp x101 x102) =
  f10 x101 x102 (rec_dmsg f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 x101);

less_eq_dmsg :: Dmsg -> Dmsg -> Bool;
less_eq_dmsg =
  (\ x y ->
    rec_dmsg (\ x_0 a -> (case a of {
                           MAg aa -> less_dagent x_0 aa;
                           MNon _ -> True;
                           MKp _ -> True;
                           MKs _ -> True;
                           MCmp _ _ -> True;
                           MEnc _ _ -> True;
                           MSig _ _ -> True;
                           MSEnc _ _ -> True;
                           MExpg -> True;
                           MModExp _ _ -> True;
                         }))
      (\ x_0 a -> (case a of {
                    MAg _ -> False;
                    MNon aa -> less_dnonce x_0 aa;
                    MKp _ -> True;
                    MKs _ -> True;
                    MCmp _ _ -> True;
                    MEnc _ _ -> True;
                    MSig _ _ -> True;
                    MSEnc _ _ -> True;
                    MExpg -> True;
                    MModExp _ _ -> True;
                  }))
      (\ x_0 a -> (case a of {
                    MAg _ -> False;
                    MNon _ -> False;
                    MKp aa -> less_dpkey x_0 aa;
                    MKs _ -> True;
                    MCmp _ _ -> True;
                    MEnc _ _ -> True;
                    MSig _ _ -> True;
                    MSEnc _ _ -> True;
                    MExpg -> True;
                    MModExp _ _ -> True;
                  }))
      (\ x_0 a -> (case a of {
                    MAg _ -> False;
                    MNon _ -> False;
                    MKp _ -> False;
                    MKs aa -> less_dskey x_0 aa;
                    MCmp _ _ -> True;
                    MEnc _ _ -> True;
                    MSig _ _ -> True;
                    MSEnc _ _ -> True;
                    MExpg -> True;
                    MModExp _ _ -> True;
                  }))
      (\ x_0 _ res_0 res_1 a ->
        (case a of {
          MAg _ -> False;
          MNon _ -> False;
          MKp _ -> False;
          MKs _ -> False;
          MCmp y_0 y_1 -> res_0 y_0 || equal_dmsg x_0 y_0 && res_1 y_1;
          MEnc _ _ -> True;
          MSig _ _ -> True;
          MSEnc _ _ -> True;
          MExpg -> True;
          MModExp _ _ -> True;
        }))
      (\ x_0 x_1 res_0 a ->
        (case a of {
          MAg _ -> False;
          MNon _ -> False;
          MKp _ -> False;
          MKs _ -> False;
          MCmp _ _ -> False;
          MEnc y_0 y_1 -> res_0 y_0 || equal_dmsg x_0 y_0 && less_dpkey x_1 y_1;
          MSig _ _ -> True;
          MSEnc _ _ -> True;
          MExpg -> True;
          MModExp _ _ -> True;
        }))
      (\ x_0 x_1 res_0 a ->
        (case a of {
          MAg _ -> False;
          MNon _ -> False;
          MKp _ -> False;
          MKs _ -> False;
          MCmp _ _ -> False;
          MEnc _ _ -> False;
          MSig y_0 y_1 -> res_0 y_0 || equal_dmsg x_0 y_0 && less_dskey x_1 y_1;
          MSEnc _ _ -> True;
          MExpg -> True;
          MModExp _ _ -> True;
        }))
      (\ x_0 _ res_0 res_1 a ->
        (case a of {
          MAg _ -> False;
          MNon _ -> False;
          MKp _ -> False;
          MKs _ -> False;
          MCmp _ _ -> False;
          MEnc _ _ -> False;
          MSig _ _ -> False;
          MSEnc y_0 y_1 -> res_0 y_0 || equal_dmsg x_0 y_0 && res_1 y_1;
          MExpg -> True;
          MModExp _ _ -> True;
        }))
      (\ a -> (case a of {
                MAg _ -> False;
                MNon _ -> False;
                MKp _ -> False;
                MKs _ -> False;
                MCmp _ _ -> False;
                MEnc _ _ -> False;
                MSig _ _ -> False;
                MSEnc _ _ -> False;
                MExpg -> False;
                MModExp _ _ -> True;
              }))
      (\ x_0 x_1 res_0 a ->
        (case a of {
          MAg _ -> False;
          MNon _ -> False;
          MKp _ -> False;
          MKs _ -> False;
          MCmp _ _ -> False;
          MEnc _ _ -> False;
          MSig _ _ -> False;
          MSEnc _ _ -> False;
          MExpg -> False;
          MModExp y_0 y_1 ->
            res_0 y_0 || equal_dmsg x_0 y_0 && less_dnonce x_1 y_1;
        }))
      x y ||
      equal_dmsg x y);

less_dmsg :: Dmsg -> Dmsg -> Bool;
less_dmsg =
  rec_dmsg (\ x_0 a -> (case a of {
                         MAg aa -> less_dagent x_0 aa;
                         MNon _ -> True;
                         MKp _ -> True;
                         MKs _ -> True;
                         MCmp _ _ -> True;
                         MEnc _ _ -> True;
                         MSig _ _ -> True;
                         MSEnc _ _ -> True;
                         MExpg -> True;
                         MModExp _ _ -> True;
                       }))
    (\ x_0 a -> (case a of {
                  MAg _ -> False;
                  MNon aa -> less_dnonce x_0 aa;
                  MKp _ -> True;
                  MKs _ -> True;
                  MCmp _ _ -> True;
                  MEnc _ _ -> True;
                  MSig _ _ -> True;
                  MSEnc _ _ -> True;
                  MExpg -> True;
                  MModExp _ _ -> True;
                }))
    (\ x_0 a -> (case a of {
                  MAg _ -> False;
                  MNon _ -> False;
                  MKp aa -> less_dpkey x_0 aa;
                  MKs _ -> True;
                  MCmp _ _ -> True;
                  MEnc _ _ -> True;
                  MSig _ _ -> True;
                  MSEnc _ _ -> True;
                  MExpg -> True;
                  MModExp _ _ -> True;
                }))
    (\ x_0 a -> (case a of {
                  MAg _ -> False;
                  MNon _ -> False;
                  MKp _ -> False;
                  MKs aa -> less_dskey x_0 aa;
                  MCmp _ _ -> True;
                  MEnc _ _ -> True;
                  MSig _ _ -> True;
                  MSEnc _ _ -> True;
                  MExpg -> True;
                  MModExp _ _ -> True;
                }))
    (\ x_0 _ res_0 res_1 a ->
      (case a of {
        MAg _ -> False;
        MNon _ -> False;
        MKp _ -> False;
        MKs _ -> False;
        MCmp y_0 y_1 -> res_0 y_0 || equal_dmsg x_0 y_0 && res_1 y_1;
        MEnc _ _ -> True;
        MSig _ _ -> True;
        MSEnc _ _ -> True;
        MExpg -> True;
        MModExp _ _ -> True;
      }))
    (\ x_0 x_1 res_0 a ->
      (case a of {
        MAg _ -> False;
        MNon _ -> False;
        MKp _ -> False;
        MKs _ -> False;
        MCmp _ _ -> False;
        MEnc y_0 y_1 -> res_0 y_0 || equal_dmsg x_0 y_0 && less_dpkey x_1 y_1;
        MSig _ _ -> True;
        MSEnc _ _ -> True;
        MExpg -> True;
        MModExp _ _ -> True;
      }))
    (\ x_0 x_1 res_0 a ->
      (case a of {
        MAg _ -> False;
        MNon _ -> False;
        MKp _ -> False;
        MKs _ -> False;
        MCmp _ _ -> False;
        MEnc _ _ -> False;
        MSig y_0 y_1 -> res_0 y_0 || equal_dmsg x_0 y_0 && less_dskey x_1 y_1;
        MSEnc _ _ -> True;
        MExpg -> True;
        MModExp _ _ -> True;
      }))
    (\ x_0 _ res_0 res_1 a ->
      (case a of {
        MAg _ -> False;
        MNon _ -> False;
        MKp _ -> False;
        MKs _ -> False;
        MCmp _ _ -> False;
        MEnc _ _ -> False;
        MSig _ _ -> False;
        MSEnc y_0 y_1 -> res_0 y_0 || equal_dmsg x_0 y_0 && res_1 y_1;
        MExpg -> True;
        MModExp _ _ -> True;
      }))
    (\ a -> (case a of {
              MAg _ -> False;
              MNon _ -> False;
              MKp _ -> False;
              MKs _ -> False;
              MCmp _ _ -> False;
              MEnc _ _ -> False;
              MSig _ _ -> False;
              MSEnc _ _ -> False;
              MExpg -> False;
              MModExp _ _ -> True;
            }))
    (\ x_0 x_1 res_0 a ->
      (case a of {
        MAg _ -> False;
        MNon _ -> False;
        MKp _ -> False;
        MKs _ -> False;
        MCmp _ _ -> False;
        MEnc _ _ -> False;
        MSig _ _ -> False;
        MSEnc _ _ -> False;
        MExpg -> False;
        MModExp y_0 y_1 ->
          res_0 y_0 || equal_dmsg x_0 y_0 && less_dnonce x_1 y_1;
      }));

instance Orderings.Ord Dmsg where {
  less_eq = less_eq_dmsg;
  less = less_dmsg;
};

instance Orderings.Preorder Dmsg where {
};

instance Orderings.Order Dmsg where {
};

instance Orderings.Linorder Dmsg where {
};

instance Eq Dnonce where {
  a == b = equal_dnonce a b;
};

insort_insert_key ::
  forall a b. (Eq b, Orderings.Linorder b) => (a -> b) -> a -> [a] -> [a];
insort_insert_key f x xs =
  (if Set.member (f x) (Set.image f (Set.Set xs)) then xs
    else List.insort_key f x xs);

atomic :: Dmsg -> [Dmsg];
atomic (MAg m) = [MAg m];
atomic (MNon m) = [MNon m];
atomic (MKp m) = [MKp m];
atomic (MKs m) = [MKs m];
atomic (MCmp m1 m2) =
  List.fold (insort_insert_key (\ x -> x)) (atomic m1) (atomic m2);
atomic (MEnc m k) = atomic m;
atomic (MSig m k) = atomic m;
atomic (MSEnc m k) = atomic m;
atomic MExpg = [MExpg];
atomic (MModExp m k) = atomic m;

dupl :: Dmsg -> Bool;
dupl (MAg uu) = False;
dupl (MNon uv) = False;
dupl (MKp uw) = False;
dupl (MKs ux) = False;
dupl (MCmp m1 m2) =
  dupl m1 ||
    (dupl m2 || not (null (filter (List.member (atomic m1)) (atomic m2))));
dupl (MEnc m k) = dupl m;
dupl (MSig m k) = dupl m;
dupl (MSEnc m k) = dupl m;
dupl MExpg = False;
dupl (MModExp m k) = dupl m;

mcmp_to_list :: Dmsg -> [Dmsg];
mcmp_to_list (MCmp m1 m2) =
  List.sort_key (\ x -> x) (mcmp_to_list m1 ++ mcmp_to_list m2);
mcmp_to_list (MAg v) = [MAg v];
mcmp_to_list (MNon v) = [MNon v];
mcmp_to_list (MKp v) = [MKp v];
mcmp_to_list (MKs v) = [MKs v];
mcmp_to_list (MEnc v va) = [MEnc v va];
mcmp_to_list (MSig v va) = [MSig v va];
mcmp_to_list (MSEnc v va) = [MSEnc v va];
mcmp_to_list MExpg = [MExpg];
mcmp_to_list (MModExp v va) = [MModExp v va];

create_cmp :: [Dmsg] -> Maybe Dmsg;
create_cmp [] = Nothing;
create_cmp [x, y] = Just (MCmp x y);
create_cmp [x] = (case create_cmp [] of {
                   Nothing -> Nothing;
                   Just y -> Just (MCmp x y);
                 });
create_cmp (x : v : vb : vc) = (case create_cmp (v : vb : vc) of {
                                 Nothing -> Nothing;
                                 Just y -> Just (MCmp x y);
                               });

msort :: Dmsg -> Dmsg;
msort (MAg a) = MAg a;
msort (MNon a) = MNon a;
msort (MKp a) = MKp a;
msort (MKs a) = MKs a;
msort (MCmp m1 m2) =
  (case create_cmp
          (List.sort_key (\ x -> x)
            (mcmp_to_list (msort m1) ++ mcmp_to_list (msort m2)))
    of {
    Nothing -> MCmp m1 m2;
    Just y -> y;
  });
msort (MEnc m k) = MEnc (msort m) k;
msort (MSig m k) = MSig (msort m) k;
msort (MSEnc m k) = MSEnc (msort m) k;
msort MExpg = MExpg;
msort (MModExp m k) = MModExp (msort m) k;

is_MKs :: Dmsg -> Bool;
is_MKs (MAg x1) = False;
is_MKs (MNon x2) = False;
is_MKs (MKp x3) = False;
is_MKs (MKs x4) = True;
is_MKs (MCmp x51 x52) = False;
is_MKs (MEnc x61 x62) = False;
is_MKs (MSig x71 x72) = False;
is_MKs (MSEnc x81 x82) = False;
is_MKs MExpg = False;
is_MKs (MModExp x101 x102) = False;

length :: Dmsg -> Arith.Nat;
length (MAg uu) = Arith.one_nat;
length (MNon uv) = Arith.one_nat;
length (MKp uw) = Arith.one_nat;
length (MKs ux) = Arith.one_nat;
length (MCmp m1 m2) = Arith.plus_nat (length m1) (length m2);
length (MEnc m k) = length m;
length (MSig m k) = length m;
length (MSEnc m k) = length m;
length MExpg = Arith.one_nat;
length (MModExp m k) = length m;

pair2 :: [Dmsg] -> [Dmsg] -> Arith.Nat -> [Dmsg];
pair2 [] ys l = [];
pair2 (x : xs) ys l =
  let {
    a = pair2 xs ys l;
  } in List.map_filter
         (\ xa ->
           (if not (equal_dmsg xa x) &&
                 Arith.less_eq_nat (Arith.plus_nat (length x) (length xa)) l &&
                   not (dupl x ||
                         (dupl xa ||
                           not (null (filter (List.member (atomic x))
                                       (atomic xa))))) &&
                     not (is_MKs x) && not (is_MKs xa)
             then Just (msort (MCmp x xa)) else Nothing))
         ys ++
         a;

enum_dagent :: [Dagent];
enum_dagent = [Alice, Bob, Intruder, Server];

enum_dpkey :: [Dpkey];
enum_dpkey = map PK enum_dagent;

allPKs :: [Dpkey];
allPKs = enum_dpkey;

break_lst :: [Dmsg] -> [Dmsg] -> [Dmsg];
break_lst [] ams = ams;
break_lst (MKp k : xs) ams = break_lst xs (List.insert (MKp k) ams);
break_lst (MKs k : xs) ams = break_lst xs (List.insert (MKs k) ams);
break_lst (MAg a : xs) ams = break_lst xs (List.insert (MAg a) ams);
break_lst (MNon a : xs) ams = break_lst xs (List.insert (MNon a) ams);
break_lst (MCmp a b : xs) ams =
  break_lst xs (List.remdups (break_lst [a] ams ++ break_lst [b] ams ++ ams));
break_lst (MEnc a (PK k) : xs) ams = break_lst xs ams;
break_lst (MSig a (SK k) : xs) ams =
  (if List.member ams (MKp (PK k))
    then break_lst (a : xs) (List.insert (MSig a (SK k)) ams)
    else let {
           rams = break_lst xs ams;
         } in (if List.member rams (MKp (PK k))
                then break_lst (a : xs) (List.insert (MSig a (SK k)) ams)
                else break_lst xs (List.insert (MSig a (SK k)) ams)));
break_lst (MSEnc m k : xs) ams =
  (case k of {
    MAg _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MNon _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MKp _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MKs _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MCmp _ _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MEnc _ _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MSig _ _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MSEnc _ _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MExpg -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MAg _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MNon _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MKp _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MKs _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MCmp _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MEnc _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MSig _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MSEnc _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp MExpg _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp (MAg _) _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp (MNon _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp (MKp _) _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp (MKs _) _) _ -> break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp (MCmp _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp (MEnc _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp (MSig _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp (MSEnc _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams);
    MModExp (MModExp MExpg a) b ->
      (if List.member ams (MModExp MExpg a) && List.member ams (MNon b) ||
            (List.member ams (MModExp MExpg b) && List.member ams (MNon a) ||
              List.member ams MExpg &&
                List.member ams (MNon a) && List.member ams (MNon b))
        then break_lst (m : xs) (List.insert (MSEnc m k) ams)
        else let {
               rams = break_lst xs ams;
             } in (if List.member rams (MModExp MExpg a) &&
                        List.member rams (MNon b) ||
                        (List.member rams (MModExp MExpg b) &&
                           List.member rams (MNon a) ||
                          List.member rams MExpg &&
                            List.member rams (MNon a) &&
                              List.member rams (MNon b))
                    then break_lst (m : xs) (List.insert (MSEnc m k) ams)
                    else break_lst xs (List.insert (MSEnc m k) ams)));
    MModExp (MModExp (MModExp _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams);
  });
break_lst (MExpg : xs) ams = break_lst xs (List.insert MExpg ams);
break_lst (MModExp a b : xs) ams = break_lst xs (List.insert (MModExp a b) ams);

breakl :: [Dmsg] -> [Dmsg];
breakl xs = break_lst xs [];

breakm :: [Dmsg] -> [Dmsg];
breakm xs = breakl (breakl xs);

mn :: Dmsg -> Dnonce;
mn (MNon x2) = x2;

mkp :: Dmsg -> Dpkey;
mkp (MKp x3) = x3;

mks :: Dmsg -> Dskey;
mks (MKs x4) = x4;

mod_exp1 :: [Dmsg] -> [Dnonce] -> [Dmsg];
mod_exp1 [] ns = [];
mod_exp1 (MModExp MExpg a : xs) ns =
  map (MModExp (MModExp MExpg a)) ns ++ mod_exp1 xs ns;
mod_exp1 (MAg v : xs) ns = mod_exp1 xs ns;
mod_exp1 (MNon v : xs) ns = mod_exp1 xs ns;
mod_exp1 (MKp v : xs) ns = mod_exp1 xs ns;
mod_exp1 (MKs v : xs) ns = mod_exp1 xs ns;
mod_exp1 (MCmp v va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MEnc v va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MSig v va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MSEnc v va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MExpg : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MAg vb) va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MNon vb) va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MKp vb) va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MKs vb) va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MCmp vb vc) va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MEnc vb vc) va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MSig vb vc) va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MSEnc vb vc) va : xs) ns = mod_exp1 xs ns;
mod_exp1 (MModExp (MModExp vb vc) va : xs) ns = mod_exp1 xs ns;

mod_exp2 :: [Dnonce] -> [Dmsg];
mod_exp2 ns = let {
                mes = map (MModExp MExpg) ns;
              } in mes ++ concatMap (\ m -> map (MModExp m) ns) mes;

allAgents :: [Dagent];
allAgents = enum_dagent;

enum_dnonce :: [Dnonce];
enum_dnonce = map N enum_dagent;

allNonces :: [Dnonce];
allNonces = enum_dnonce;

allPKsLst :: [Dmsg];
allPKsLst = map MKp allPKs;

un_fake_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_fake_C (Fake_C x5) = x5;

is_fake_C :: Chan -> Bool;
is_fake_C (Env_C x1) = False;
is_fake_C (Send_C x2) = False;
is_fake_C (Recv_C x3) = False;
is_fake_C (Hear_C x4) = False;
is_fake_C (Fake_C x5) = True;
is_fake_C (Leak_C x6) = False;
is_fake_C (Sig_C x7) = False;
is_fake_C (Terminate_C x8) = False;

fake :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
fake = Channel_Type.ctor_prism Fake_C is_fake_C un_fake_C;

un_hear_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_hear_C (Hear_C x4) = x4;

is_hear_C :: Chan -> Bool;
is_hear_C (Env_C x1) = False;
is_hear_C (Send_C x2) = False;
is_hear_C (Recv_C x3) = False;
is_hear_C (Hear_C x4) = True;
is_hear_C (Fake_C x5) = False;
is_hear_C (Leak_C x6) = False;
is_hear_C (Sig_C x7) = False;
is_hear_C (Terminate_C x8) = False;

hear :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
hear = Channel_Type.ctor_prism Hear_C is_hear_C un_hear_C;

un_leak_C :: Chan -> Dmsg;
un_leak_C (Leak_C x6) = x6;

is_leak_C :: Chan -> Bool;
is_leak_C (Env_C x1) = False;
is_leak_C (Send_C x2) = False;
is_leak_C (Recv_C x3) = False;
is_leak_C (Hear_C x4) = False;
is_leak_C (Fake_C x5) = False;
is_leak_C (Leak_C x6) = True;
is_leak_C (Sig_C x7) = False;
is_leak_C (Terminate_C x8) = False;

leak :: Prisms.Prism_ext Dmsg Chan ();
leak = Channel_Type.ctor_prism Leak_C is_leak_C un_leak_C;

un_recv_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_recv_C (Recv_C x3) = x3;

is_recv_C :: Chan -> Bool;
is_recv_C (Env_C x1) = False;
is_recv_C (Send_C x2) = False;
is_recv_C (Recv_C x3) = True;
is_recv_C (Hear_C x4) = False;
is_recv_C (Fake_C x5) = False;
is_recv_C (Leak_C x6) = False;
is_recv_C (Sig_C x7) = False;
is_recv_C (Terminate_C x8) = False;

recv :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
recv = Channel_Type.ctor_prism Recv_C is_recv_C un_recv_C;

un_send_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_send_C (Send_C x2) = x2;

is_send_C :: Chan -> Bool;
is_send_C (Env_C x1) = False;
is_send_C (Send_C x2) = True;
is_send_C (Recv_C x3) = False;
is_send_C (Hear_C x4) = False;
is_send_C (Fake_C x5) = False;
is_send_C (Leak_C x6) = False;
is_send_C (Sig_C x7) = False;
is_send_C (Terminate_C x8) = False;

send :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
send = Channel_Type.ctor_prism Send_C is_send_C un_send_C;

is_MNon :: Dmsg -> Bool;
is_MNon (MAg x1) = False;
is_MNon (MNon x2) = True;
is_MNon (MKp x3) = False;
is_MNon (MKs x4) = False;
is_MNon (MCmp x51 x52) = False;
is_MNon (MEnc x61 x62) = False;
is_MNon (MSig x71 x72) = False;
is_MNon (MSEnc x81 x82) = False;
is_MNon MExpg = False;
is_MNon (MModExp x101 x102) = False;

extract_nonces :: [Dmsg] -> [Dnonce];
extract_nonces xs =
  List.map_filter (\ x -> (if is_MNon x then Just (mn x) else Nothing)) xs;

mod_exp1a :: [Dmsg] -> [Dmsg];
mod_exp1a xs = mod_exp1 xs (extract_nonces xs);

mod_exp2a :: [Dmsg] -> [Dmsg];
mod_exp2a ns =
  (if List.member ns MExpg then mod_exp2 (extract_nonces ns) else []);

is_MKp :: Dmsg -> Bool;
is_MKp (MAg x1) = False;
is_MKp (MNon x2) = False;
is_MKp (MKp x3) = True;
is_MKp (MKs x4) = False;
is_MKp (MCmp x51 x52) = False;
is_MKp (MEnc x61 x62) = False;
is_MKp (MSig x71 x72) = False;
is_MKp (MSEnc x81 x82) = False;
is_MKp MExpg = False;
is_MKp (MModExp x101 x102) = False;

sig_1 :: [Dmsg] -> [Dskey] -> [Dmsg];
sig_1 [] sks = [];
sig_1 (x : xs) sks =
  (if is_MKs x then sig_1 xs sks else map (MSig x) sks ++ sig_1 xs sks);

allAgentsLst :: [Dmsg];
allAgentsLst = map MAg allAgents;

allNoncesLst :: [Dmsg];
allNoncesLst = map MNon allNonces;

senc_1 :: [Dmsg] -> [Dmsg] -> [Dmsg];
senc_1 [] eks = [];
senc_1 (x : xs) eks =
  (if is_MKs x then senc_1 xs eks else map (MSEnc x) eks ++ senc_1 xs eks);

extract_dskey :: [Dmsg] -> [Dskey];
extract_dskey xs =
  List.map_filter (\ x -> (if is_MKs x then Just (mks x) else Nothing)) xs;

sig_1a :: [Dmsg] -> [Dmsg];
sig_1a xs = sig_1 xs (extract_dskey xs);

is_MModExp :: Dmsg -> Bool;
is_MModExp (MAg x1) = False;
is_MModExp (MNon x2) = False;
is_MModExp (MKp x3) = False;
is_MModExp (MKs x4) = False;
is_MModExp (MCmp x51 x52) = False;
is_MModExp (MEnc x61 x62) = False;
is_MModExp (MSig x71 x72) = False;
is_MModExp (MSEnc x81 x82) = False;
is_MModExp MExpg = False;
is_MModExp (MModExp x101 x102) = True;

senc_1a :: [Dmsg] -> [Dmsg];
senc_1a xs = senc_1 xs (filter is_MModExp xs);

build_n ::
  [Dmsg] -> [Dpkey] -> [Dskey] -> Arith.Nat -> Arith.Nat -> Arith.Nat -> [Dmsg];
build_n xs pks sks nc ne l =
  (if Arith.equal_nat ne Arith.zero_nat
    then (if Arith.equal_nat nc Arith.zero_nat then xs
           else build_n (List.union (pair2 xs xs l) xs) pks sks
                  (Arith.minus_nat nc Arith.one_nat) Arith.zero_nat l)
    else (if Arith.equal_nat nc Arith.zero_nat
           then build_n (List.union (senc_1a xs) xs) pks sks Arith.zero_nat
                  (Arith.minus_nat ne Arith.one_nat) l
           else (if Arith.equal_nat (Arith.minus_nat ne Arith.one_nat)
                      Arith.zero_nat
                  then build_n (List.union (pair2 xs xs l) xs) pks sks
                         (Arith.minus_nat nc Arith.one_nat)
                         (Arith.suc Arith.zero_nat) l
                  else List.union
                         (build_n (List.union (pair2 xs xs l) xs) pks sks
                           (Arith.minus_nat nc Arith.one_nat)
                           (Arith.suc (Arith.minus_nat ne Arith.one_nat)) l)
                         (build_n (List.union (senc_1a xs) xs) pks sks
                           (Arith.suc (Arith.minus_nat nc Arith.one_nat))
                           (Arith.minus_nat ne Arith.one_nat) l))));

extract_dpkey :: [Dmsg] -> [Dpkey];
extract_dpkey xs =
  List.map_filter (\ x -> (if is_MKp x then Just (mkp x) else Nothing)) xs;

un_terminate_C :: Chan -> ();
un_terminate_C (Terminate_C x8) = x8;

is_terminate_C :: Chan -> Bool;
is_terminate_C (Env_C x1) = False;
is_terminate_C (Send_C x2) = False;
is_terminate_C (Recv_C x3) = False;
is_terminate_C (Hear_C x4) = False;
is_terminate_C (Fake_C x5) = False;
is_terminate_C (Leak_C x6) = False;
is_terminate_C (Sig_C x7) = False;
is_terminate_C (Terminate_C x8) = True;

terminate :: Prisms.Prism_ext () Chan ();
terminate = Channel_Type.ctor_prism Terminate_C is_terminate_C un_terminate_C;

build1_n :: [Dmsg] -> Arith.Nat -> Arith.Nat -> Arith.Nat -> [Dmsg];
build1_n ns c e l =
  let {
    xs = mod_exp2a ns;
    ys = mod_exp1a ns;
    zs = List.remdups xs ++ ys ++ ns;
    ss = sig_1a zs;
  } in build_n (zs ++ ss) (extract_dpkey ss) (extract_dskey ss) c e l;

build1_n_0 :: [Dmsg] -> [Dmsg];
build1_n_0 ns = build1_n ns Arith.zero_nat Arith.one_nat Arith.one_nat;

}
