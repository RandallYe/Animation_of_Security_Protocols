{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Sec_Messages(Dagent(..), equal_dagent, Dsig(..), equal_dsig, Dbitmask(..),
                equal_dbitmask, Dkey(..), equal_dkey, Dmsg(..), equal_dmsg,
                Chan(..), equal_chan, last4, pKsLst, sKsLst, submsg_list,
                submsgs_list, less_eq_dbitmask, one_step, step_once,
                iter_closure, breakl, ks, ma, mn, sn, sp, un_env_C, is_env_C,
                env, un_sig_C, is_sig_C, sig, mc1, mc2, mem, pk_of_sk,
                agentsLst, noncesLst, buildable, un_leak_C, is_leak_C, leak,
                un_recv_C, is_recv_C, recv, un_send_C, is_send_C, send,
                un_terminate_C, is_terminate_C, terminate, filter_buildable)
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
import qualified Channel_Type;
import qualified Prisms;
import qualified List;
import qualified Arith;
import qualified Set;
import qualified FSNat;
import qualified Typerep;
import qualified Type_Length;

data Dagent a = Agent (FSNat.Fsnat a) | Intruder | Server
  deriving (Prelude.Read, Prelude.Show);

equal_dagent :: forall a. (Type_Length.Len a) => Dagent a -> Dagent a -> Bool;
equal_dagent Intruder Server = False;
equal_dagent Server Intruder = False;
equal_dagent (Agent x1) Server = False;
equal_dagent Server (Agent x1) = False;
equal_dagent (Agent x1) Intruder = False;
equal_dagent Intruder (Agent x1) = False;
equal_dagent (Agent x1) (Agent y1) = FSNat.equal_fsnat x1 y1;
equal_dagent Server Server = True;
equal_dagent Intruder Intruder = True;

data Dsig a b = ClaimSecret (Dagent a) (FSNat.Fsnat b) (Set.Set (Dagent a))
  | StartProt (Dagent a) (Dagent a) (FSNat.Fsnat b) (FSNat.Fsnat b)
  | EndProt (Dagent a) (Dagent a) (FSNat.Fsnat b) (FSNat.Fsnat b)
  deriving (Prelude.Read, Prelude.Show);

instance (Type_Length.Len a) => Eq (Dagent a) where {
  a == b = equal_dagent a b;
};

equal_dsig ::
  forall a b.
    (Type_Length.Len a, Type_Length.Len b) => Dsig a b -> Dsig a b -> Bool;
equal_dsig (StartProt x21 x22 x23 x24) (EndProt x31 x32 x33 x34) = False;
equal_dsig (EndProt x31 x32 x33 x34) (StartProt x21 x22 x23 x24) = False;
equal_dsig (ClaimSecret x11 x12 x13) (EndProt x31 x32 x33 x34) = False;
equal_dsig (EndProt x31 x32 x33 x34) (ClaimSecret x11 x12 x13) = False;
equal_dsig (ClaimSecret x11 x12 x13) (StartProt x21 x22 x23 x24) = False;
equal_dsig (StartProt x21 x22 x23 x24) (ClaimSecret x11 x12 x13) = False;
equal_dsig (EndProt x31 x32 x33 x34) (EndProt y31 y32 y33 y34) =
  equal_dagent x31 y31 &&
    equal_dagent x32 y32 &&
      FSNat.equal_fsnat x33 y33 && FSNat.equal_fsnat x34 y34;
equal_dsig (StartProt x21 x22 x23 x24) (StartProt y21 y22 y23 y24) =
  equal_dagent x21 y21 &&
    equal_dagent x22 y22 &&
      FSNat.equal_fsnat x23 y23 && FSNat.equal_fsnat x24 y24;
equal_dsig (ClaimSecret x11 x12 x13) (ClaimSecret y11 y12 y13) =
  equal_dagent x11 y11 && FSNat.equal_fsnat x12 y12 && Set.equal_set x13 y13;

data Dbitmask a b = Null | Bm (FSNat.Fsnat a) (FSNat.Fsnat b)
  deriving (Prelude.Read, Prelude.Show);

equal_dbitmask ::
  forall a b.
    (Type_Length.Len a,
      Type_Length.Len b) => Dbitmask a b -> Dbitmask a b -> Bool;
equal_dbitmask Null (Bm x21 x22) = False;
equal_dbitmask (Bm x21 x22) Null = False;
equal_dbitmask (Bm x21 x22) (Bm y21 y22) =
  FSNat.equal_fsnat x21 y21 && FSNat.equal_fsnat x22 y22;
equal_dbitmask Null Null = True;

data Dkey a b = Kp (FSNat.Fsnat a) | Ks (FSNat.Fsnat b)
  deriving (Prelude.Read, Prelude.Show);

equal_dkey ::
  forall a b.
    (Type_Length.Len a, Type_Length.Len b) => Dkey a b -> Dkey a b -> Bool;
equal_dkey (Kp x1) (Ks x2) = False;
equal_dkey (Ks x2) (Kp x1) = False;
equal_dkey (Ks x2) (Ks y2) = FSNat.equal_fsnat x2 y2;
equal_dkey (Kp x1) (Kp y1) = FSNat.equal_fsnat x1 y1;

data Dmsg a b c d e f g = MAg (Dagent a) | MNon (FSNat.Fsnat b) | MK (Dkey c d)
  | MPair (Dmsg a b c d e f g) (Dmsg a b c d e f g)
  | MAEnc (Dmsg a b c d e f g) (Dmsg a b c d e f g)
  | MSig (Dmsg a b c d e f g) (Dmsg a b c d e f g)
  | MSEnc (Dmsg a b c d e f g) (Dmsg a b c d e f g) | MExpg (FSNat.Fsnat e)
  | MModExp (Dmsg a b c d e f g) (Dmsg a b c d e f g) | MBitm (Dbitmask f g)
  | MWat (Dmsg a b c d e f g) (Dmsg a b c d e f g)
  | MJam (Dmsg a b c d e f g) (Dmsg a b c d e f g)
  deriving (Prelude.Read, Prelude.Show);

equal_dmsg ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => Dmsg a b c d e f g -> Dmsg a b c d e f g -> Bool;
equal_dmsg (MWat x111 x112) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MWat x111 x112) = False;
equal_dmsg (MBitm x10) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MBitm x10) = False;
equal_dmsg (MModExp x91 x92) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MModExp x91 x92) = False;
equal_dmsg (MExpg x8) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MExpg x8) = False;
equal_dmsg (MSEnc x71 x72) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MSEnc x71 x72) = False;
equal_dmsg (MSig x61 x62) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MSig x61 x62) = False;
equal_dmsg (MAEnc x51 x52) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MAEnc x51 x52) = False;
equal_dmsg (MPair x41 x42) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MPair x41 x42) = False;
equal_dmsg (MK x3) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MK x3) = False;
equal_dmsg (MK x3) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MK x3) = False;
equal_dmsg (MK x3) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MK x3) = False;
equal_dmsg (MK x3) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MK x3) = False;
equal_dmsg (MK x3) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MK x3) = False;
equal_dmsg (MK x3) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MK x3) = False;
equal_dmsg (MK x3) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MK x3) = False;
equal_dmsg (MK x3) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MK x3) = False;
equal_dmsg (MK x3) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MK x3) = False;
equal_dmsg (MNon x2) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MNon x2) = False;
equal_dmsg (MNon x2) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MNon x2) = False;
equal_dmsg (MNon x2) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MNon x2) = False;
equal_dmsg (MNon x2) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MNon x2) = False;
equal_dmsg (MNon x2) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MNon x2) = False;
equal_dmsg (MNon x2) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MNon x2) = False;
equal_dmsg (MNon x2) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MNon x2) = False;
equal_dmsg (MNon x2) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MNon x2) = False;
equal_dmsg (MNon x2) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MNon x2) = False;
equal_dmsg (MNon x2) (MK x3) = False;
equal_dmsg (MK x3) (MNon x2) = False;
equal_dmsg (MAg x1) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MAg x1) = False;
equal_dmsg (MAg x1) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MAg x1) = False;
equal_dmsg (MAg x1) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MAg x1) = False;
equal_dmsg (MAg x1) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MAg x1) = False;
equal_dmsg (MAg x1) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MAg x1) = False;
equal_dmsg (MAg x1) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MAg x1) = False;
equal_dmsg (MAg x1) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MAg x1) = False;
equal_dmsg (MAg x1) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MAg x1) = False;
equal_dmsg (MAg x1) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MAg x1) = False;
equal_dmsg (MAg x1) (MK x3) = False;
equal_dmsg (MK x3) (MAg x1) = False;
equal_dmsg (MAg x1) (MNon x2) = False;
equal_dmsg (MNon x2) (MAg x1) = False;
equal_dmsg (MJam x121 x122) (MJam y121 y122) =
  equal_dmsg x121 y121 && equal_dmsg x122 y122;
equal_dmsg (MWat x111 x112) (MWat y111 y112) =
  equal_dmsg x111 y111 && equal_dmsg x112 y112;
equal_dmsg (MBitm x10) (MBitm y10) = equal_dbitmask x10 y10;
equal_dmsg (MModExp x91 x92) (MModExp y91 y92) =
  equal_dmsg x91 y91 && equal_dmsg x92 y92;
equal_dmsg (MExpg x8) (MExpg y8) = FSNat.equal_fsnat x8 y8;
equal_dmsg (MSEnc x71 x72) (MSEnc y71 y72) =
  equal_dmsg x71 y71 && equal_dmsg x72 y72;
equal_dmsg (MSig x61 x62) (MSig y61 y62) =
  equal_dmsg x61 y61 && equal_dmsg x62 y62;
equal_dmsg (MAEnc x51 x52) (MAEnc y51 y52) =
  equal_dmsg x51 y51 && equal_dmsg x52 y52;
equal_dmsg (MPair x41 x42) (MPair y41 y42) =
  equal_dmsg x41 y41 && equal_dmsg x42 y42;
equal_dmsg (MK x3) (MK y3) = equal_dkey x3 y3;
equal_dmsg (MNon x2) (MNon y2) = FSNat.equal_fsnat x2 y2;
equal_dmsg (MAg x1) (MAg y1) = equal_dagent x1 y1;

data Chan a b c d e f g = Env_C (Dagent a, Dagent a)
  | Send_C (Dagent a, (Dagent a, (Dagent a, Dmsg a b c d e f g)))
  | Cjam_C (Dmsg a b c d e f g) | Cdejam_C (Dmsg a b c d e f g)
  | Recv_C (Dagent a, (Dagent a, (Dagent a, Dmsg a b c d e f g)))
  | Leak_C (Dmsg a b c d e f g) | Sig_C (Dsig a b) | Terminate_C ()
  deriving (Prelude.Read, Prelude.Show);

instance (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c,
           Type_Length.Len d, Type_Length.Len e, Type_Length.Len f,
           Type_Length.Len g) => Eq (Dmsg a b c d e f g) where {
  a == b = equal_dmsg a b;
};

equal_chan ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Chan a b c d e f g -> Bool;
equal_chan (Sig_C x7) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Sig_C x7) = False;
equal_chan (Leak_C x6) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Leak_C x6) = False;
equal_chan (Recv_C x5) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Recv_C x5) = False;
equal_chan (Cdejam_C x4) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Cdejam_C x4) = False;
equal_chan (Cjam_C x3) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Cjam_C x3) = False;
equal_chan (Send_C x2) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Send_C x2) = False;
equal_chan (Send_C x2) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Send_C x2) = False;
equal_chan (Send_C x2) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Send_C x2) = False;
equal_chan (Send_C x2) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Send_C x2) = False;
equal_chan (Send_C x2) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Send_C x2) = False;
equal_chan (Send_C x2) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Send_C x2) = False;
equal_chan (Env_C x1) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Env_C x1) = False;
equal_chan (Env_C x1) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Env_C x1) = False;
equal_chan (Env_C x1) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Env_C x1) = False;
equal_chan (Env_C x1) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Env_C x1) = False;
equal_chan (Env_C x1) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Env_C x1) = False;
equal_chan (Env_C x1) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Env_C x1) = False;
equal_chan (Env_C x1) (Send_C x2) = False;
equal_chan (Send_C x2) (Env_C x1) = False;
equal_chan (Terminate_C x8) (Terminate_C y8) = x8 == y8;
equal_chan (Sig_C x7) (Sig_C y7) = equal_dsig x7 y7;
equal_chan (Leak_C x6) (Leak_C y6) = equal_dmsg x6 y6;
equal_chan (Recv_C x5) (Recv_C y5) = x5 == y5;
equal_chan (Cdejam_C x4) (Cdejam_C y4) = equal_dmsg x4 y4;
equal_chan (Cjam_C x3) (Cjam_C y3) = equal_dmsg x3 y3;
equal_chan (Send_C x2) (Send_C y2) = x2 == y2;
equal_chan (Env_C x1) (Env_C y1) = x1 == y1;

instance (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b,
           Typerep.Typerep b, Type_Length.Len c, Typerep.Typerep c,
           Type_Length.Len d, Typerep.Typerep d, Type_Length.Len e,
           Typerep.Typerep e, Type_Length.Len f, Typerep.Typerep f,
           Type_Length.Len g,
           Typerep.Typerep g) => Eq (Chan a b c d e f g) where {
  a == b = equal_chan a b;
};

last4 :: forall a b c d. (a, (b, (c, d))) -> d;
last4 x = snd (snd (snd x));

pKsLst ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => [Dkey a b] -> [Dmsg c d a b e f g];
pKsLst pks = map MK pks;

sKsLst ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => [Dkey a b] -> [Dmsg c d a b e f g];
sKsLst sks = map MK sks;

submsg_list ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c c d e f -> [Dmsg a b c c d e f];
submsg_list (MAg a) = [MAg a];
submsg_list (MNon a) = [MNon a];
submsg_list (MK a) = [MK a];
submsg_list (MPair m1 m2) = MPair m1 m2 : submsg_list m1 ++ submsg_list m2;
submsg_list (MAEnc m k) = MAEnc m k : submsg_list m ++ submsg_list k;
submsg_list (MSig m k) = MSig m k : submsg_list m ++ submsg_list k;
submsg_list (MSEnc m k) = MSEnc m k : submsg_list m ++ submsg_list k;
submsg_list (MExpg a) = [MExpg a];
submsg_list (MModExp m k) = MModExp m k : submsg_list m ++ submsg_list k;
submsg_list (MBitm b) = [MBitm b];
submsg_list (MWat m k) = MWat m k : submsg_list m ++ submsg_list k;
submsg_list (MJam m k) = MJam m k : submsg_list m ++ submsg_list k;

submsgs_list ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => [Dmsg a b c c d e f] -> [Dmsg a b c c d e f];
submsgs_list xs = List.remdups (concatMap submsg_list xs);

less_eq_dbitmask ::
  forall a b.
    (Type_Length.Len a,
      Type_Length.Len b) => Dbitmask a b -> Dbitmask a b -> Bool;
less_eq_dbitmask =
  (\ a b ->
    (case a of {
      Null -> True;
      Bm x1 y1 ->
        (case b of {
          Null -> False;
          Bm x2 y2 -> FSNat.equal_fsnat x1 x2 && FSNat.less_eq_fsnat y1 y2;
        });
    }));

one_step ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c c d e f ->
                              Set.Set (Dmsg a b c c d e f) ->
                                [Dmsg a b c c d e f];
one_step m k =
  (case m of {
    MAg _ -> [];
    MNon _ -> [];
    MK _ -> [];
    MPair m1 m2 -> [m1, m2];
    MAEnc _ (MAg _) -> [];
    MAEnc _ (MNon _) -> [];
    MAEnc ma (MK (Kp ka)) -> (if Set.member (MK (Ks ka)) k then [ma] else []);
    MAEnc _ (MK (Ks _)) -> [];
    MAEnc _ (MPair _ _) -> [];
    MAEnc _ (MAEnc _ _) -> [];
    MAEnc _ (MSig _ _) -> [];
    MAEnc _ (MSEnc _ _) -> [];
    MAEnc _ (MExpg _) -> [];
    MAEnc _ (MModExp _ _) -> [];
    MAEnc _ (MBitm _) -> [];
    MAEnc _ (MWat _ _) -> [];
    MAEnc _ (MJam _ _) -> [];
    MSig _ (MAg _) -> [];
    MSig _ (MNon _) -> [];
    MSig _ (MK (Kp _)) -> [];
    MSig ma (MK (Ks ka)) -> (if Set.member (MK (Kp ka)) k then [ma] else []);
    MSig _ (MPair _ _) -> [];
    MSig _ (MAEnc _ _) -> [];
    MSig _ (MSig _ _) -> [];
    MSig _ (MSEnc _ _) -> [];
    MSig _ (MExpg _) -> [];
    MSig _ (MModExp _ _) -> [];
    MSig _ (MBitm _) -> [];
    MSig _ (MWat _ _) -> [];
    MSig _ (MJam _ _) -> [];
    MSEnc _ (MAg _) -> [];
    MSEnc _ (MNon _) -> [];
    MSEnc _ (MK (Kp _)) -> [];
    MSEnc ma (MK (Ks ka)) -> (if Set.member (MK (Ks ka)) k then [ma] else []);
    MSEnc _ (MPair _ _) -> [];
    MSEnc _ (MAEnc _ _) -> [];
    MSEnc _ (MSig _ _) -> [];
    MSEnc _ (MSEnc _ _) -> [];
    MSEnc _ (MExpg _) -> [];
    MSEnc _ (MModExp (MAg _) _) -> [];
    MSEnc _ (MModExp (MNon _) _) -> [];
    MSEnc _ (MModExp (MK _) _) -> [];
    MSEnc _ (MModExp (MPair _ _) _) -> [];
    MSEnc _ (MModExp (MAEnc _ _) _) -> [];
    MSEnc _ (MModExp (MSig _ _) _) -> [];
    MSEnc _ (MModExp (MSEnc _ _) _) -> [];
    MSEnc _ (MModExp (MExpg _) _) -> [];
    MSEnc _ (MModExp (MModExp (MAg _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MNon _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MK _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MPair _ _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MAEnc _ _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MSig _ _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MSEnc _ _) _) _) -> [];
    MSEnc ma (MModExp (MModExp (MExpg gn) a) b) ->
      (if Set.member (MModExp (MExpg gn) a) k && Set.member b k ||
            (Set.member (MModExp (MExpg gn) b) k && Set.member a k ||
              Set.member (MExpg gn) k && Set.member a k && Set.member b k)
        then [ma] else []);
    MSEnc _ (MModExp (MModExp (MModExp _ _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MBitm _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MWat _ _) _) _) -> [];
    MSEnc _ (MModExp (MModExp (MJam _ _) _) _) -> [];
    MSEnc _ (MModExp (MBitm _) _) -> [];
    MSEnc _ (MModExp (MWat _ _) _) -> [];
    MSEnc _ (MModExp (MJam _ _) _) -> [];
    MSEnc _ (MBitm _) -> [];
    MSEnc _ (MWat _ _) -> [];
    MSEnc _ (MJam _ _) -> [];
    MExpg _ -> [];
    MModExp _ _ -> [];
    MBitm _ -> [];
    MWat ma _ -> [ma];
    MJam (MAg _) _ -> [];
    MJam (MNon _) _ -> [];
    MJam (MK _) _ -> [];
    MJam (MPair _ _) _ -> [];
    MJam (MAEnc _ _) _ -> [];
    MJam (MSig _ _) _ -> [];
    MJam (MSEnc _ _) _ -> [];
    MJam (MExpg _) _ -> [];
    MJam (MModExp _ _) _ -> [];
    MJam (MBitm _) _ -> [];
    MJam (MWat _ (MAg _)) _ -> [];
    MJam (MWat _ (MNon _)) _ -> [];
    MJam (MWat _ (MK _)) _ -> [];
    MJam (MWat _ (MPair _ _)) _ -> [];
    MJam (MWat _ (MAEnc _ _)) _ -> [];
    MJam (MWat _ (MSig _ _)) _ -> [];
    MJam (MWat _ (MSEnc _ _)) _ -> [];
    MJam (MWat _ (MExpg _)) _ -> [];
    MJam (MWat _ (MModExp _ _)) _ -> [];
    MJam (MWat _ (MBitm _)) (MAg _) -> [];
    MJam (MWat _ (MBitm _)) (MNon _) -> [];
    MJam (MWat _ (MBitm _)) (MK _) -> [];
    MJam (MWat _ (MBitm _)) (MPair _ _) -> [];
    MJam (MWat _ (MBitm _)) (MAEnc _ _) -> [];
    MJam (MWat _ (MBitm _)) (MSig _ _) -> [];
    MJam (MWat _ (MBitm _)) (MSEnc _ _) -> [];
    MJam (MWat _ (MBitm _)) (MExpg _) -> [];
    MJam (MWat _ (MBitm _)) (MModExp _ _) -> [];
    MJam (MWat ma (MBitm bb)) (MBitm b) ->
      (if equal_dbitmask b Null ||
            less_eq_dbitmask b bb && Set.member (MBitm b) k
        then [ma] else []);
    MJam (MWat _ (MBitm _)) (MWat _ _) -> [];
    MJam (MWat _ (MBitm _)) (MJam _ _) -> [];
    MJam (MWat _ (MWat _ _)) _ -> [];
    MJam (MWat _ (MJam _ _)) _ -> [];
    MJam (MJam _ _) _ -> [];
  });

step_once ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => [Dmsg a b c c d e f] -> [Dmsg a b c c d e f];
step_once k = List.remdups (k ++ concatMap (\ m -> one_step m (Set.Set k)) k);

iter_closure ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Arith.Nat ->
                              [Dmsg a b c c d e f] -> [Dmsg a b c c d e f];
iter_closure n k =
  (if Arith.equal_nat n Arith.zero_nat then k
    else iter_closure (Arith.minus_nat n Arith.one_nat) (step_once k));

breakl ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => [Dmsg a b c c d e f] -> [Dmsg a b c c d e f];
breakl xs =
  iter_closure (Arith.plus_nat (List.size_list (submsgs_list xs)) Arith.one_nat)
    (List.remdups xs);

ks :: forall a b.
        (Type_Length.Len a, Type_Length.Len b) => Dkey a b -> FSNat.Fsnat b;
ks (Ks x2) = x2;

ma :: forall a b c d e f g.
        (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c,
          Type_Length.Len d, Type_Length.Len e, Type_Length.Len f,
          Type_Length.Len g) => Dmsg a b c d e f g -> Dagent a;
ma (MAg x1) = x1;

mn :: forall a b c d e f g.
        (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c,
          Type_Length.Len d, Type_Length.Len e, Type_Length.Len f,
          Type_Length.Len g) => Dmsg a b c d e f g -> FSNat.Fsnat b;
mn (MNon x2) = x2;

sn :: forall a b.
        (Type_Length.Len a, Type_Length.Len b) => Dsig a b -> FSNat.Fsnat b;
sn (ClaimSecret x11 x12 x13) = x12;

sp :: forall a b.
        (Type_Length.Len a,
          Type_Length.Len b) => Dsig a b -> Set.Set (Dagent a);
sp (ClaimSecret x11 x12 x13) = x13;

un_env_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> (Dagent a, Dagent a);
un_env_C (Env_C x1) = x1;

is_env_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Bool;
is_env_C (Env_C x1) = True;
is_env_C (Send_C x2) = False;
is_env_C (Cjam_C x3) = False;
is_env_C (Cdejam_C x4) = False;
is_env_C (Recv_C x5) = False;
is_env_C (Leak_C x6) = False;
is_env_C (Sig_C x7) = False;
is_env_C (Terminate_C x8) = False;

env ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Prisms.Prism_ext (Dagent a, Dagent a)
                              (Chan a b c d e f g) ();
env = Channel_Type.ctor_prism Env_C is_env_C un_env_C;

un_sig_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Dsig a b;
un_sig_C (Sig_C x7) = x7;

is_sig_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Bool;
is_sig_C (Env_C x1) = False;
is_sig_C (Send_C x2) = False;
is_sig_C (Cjam_C x3) = False;
is_sig_C (Cdejam_C x4) = False;
is_sig_C (Recv_C x5) = False;
is_sig_C (Leak_C x6) = False;
is_sig_C (Sig_C x7) = True;
is_sig_C (Terminate_C x8) = False;

sig ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Prisms.Prism_ext (Dsig a b) (Chan a b c d e f g) ();
sig = Channel_Type.ctor_prism Sig_C is_sig_C un_sig_C;

mc1 ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => Dmsg a b c d e f g -> Dmsg a b c d e f g;
mc1 (MPair x41 x42) = x41;

mc2 ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => Dmsg a b c d e f g -> Dmsg a b c d e f g;
mc2 (MPair x41 x42) = x42;

mem ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => Dmsg a b c d e f g -> Dmsg a b c d e f g;
mem (MAEnc x51 x52) = x51;

pk_of_sk ::
  forall a b c.
    (Type_Length.Len a, Type_Length.Len b,
      Type_Length.Len c) => Dkey a b -> Dkey b c;
pk_of_sk pk = Kp (ks pk);

agentsLst ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => [Dagent a] -> [Dmsg a b c d e f g];
agentsLst asa = map MAg asa;

noncesLst ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => [FSNat.Fsnat a] -> [Dmsg b a c d e f g];
noncesLst xs = map MNon xs;

buildable ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => Dmsg a b c d e f g ->
                              Set.Set (Dmsg a b c d e f g) -> Bool;
buildable m ms =
  (if Set.member m ms then True
    else (case m of {
           MAg _ -> False;
           MNon _ -> False;
           MK _ -> False;
           MPair m1 m2 -> buildable m1 ms && buildable m2 ms;
           MAEnc ma k -> buildable ma ms && buildable k ms;
           MSig ma k -> buildable ma ms && buildable k ms;
           MSEnc ma k -> buildable ma ms && buildable k ms;
           MExpg _ -> False;
           MModExp ma k -> buildable ma ms && buildable k ms;
           MBitm _ -> False;
           MWat ma k -> buildable ma ms && buildable k ms;
           MJam _ _ -> False;
         }));

un_leak_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Dmsg a b c d e f g;
un_leak_C (Leak_C x6) = x6;

is_leak_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Bool;
is_leak_C (Env_C x1) = False;
is_leak_C (Send_C x2) = False;
is_leak_C (Cjam_C x3) = False;
is_leak_C (Cdejam_C x4) = False;
is_leak_C (Recv_C x5) = False;
is_leak_C (Leak_C x6) = True;
is_leak_C (Sig_C x7) = False;
is_leak_C (Terminate_C x8) = False;

leak ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Prisms.Prism_ext (Dmsg a b c d e f g)
                              (Chan a b c d e f g) ();
leak = Channel_Type.ctor_prism Leak_C is_leak_C un_leak_C;

un_recv_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g ->
                              (Dagent a,
                                (Dagent a, (Dagent a, Dmsg a b c d e f g)));
un_recv_C (Recv_C x5) = x5;

is_recv_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Bool;
is_recv_C (Env_C x1) = False;
is_recv_C (Send_C x2) = False;
is_recv_C (Cjam_C x3) = False;
is_recv_C (Cdejam_C x4) = False;
is_recv_C (Recv_C x5) = True;
is_recv_C (Leak_C x6) = False;
is_recv_C (Sig_C x7) = False;
is_recv_C (Terminate_C x8) = False;

recv ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Prisms.Prism_ext
                              (Dagent a,
                                (Dagent a, (Dagent a, Dmsg a b c d e f g)))
                              (Chan a b c d e f g) ();
recv = Channel_Type.ctor_prism Recv_C is_recv_C un_recv_C;

un_send_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g ->
                              (Dagent a,
                                (Dagent a, (Dagent a, Dmsg a b c d e f g)));
un_send_C (Send_C x2) = x2;

is_send_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Bool;
is_send_C (Env_C x1) = False;
is_send_C (Send_C x2) = True;
is_send_C (Cjam_C x3) = False;
is_send_C (Cdejam_C x4) = False;
is_send_C (Recv_C x5) = False;
is_send_C (Leak_C x6) = False;
is_send_C (Sig_C x7) = False;
is_send_C (Terminate_C x8) = False;

send ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Prisms.Prism_ext
                              (Dagent a,
                                (Dagent a, (Dagent a, Dmsg a b c d e f g)))
                              (Chan a b c d e f g) ();
send = Channel_Type.ctor_prism Send_C is_send_C un_send_C;

un_terminate_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> ();
un_terminate_C (Terminate_C x8) = x8;

is_terminate_C ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Chan a b c d e f g -> Bool;
is_terminate_C (Env_C x1) = False;
is_terminate_C (Send_C x2) = False;
is_terminate_C (Cjam_C x3) = False;
is_terminate_C (Cdejam_C x4) = False;
is_terminate_C (Recv_C x5) = False;
is_terminate_C (Leak_C x6) = False;
is_terminate_C (Sig_C x7) = False;
is_terminate_C (Terminate_C x8) = True;

terminate ::
  forall a b c d e f g.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f, Type_Length.Len g,
      Typerep.Typerep g) => Prisms.Prism_ext () (Chan a b c d e f g) ();
terminate = Channel_Type.ctor_prism Terminate_C is_terminate_C un_terminate_C;

filter_buildable ::
  forall a b c d e f g.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f,
      Type_Length.Len g) => [Dmsg a b c d e f g] ->
                              Set.Set (Dmsg a b c d e f g) ->
                                [Dmsg a b c d e f g];
filter_buildable xs ms =
  concatMap (\ x -> (if buildable x ms then [x] else [])) xs;

}
