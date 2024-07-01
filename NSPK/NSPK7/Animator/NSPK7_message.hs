{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  NSPK7_message(Dagent(..), equal_dagent, Dnonce(..), equal_dnonce, Dsig(..),
                 equal_dsig, Dskey(..), equal_dskey, Dpkey(..), equal_dpkey,
                 Dmsg(..), equal_dmsg, Chan(..), equal_Chan, Dkey(..),
                 equal_dkey, atomic, dupl, is_MKs, length, pair2, enum_dagent,
                 enum_dpkey, allPKs, mks, extract_dskey, extract_dkeys,
                 break_sk, breakm, ma, mn, sn, sp, un_env_C, is_env_C, env,
                 un_sig_C, is_sig_C, sig, mc1, mc2, mem, mkp, msd, allAgents,
                 enum_dnonce, allNonces, allPKsLst, un_fake_C, is_fake_C, fake,
                 un_hear_C, is_hear_C, hear, un_leak_C, is_leak_C, leak,
                 un_recv_C, is_recv_C, recv, un_send_C, is_send_C, send, is_MKp,
                 enc_1, allAgentsLst, allNoncesLst, build_n, extract_dpkey,
                 un_terminate_C, is_terminate_C, terminate, build_n_1,
                 un_recv_s_C, is_recv_s_C, recv_s, un_send_s_C, is_send_s_C,
                 send_s)
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
import qualified List;
import qualified Set;

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
  | MEnc Dmsg Dpkey | MSig Dmsg Dskey deriving (Prelude.Read, Prelude.Show);

equal_dmsg :: Dmsg -> Dmsg -> Bool;
equal_dmsg (MEnc x61 x62) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MEnc x61 x62) = False;
equal_dmsg (MCmp x51 x52) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MCmp x51 x52) = False;
equal_dmsg (MKs x4) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MKs x4) = False;
equal_dmsg (MKs x4) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MKs x4) = False;
equal_dmsg (MKs x4) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MKs x4) = False;
equal_dmsg (MKp x3) (MSig x71 x72) = False;
equal_dmsg (MSig x71 x72) (MKp x3) = False;
equal_dmsg (MKp x3) (MEnc x61 x62) = False;
equal_dmsg (MEnc x61 x62) (MKp x3) = False;
equal_dmsg (MKp x3) (MCmp x51 x52) = False;
equal_dmsg (MCmp x51 x52) (MKp x3) = False;
equal_dmsg (MKp x3) (MKs x4) = False;
equal_dmsg (MKs x4) (MKp x3) = False;
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

data Chan = Env_C (Dagent, Dagent) | Send_C (Dagent, (Dagent, Dmsg))
  | Recv_C (Dagent, (Dagent, Dmsg)) | Send_s_C (Dagent, (Dagent, Dmsg))
  | Recv_s_C (Dagent, (Dagent, Dmsg)) | Hear_C (Dagent, (Dagent, Dmsg))
  | Fake_C (Dagent, (Dagent, Dmsg)) | Leak_C Dmsg | Sig_C Dsig | Terminate_C ()
  deriving (Prelude.Read, Prelude.Show);

instance Eq Dmsg where {
  a == b = equal_dmsg a b;
};

equal_Chan :: Chan -> Chan -> Bool;
equal_Chan (Sig_C x9) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Sig_C x9) = False;
equal_Chan (Leak_C x8) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Leak_C x8) = False;
equal_Chan (Leak_C x8) (Sig_C x9) = False;
equal_Chan (Sig_C x9) (Leak_C x8) = False;
equal_Chan (Fake_C x7) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Fake_C x7) = False;
equal_Chan (Fake_C x7) (Sig_C x9) = False;
equal_Chan (Sig_C x9) (Fake_C x7) = False;
equal_Chan (Fake_C x7) (Leak_C x8) = False;
equal_Chan (Leak_C x8) (Fake_C x7) = False;
equal_Chan (Hear_C x6) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Hear_C x6) = False;
equal_Chan (Hear_C x6) (Sig_C x9) = False;
equal_Chan (Sig_C x9) (Hear_C x6) = False;
equal_Chan (Hear_C x6) (Leak_C x8) = False;
equal_Chan (Leak_C x8) (Hear_C x6) = False;
equal_Chan (Hear_C x6) (Fake_C x7) = False;
equal_Chan (Fake_C x7) (Hear_C x6) = False;
equal_Chan (Recv_s_C x5) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Recv_s_C x5) = False;
equal_Chan (Recv_s_C x5) (Sig_C x9) = False;
equal_Chan (Sig_C x9) (Recv_s_C x5) = False;
equal_Chan (Recv_s_C x5) (Leak_C x8) = False;
equal_Chan (Leak_C x8) (Recv_s_C x5) = False;
equal_Chan (Recv_s_C x5) (Fake_C x7) = False;
equal_Chan (Fake_C x7) (Recv_s_C x5) = False;
equal_Chan (Recv_s_C x5) (Hear_C x6) = False;
equal_Chan (Hear_C x6) (Recv_s_C x5) = False;
equal_Chan (Send_s_C x4) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Send_s_C x4) = False;
equal_Chan (Send_s_C x4) (Sig_C x9) = False;
equal_Chan (Sig_C x9) (Send_s_C x4) = False;
equal_Chan (Send_s_C x4) (Leak_C x8) = False;
equal_Chan (Leak_C x8) (Send_s_C x4) = False;
equal_Chan (Send_s_C x4) (Fake_C x7) = False;
equal_Chan (Fake_C x7) (Send_s_C x4) = False;
equal_Chan (Send_s_C x4) (Hear_C x6) = False;
equal_Chan (Hear_C x6) (Send_s_C x4) = False;
equal_Chan (Send_s_C x4) (Recv_s_C x5) = False;
equal_Chan (Recv_s_C x5) (Send_s_C x4) = False;
equal_Chan (Recv_C x3) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Sig_C x9) = False;
equal_Chan (Sig_C x9) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Leak_C x8) = False;
equal_Chan (Leak_C x8) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Fake_C x7) = False;
equal_Chan (Fake_C x7) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Hear_C x6) = False;
equal_Chan (Hear_C x6) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Recv_s_C x5) = False;
equal_Chan (Recv_s_C x5) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Send_s_C x4) = False;
equal_Chan (Send_s_C x4) (Recv_C x3) = False;
equal_Chan (Send_C x2) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Send_C x2) = False;
equal_Chan (Send_C x2) (Sig_C x9) = False;
equal_Chan (Sig_C x9) (Send_C x2) = False;
equal_Chan (Send_C x2) (Leak_C x8) = False;
equal_Chan (Leak_C x8) (Send_C x2) = False;
equal_Chan (Send_C x2) (Fake_C x7) = False;
equal_Chan (Fake_C x7) (Send_C x2) = False;
equal_Chan (Send_C x2) (Hear_C x6) = False;
equal_Chan (Hear_C x6) (Send_C x2) = False;
equal_Chan (Send_C x2) (Recv_s_C x5) = False;
equal_Chan (Recv_s_C x5) (Send_C x2) = False;
equal_Chan (Send_C x2) (Send_s_C x4) = False;
equal_Chan (Send_s_C x4) (Send_C x2) = False;
equal_Chan (Send_C x2) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Send_C x2) = False;
equal_Chan (Env_C x1) (Terminate_C x10) = False;
equal_Chan (Terminate_C x10) (Env_C x1) = False;
equal_Chan (Env_C x1) (Sig_C x9) = False;
equal_Chan (Sig_C x9) (Env_C x1) = False;
equal_Chan (Env_C x1) (Leak_C x8) = False;
equal_Chan (Leak_C x8) (Env_C x1) = False;
equal_Chan (Env_C x1) (Fake_C x7) = False;
equal_Chan (Fake_C x7) (Env_C x1) = False;
equal_Chan (Env_C x1) (Hear_C x6) = False;
equal_Chan (Hear_C x6) (Env_C x1) = False;
equal_Chan (Env_C x1) (Recv_s_C x5) = False;
equal_Chan (Recv_s_C x5) (Env_C x1) = False;
equal_Chan (Env_C x1) (Send_s_C x4) = False;
equal_Chan (Send_s_C x4) (Env_C x1) = False;
equal_Chan (Env_C x1) (Recv_C x3) = False;
equal_Chan (Recv_C x3) (Env_C x1) = False;
equal_Chan (Env_C x1) (Send_C x2) = False;
equal_Chan (Send_C x2) (Env_C x1) = False;
equal_Chan (Terminate_C x10) (Terminate_C y10) = x10 == y10;
equal_Chan (Sig_C x9) (Sig_C y9) = equal_dsig x9 y9;
equal_Chan (Leak_C x8) (Leak_C y8) = equal_dmsg x8 y8;
equal_Chan (Fake_C x7) (Fake_C y7) = x7 == y7;
equal_Chan (Hear_C x6) (Hear_C y6) = x6 == y6;
equal_Chan (Recv_s_C x5) (Recv_s_C y5) = x5 == y5;
equal_Chan (Send_s_C x4) (Send_s_C y4) = x4 == y4;
equal_Chan (Recv_C x3) (Recv_C y3) = x3 == y3;
equal_Chan (Send_C x2) (Send_C y2) = x2 == y2;
equal_Chan (Env_C x1) (Env_C y1) = x1 == y1;

instance Eq Chan where {
  a == b = equal_Chan a b;
};

data Dkey = Kp Dpkey | Ks Dskey deriving (Prelude.Read, Prelude.Show);

equal_dkey :: Dkey -> Dkey -> Bool;
equal_dkey (Kp x1) (Ks x2) = False;
equal_dkey (Ks x2) (Kp x1) = False;
equal_dkey (Ks x2) (Ks y2) = equal_dskey x2 y2;
equal_dkey (Kp x1) (Kp y1) = equal_dpkey x1 y1;

instance Eq Dkey where {
  a == b = equal_dkey a b;
};

instance Eq Dnonce where {
  a == b = equal_dnonce a b;
};

atomic :: Dmsg -> [Dmsg];
atomic (MAg m) = [MAg m];
atomic (MNon m) = [MNon m];
atomic (MKp m) = [MKp m];
atomic (MKs m) = [MKs m];
atomic (MCmp m1 m2) = List.union (atomic m1) (atomic m2);
atomic (MEnc m k) = atomic m;
atomic (MSig m k) = atomic m;

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

is_MKs :: Dmsg -> Bool;
is_MKs (MAg x1) = False;
is_MKs (MNon x2) = False;
is_MKs (MKp x3) = False;
is_MKs (MKs x4) = True;
is_MKs (MCmp x51 x52) = False;
is_MKs (MEnc x61 x62) = False;
is_MKs (MSig x71 x72) = False;

length :: Dmsg -> Arith.Nat;
length (MAg uu) = Arith.one_nat;
length (MNon uv) = Arith.one_nat;
length (MKp uw) = Arith.one_nat;
length (MKs ux) = Arith.one_nat;
length (MCmp m1 m2) = Arith.plus_nat (length m1) (length m2);
length (MEnc m k) = length m;
length (MSig m k) = length m;

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
             then Just (MCmp x xa) else Nothing))
         ys ++
         a;

enum_dagent :: [Dagent];
enum_dagent = [Alice, Bob, Intruder, Server];

enum_dpkey :: [Dpkey];
enum_dpkey = map PK enum_dagent;

allPKs :: [Dpkey];
allPKs = enum_dpkey;

mks :: Dmsg -> Dskey;
mks (MKs x4) = x4;

extract_dskey :: [Dmsg] -> [Dskey];
extract_dskey xs =
  List.map_filter (\ x -> (if is_MKs x then Just (mks x) else Nothing)) xs;

extract_dkeys :: [Dmsg] -> [Dkey];
extract_dkeys xs = map Ks (extract_dskey xs);

break_sk :: [Dmsg] -> Set.Set Dkey -> [Dmsg];
break_sk [] sks = [];
break_sk (MKp k : xs) sks = List.insert (MKp k) (break_sk xs sks);
break_sk (MKs k : xs) sks = List.insert (MKs k) (break_sk xs sks);
break_sk (MAg a : xs) sks = List.insert (MAg a) (break_sk xs sks);
break_sk (MNon a : xs) sks = List.insert (MNon a) (break_sk xs sks);
break_sk (MCmp a b : xs) sks =
  List.remdups (break_sk [a] sks ++ break_sk [b] sks ++ break_sk xs sks);
break_sk (MEnc a (PK k) : xs) sks =
  (if Set.member (Ks (SK k)) sks
    then List.insert (MEnc a (PK k))
           (List.remdups (break_sk [a] sks ++ break_sk xs sks))
    else List.insert (MEnc a (PK k)) (break_sk xs sks));
break_sk (MSig a (SK k) : xs) sks =
  (if Set.member (Kp (PK k)) sks
    then List.insert (MSig a (SK k))
           (List.remdups (break_sk [a] sks ++ break_sk xs sks))
    else List.insert (MSig a (SK k)) (break_sk xs sks));

breakm :: [Dmsg] -> [Dmsg];
breakm xs = break_sk xs (Set.Set (extract_dkeys xs));

ma :: Dmsg -> Dagent;
ma (MAg x1) = x1;

mn :: Dmsg -> Dnonce;
mn (MNon x2) = x2;

sn :: Dsig -> Dnonce;
sn (ClaimSecret x11 x12 x13) = x12;

sp :: Dsig -> Set.Set Dagent;
sp (ClaimSecret x11 x12 x13) = x13;

un_env_C :: Chan -> (Dagent, Dagent);
un_env_C (Env_C x1) = x1;

is_env_C :: Chan -> Bool;
is_env_C (Env_C x1) = True;
is_env_C (Send_C x2) = False;
is_env_C (Recv_C x3) = False;
is_env_C (Send_s_C x4) = False;
is_env_C (Recv_s_C x5) = False;
is_env_C (Hear_C x6) = False;
is_env_C (Fake_C x7) = False;
is_env_C (Leak_C x8) = False;
is_env_C (Sig_C x9) = False;
is_env_C (Terminate_C x10) = False;

env :: Prisms.Prism_ext (Dagent, Dagent) Chan ();
env = Channel_Type.ctor_prism Env_C is_env_C un_env_C;

un_sig_C :: Chan -> Dsig;
un_sig_C (Sig_C x9) = x9;

is_sig_C :: Chan -> Bool;
is_sig_C (Env_C x1) = False;
is_sig_C (Send_C x2) = False;
is_sig_C (Recv_C x3) = False;
is_sig_C (Send_s_C x4) = False;
is_sig_C (Recv_s_C x5) = False;
is_sig_C (Hear_C x6) = False;
is_sig_C (Fake_C x7) = False;
is_sig_C (Leak_C x8) = False;
is_sig_C (Sig_C x9) = True;
is_sig_C (Terminate_C x10) = False;

sig :: Prisms.Prism_ext Dsig Chan ();
sig = Channel_Type.ctor_prism Sig_C is_sig_C un_sig_C;

mc1 :: Dmsg -> Dmsg;
mc1 (MCmp x51 x52) = x51;

mc2 :: Dmsg -> Dmsg;
mc2 (MCmp x51 x52) = x52;

mem :: Dmsg -> Dmsg;
mem (MEnc x61 x62) = x61;

mkp :: Dmsg -> Dpkey;
mkp (MKp x3) = x3;

msd :: Dmsg -> Dmsg;
msd (MSig x71 x72) = x71;

allAgents :: [Dagent];
allAgents = enum_dagent;

enum_dnonce :: [Dnonce];
enum_dnonce = map N enum_dagent;

allNonces :: [Dnonce];
allNonces = enum_dnonce;

allPKsLst :: [Dmsg];
allPKsLst = map MKp allPKs;

un_fake_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_fake_C (Fake_C x7) = x7;

is_fake_C :: Chan -> Bool;
is_fake_C (Env_C x1) = False;
is_fake_C (Send_C x2) = False;
is_fake_C (Recv_C x3) = False;
is_fake_C (Send_s_C x4) = False;
is_fake_C (Recv_s_C x5) = False;
is_fake_C (Hear_C x6) = False;
is_fake_C (Fake_C x7) = True;
is_fake_C (Leak_C x8) = False;
is_fake_C (Sig_C x9) = False;
is_fake_C (Terminate_C x10) = False;

fake :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
fake = Channel_Type.ctor_prism Fake_C is_fake_C un_fake_C;

un_hear_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_hear_C (Hear_C x6) = x6;

is_hear_C :: Chan -> Bool;
is_hear_C (Env_C x1) = False;
is_hear_C (Send_C x2) = False;
is_hear_C (Recv_C x3) = False;
is_hear_C (Send_s_C x4) = False;
is_hear_C (Recv_s_C x5) = False;
is_hear_C (Hear_C x6) = True;
is_hear_C (Fake_C x7) = False;
is_hear_C (Leak_C x8) = False;
is_hear_C (Sig_C x9) = False;
is_hear_C (Terminate_C x10) = False;

hear :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
hear = Channel_Type.ctor_prism Hear_C is_hear_C un_hear_C;

un_leak_C :: Chan -> Dmsg;
un_leak_C (Leak_C x8) = x8;

is_leak_C :: Chan -> Bool;
is_leak_C (Env_C x1) = False;
is_leak_C (Send_C x2) = False;
is_leak_C (Recv_C x3) = False;
is_leak_C (Send_s_C x4) = False;
is_leak_C (Recv_s_C x5) = False;
is_leak_C (Hear_C x6) = False;
is_leak_C (Fake_C x7) = False;
is_leak_C (Leak_C x8) = True;
is_leak_C (Sig_C x9) = False;
is_leak_C (Terminate_C x10) = False;

leak :: Prisms.Prism_ext Dmsg Chan ();
leak = Channel_Type.ctor_prism Leak_C is_leak_C un_leak_C;

un_recv_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_recv_C (Recv_C x3) = x3;

is_recv_C :: Chan -> Bool;
is_recv_C (Env_C x1) = False;
is_recv_C (Send_C x2) = False;
is_recv_C (Recv_C x3) = True;
is_recv_C (Send_s_C x4) = False;
is_recv_C (Recv_s_C x5) = False;
is_recv_C (Hear_C x6) = False;
is_recv_C (Fake_C x7) = False;
is_recv_C (Leak_C x8) = False;
is_recv_C (Sig_C x9) = False;
is_recv_C (Terminate_C x10) = False;

recv :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
recv = Channel_Type.ctor_prism Recv_C is_recv_C un_recv_C;

un_send_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_send_C (Send_C x2) = x2;

is_send_C :: Chan -> Bool;
is_send_C (Env_C x1) = False;
is_send_C (Send_C x2) = True;
is_send_C (Recv_C x3) = False;
is_send_C (Send_s_C x4) = False;
is_send_C (Recv_s_C x5) = False;
is_send_C (Hear_C x6) = False;
is_send_C (Fake_C x7) = False;
is_send_C (Leak_C x8) = False;
is_send_C (Sig_C x9) = False;
is_send_C (Terminate_C x10) = False;

send :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
send = Channel_Type.ctor_prism Send_C is_send_C un_send_C;

is_MKp :: Dmsg -> Bool;
is_MKp (MAg x1) = False;
is_MKp (MNon x2) = False;
is_MKp (MKp x3) = True;
is_MKp (MKs x4) = False;
is_MKp (MCmp x51 x52) = False;
is_MKp (MEnc x61 x62) = False;
is_MKp (MSig x71 x72) = False;

enc_1 :: [Dmsg] -> [Dpkey] -> [Dmsg];
enc_1 [] pks = [];
enc_1 (x : xs) pks =
  (if is_MKs x then enc_1 xs pks else map (MEnc x) pks ++ enc_1 xs pks);

allAgentsLst :: [Dmsg];
allAgentsLst = map MAg allAgents;

allNoncesLst :: [Dmsg];
allNoncesLst = map MNon allNonces;

build_n ::
  [Dmsg] -> [Dpkey] -> [Dskey] -> Arith.Nat -> Arith.Nat -> Arith.Nat -> [Dmsg];
build_n xs pks sks nc ne l =
  (if Arith.equal_nat ne Arith.zero_nat
    then (if Arith.equal_nat nc Arith.zero_nat then xs
           else build_n (List.union (pair2 xs xs l) xs) pks sks
                  (Arith.minus_nat nc Arith.one_nat) Arith.zero_nat l)
    else (if Arith.equal_nat nc Arith.zero_nat
           then build_n (List.union (enc_1 xs pks) xs) pks sks Arith.zero_nat
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
                         (build_n (List.union (enc_1 xs pks) xs) pks sks
                           (Arith.suc (Arith.minus_nat nc Arith.one_nat))
                           (Arith.minus_nat ne Arith.one_nat) l))));

extract_dpkey :: [Dmsg] -> [Dpkey];
extract_dpkey xs =
  List.map_filter (\ x -> (if is_MKp x then Just (mkp x) else Nothing)) xs;

un_terminate_C :: Chan -> ();
un_terminate_C (Terminate_C x10) = x10;

is_terminate_C :: Chan -> Bool;
is_terminate_C (Env_C x1) = False;
is_terminate_C (Send_C x2) = False;
is_terminate_C (Recv_C x3) = False;
is_terminate_C (Send_s_C x4) = False;
is_terminate_C (Recv_s_C x5) = False;
is_terminate_C (Hear_C x6) = False;
is_terminate_C (Fake_C x7) = False;
is_terminate_C (Leak_C x8) = False;
is_terminate_C (Sig_C x9) = False;
is_terminate_C (Terminate_C x10) = True;

terminate :: Prisms.Prism_ext () Chan ();
terminate = Channel_Type.ctor_prism Terminate_C is_terminate_C un_terminate_C;

build_n_1 :: [Dmsg] -> [Dmsg];
build_n_1 ns =
  build_n ns (extract_dpkey ns) (extract_dskey ns) Arith.one_nat Arith.one_nat
    (Arith.nat_of_integer (3 :: Integer));

un_recv_s_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_recv_s_C (Recv_s_C x5) = x5;

is_recv_s_C :: Chan -> Bool;
is_recv_s_C (Env_C x1) = False;
is_recv_s_C (Send_C x2) = False;
is_recv_s_C (Recv_C x3) = False;
is_recv_s_C (Send_s_C x4) = False;
is_recv_s_C (Recv_s_C x5) = True;
is_recv_s_C (Hear_C x6) = False;
is_recv_s_C (Fake_C x7) = False;
is_recv_s_C (Leak_C x8) = False;
is_recv_s_C (Sig_C x9) = False;
is_recv_s_C (Terminate_C x10) = False;

recv_s :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
recv_s = Channel_Type.ctor_prism Recv_s_C is_recv_s_C un_recv_s_C;

un_send_s_C :: Chan -> (Dagent, (Dagent, Dmsg));
un_send_s_C (Send_s_C x4) = x4;

is_send_s_C :: Chan -> Bool;
is_send_s_C (Env_C x1) = False;
is_send_s_C (Send_C x2) = False;
is_send_s_C (Recv_C x3) = False;
is_send_s_C (Send_s_C x4) = True;
is_send_s_C (Recv_s_C x5) = False;
is_send_s_C (Hear_C x6) = False;
is_send_s_C (Fake_C x7) = False;
is_send_s_C (Leak_C x8) = False;
is_send_s_C (Sig_C x9) = False;
is_send_s_C (Terminate_C x10) = False;

send_s :: Prisms.Prism_ext (Dagent, (Dagent, Dmsg)) Chan ();
send_s = Channel_Type.ctor_prism Send_s_C is_send_s_C un_send_s_C;

}
