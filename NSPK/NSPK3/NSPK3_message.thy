section \<open> Modelling, verification, and animation of security protocols \<close>
theory NSPK3_message
  imports "../../CSP_operators"
begin

unbundle Z_Relation_Syntax

subsection \<open> General definitions \<close>

subsection \<open> Data types \<close>
datatype dagent = Alice | Bob | Intruder

instantiation dagent :: enum
begin
definition enum_dagent :: "dagent list" where
"enum_dagent = [Alice, Bob, Intruder]"

definition enum_all_dagent :: "(dagent \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dagent P = (\<forall>b :: dagent \<in> set enum_class.enum. P b)"

definition enum_ex_dagent :: "(dagent \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dagent P = (\<exists>b ::  dagent \<in> set enum_class.enum. P b)"

instance
  apply (intro_classes)
  prefer 2
  apply (simp_all add: enum_dagent_def)+
  using dagent.exhaust apply blast
  apply (simp_all add: enum_dagent_def enum_all_dagent_def enum_ex_dagent_def)
  by (metis dagent.exhaust)+
end

datatype dnonce = N dagent
value "map N (enum_class.enum::dagent list)"

find_theorems name:"dagent*"
instantiation dnonce :: enum
begin
definition enum_dnonce :: "dnonce list" where
"enum_dnonce = map N (enum_class.enum::dagent list)"

definition enum_all_dnonce :: "(dnonce \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dnonce P = (\<forall>b :: dnonce \<in> set enum_class.enum. P b)"

definition enum_ex_dnonce :: "(dnonce \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dnonce P = (\<exists>b ::  dnonce \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: dnonce list)"
    apply (simp add: enum_dnonce_def)
    apply (simp add: distinct_map, auto)
    apply (simp add: enum_dagent_def)
    using inj_on_def by auto
  
  show univ_eq:  "UNIV = set (enum_class.enum :: dnonce list)"
    apply (simp add: enum_dnonce_def)
    apply (auto simp add: enum_UNIV)
    by (metis dnonce.exhaust rangeI)

  fix P :: "dnonce \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_dnonce_def enum_ex_dnonce_def)
qed
end

datatype dpkey = PK dagent 
datatype dskey = SK dagent
datatype dkey = Kp dpkey | Ks dskey

instantiation dpkey :: enum
begin
definition enum_dpkey :: "dpkey list" where
"enum_dpkey = map PK (enum_class.enum::dagent list)"

definition enum_all_dpkey :: "(dpkey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dpkey P = (\<forall>b :: dpkey \<in> set enum_class.enum. P b)"

definition enum_ex_dpkey :: "(dpkey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dpkey P = (\<exists>b ::  dpkey \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: dpkey list)"
    apply (simp add: enum_dpkey_def)
    apply (simp add: distinct_map, auto)
    apply (simp add: enum_dagent_def)
    using inj_on_def by auto
  
  show univ_eq:  "UNIV = set (enum_class.enum :: dpkey list)"
    apply (simp add: enum_dpkey_def)
    apply (auto simp add: enum_UNIV)
    by (metis dpkey.exhaust rangeI)

  fix P :: "dpkey \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_dpkey_def enum_ex_dpkey_def)
qed
end

instantiation dskey :: enum
begin
definition enum_dskey :: "dskey list" where
"enum_dskey = map SK (enum_class.enum::dagent list)"

definition enum_all_dskey :: "(dskey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dskey P = (\<forall>b :: dskey \<in> set enum_class.enum. P b)"

definition enum_ex_dskey :: "(dskey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dskey P = (\<exists>b ::  dskey \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: dskey list)"
    apply (simp add: enum_dskey_def)
    apply (simp add: distinct_map, auto)
    apply (simp add: enum_dagent_def)
    using inj_on_def by auto
  
  show univ_eq:  "UNIV = set (enum_class.enum :: dskey list)"
    apply (simp add: enum_dskey_def)
    apply (auto simp add: enum_UNIV)
    by (metis dskey.exhaust rangeI)

  fix P :: "dskey \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_dskey_def enum_ex_dskey_def)
qed
end

instantiation dkey :: enum
begin
definition enum_dkey :: "dkey list" where
"enum_dkey = map Kp (enum_class.enum::dpkey list) @ map Ks (enum_class.enum::dskey list)"

definition enum_all_dkey :: "(dkey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dkey P = (\<forall>b :: dkey \<in> set enum_class.enum. P b)"

definition enum_ex_dkey :: "(dkey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dkey P = (\<exists>b ::  dkey \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: dkey list)"
    apply (simp add: enum_dkey_def)
    apply (simp add: distinct_map, auto)
    apply (simp_all add: enum_dkey_def enum_dskey_def enum_dpkey_def)
    apply (simp_all add: distinct_map, auto)
    by (simp_all add: enum_dagent_def)    
  
  show univ_eq:  "UNIV = set (enum_class.enum :: dkey list)"
    apply (simp add: enum_dkey_def)
    apply (auto simp add: enum_UNIV)
    by (metis dkey.exhaust rangeI)

  fix P :: "dkey \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_dkey_def enum_ex_dkey_def)
qed
end

value "(enum_class.enum::dkey list)"

datatype dmsg = MAg (ma:dagent) 
  | MNon (mn:dnonce) 
  | MKp (mkp:dpkey)
  | MKs (mks:dskey)
  | MCmp (mc1:dmsg) (mc2:dmsg)
  | MEnc (mem:dmsg) (mek:dpkey)

text\<open>Concrete syntax for dmsg \<close>
syntax
  "_CompMsg" :: "['a, args] \<Rightarrow> 'a * 'b"  ("(2\<lbrace>_,/ _\<rbrace>\<^sub>m)")
  "_EncryptMsg" :: "['a, 'a] \<Rightarrow> 'a"      ("(2{_}\<^bsub>_\<^esub>)")
translations
  "\<lbrace>w, x, y, z\<rbrace>\<^sub>m" \<rightleftharpoons> "\<lbrace>w, \<lbrace>x, \<lbrace>y, z\<rbrace>\<^sub>m\<rbrace>\<^sub>m\<rbrace>\<^sub>m"
  "\<lbrace>x, y, z\<rbrace>\<^sub>m" \<rightleftharpoons> "\<lbrace>x, \<lbrace>y, z\<rbrace>\<^sub>m\<rbrace>\<^sub>m"
  "\<lbrace>x, y\<rbrace>\<^sub>m" \<rightleftharpoons> "CONST MCmp x y"
  "{m}\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MEnc m k"

value "{MNon (N Alice)}\<^bsub>PK Alice\<^esub>"
value "\<lbrace>MNon (N Alice), MKp (PK Bob)\<rbrace>\<^sub>m"

definition "AllAgents = ((enum_class.enum:: (dagent) list))"
definition "AllAgentMsgs = MAg ` (set AllAgents)"
definition "AllAgentsLst = map MAg AllAgents"

definition "isPK k = (\<exists>x. PK x = k)"
definition "AllPKs = (enum_class.enum:: (dpkey) list)"
definition "AllPKMsgs = MKp ` (set AllPKs)"
definition "AllPKsLst = map MKp AllPKs"
value "AllPKs"
value "AllPKsLst"

definition "isSK k = (\<exists>x. SK x = k)"
definition "AllSKs = (enum_class.enum:: (dskey) list)"
definition "AllSKMsgs = MKs ` (set AllSKs)"
definition "AllSKsLst = map MKs AllSKs"
value "AllSKsData"

definition "AllNonces = (enum_class.enum:: (dnonce) list)"
definition "AllNonceMsgs = MNon ` (set AllNonces)"
definition "AllNoncesLst = map MNon AllNonces"
value "AllNoncesData"

fun length:: "dmsg \<Rightarrow> nat" where 
"length (MAg _) = 1" |
"length (MNon _) = 1" |
"length (MKp _) = 1" |
"length (MKs _) = 1" |
"length (MCmp m1 m2) = length m1 + length m2" |
"length (MEnc m k) = length m"

fun atomic :: "dmsg \<Rightarrow> dmsg list" where
"atomic (MAg m) = [(MAg m)]" |
"atomic (MNon m) = [(MNon m)]" |
"atomic (MKp m) = [(MKp m)]" |
"atomic (MKs m) = [(MKs m)]" |
"atomic (MCmp m1 m2) = List.union (atomic m1) (atomic m2)" |
"atomic (MEnc m k) = atomic m"

fun dupl :: "dmsg \<Rightarrow> bool" where
"dupl (MAg _) = False" |
"dupl (MNon _) = False" |
"dupl (MKp _) = False" |
"dupl (MKs _) = False" |
"dupl (MCmp m1 m2) = ((dupl m1) \<or> (dupl m2) \<or> (filter (\<lambda>s. List.member (atomic m1) s) (atomic m2) \<noteq> []))" |
"dupl (MEnc m k) = dupl m"

abbreviation "dupl2 m1 m2 \<equiv> (dupl m1) \<or> (dupl m2) \<or> (filter (\<lambda>s. List.member (atomic m1) s) (atomic m2) \<noteq> [])"

datatype dsig = ClaimSecret (sag:dagent) (sn:dnonce) (sp: "\<bbbP> dagent")
  | StartProt dagent dagent dnonce dnonce
  | EndProt dagent dagent dnonce dnonce

subsection \<open> Message inferences \<close>
definition "extract_dskey xs = map mks (filter is_MKs xs)"
definition "extract_dpkey xs = map mkp (filter is_MKp xs)"

text \<open> @{text "break_sk xs sks"}: break a list of messages from a list (xs) of known messages and 
assume private keys would never be in compound messages and encrypted messages, and only from 
@{text "sks"}.\<close>
fun break_sk::"dmsg list \<Rightarrow> dskey set \<Rightarrow> dmsg list" where
"break_sk [] sks = []" |
"break_sk ((MKp k)#xs) sks = List.insert (MKp k) (break_sk xs sks)" |
"break_sk ((MKs k)#xs) sks = List.insert (MKs k) (break_sk xs sks)" |
"break_sk ((MAg A)#xs) sks = List.insert  (MAg A) (break_sk xs sks)" |
"break_sk ((MNon A)#xs) sks = List.insert (MNon A) (break_sk xs sks)" |
"break_sk ((MCmp A B)#xs) sks = 
    remdups (break_sk [A] sks @ break_sk [B] sks @ break_sk xs sks)" |
"break_sk ((MEnc A (PK k))#xs) sks = 
    (if SK k \<in> sks then 
      List.insert (MEnc A (PK k)) (remdups (break_sk [A] sks @ break_sk xs sks))
    else 
      List.insert (MEnc A (PK k)) (break_sk xs sks))"

text \<open> All should be atomic \<close>
value "let knowledge = [
    MNon (N Alice), 
    \<lbrace>{(\<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m)}\<^bsub>PK Bob\<^esub> , (MAg Alice)\<rbrace>\<^sub>m,
    MKs (SK Bob)] 
  in break_sk knowledge (set (extract_dskey knowledge))"

text \<open> All should be atomic except for @{text "{(\<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m)}\<^bsub>PK Bob\<^esub> "} which 
is not break_skable (so in the result too) \<close>
value "let knowledge = [
    MNon (N Alice), 
    \<lbrace>{(\<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m)}\<^bsub>PK Bob\<^esub> , (MAg Alice)\<rbrace>\<^sub>m,
    MKs (SK Alice)] 
  in break_sk knowledge (set (extract_dskey knowledge))"

definition "breakm xs = break_sk xs (set (extract_dskey xs))"

text \<open> Build new messages from atomic messages by composition and encryption. 
To make the process executable, we limit the number of composition and encryption

1. atomic messages are buildable;
2. 
\<close>
text \<open> @{text "pair2 xs ys l"}: pair message once for each element of @{text "xs"} with 
every element of @{text "ys"} if they are different, their length does not exceed the given @{text 
"l"} which denotes the maximum length of a composed message. 
\<close>
fun pair2 :: "dmsg list \<Rightarrow> dmsg list \<Rightarrow> nat \<Rightarrow> dmsg list" where
"pair2 [] ys l = []" |
"pair2 (x#xs) ys l = (let cs = pair2 xs ys l in
  (map (\<lambda>n. MCmp x n) 
    (filter 
      \<comment> \<open> they are not the same, length won't exceed l, and they are not private keys  \<close>
      (\<lambda>y. y \<noteq> x \<and> length x + length y \<le> l \<and> \<not> dupl2 x y \<and> \<not> is_MKs x \<and> \<not> is_MKs y)
    ys)
  ) @ cs)"

text \<open> Should be [] \<close>
value "pair2 [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] 
    [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] 3"

value "pair2 [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] 
    [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Bob))\<rbrace>\<^sub>m] 3"

text \<open> @{text "enc\<^sub>1 xs ks"}: encrypt each element of @{text "xs"} that is not a private key with 
every key of @{text "ks"} \<close>
fun enc\<^sub>1 :: "dmsg list \<Rightarrow> dpkey list \<Rightarrow> dmsg list" where
"enc\<^sub>1 [] ks = []" |
"enc\<^sub>1 (x#xs) ks = (if is_MKs x then enc\<^sub>1 xs ks 
  else (map (\<lambda>k. MEnc x k) ks) @ enc\<^sub>1 xs ks)"

value "enc\<^sub>1 [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] [PK Bob, PK Alice, PK Intruder]"

definition "enc\<^sub>1' xs = (enc\<^sub>1 xs (extract_dpkey xs))"

text \<open> @{text "buildable knows (set knows) nc ne l"} where @{text "knows"} is a list of atomic messages;
; @{text "nc"} denotes the number of times of composition;  
@{text "ne"} denotes the number of times of encryption; 
@{text "l"} denotes the maximum length of a composed message
\<close>

fun build\<^sub>n::"dmsg list \<Rightarrow> dpkey list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dmsg list" where
\<comment> \<open> Original xs is always in the result \<close>
"build\<^sub>n xs ks 0 0 l = xs" |
\<comment> \<open> Original xs is always in the result, composed messages (cs) also are in the result, along with 
new messages built from xs + cs \<close>
"build\<^sub>n xs ks (Suc nc) 0 l = (build\<^sub>n (List.union (pair2 xs xs l) xs) ks nc 0 l)" |
"build\<^sub>n xs ks 0 (Suc ne) l = (build\<^sub>n (List.union (enc\<^sub>1 xs ks) xs) ks 0 ne l)" |
\<comment> \<open> Original xs + new messages after composition + new messages after encryption \<close>
"build\<^sub>n xs ks (Suc nc) (Suc ne) l = (if ne = 0 then
  \<comment> \<open> If only one encryption, we treat it as outermost so composition first \<close>
  (build\<^sub>n (List.union (pair2 xs xs l) xs) ks nc (Suc 0) l)
else 
    (List.union 
  \<comment> \<open> New messages after composition \<close>
    (build\<^sub>n (List.union (pair2 xs xs l) xs) ks nc (Suc ne) l)
  \<comment> \<open> New messages after encryption \<close>
    (build\<^sub>n (List.union (enc\<^sub>1 xs ks) xs) ks (Suc nc) ne l)
  )
)"

\<comment> \<open> expected "[MNon (N Alice), (MAg Bob), MKp (PK Bob)]" \<close>
value "let ns = [MNon (N Alice), (MAg Bob), MKp (PK Bob)]
  in build\<^sub>n ns (extract_dpkey ns) 0 0"

value "let ns = [MNon (N Alice), MKp (PK Bob)]
  in build\<^sub>n ns (extract_dpkey ns) 1 1"

definition "build\<^sub>n_1 ns = (build\<^sub>n ns (extract_dpkey ns) 1 1 3)"

definition "build\<^sub>n_2 ns = (build\<^sub>n ns (extract_dpkey ns) 2 1 3)"

subsection \<open> Processes \<close>
chantype Chan =
  env :: "dagent \<times> dagent"
\<comment> \<open> Send to public channels, which are controlled by Intruders. In this attack model, it just means
 the destination is @{text "Intruder"} \<close>
\<comment> \<open> For private channels, both neither source nor destination is @{text "Intruder"}  \<close>
  send :: "dagent \<times> dagent \<times> dmsg"
  recv :: "dagent \<times> dagent \<times> dmsg"
  hear :: "dagent \<times> dagent \<times> dmsg"
  fake :: "dagent \<times> dagent \<times> dmsg"
  leak :: "dmsg"
  sig :: "dsig"
  terminate :: "unit"

end
