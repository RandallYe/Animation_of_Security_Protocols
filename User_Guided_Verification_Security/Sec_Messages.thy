section \<open> The definition of messages for the modelling of security protocols \<close>
theory Sec_Messages
  imports "ITree_Security.CSP_operators"
          "ITree_Security.FSNat"
begin

declare [[show_types]]

declare [[typedef_overloaded]]

subsection \<open> General definitions \<close>

subsubsection \<open> Agents \<close>
datatype ('a::len) dagent = Agent (ag: "'a fsnat") | Intruder | Server

value "ag (Agent (nmk 1):: 2 dagent)"

definition aglist :: "(('a::len) dagent) list" where
"aglist = map Agent (fsnatlist)"

lemma distinct_aglist: "distinct (aglist)"
  apply (simp add: aglist_def fsnatlist_def distinct_map inj_on_def)
  using fsnat_of_nat_inject by blast

lemma dagent_univ: 
  shows "set ([Intruder, Server] @ aglist) = UNIV"
  apply (simp add: aglist_def fsnatlist_def image_def)
  apply (auto)
  by (metis dagent.exhaust_sel nat_of_fsnat nat_of_fsnat_inverse)

instantiation dagent :: (len) enum
begin
definition enum_dagent :: "('a::len) dagent list" where
"enum_dagent = [Intruder, Server] @ aglist"

definition enum_all_dagent :: "(('a::len) dagent \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dagent P = (\<forall>b :: 'a dagent \<in> set enum_class.enum. P b)"

definition enum_ex_dagent :: "(('a::len)dagent \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dagent P = (\<exists>b :: 'a dagent \<in> set enum_class.enum. P b)"

instance
  apply (intro_classes)
  prefer 2
  apply (simp_all add: enum_dagent_def)+
  using distinct_aglist apply (metis aglist_def dagent.distinct(1) dagent.distinct(3) ex_map_conv)
  apply (simp_all add: enum_dagent_def enum_all_dagent_def enum_ex_dagent_def)
  apply (auto)
  using dagent_univ apply auto[1]
  by (metis UNIV_I UnE dagent_univ empty_set equals0D set_ConsD set_append)+
end

value "enum_class.enum::(2 dagent) list"

subsubsection \<open> Nonces \<close>

type_synonym ('a) dnonce = "fsnat['a]"

type_synonym ('a) dexpg = "fsnat['a]"

subsubsection \<open> Keys \<close>
datatype ('k::len,'s::len) dkey = Kp (kp: "fsnat['k]") | Ks (ks: "fsnat['s]")

fun is_Ks :: "('k::len, 's::len) dkey \<Rightarrow> \<bool>"  where
"is_Ks (Kp _) = False" | 
"is_Ks (Ks _) = True"

definition sk_of_pk where 
"sk_of_pk pk = Ks (kp (pk))"

definition pk_of_sk where 
"pk_of_sk pk = Kp (ks (pk))"

definition pklist :: "(('k::len,'s::len) dkey) list" where
"pklist = map Kp (fsnatlist) @ map Ks (fsnatlist)"

lemma dkey_univ:  
  shows "set pklist = UNIV"
  apply (simp add: pklist_def fsnatlist_def)
  apply (auto)
  by (smt (verit, del_insts) dkey.exhaust image_eqI nat_of_fsnat nat_of_fsnat_inverse)

instantiation dkey :: (len, len) enum
begin
definition enum_dkey :: "('k::len, 's::len) dkey list" where
"enum_dkey = pklist"

definition enum_all_dkey :: "(('k::len, 's::len) dkey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dkey P = (\<forall>b :: ('k::len, 's::len) dkey \<in> set enum_class.enum. P b)"

definition enum_ex_dkey :: "(('k::len, 's::len) dkey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dkey P = (\<exists>b :: ('k::len, 's::len) dkey \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show univ_eq: "UNIV = set (enum_class.enum :: ('k::len, 's::len) dkey list)"
    by (simp add: dkey_univ enum_dkey_def image_def enum_fsnat_def fsnatlist_def)

  show "distinct (enum_class.enum :: ('k::len, 's::len) dkey list)"
    apply (simp add: enum_dkey_def enum_fsnat_def fsnatlist_def pklist_def)
    apply (simp add: distinct_map, auto)
    apply (smt (verit) atLeastLessThan_iff comp_apply dkey.sel(1) inj_onI mod_less fsnat_of_nat_inverse)
    by (smt (verit) atLeastLessThan_iff comp_apply dkey.sel(2) inj_onI mod_less fsnat_of_nat_inverse)
  
  fix P :: "('k::len, 's::len) dkey \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_dkey_def enum_ex_dkey_def)
qed
end

subsubsection \<open> Bitmask \<close>
text \<open> In @{text "dbitmask"}, we use the first fsnat to differentiate different bitmasks (how many 
bitmasks), and the second fsnat to represent the number of samples used for watermarking and jamming. 
So @{text "(3, 4) dbitmask"} denotes a type with three bitmasks and each bitmask having samples up to 4. 
We usually use 4 for watermarking and then may choose a smaller number such as 3 for jamming to save 
energy. \<close>
datatype ('a::len, 'b::len) dbitmask = Null | Bm (bm: "'a fsnat") (ln: "'b fsnat")

definition bmlist :: "(('a::len, 'b::len) dbitmask) list" where
"bmlist = concat (map (\<lambda>a::fsnat['a]. map (Bm a) fsnatlist) fsnatlist)"
(* "bmlist = concat (map (\<lambda>b. map (\<lambda>l. Bm b l) (fsnatlist::(fsnat['b::len]) list)) (fsnatlist::(fsnat['a::len]) list))" *)

(* "bmlist = [Bm a b. a \<leftarrow> (fsnatlist::(fsnat['a::len]) list), b \<leftarrow> (fsnatlist::(fsnat['b::len]) list)]" *)

thm "map_concat"

value "bmlist :: (2,3) dbitmask list"

value "(Bm (nmk 3) (nmk 2)) :: (2,3) dbitmask"

lemma distinct_map_Bm_fsnatlist: "distinct (map (Bm a) fsnatlist)"
  apply (simp add: distinct_map)
  by (simp add: distinct_fsnat inj_on_def)

lemma distinct_bmlist: "distinct (bmlist)"
  apply (simp add: bmlist_def)
  apply (rule distinct_concat)
  apply (simp add: fsnatlist_def distinct_map inj_on_def)
  apply (meson fsnat_of_nat_inject len_gt_0)
  using distinct_map_Bm_fsnatlist apply auto[1]
  by force

lemma dbitmask_univ: 
  shows "set ([Null] @ bmlist) = UNIV"
  apply (simp add: bmlist_def)
  apply (auto)
  using dbitmask.exhaust_sel by (metis UNIV_I fsnatlist_univ range_eqI)

instantiation dbitmask :: (len, len) enum
begin
definition enum_dbitmask :: "('a::len, 'b::len) dbitmask list" where
"enum_dbitmask = [Null] @ bmlist"

definition enum_all_dbitmask :: "(('a::len, 'b::len) dbitmask \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dbitmask P = (\<forall>b :: ('a::len, 'b::len) dbitmask \<in> set enum_class.enum. P b)"

definition enum_ex_dbitmask :: "(('a::len, 'b::len) dbitmask \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dbitmask P = (\<exists>b :: ('a::len, 'b::len) dbitmask \<in> set enum_class.enum. P b)"

instance
  apply (intro_classes)
  prefer 2
  apply (simp_all add: enum_dbitmask_def)+
  apply (rule conjI)
  apply (simp add: bmlist_def)
  apply blast
  apply (simp add: distinct_bmlist)
  apply (simp_all add: enum_dbitmask_def enum_all_dbitmask_def enum_ex_dbitmask_def)
  apply (auto)
  using dbitmask_univ apply auto[1]
  by (metis UNIV_I UnE dbitmask_univ empty_set equals0D set_ConsD set_append)+
end

instantiation dbitmask :: (len, len) order
begin

lift_definition less_eq_dbitmask :: "('a::len, 'b::len) dbitmask \<Rightarrow> ('a::len, 'b::len) dbitmask \<Rightarrow> bool"
  is "\<lambda>a b. case a of Null \<Rightarrow> True | Bm x1 y1 \<Rightarrow> (case b of Null \<Rightarrow> False | Bm x2 y2 \<Rightarrow> (x1 = x2) \<and> y1 \<le> y2)" .

lift_definition less_dbitmask :: "('a::len, 'b::len) dbitmask \<Rightarrow> ('a::len, 'b::len) dbitmask \<Rightarrow> bool"
  is "\<lambda>a b. case (a,b) of (Null, Null) \<Rightarrow> False | (Null, Bm x2 y2) \<Rightarrow> True | (Bm x1 y1, Null) \<Rightarrow> False | 
  (Bm x1 y1, Bm x2 y2) \<Rightarrow> (x1 = x2) \<and> (y1 < y2)" .

instance
  apply (standard)
  apply (simp_all add: less_eq_dbitmask_def less_dbitmask_def)
  apply (smt (verit) dbitmask.case_eq_if nless_le order_antisym_conv)
  apply (simp add: dbitmask.case_eq_if)
  apply (smt (z3) dbitmask.case_eq_if order.trans)
  by (smt (z3) dbitmask.case_eq_if dbitmask.exhaust_sel nle_le)
end

(* True *)
value "((Bm (nmk 1) (nmk 2)) :: (2,3) dbitmask) \<le> (Bm (nmk 1) (nmk 2))"
value "((Bm (nmk 1) (nmk 1)) :: (2,3) dbitmask) \<le> (Bm (nmk 1) (nmk 2))"

(* False *)
value "((Bm (nmk 3) (nmk 2)) :: (2,3) dbitmask) \<le> (Bm (nmk 1) (nmk 1))"

subsubsection \<open> Messages \<close>
datatype ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg 
=   MAg   (ma: "'a dagent")
  | MNon  (mn: "'n dnonce")
  | MK    (mk: "('k, 's) dkey")
  | MPair (mc1: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mc2: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  \<comment> \<open> Asymmetric encryption \<close>
  | MAEnc  (mem: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mek: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  \<comment> \<open> Digital signature \<close>
  | MSig  (msd: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (msk: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  \<comment> \<open> Symmetric encryption \<close>
  | MSEnc (msem: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (msek: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  \<comment> \<open> The base g in a modular exponentiation @{text "(g\<^sup>a mod p)"} \<close>
  | MExpg (eg: "'g dexpg")
  \<comment> \<open> The power @{text "g\<^sup>a"} in a modular exponentiation @{text "(g\<^sup>a mod p)"} \<close>
  | MModExp (mmem: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mmek: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  | MBitm (mbm: "('bm, 'bl) dbitmask")
  | MWat (mwm: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mwb: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  | MJam (mjm: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mjb: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")

text \<open> Generate linorder for all these types in order to support comparison between dmsg, particularly 
for MPair to reduce the number of messages that intruder can build because we can treat 
@{text "MPair a1 a2"} and @{text "MPair a2 a1"} as the same, and 
@{text "MPair (MPair a3 a1) a2"} and @{text "MPair a2 (MPair a3 a1)"} also as the same. 
\<close>

text\<open>Concrete syntax for dmsg \<close>
syntax
  "_PairMsg" :: "['a, args] \<Rightarrow> 'a * 'b"  ("(2\<lbrace>_,/ _\<rbrace>\<^sub>m)")
  "_AEncryptMsg" :: "['a, 'a] \<Rightarrow> 'a"      ("(2{_}\<^sup>a\<^bsub>_\<^esub>)")
  "_SEncryptMsg" :: "['a, 'a] \<Rightarrow> 'a"     ("(2{_}\<^sup>s\<^bsub>_\<^esub>)")
  "_SignMsg" :: "['a, 'a] \<Rightarrow> 'a"         ("(2{_}\<^sup>d\<^bsub>_\<^esub>)")
  "_ModExpMsg" :: "['a, 'a] \<Rightarrow> 'a"       (infixl "^\<^sub>m" 50)
  "_MExpg" :: "'a \<Rightarrow> 'a" ("g\<^sub>m _")
  "_WatMsg" :: "['a, 'a] \<Rightarrow> 'a"          ("(2{_}\<^sup>w\<^bsub>_\<^esub>)")
  "_JamMsg" :: "['a, 'a] \<Rightarrow> 'a"          ("(2{_}\<^sup>j\<^bsub>_\<^esub>)")
translations
  "\<lbrace>w, x, y, z\<rbrace>\<^sub>m" \<rightleftharpoons> "\<lbrace>w, \<lbrace>x, \<lbrace>y, z\<rbrace>\<^sub>m\<rbrace>\<^sub>m\<rbrace>\<^sub>m"
  "\<lbrace>x, y, z\<rbrace>\<^sub>m" \<rightleftharpoons> "\<lbrace>x, \<lbrace>y, z\<rbrace>\<^sub>m\<rbrace>\<^sub>m"
  "\<lbrace>x, y\<rbrace>\<^sub>m" \<rightleftharpoons> "CONST MPair x y"
  "{m}\<^sup>a\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MAEnc m k"
  "{m}\<^sup>d\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MSig m k"
  "{m}\<^sup>s\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MSEnc m k"
  "m^\<^sub>me" \<rightleftharpoons> "CONST MModExp m e"
  "g\<^sub>m e"  \<rightleftharpoons> "CONST MExpg e"
  "{m}\<^sup>w\<^bsub>bm\<^esub>" \<rightleftharpoons> "CONST MWat m bm"
  "{m}\<^sup>j\<^bsub>bm\<^esub>" \<rightleftharpoons> "CONST MJam m bm"

abbreviation "mkbm m l \<equiv> MBitm (Bm (nmk m) (nmk l))"
abbreviation "mkag x \<equiv> MAg (Agent (nmk x))"
abbreviation "mknon x \<equiv> MNon (nmk x)"
abbreviation "mkpk x \<equiv> MK (Kp (nmk x))"
abbreviation "mksk x \<equiv> MK (Ks (nmk x))"

value "{MNon (nmk 1)}\<^sup>a\<^bsub>MK (Ks (nmk 1))\<^esub> :: (2,4,4,4,1,1,1) dmsg"
value "{MNon (nmk 1)}\<^sup>d\<^bsub>MK (Ks (nmk 1))\<^esub>  :: (2,4,4,4,1,1,1) dmsg"
value "\<lbrace>MNon (nmk 1), MK (Kp (nmk 1))\<rbrace>\<^sub>m  :: (2,4,4,4,1,1,1) dmsg"
value "(g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 1)) ^\<^sub>m (MNon (nmk 1))  :: (2,4,4,4,1,1,1) dmsg"

definition is_MKs:: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> bool" where 
"is_MKs m = (is_MK m \<and> (is_Ks (mk m)))"

value "is_MKs ((MK (Ks (nmk 1))) :: (2,4,4,4,1,1,1) dmsg)"

paragraph \<open> Message functions \<close>
fun msg_length:: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> nat" where
"msg_length (MAg _) = 1" |
"msg_length (MNon _) = 1" |
"msg_length (MK _) = 1" |
"msg_length (MPair m1 m2) = msg_length m1 + msg_length m2" |
"msg_length (MAEnc m k) = msg_length m" |
"msg_length (MSig m k) = msg_length m" |
"msg_length (MSEnc m k) = msg_length m" |
"msg_length (MExpg _) = 1" |
"msg_length (MModExp m k) = msg_length m" |
"msg_length (MBitm _) = 1" |
"msg_length (MWat m k) = msg_length m" |
"msg_length (MJam m k) = msg_length m"

fun num_aenc:: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> nat" where
"num_aenc (MAg _) = 0" |
"num_aenc (MNon _) = 0" |
"num_aenc (MK _) = 0" |
"num_aenc (MPair m1 m2) = max (num_aenc m1) (num_aenc m2)" |
"num_aenc (MAEnc m k) = 1 + num_aenc m" |
"num_aenc (MSig m k) = num_aenc m" |
"num_aenc (MSEnc m k) = num_aenc m" |
"num_aenc (MExpg _) = 0" |
"num_aenc (MModExp m k) = num_aenc m" |
"num_aenc (MBitm _) = 0" |
"num_aenc (MWat m k) = num_aenc m" |
"num_aenc (MJam m k) = num_aenc m"

fun atomic :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"atomic (MAg m) = [(MAg m)]" |
"atomic (MNon m) = [(MNon m)]" |
"atomic (MK m) = [(MK m)]" |
"atomic (MPair m1 m2) = List.union (atomic m1) (atomic m2)" |
"atomic (MAEnc m k) = atomic m" |
"atomic (MSig m k) = atomic m" |
"atomic (MSEnc m k) = atomic m" |
"atomic (MExpg m) = [(MExpg m)]" |
"atomic (MModExp m k) = atomic m" |
"atomic (MBitm b) = [(MBitm b)]" |
"atomic (MWat m k) = atomic m" |
"atomic (MJam m k) = atomic m"

definition atomics :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
                       ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"atomics xs = List.concat (map atomic xs)"

fun dupl :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> bool" where
"dupl (MAg _) = False" |
"dupl (MNon _) = False" |
"dupl (MK _) = False" |
"dupl (MPair m1 m2) = ((dupl m1) \<or> (dupl m2) \<or> (filter (\<lambda>s. List.member (atomic m1) s) (atomic m2) \<noteq> []))" |
"dupl (MAEnc m k) = dupl m" |
"dupl (MSig m k) = dupl m" |
"dupl (MSEnc m k) = dupl m" |
"dupl (MExpg _) = False" |
"dupl (MModExp m k) = dupl m" |
"dupl (MBitm b) = False" |
"dupl (MWat m k) = dupl m" |
"dupl (MJam m k) = dupl m"

abbreviation "dupl2 m1 m2 \<equiv> (dupl m1) \<or> (dupl m2) \<or> (filter (\<lambda>s. List.member (atomic m1) s) (atomic m2) \<noteq> [])"

text \<open> Create a MPair from a list of messages \<close>
fun create_cmp :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
                   ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg option" where
"create_cmp [] = None" |
"create_cmp (x#[y]) = Some (MPair x y)" |
"create_cmp (x#ys) = (case (create_cmp ys) of 
  None \<Rightarrow> None |
  Some y \<Rightarrow> Some (MPair x y))
"

value "create_cmp [mknon 1, mkag 1, mkpk 1, mksk 1] :: (2, 4, 4, 4, 4, 2, 2) dmsg option"

text \<open> Transform a MPair into a list of sorted messages \<close>
fun mpair_to_list :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> 
                      ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"mpair_to_list (MPair m1 m2) = List.union (mpair_to_list m1) (mpair_to_list m2)" |
"mpair_to_list a = [a]"

value "mpair_to_list (MPair 
  (MPair 
      (MSEnc (MPair (MAg (Agent (nmk 1))) (MNon (nmk 0))) (MK (Ks (nmk 0)))) 
      (MAg (Agent (nmk 0)))
  )
  (MNon (nmk 1))
) :: (2,4,4,2,2,1,1) dmsg list"


definition "extract_dkey xs = map (mk)  (filter is_MK xs)"
definition "extract_dkeys xs = (filter is_Ks (extract_dkey xs))"
definition "extract_dkeyp xs = (filter is_Kp (extract_dkey xs))"
definition "extract_nonces xs = (filter is_MNon xs)"

value "extract_dkeys [((MK (Ks (nmk 1))) :: (2,4,4,2,2,1,1) dmsg)]"

subsection \<open> Message inferences \<close>

(*
fun break_one :: 
  "('a::len,'n::len,'k::len,'k::len,'g::len,'bm::len,'bl::len) dmsg \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg list \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg set \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg list" where
  "break_one (MK k) ams as = List.insert (MK k) ams"
| "break_one (MAg A) ams as = List.insert (MAg A) ams"
| "break_one (MNon A) ams as = List.insert (MNon A) ams"
| "break_one (MPair A B) ams as =
     (let ams1 = break_one A ams as in
      break_one B ams1 as)"
| "break_one (MAEnc A (MK (Kp k))) ams as =
     (let ams' = List.insert (MAEnc A (MK (Kp k))) ams in
     if MK (Ks k) \<in> set ams then
       break_one A ams' as
     else ams')"
| "break_one (MSig A (MK (Ks k))) ams as =
     (let ams' = List.insert (MSig A (MK (Ks k))) ams in
     if MK (Kp k) \<in> set ams then
       break_one A ams' as
     else ams')"
| "break_one (MSEnc A (MK (Ks k))) ams as =
     (let ams' = List.insert (MSEnc A (MK (Ks k))) ams in
     if MK (Ks k) \<in> set ams then
       break_one A ams' as
     else ams')"
| "break_one m ams as = List.insert m ams"

(* One pass over a list, no look-ahead *)
fun break_pass ::
  "('a::len,'n::len,'k::len,'k::len,'g::len,'bm::len,'bl::len) dmsg list \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg list \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg set \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg list" where
  "break_pass [] ams as = ams"
| "break_pass (x#xs) ams as = break_pass xs (break_one x ams as) as"

(* Iterate until stable, termination by finiteness of the type *)
function break_fix ::
  "('a::len,'n::len,'k::len,'k::len,'g::len,'bm::len,'bl::len) dmsg list \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg list \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg set \<Rightarrow>
   ('a,'n,'k,'k,'g,'bm,'bl) dmsg list" where
  "break_fix xs ams as =
     (let ams' = break_pass xs ams as in
      if set ams' = set ams then ams
      else break_fix xs ams' as)"
  apply auto[1]
  by fastforce


value "break_fix value ([MAg (Agent (nmk 1)), MAg (Agent (nmk 0))] :: (2,4,4,4,2,2,2) dmsg list)"
*)

fun submsg_list :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"submsg_list (MAg a)       = [MAg a]" |
"submsg_list (MNon a)      = [MNon a]" |
"submsg_list (MK a)        = [MK a]" |
"submsg_list (MPair m1 m2) = (MPair m1 m2) # submsg_list m1 @ submsg_list m2" |
"submsg_list (MAEnc m k)   = (MAEnc m k) # submsg_list m @ submsg_list k" |
"submsg_list (MSig m k)    = (MSig m k) # submsg_list m @ submsg_list k" |
"submsg_list (MSEnc m k)   = (MSEnc m k) # submsg_list m @ submsg_list k" |
"submsg_list (MExpg a)     = [MExpg a]" |
"submsg_list (MModExp m k) = (MModExp m k) # submsg_list m @ submsg_list k" |
"submsg_list (MBitm b)     = [MBitm b]" |
"submsg_list (MWat m k)    = (MWat m k) # submsg_list m @ submsg_list k" |
"submsg_list (MJam m k)    = (MJam m k) # submsg_list m @ submsg_list k"

definition submsgs_list :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list 
  \<Rightarrow> ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"submsgs_list xs = remdups (concat (map submsg_list xs))"

fun one_step :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg set \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"one_step m K = (case m of
    MPair m1 m2 \<Rightarrow> [m1, m2]
  | MAEnc m' (MK (Kp k)) \<Rightarrow> (if MK (Ks k) \<in> K then [m'] else [])
  | MSig m' (MK (Ks k)) \<Rightarrow> (if MK (Kp k) \<in> K then [m'] else [])
  | MSEnc m' (MK (Ks k)) \<Rightarrow> (if MK (Ks k) \<in> K then [m'] else [])
  | MSEnc m' (MModExp (MModExp (MExpg gn) a) b) \<Rightarrow>
      (if (MModExp (MExpg gn) a \<in> K \<and> b \<in> K) \<or>
          (MModExp (MExpg gn) b \<in> K \<and> a \<in> K) \<or>
          (MExpg gn \<in> K \<and> a \<in> K \<and> b \<in> K)
       then [m'] else [])
  | MWat m' k \<Rightarrow> [m']
  | MJam (MWat m' (MBitm bb)) (MBitm b) \<Rightarrow>
      (if b = Null \<or> (b \<le> bb \<and> MBitm b \<in> K) then [m'] else [])
  | _ \<Rightarrow> [])"

definition step_once :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list 
  \<Rightarrow> ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"step_once K = remdups (K @ concat (map (\<lambda>m. one_step m (set K)) K))"

fun iter_closure :: "nat \<Rightarrow> ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"iter_closure 0 K = K" |
"iter_closure (Suc n) K = iter_closure n (step_once K)"

definition breakl :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"breakl xs = iter_closure (List.length (submsgs_list xs) + 1) (remdups xs)"

value "breakl [MAEnc (MK (Ks (nmk 1))) (MK (Kp (nmk 0))), 
  MAEnc (MAg (Agent (nmk 0))) (MK (Kp (nmk 1))), MK (Ks (nmk 0))] :: (2,4,4,4,2,2,3) dmsg list"

text \<open> jam1: not breakable since the bitmask b' of the jammed message is not known \<close>
value "breakl [
  MJam (MWat (mknon 0) ((mkbm 0 1))) (mkbm 0 2)] 
  :: (2,4,4,4,2,2,3) dmsg list"

text \<open> jam1: not breakable even b' is known because the jammed message is not watermarked. \<close>
value "breakl [
  MJam (mknon 0) (mkbm 0 1), (mkbm 0 1)] 
  :: (2,4,4,4,2,2,3) dmsg list"

text \<open> jam1: not breakable since the bitmask b' of the jammed message is not a prefix of that (b) of 
  the watermarked message. \<close>
value "breakl [
  MJam (MWat (mknon 0) ((mkbm 0 1))) (mkbm 0 2), (mkbm 0 2)] 
  :: (2,4,4,4,2,2,3) dmsg list"

value "((Bm (nmk 0) (nmk 2)) :: (2,3) dbitmask) \<le> (Bm (nmk 0) (nmk 1))"

text \<open> jam1: breakable since b' <= b and b' is known \<close>
value "breakl [
  MJam (MWat (mknon 0) ((mkbm 0 1))) (mkbm 0 1),
  (mkbm 0 1)] 
  :: (2,4,4,4,2,2,3) dmsg list"

text \<open> jam1: breakable since b' <= b and b' is known \<close>
value "breakl [
  MJam (MWat (mknon 0) ((mkbm 0 2))) (mkbm 0 1),
  (mkbm 0 1)] 
  :: (2,4,4,4,2,2,2) dmsg list"

(*
text \<open> @{text "break_lst xs ys as"} break down a list of messages and ys is the list of messages that 
have been broken down previously, and as is the set of atomic messages (parts), used to decide if it
is necessary to carry further break down or not for an encrypted or signed message. \<close>
fun break_lst::"('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg set \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"break_lst [] ams as = ams" |
"break_lst ((MK k)#xs) ams as = (break_lst xs (List.insert (MK k) ams) as)" |
"break_lst ((MAg A)#xs) ams as = (break_lst xs (List.insert (MAg A) ams) as)" |
"break_lst ((MNon A)#xs) ams as = (break_lst xs (List.insert (MNon A) ams) as)" |
\<comment> \<open> A and B might be mutual dependent, such as @{text "\<lbrace>{g\<^sub>m ^\<^sub>m (na)}\<^sub>s\<^bsub>SK A\<^esub> , MKp (PK A)\<rbrace>\<^sub>m"}. 
  We could proceed as follows, but now the @{text "{g\<^sub>m ^\<^sub>m (na)}\<^sub>s\<^bsub>SK A\<^esub>"} would be in the @{text "ams"} 
though it still can be breakdown.
\<close>
(* The right way might be "break_lst (A#(B#xs)) ams" but it is hard to prove it will be terminated *)
"break_lst ((MPair A B)#xs) ams as = (
    break_lst xs (remdups ((break_lst [A] ams as) @ (break_lst [B] ams as) @ ams)) as
  )" |
"break_lst ((MAEnc A (MK (Kp k)))#xs) ams as = 
  \<comment> \<open> If the corresponding private key is in as \<close>
  (if (MK (Ks k)) \<in> as then
    (if List.member ams (MK (Ks k)) then
      break_lst (A#xs) (List.insert (MAEnc A (MK (Kp k))) ams) as
    else 
      let rams = break_lst xs ams as
      in  if List.member rams (MK (Ks k)) then
          break_lst (A#xs) (List.insert (MAEnc A (MK (Kp k))) ams) as
        else
          break_lst xs (List.insert (MAEnc A (MK (Kp k))) (ams)) as
    )
  else
    break_lst xs (List.insert (MAEnc A (MK (Kp k))) (ams)) as
)" |
"break_lst ((MSig A (MK (Ks k)))#xs) ams as = 
  \<comment> \<open> If the corresponding public key is in as \<close>
  (if (MK (Kp k)) \<in> as then
    (if List.member ams (MK (Kp k)) then
      break_lst (A#xs) (List.insert (MSig A (MK (Ks k))) ams) as
    else 
      let rams = break_lst xs ams as
      in if List.member rams (MK (Kp k)) then
          \<comment> \<open> TODO: do we need to re-do it again for xs? It seems so because A may have more info. 
          Current solution is to apply @{text break_lst} twice. \<close>
          break_lst (A#xs) (List.insert (MSig A (MK (Ks k))) ams) as
        else
          break_lst xs (List.insert (MSig A (MK (Ks k))) (ams)) as
    )
  else 
    break_lst xs (List.insert (MSig A (MK (Ks k))) (ams)) as
)" |
\<comment> \<open> Particularly, we are looking at the k having a form @{text "((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)"}. 
  @{text "{m}\<^sub>S\<^bsub>((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)\<^esub> "} can be broken if (@{text "(g\<^sub>m ^\<^sub>m a)"} and @{text "b"})
  or (@{text "(g\<^sub>m ^\<^sub>m b)"} and @{text "a"}) in the messages because 
  @{text "((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)"} is equal to @{text "((g\<^sub>m ^\<^sub>m b) ^\<^sub>m a)"}.
\<close>
"break_lst ((MSEnc m (MK (Ks k)))#xs) ams as =
  \<comment> \<open> If symmetric encryption using a private key, \<close>
  (if (MK (Ks k)) \<in> as then
    (if List.member ams (MK (Ks k)) then
      break_lst (m#xs) (List.insert (MSEnc m (MK (Ks k))) ams) as
    else
      let rams = break_lst xs ams as
      in  if List.member rams (MK (Ks k)) then
          break_lst (m#xs) (List.insert (MSEnc m (MK (Ks k))) ams) as
        else
          break_lst xs (List.insert (MSEnc m (MK (Ks k))) (ams)) as
    )
  else
    break_lst xs (List.insert (MSEnc m (MK (Ks k))) (ams)) as
  )" |
"break_lst ((MSEnc m (((g\<^sub>m gn) ^\<^sub>m a) ^\<^sub>m b))#xs) ams as =
  \<comment> \<open> If the key is a modular exponentiation used in Diffie-Hellman, \<close>
  (if (List.member ams (((g\<^sub>m gn) ^\<^sub>m a)) \<and> List.member ams (b)) \<or>
      (List.member ams (((g\<^sub>m gn) ^\<^sub>m b)) \<and> List.member ams (a)) \<or>
      (List.member ams ((g\<^sub>m gn)) \<and> List.member ams (a) \<and> List.member ams (b)) then
     break_lst (m#xs) (List.insert (MSEnc m (((g\<^sub>m gn) ^\<^sub>m a) ^\<^sub>m b)) ams) as
   else
     let rams = break_lst xs ams as
     in if (List.member rams (((g\<^sub>m gn) ^\<^sub>m a)) \<and> List.member rams (b)) \<or>
           (List.member rams (((g\<^sub>m gn) ^\<^sub>m b)) \<and> List.member rams (a)) \<or>
           (List.member rams ((g\<^sub>m gn)) \<and> List.member rams (a) \<and> List.member rams (b)) then
          break_lst (m#xs) (List.insert (MSEnc m (((g\<^sub>m gn) ^\<^sub>m a) ^\<^sub>m b)) ams) as
        else
          break_lst xs (List.insert (MSEnc m (((g\<^sub>m gn) ^\<^sub>m a) ^\<^sub>m b)) (ams)) as
  )" |
\<comment> \<open> Otherwise, we won't break it \<close>
"break_lst ((MSEnc m k)#xs) ams as = break_lst xs (List.insert (MSEnc m k) (ams)) as"
| 
"break_lst ((MExpg a)#xs) ams as = break_lst xs (List.insert (MExpg a) (ams)) as" |
\<comment> \<open> We cannot break anything from a^b but the message should be kept \<close>
"break_lst ((a ^\<^sub>m b)#xs) ams as = break_lst xs (List.insert (a ^\<^sub>m b) (ams)) as" |
"break_lst ((MBitm b)#xs) ams as = (break_lst xs (List.insert (MBitm b) ams) as)" |
\<comment> \<open> What can we break down from a watermarked message?
We can always know m from a watermarked message wat(m, bm)
\<close>
"break_lst (({m}\<^sup>w\<^bsub>b\<^esub> )#xs) ams as = break_lst xs (List.insert (m) (ams)) as" |
\<comment> \<open> We can break jam(m, b) if and only if we know b \<close>
"break_lst (({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> )#xs) ams as = \<comment> \<open> If the corresponding bitmask is in as \<close>
  (if b \<noteq> Null then
    \<comment> \<open> m should be a watermarked message using the same bitmask but may use less bits
    \<close>
    (if is_MWat m \<and> b \<le> mbm (mwb m) \<and> (MBitm (b)) \<in> as then
      (if List.member ams (MBitm (b)) then
        break_lst (m#xs) (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) ams) as
      else 
        let rams = break_lst xs ams as
        in  if List.member rams (MBitm (b)) then
            break_lst (m#xs) (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) ams) as
          else
            break_lst xs (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) (ams)) as
      )
    else
      \<comment> \<open> If not watermarked or ..., but the jamming bitmask is known, we still can learn the message. \<close>
      (if List.member ams (MBitm (b)) then
        break_lst (m#xs) (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) ams) as
      else 
        break_lst xs (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) (ams)) as
      )
    )
  else
    break_lst (m#xs) (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) ams) as
)" |
"break_lst (x#xs) ams as = break_lst xs (List.insert (x) (ams)) as"

definition "breakl xs = break_lst xs [] (set (atomics xs))"

text \<open> Our strategy to deal with @{text "(MPair A B)"} is the application of breakl twice. \<close>
definition "breakm xs = 
  (let as = (set (atomics xs));
       ys = break_lst xs [] as
   in break_lst ys [] as)"

value "breakl ([MAg (Agent (nmk 1)), MAg (Agent (nmk 0))] :: (2,4,4,4,2,2,2) dmsg list)"
value "breakl ([{MAg (Agent (nmk 1))}\<^sup>a\<^bsub>(MK (Kp (nmk 1)))\<^esub> , (MK (Ks (nmk 1)))]:: (2,4,4,4,2,2,2) dmsg list)"
value "breakl ([\<lbrace>
  {(g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 0))}\<^sup>d\<^bsub>(MK (Ks (nmk 1)))\<^esub> , 
  MK (Kp (nmk 1)), MAg (Agent (nmk 21)) \<rbrace>\<^sub>m] :: (2,4,4,4,2,2,2) dmsg list)"
text \<open> In the following example, we expect the signed modular exponentiation will be derived. \<close>
value "breakm ([\<lbrace> 
  {(g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 0))}\<^sup>d\<^bsub>(MK (Ks (nmk 1)))\<^esub> , 
  MK (Kp (nmk 1)), 
  MAg (Agent (nmk 21)) 
\<rbrace>\<^sub>m] :: (2,4,4,4,2,2,2) dmsg list)"

value "breakl [{{(mknon 1)}\<^sup>w\<^bsub>(mkbm 0 2)\<^esub> }\<^sup>j\<^bsub>(mkbm 0 2)\<^esub> , (mkbm 0 2)] :: (2,4,4,4,2,2,2) dmsg list"

value "breakl [mkag 1, mkag 0, (mknon 0), {(mknon 1)}\<^sup>j\<^bsub>(mkbm 0 2)\<^esub> , (mkbm 0 1)] :: (2,4,4,4,2,2,2) dmsg list"

text \<open> Should @{text "(mknon 1)"} be learned. \<close>
value "breakm [mkag 1, mkag 0, (mknon 0), {(mknon 1)}\<^sup>j\<^bsub>(mkbm 0 2)\<^esub> , (mkbm 0 2)] :: (2,4,4,4,2,2,2) dmsg list"
*)

text \<open> Assume @{text "((g\<^sub>m x) ^\<^sub>m a ^\<^sub>m b) = ((g\<^sub>m x) ^\<^sub>m b ^\<^sub>m a)"}, use this function to swap a and b. \<close>
fun swap_mod_exp :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg" where 
"swap_mod_exp ((g\<^sub>m x) ^\<^sub>m a ^\<^sub>m b) = ((g\<^sub>m x) ^\<^sub>m b ^\<^sub>m a)" |
"swap_mod_exp m = m"

(*
chantype chan = terminate :: "unit"

definition PP::"(chan, (3, 3, 3, 3, 3) dmsg list) itree" where "PP = 
(Ret (breakl [{MAg (Agent (mkagent TYPE(3) 1))}\<^sup>a\<^bsub>(MK (Kp (mkkey TYPE(3) 1)))\<^esub> , (MK (Ks (mkkey TYPE(3) 1)))]) \<box> stop)"
value (*[simp]*) "PP"
code_thms PP
export_code "PP" in Haskell
*)

(*
text \<open> @{text "pair2 xs ys l"}: pair message once for each element of @{text "xs"} with 
every element of @{text "ys"} if they are different, their length does not exceed the given @{text 
"l"} which denotes the maximum length of a composed message. 
\<close>
fun pair2 :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
    ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> nat \<Rightarrow> 
    ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"pair2 [] ys l = []" |
"pair2 (x#xs) ys l = (let cs = pair2 xs ys l in
  (map (\<lambda>n. (MPair x n)) \<comment> \<open> Sort the components in MPair \<close>
    (filter 
      \<comment> \<open> they are not the same, length won't exceed l, and they are not private keys  \<close>
      (\<lambda>y. y \<noteq> x \<and> msg_length x + msg_length y \<le> l \<and> \<not> dupl2 x y \<and> \<not> is_MK x \<and> \<not> is_MK y) 
    ys)
  ) @ cs)"

value "msg_length \<lbrace>(MAg (Server))::(2,2,4,4,1) dmsg, (MNon (nmk 1))\<rbrace>\<^sub>m"
value "pair2 [MNon (nmk 1)::(2,2,4,4,1) dmsg, \<lbrace>(MAg (Agent (nmk 0))), (MNon (nmk 2))\<rbrace>\<^sub>m] 
             [MNon (nmk 2), \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 2))\<rbrace>\<^sub>m] 3"
\<comment> \<open> We expect [] because equal or duplicate cases \<close>
value "pair2 [MNon (nmk 1)::(2,2,4,4,1) dmsg, \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 1))\<rbrace>\<^sub>m] 
             [MNon (nmk 1), \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 1))\<rbrace>\<^sub>m] 3"

text \<open> @{text "aenc\<^sub>1 xs ks"}: asymmetric encrypt of each element of @{text "xs"} using 
every key of @{text "ks"} \<close>
fun aenc\<^sub>1 :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> ('k, 's) dkey list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"aenc\<^sub>1 [] pks = []" |
"aenc\<^sub>1 (x#xs) pks = (if is_MKs x then aenc\<^sub>1 xs pks \<comment> \<open> Ignore private keys because we won't send private keys directly\<close>
  else (map (\<lambda>k. MAEnc x (MK k)) pks) @ aenc\<^sub>1 xs pks)"

text \<open> @{text "n"} is the limit of number of asymmetric encryption. \<close>
fun aenc\<^sub>n :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> ('k, 's) dkey list \<Rightarrow> nat \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"aenc\<^sub>n [] pks n = []" |
"aenc\<^sub>n (x#xs) pks n = (if is_MKs x \<or> num_aenc x \<ge> n then aenc\<^sub>n xs pks n \<comment> \<open> Ignore private keys because we won't send private keys directly and if the number of encryption exeeds.\<close>
  else (map (\<lambda>k. MAEnc x (MK k)) pks) @ aenc\<^sub>n xs pks n)"

value "aenc\<^sub>1 [MNon (nmk 0)::(2,2,4,4,1) dmsg, \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 0))\<rbrace>\<^sub>m] 
  [Kp (nmk 0), Kp (nmk 1), Kp (nmk 2)]"

definition "aenc\<^sub>1' xs = (aenc\<^sub>1 xs (extract_dkeyp xs))"
definition "aenc\<^sub>n' xs = (aenc\<^sub>n xs (extract_dkeyp xs))"

text \<open> @{text "dsig\<^sub>1 xs ks"}: digital signature of each element of @{text "xs"} using 
every key of @{text "ks"} \<close>
fun dsig\<^sub>1 :: "dmsg list \<Rightarrow> dkey list \<Rightarrow> dmsg list" where
"dsig\<^sub>1 [] sks = []" |
"dsig\<^sub>1 (x#xs) sks = (if is_MKs x then dsig\<^sub>1 xs sks 
  else (map (\<lambda>k. MSig x (MK k)) sks) @ dsig\<^sub>1 xs sks)"

value "dsig\<^sub>1 [MNon (nmk 0), \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 0))\<rbrace>\<^sub>m] [Ks (nmk 3)]"

definition "dsig\<^sub>1' xs = dsig\<^sub>1 xs (extract_dkeys xs)"

text \<open> @{text "senc\<^sub>1 xs eks"}: symmetric encrypt of each element of @{text "xs"} using 
every key of @{text "eks"} (a set of MModExp)  \<close>
fun senc\<^sub>1 :: "dmsg list \<Rightarrow> dkey list \<Rightarrow> dmsg list" where
"senc\<^sub>1 [] eks = []" |
"senc\<^sub>1 (x#xs) eks = (if is_MKs x then senc\<^sub>1 xs eks 
  else (map (\<lambda>k. MSEnc x (MK k)) eks) @ senc\<^sub>1 xs eks)"

definition "senc\<^sub>1' xs = senc\<^sub>1 xs (extract_dkeys xs)"

value "senc\<^sub>1' [MNon (nmk 0), (MAg (Agent (nmk 1))), (MNon (nmk 1)), 
  (g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 0)) ^\<^sub>m (MNon (nmk 1)), MK (Ks (nmk 4))]"

text \<open> @{text "senc\<^sub>1 xs eks"}: encrypt each element of @{text "xs"} with 
every key of @{text "eks"} (a set of MModExp)  \<close>
fun sencm\<^sub>1 :: "dmsg list \<Rightarrow> dmsg list \<Rightarrow> dmsg list" where
"sencm\<^sub>1 [] eks = []" |
"sencm\<^sub>1 (x#xs) eks = (if is_MKs x then sencm\<^sub>1 xs eks 
  else (map (\<lambda>k. MSEnc x k) eks) @ sencm\<^sub>1 xs eks)"

definition "sencm\<^sub>1' xs = sencm\<^sub>1 xs (filter is_MModExp xs)"

value "sencm\<^sub>1' [MNon (nmk 0), (MAg (Agent (nmk 1))), (MNon (nmk 1)), 
  (g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 0)) ^\<^sub>m (MNon (nmk 1))]"

text \<open> Apply @{text "^\<^sub>m"} up to twice, based on @{text "g\<^sub>m"} \<close>
definition mod_exp2 :: "dmsg list \<Rightarrow> dmsg list" where
"mod_exp2 xs = (let mes = (map (\<lambda>n. (g\<^sub>m (nmk 0)) ^\<^sub>m n) xs) 
   in mes @ concat (map (\<lambda>m. (map (\<lambda>n. m ^\<^sub>m n) xs)) mes)
)"

value "mod_exp2 [MNon (nmk 0), MNon (nmk 1)]"

definition "mod_exp2' xs = (if List.member xs g\<^sub>m (nmk 0) then mod_exp2 xs else [])"

text \<open> Apply @{text "^\<^sub>m"} up to once to @{text "g\<^sub>m ^\<^sub>m a"} \<close>
fun mod_exp1 :: "dmsg list \<Rightarrow> dmsg list \<Rightarrow> dmsg list" where
"mod_exp1 [] ys = []" |
"mod_exp1 (((g\<^sub>m x) ^\<^sub>m a)#xs) ys = (map (\<lambda>n. ((g\<^sub>m x) ^\<^sub>m a) ^\<^sub>m n) ys) @ mod_exp1 xs ys" | 
"mod_exp1 (x#xs) ys = mod_exp1 xs ys"

value "mod_exp1 [(g\<^sub>m (nmk 0)) ^\<^sub>m (MNon (nmk 0))] [(MNon (nmk 0)), (MNon (nmk 1))]"

definition "mod_exp1' xs = (mod_exp1 xs (extract_nonces xs))"

text \<open> @{text "build1\<^sub>n knows pks sks nc ne l"} where 
@{text "knows"} is a list of atomic messages;
@{text "pks"} - a list of public keys;
@{text "sks"} - a list of private keys; 
@{text "nc"} - the number of times of composition;  
@{text "ne"} - the number of times of encryption (symmetric this case); 
@{text "l"} - the maximum length of a composed message
\<close>
fun build\<^sub>ns::"dmsg list \<Rightarrow> dkey list \<Rightarrow> dkey list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dmsg list" where
\<comment> \<open> Original xs is always in the result \<close>
"build\<^sub>ns xs pks sks 0 0 l = xs" |
"build\<^sub>ns xs pks sks (Suc nc) 0 l = (build\<^sub>ns (List.union (pair2 xs xs l) xs) pks sks nc 0 l)" | 
"build\<^sub>ns xs pks sks 0 (Suc ne) l = (build\<^sub>ns (List.union (senc\<^sub>1' xs) xs) pks sks 0 ne l)" |
\<comment> \<open> Original xs + new messages after composition + new messages after encryption \<close>
"build\<^sub>ns xs pks sks (Suc nc) (Suc ne) l = (if ne = 0 then
  \<comment> \<open> If only one encryption, we treat it as outermost so composition first \<close>
  (build\<^sub>ns (List.union (pair2 xs xs l) xs) pks sks nc (Suc 0) l)
else 
  (List.union 
  \<comment> \<open> New messages after composition \<close>
    (build\<^sub>ns (List.union (pair2 xs xs l) xs) pks sks nc (Suc ne) l)
  \<comment> \<open> New messages after encryption \<close>
    (build\<^sub>ns (List.union (senc\<^sub>1' xs) xs) pks sks (Suc nc) ne l)
  )
)"

fun build\<^sub>na::"dmsg list \<Rightarrow> dkey list \<Rightarrow> dkey list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dmsg list" where
\<comment> \<open> Original xs is always in the result \<close>
"build\<^sub>na xs pks sks 0 0 l = xs" |
"build\<^sub>na xs pks sks (Suc nc) 0 l = (build\<^sub>na (List.union (pair2 xs xs l) xs) pks sks nc 0 l)" | 
"build\<^sub>na xs pks sks 0 (Suc ne) l = (build\<^sub>na (List.union (aenc\<^sub>1' xs) xs) pks sks 0 ne l)" |
\<comment> \<open> Original xs + new messages after composition + new messages after encryption \<close>
"build\<^sub>na xs pks sks (Suc nc) (Suc ne) l = (if ne = 0 then
  \<comment> \<open> If only one encryption, we treat it as outermost so composition first \<close>
  (build\<^sub>na (List.union (pair2 xs xs l) xs) pks sks nc (Suc 0) l)
else 
  (List.union 
  \<comment> \<open> New messages after composition \<close>
    (build\<^sub>na (List.union (pair2 xs xs l) xs) pks sks nc (Suc ne) l)
  \<comment> \<open> New messages after encryption \<close>
    (build\<^sub>na (List.union (aenc\<^sub>1' xs) xs) pks sks (Suc nc) ne l)
  )
)"

fun build\<^sub>nd::"dmsg list \<Rightarrow> dkey list \<Rightarrow> dkey list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dmsg list" where
\<comment> \<open> Original xs is always in the result \<close>
"build\<^sub>nd xs pks sks 0 0 l = xs" |
"build\<^sub>nd xs pks sks (Suc nc) 0 l = (build\<^sub>nd (List.union (pair2 xs xs l) xs) pks sks nc 0 l)" | 
"build\<^sub>nd xs pks sks 0 (Suc ne) l = (build\<^sub>nd (List.union (dsig\<^sub>1' xs) xs) pks sks 0 ne l)" |
\<comment> \<open> Original xs + new messages after composition + new messages after encryption \<close>
"build\<^sub>nd xs pks sks (Suc nc) (Suc ne) l = (if ne = 0 then
  \<comment> \<open> If only one encryption, we treat it as outermost so composition first \<close>
  (build\<^sub>nd (List.union (pair2 xs xs l) xs) pks sks nc (Suc 0) l)
else 
  (List.union 
  \<comment> \<open> New messages after composition \<close>
    (build\<^sub>nd (List.union (pair2 xs xs l) xs) pks sks nc (Suc ne) l)
  \<comment> \<open> New messages after encryption \<close>
    (build\<^sub>nd (List.union (dsig\<^sub>1' xs) xs) pks sks (Suc nc) ne l)
  )
)"

value "let xs = sort [MNon (nmk 0), (MAg (Agent (nmk 1))), MK (Kp (nmk 0))]
  in build\<^sub>ns xs (extract_dkeyp xs) (extract_dkeys xs) 0 0 2"

value "let xs = sort [MNon (nmk 0), MK (Kp (nmk 1))]
  in build\<^sub>ns xs (extract_dkeyp xs) (extract_dkeys xs) 1 1 2"
*)

text \<open> Instead of building up messages, we can alternatively ask whether the supplied messages can 
be built up from the given atomic message. \<close>
fun buildable :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg set \<Rightarrow> bool" where
"buildable m ms = (if m \<in> ms then True else 
  (case m of 
    (MAg a) \<Rightarrow> False |
    (MNon a) \<Rightarrow> False |
    (MK a) \<Rightarrow> False |
    (MPair m1 m2) \<Rightarrow> buildable m1 ms \<and> buildable m2 ms |
    (MAEnc m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MSig m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MSEnc m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MExpg a) \<Rightarrow> False |
    (MModExp m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MBitm b) \<Rightarrow> False |
    (MWat m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    \<comment> \<open>Jam2 is omitted: building a jammed message is not part of the intruder's capabilities here. \<close>
    (MJam m k) \<Rightarrow> False
  )
)
"

value "buildable (MAg (Agent (nmk 0)) :: (2,4,4,2,2,2,1) dmsg) {MAg (Agent (nmk 1)), MAg (Agent (nmk 0))}"
value "buildable (MAg (Agent (nmk 1)) :: (2,4,4,2,2,2,1) dmsg) {MAg (Agent (nmk 0))}"

definition filter_buildable :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg set \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"filter_buildable xs ms = [x. x \<leftarrow> xs, buildable x ms]"

text \<open> To get the last element from a tuple of 4 elements \<close>
definition last4 :: "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'd" where
"last4 x = snd (snd (snd x))"

(*
text \<open> @{text "pair2 xs ys l"}: pair message once for each element of @{text "xs"} with 
every element of @{text "ys"} if they are different, their length does not exceed the given @{text 
"l"} which denotes the maximum length of a composed message. 
\<close>
fun pair2 :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> nat \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"pair2 [] ys l = []" |
"pair2 (x#xs) ys l = 
\<comment> \<open> If a watermarked or jammed message, ignore it.\<close>
\<^cancel>\<open>(if is_MWat x \<or> is_MJam x then pair2 xs ys l
 else \<close>
(let cs = pair2 xs ys l in
    (map (\<lambda>n. msort (MPair x n)) \<comment> \<open> Sort the components in MPair \<close>
      (filter 
        \<comment> \<open> they are not the same, length won't exceed l, and they are not watermarked and jammed \<close>
        (\<lambda>y. y \<noteq> x \<and> msg_length x + msg_length y \<le> l \<and> \<not> is_MWat y \<and> \<not> is_MJam y) 
      ys)
    ) @ cs)
\<^cancel>\<open>)\<close>"

text \<open> @{text "wat msgs bitms"} - watermark all messages in @{text "msgs"} with each bitmark from bitms\<close>
fun wat :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"wat [] bms = []" |
"wat (x#xs) bms = 
  \<comment> \<open> Ignore bitmasks, watermarked, and jammed messages because we won't watermark these messages \<close>
  (if is_MBitm x \<or> is_MJam x \<or> is_MWat x then wat xs bms 
   else (map (\<lambda>k. MWat x k) bms) @ wat xs bms)"

value "wat [mknon 0, \<lbrace>(mkag 1), (mknon 0)\<rbrace>\<^sub>m] [mkbm 0, mkbm 1] :: (2,4,4,2,2,2) dmsg list "

definition "wat' xs = (wat xs (filter is_MBitm xs))"

text \<open> @{text "jam msgs bitms"} - jam all messages in @{text "msgs"} with each bitmark from bitms\<close>
fun jam :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"jam [] bms = []" |
"jam (x#xs) bms = (if is_MBitm x then jam xs bms \<comment> \<open> Ignore bitmasks\<close>
  else (map (\<lambda>k. MJam x k) bms) @ jam xs bms)"

definition "jam' xs = (jam xs (filter is_MBitm xs))"

text \<open> Watermarked input messages using bitmarks in those messages \<close>
definition buildw :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> nat 
  \<Rightarrow> ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"buildw xs n = (let 
    \<comment> \<open> We won't pair watermarked or jammed messages \<close>
    xs' = filter (\<lambda>m. \<not> (is_MWat m \<or> is_MJam m)) xs;
    ps = (pair2 xs' xs' n);
    cs = (List.union ps xs)
  in
    wat' cs
    \<^cancel>\<open>(List.union (wat' cs) cs)\<close>
)"

value "buildw [mknon 0, mknon 1, mkbm 2] 2"
*)

subsection \<open> Metatheoretic properties \<close>

text \<open> We record and prove the metatheoretic properties of the symbolic framework stated
informally in the accompanying paper. They are properties of the message theory itself, rather
than of any particular protocol instance: knowledge monotonicity for the build-up inference
relation, injectivity of watermarking and jamming (non-forgeability), the prefix characterisation
of the bitmask order that underlies jamming elimination, and the asymmetry between replay (rule
Wat1) and forgery (rule Wat2) at the level of the breakdown function @{text breakl}. \<close>

subsubsection \<open> Buildable messages \<close>

text \<open> We record the defining equation of @{text buildable} for each constructor, so that
@{text simp} unfolds @{text "buildable m ms"} only when @{text m} is a concrete message; this
avoids splitting on the structure of sub-term variables during the structural inductions below. \<close>

declare buildable.simps[simp del]

lemma buildable_MAg[simp]: "buildable (MAg a) ms = (MAg a \<in> ms)"
  by (simp add: buildable.simps)
lemma buildable_MNon[simp]: "buildable (MNon a) ms = (MNon a \<in> ms)"
  by (simp add: buildable.simps)
lemma buildable_MK[simp]: "buildable (MK a) ms = (MK a \<in> ms)"
  by (simp add: buildable.simps)
lemma buildable_MPair[simp]:
  "buildable (MPair m1 m2) ms = (MPair m1 m2 \<in> ms \<or> (buildable m1 ms \<and> buildable m2 ms))"
  by (simp add: buildable.simps)
lemma buildable_MAEnc[simp]:
  "buildable (MAEnc m k) ms = (MAEnc m k \<in> ms \<or> (buildable m ms \<and> buildable k ms))"
  by (simp add: buildable.simps)
lemma buildable_MSig[simp]:
  "buildable (MSig m k) ms = (MSig m k \<in> ms \<or> (buildable m ms \<and> buildable k ms))"
  by (simp add: buildable.simps)
lemma buildable_MSEnc[simp]:
  "buildable (MSEnc m k) ms = (MSEnc m k \<in> ms \<or> (buildable m ms \<and> buildable k ms))"
  by (simp add: buildable.simps)
lemma buildable_MExpg[simp]: "buildable (MExpg a) ms = (MExpg a \<in> ms)"
  by (simp add: buildable.simps)
lemma buildable_MModExp[simp]:
  "buildable (MModExp m k) ms = (MModExp m k \<in> ms \<or> (buildable m ms \<and> buildable k ms))"
  by (simp add: buildable.simps)
lemma buildable_MBitm[simp]: "buildable (MBitm b) ms = (MBitm b \<in> ms)"
  by (simp add: buildable.simps)
lemma buildable_MWat[simp]:
  "buildable (MWat m k) ms = (MWat m k \<in> ms \<or> (buildable m ms \<and> buildable k ms))"
  by (simp add: buildable.simps)
lemma buildable_MJam[simp]: "buildable (MJam m k) ms = (MJam m k \<in> ms)"
  by (simp add: buildable.simps)

subsubsection \<open> Declarative inference relations \<close>

text \<open> Table 3 of the accompanying paper states the intruder's inference rules in a rule style,
whereas @{text break_lst} and @{text buildable} implement them. To relate the two we record the
rules as inductive relations over the intruder's knowledge @{text K}: @{text "K \<turnstile>\<^sub>\<Down> m"} for
the breakdown rules and @{text "K \<turnstile>\<^sub>\<Up> m"} for the build-up rules. The names of the rules
(@{text Mb}, @{text Up}, @{text Dec}, @{text Ver}, @{text Wat1}, @{text Jam}, @{text Dh}, @{text Pa},
@{text Enc}, @{text Sig}, @{text SDec}, @{text Wat2}, @{text Jam2}, @{text Ex}) follow the table. The
premises of a rule are stated in terms of the relation itself, so that the closure is computed
over knowledge that the intruder has already derived, as in the implementation. \<close>

inductive
  breakdown :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg set
                \<Rightarrow> ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>\<Down> _" [50, 50] 50)
where
  Mb_break: "m \<in> K \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m" |
  Up_break1: "K \<turnstile>\<^sub>\<Down> MPair m1 m2 \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m1" |
  Up_break2: "K \<turnstile>\<^sub>\<Down> MPair m1 m2 \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m2" |
  Dec_break: "\<lbrakk> K \<turnstile>\<^sub>\<Down> MAEnc m (MK (Kp k)); K \<turnstile>\<^sub>\<Down> MK (Ks k) \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m" |
  Ver_break: "\<lbrakk> K \<turnstile>\<^sub>\<Down> MSig m (MK (Ks k)); K \<turnstile>\<^sub>\<Down> MK (Kp k) \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m" |
  SDec_break: "\<lbrakk> K \<turnstile>\<^sub>\<Down> MSEnc m (MK (Ks k)); K \<turnstile>\<^sub>\<Down> MK (Ks k) \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m" |
  Wat1_break: "K \<turnstile>\<^sub>\<Down> MWat m b \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m" |
  Jam_break: "\<lbrakk> K \<turnstile>\<^sub>\<Down> MJam (MWat m (MBitm (bb :: ('bm, 'bl) dbitmask))) (MBitm (b :: ('bm, 'bl) dbitmask));
                b = (Null :: ('bm, 'bl) dbitmask) \<or> (b \<le> bb \<and> K \<turnstile>\<^sub>\<Down> MBitm b) \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m" |
  Dh_break1: "\<lbrakk> K \<turnstile>\<^sub>\<Down> MSEnc m (MModExp (MModExp (MExpg gn) a) b);
               K \<turnstile>\<^sub>\<Down> MModExp (MExpg gn) a; K \<turnstile>\<^sub>\<Down> b \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m" |
  Dh_break2: "\<lbrakk> K \<turnstile>\<^sub>\<Down> MSEnc m (MModExp (MModExp (MExpg gn) a) b);
               K \<turnstile>\<^sub>\<Down> MModExp (MExpg gn) b; K \<turnstile>\<^sub>\<Down> a \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m" |
  Dh_break3: "\<lbrakk> K \<turnstile>\<^sub>\<Down> MSEnc m (MModExp (MModExp (MExpg gn) a) b);
               K \<turnstile>\<^sub>\<Down> MExpg gn; K \<turnstile>\<^sub>\<Down> a; K \<turnstile>\<^sub>\<Down> b \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m"

inductive
  buildup :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg set
              \<Rightarrow> ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>\<Up> _" [50, 50] 50)
where
  Mb_build: "m \<in> K \<Longrightarrow> K \<turnstile>\<^sub>\<Up> m" |
  Pa_build: "\<lbrakk> K \<turnstile>\<^sub>\<Up> m1; K \<turnstile>\<^sub>\<Up> m2 \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Up> MPair m1 m2" |
  Enc_build: "\<lbrakk> K \<turnstile>\<^sub>\<Up> m; K \<turnstile>\<^sub>\<Up> k \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Up> MAEnc m k" |
  Sig_build: "\<lbrakk> K \<turnstile>\<^sub>\<Up> m; K \<turnstile>\<^sub>\<Up> k \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Up> MSig m k" |
  SEnc_build: "\<lbrakk> K \<turnstile>\<^sub>\<Up> m; K \<turnstile>\<^sub>\<Up> k \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Up> MSEnc m k" |
  Ex_build: "\<lbrakk> K \<turnstile>\<^sub>\<Up> m; K \<turnstile>\<^sub>\<Up> e \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Up> MModExp m e" |
  Wat2_build: "\<lbrakk> K \<turnstile>\<^sub>\<Up> m; K \<turnstile>\<^sub>\<Up> b \<rbrakk> \<Longrightarrow> K \<turnstile>\<^sub>\<Up> MWat m b"

text \<open> The build-up relation is exactly the predicate @{text buildable}: the two are the same
least fixed point, which is what relates the right-hand column of the table to the function that
the intruder process uses to choose the messages she sends. \<close>

lemma buildup_buildable: "K \<turnstile>\<^sub>\<Up> m \<longleftrightarrow> buildable m K"
proof
  assume "K \<turnstile>\<^sub>\<Up> m"
  then show "buildable m K" by (induct) (auto simp: buildable.simps)
next
  assume "buildable m K"
  then show "K \<turnstile>\<^sub>\<Up> m" by (induct m) (auto intro: buildup.intros)
qed

text \<open> Two remarks on how the relations correspond to the implementation, both of which are
visible in the equations of @{text break_lst}. First, the equation for @{text MJam} recovers the
jammed message as soon as the jamming bitmask is known or empty, without requiring the jammed
message to be a watermark that the bitmask prefixes; rule @{text Jam_break} therefore generalises
the entry of the table, whose premise is the prefix test performed by the receiver. Second, the
equation for @{text MPair} keeps the closures of the two components but not the pair itself, so the
pair is recovered through the build-up rule @{text Pa_build} rather than through @{text Up}. The
type variable duplicated in the signature of @{text breakdown} mirrors the signature of
@{text break_lst}, where public and private keys share one index space. \<close>

subsubsection \<open> Closure laws \<close>

text \<open> Elementary properties of the saturation loop: it retains its argument, it is extensive
in the number of rounds, and every round is monotone in the sub-term closure. \<close>

lemma iter_closure_fix: "step_once K = K \<Longrightarrow> iter_closure n K = K"
  by (induct n) auto

lemma step_once_extensive: "set K \<subseteq> set (step_once K)"
  by (auto simp: step_once_def)

lemma iter_closure_extensive: "set K \<subseteq> set (iter_closure n K)"
proof (induct n arbitrary: K)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have h1: "set K \<subseteq> set (step_once K)" by (rule step_once_extensive)
  have h2: "set (step_once K) \<subseteq> set (iter_closure n (step_once K))" by (rule Suc)
  show ?case using subset_trans[OF h1 h2] by simp
qed

lemma breakl_extensive: "set xs \<subseteq> set (breakl xs)"
  unfolding breakl_def
  using iter_closure_extensive[of "remdups xs" "List.length (submsgs_list xs) + 1"]
  by (simp add: set_remdups)

lemma step_once_subset_iter_Suc: "set (step_once K) \<subseteq> set (iter_closure (Suc n) K)"
  using iter_closure_extensive[of "step_once K" n] by simp

subsubsection \<open> Soundness of the implementation \<close>

text \<open> The closure @{text breakl} derives only messages derivable by the breakdown rules of the
table. A round of @{text step_once} adds the immediate consequences of the messages already known,
so it suffices to check that @{text one_step} implements one rule application: whenever the side
conditions of a case hold, the conclusion of the corresponding rule follows from the message and
the messages already in the accumulator. \<close>

lemma one_step_sound:
  fixes K0 :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg set"
  assumes hK: "K \<subseteq> {m. K0 \<turnstile>\<^sub>\<Down> m}" and hm: "K0 \<turnstile>\<^sub>\<Down> m"
  shows "set (one_step m K) \<subseteq> {m. K0 \<turnstile>\<^sub>\<Down> m}"
  using assms
proof (cases m)
  case (MAg a)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MNon a)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MK k)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MPair m1 m2)
  then show ?thesis using hm by (auto simp: one_step.simps intro: Up_break1 Up_break2)
next
  case (MAEnc m' k)
  then show ?thesis
  proof (cases k)
    case (MK k')
    then show ?thesis using hm MAEnc
      by (cases k'; auto simp: one_step.simps intro: Dec_break dest: subsetD[OF hK])
  qed (simp_all add: one_step.simps)
next
  case (MSig m' k)
  then show ?thesis
  proof (cases k)
    case (MK k')
    then show ?thesis using hm MSig
      by (cases k'; auto simp: one_step.simps intro: Ver_break dest: subsetD[OF hK])
  qed (simp_all add: one_step.simps)
next
  case (MSEnc m' k)
  note hmk = \<open>m = MSEnc m' k\<close>
  then show ?thesis using hm
  proof (cases k)
    case (MK k')
    note hk = \<open>k = MK k'\<close>
    then show ?thesis using hm
      by (cases k'; auto simp: one_step.simps hmk hk intro: SDec_break dest: subsetD[OF hK])
  next
    case (MModExp k1 k2)
    note hk = \<open>k = MModExp k1 k2\<close>
    then show ?thesis using hm
    proof (cases k1)
      case (MModExp k11 k12)
      note hk1 = \<open>k1 = MModExp k11 k12\<close>
      then show ?thesis using hm
      proof (cases k11)
        case (MExpg gn)
        then show ?thesis using hm
          by (auto simp: one_step.simps hmk hk hk1 \<open>k11 = MExpg gn\<close>
                   intro: Dh_break1 Dh_break2 Dh_break3 dest: subsetD[OF hK])
      qed (auto simp: one_step.simps hmk hk hk1)
    qed (auto simp: one_step.simps hmk hk)
  qed (auto simp: one_step.simps hmk)
next
  case (MExpg a)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MModExp m' k)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MBitm b)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MWat m' b)
  then show ?thesis using hm by (auto simp: one_step.simps intro: Wat1_break)
next
  case (MJam m' k)
  then show ?thesis
  proof (cases k)
    case (MBitm b)
    then show ?thesis using hm MJam
    proof (cases m')
      case (MWat m'' k2)
      then show ?thesis using hm MJam MBitm
      proof (cases k2)
        case (MBitm bb)
        then show ?thesis using hm MJam MBitm MWat
          by (auto simp: one_step.simps intro: Jam_break dest: subsetD[OF hK])
      qed (simp_all add: one_step.simps)
    qed (simp_all add: one_step.simps)
  qed (simp_all add: one_step.simps)
qed

lemma step_once_sound:
  fixes K0 :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg set"
  assumes hK: "set K \<subseteq> {m. K0 \<turnstile>\<^sub>\<Down> m}"
  shows "set (step_once K) \<subseteq> {m. K0 \<turnstile>\<^sub>\<Down> m}"
proof
  fix m
  assume hm: "m \<in> set (step_once K)"
  have step: "m \<in> set K \<or> (\<exists>x\<in>set K. m \<in> set (one_step x (set K)))"
    using hm by (auto simp: step_once_def)
  from step show "m \<in> {m. K0 \<turnstile>\<^sub>\<Down> m}"
  proof (rule disjE)
    assume hmK: "m \<in> set K"
    from subsetD[OF hK hmK] show "m \<in> {m. K0 \<turnstile>\<^sub>\<Down> m}" .
  next
    assume "\<exists>x\<in>set K. m \<in> set (one_step x (set K))"
    then obtain x where hx: "x \<in> set K" and hmx: "m \<in> set (one_step x (set K))" by auto
    from subsetD[OF hK hx] have hxK: "K0 \<turnstile>\<^sub>\<Down> x" by simp
    from one_step_sound[OF hK hxK] have "set (one_step x (set K)) \<subseteq> {m. K0 \<turnstile>\<^sub>\<Down> m}" .
    from subsetD[OF this hmx] show "m \<in> {m. K0 \<turnstile>\<^sub>\<Down> m}" .
  qed
qed

lemma iter_closure_sound:
  fixes K0 :: "('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg set"
  shows "\<And>K. set K \<subseteq> {m. K0 \<turnstile>\<^sub>\<Down> m} \<Longrightarrow> set (iter_closure n K) \<subseteq> {m. K0 \<turnstile>\<^sub>\<Down> m}"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have h: "set (step_once K) \<subseteq> {m. K0 \<turnstile>\<^sub>\<Down> m}" using Suc.prems by (rule step_once_sound)
  from Suc.hyps(1)[OF h] show ?case by simp
qed

lemma breakl_sound: "set (breakl xs) \<subseteq> {m. set xs \<turnstile>\<^sub>\<Down> m}"
proof -
  have h: "set (remdups xs) \<subseteq> {m. set xs \<turnstile>\<^sub>\<Down> m}" by (auto intro: breakdown.intros)
  have h2: "set (step_once (remdups xs)) \<subseteq> {m. set xs \<turnstile>\<^sub>\<Down> m}"
    using h by (rule step_once_sound)
  have h3: "set (iter_closure (List.length (submsgs_list xs)) (step_once (remdups xs)))
            \<subseteq> {m. set xs \<turnstile>\<^sub>\<Down> m}"
    using iter_closure_sound[OF h2] .
  have "set (breakl xs) = set (iter_closure (List.length (submsgs_list xs)) (step_once (remdups xs)))"
    by (simp add: breakl_def)
  with h3 show ?thesis by simp
qed

subsubsection \<open> Completeness of the implementation \<close>

text \<open> Conversely every message that the rules derive occurs in the closure. Since @{text step_once}
retains its argument it suffices to show that the closure is stable, i.e. that after enough rounds
no new message appears. Every message produced by @{text one_step} is a sub-term of the message it
is applied to, so all rounds stay inside the sub-term closure of the input, and @{text breakl}
performs as many rounds as that closure has elements. \<close>

lemma submsg_list_self: "m \<in> set (submsg_list m)"
  by (induct m) auto

lemma submsg_list_mono:
  "m' \<in> set (submsg_list m) \<Longrightarrow> set (submsg_list m') \<subseteq> set (submsg_list m)"
  by (induct m) auto

lemma one_step_subterms: "set (one_step m K) \<subseteq> set (submsg_list m)"
proof (cases m)
  case (MAg a)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MNon a)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MK k)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MPair m1 m2)
  then show ?thesis by (auto simp: one_step.simps submsg_list_self)
next
  case (MAEnc m' k)
  note hm = \<open>m = MAEnc m' k\<close>
  then show ?thesis
  proof (cases k)
    case (MK k')
    then show ?thesis using MAEnc
      by (cases k'; auto simp: one_step.simps submsg_list_self hm \<open>k = MK k'\<close>)
  qed (auto simp: one_step.simps hm)
next
  case (MSig m' k)
  note hm = \<open>m = MSig m' k\<close>
  then show ?thesis
  proof (cases k)
    case (MK k')
    then show ?thesis using MSig
      by (cases k'; auto simp: one_step.simps submsg_list_self hm \<open>k = MK k'\<close>)
  qed (auto simp: one_step.simps hm)
next
  case (MSEnc m' k)
  note hm = \<open>m = MSEnc m' k\<close>
  then show ?thesis
  proof (cases k)
    case (MK k')
    then show ?thesis using MSEnc
      by (cases k'; auto simp: one_step.simps submsg_list_self hm \<open>k = MK k'\<close>)
  next
    case (MModExp k1 k2)
    note hk = \<open>k = MModExp k1 k2\<close>
    then show ?thesis using MSEnc
    proof (cases k1)
      case (MModExp k11 k12)
      note hk1 = \<open>k1 = MModExp k11 k12\<close>
      then show ?thesis using MSEnc MModExp
      proof (cases k11)
        case (MExpg gn)
        then show ?thesis using MSEnc MModExp MModExp MExpg
          by (auto simp: one_step.simps submsg_list_self hm hk hk1 \<open>k11 = MExpg gn\<close>)
      qed (auto simp: one_step.simps hm hk hk1)
    qed (auto simp: one_step.simps hm hk)
  qed (auto simp: one_step.simps hm)
next
  case (MExpg a)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MModExp m' k)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MBitm b)
  then show ?thesis by (simp add: one_step.simps)
next
  case (MWat m' b)
  then show ?thesis by (auto simp: one_step.simps submsg_list_self)
next
  case (MJam m' k)
  note hm = \<open>m = MJam m' k\<close>
  then show ?thesis
  proof (cases k)
    case (MBitm b)
    note hk = \<open>k = MBitm b\<close>
    then show ?thesis using MJam
    proof (cases m')
      case (MWat m'' k2)
      note hm' = \<open>m' = MWat m'' k2\<close>
      then show ?thesis using MJam MBitm
      proof (cases k2)
        case (MBitm bb)
        then show ?thesis using MJam MBitm MWat
          by (auto simp: one_step.simps submsg_list_self hm hk hm' \<open>k2 = MBitm bb\<close>)
      qed (auto simp: one_step.simps hm hk hm')
    qed (auto simp: one_step.simps hm hk)
  qed (auto simp: one_step.simps hm)
qed

lemma submsgs_list_closed:
  "m \<in> set (submsgs_list xs) \<Longrightarrow> set (submsg_list m) \<subseteq> set (submsgs_list xs)"
proof -
  assume "m \<in> set (submsgs_list xs)"
  then obtain x where hx: "x \<in> set xs" and hm: "m \<in> set (submsg_list x)"
    by (auto simp: submsgs_list_def)
  have "set (submsg_list m) \<subseteq> set (submsg_list x)" using hm by (rule submsg_list_mono)
  also have "\<dots> \<subseteq> set (submsgs_list xs)" using hx by (auto simp: submsgs_list_def)
  finally show ?thesis .
qed

lemma step_once_subterms:
  assumes h: "set K \<subseteq> set (submsgs_list xs)"
  shows "set (step_once K) \<subseteq> set (submsgs_list xs)"
proof
  fix x
  assume hx: "x \<in> set (step_once K)"
  have step: "x \<in> set K \<or> (\<exists>m\<in>set K. x \<in> set (one_step m (set K)))"
    using hx by (auto simp: step_once_def)
  from step show "x \<in> set (submsgs_list xs)"
  proof (rule disjE)
    assume "x \<in> set K"
    with h show "x \<in> set (submsgs_list xs)" by (rule subsetD)
  next
    assume "\<exists>m\<in>set K. x \<in> set (one_step m (set K))"
    then obtain m where hm: "m \<in> set K" and hx2: "x \<in> set (one_step m (set K))" by auto
    from h hm have hmS: "m \<in> set (submsgs_list xs)" by (rule subsetD)
    have hxsub: "x \<in> set (submsg_list m)" using hx2 by (rule subsetD[OF one_step_subterms])
    from submsgs_list_closed[OF hmS] hxsub show "x \<in> set (submsgs_list xs)" by (rule subsetD)
  qed
qed

definition "cstep S = S \<union> (\<Union>x\<in>S. set (one_step x S))"

lemma set_step_once: "set (step_once K) = cstep (set K)"
  by (auto simp: step_once_def cstep_def)

lemma iter_closure_Suc: "iter_closure (Suc n) K = step_once (iter_closure n K)"
proof (induct n arbitrary: K)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case using Suc.hyps(1)[of "step_once K"] by simp
qed

lemma iter_closure_set_Suc:
  "set (iter_closure (Suc n) K) = cstep (set (iter_closure n K))"
  by (metis iter_closure_Suc set_step_once)

lemma set_iter_closure: "set (iter_closure n K) = (cstep ^^ n) (set K)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have ih: "set (iter_closure n K) = (cstep ^^ n) (set K)" using Suc.hyps(1) .
  have "set (iter_closure (Suc n) K) = cstep (set (iter_closure n K))"
    by (rule iter_closure_set_Suc)
  also have "\<dots> = cstep ((cstep ^^ n) (set K))" by (simp add: ih)
  also have "\<dots> = (cstep ^^ Suc n) (set K)" by simp
  finally show ?case .
qed

lemma cstep_extensive: "S \<subseteq> cstep S"
  by (auto simp: cstep_def)

lemma cstep_subterms:
  assumes h: "S \<subseteq> set (submsgs_list xs)"
  shows "cstep S \<subseteq> set (submsgs_list xs)"
proof
  fix x
  assume hx: "x \<in> cstep S"
  have "x \<in> S \<or> (\<exists>m\<in>S. x \<in> set (one_step m S))" using hx by (auto simp: cstep_def)
  then show "x \<in> set (submsgs_list xs)"
  proof (rule disjE)
    assume "x \<in> S"
    with h show "x \<in> set (submsgs_list xs)" by (rule subsetD)
  next
    assume "\<exists>m\<in>S. x \<in> set (one_step m S)"
    then obtain m where hm: "m \<in> S" and hx2: "x \<in> set (one_step m S)" by auto
    from h hm have hmS: "m \<in> set (submsgs_list xs)" by (rule subsetD)
    have hxsub: "x \<in> set (submsg_list m)" using hx2 by (rule subsetD[OF one_step_subterms])
    from submsgs_list_closed[OF hmS] hxsub show "x \<in> set (submsgs_list xs)" by (rule subsetD)
  qed
qed

lemma cstep_chain:
  assumes h: "S \<subseteq> set (submsgs_list xs)"
  shows "(cstep ^^ n) S \<subseteq> set (submsgs_list xs)"
  using h
proof (induct n arbitrary: S)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "cstep ((cstep ^^ n) S) \<subseteq> set (submsgs_list xs)"
    using cstep_subterms[OF Suc.hyps(1)[OF Suc.prems]] .
  then show ?case by simp
qed

lemma cstep_fixed: "cstep X = X \<Longrightarrow> (cstep ^^ n) X = X"
  by (induct n) auto

lemma cstep_card_growth:
  assumes hS: "S \<subseteq> set (submsgs_list xs)"
  shows "(\<And>i. i < n \<Longrightarrow> cstep ((cstep ^^ i) S) \<noteq> (cstep ^^ i) S)
         \<Longrightarrow> card S + n \<le> card ((cstep ^^ n) S)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have ih: "card S + n \<le> card ((cstep ^^ n) S)"
  proof (rule Suc.hyps)
    fix i assume "i < n"
    with Suc.prems show "cstep ((cstep ^^ i) S) \<noteq> (cstep ^^ i) S" by simp
  qed
  have sub: "(cstep ^^ n) S \<subseteq> cstep ((cstep ^^ n) S)" by (rule cstep_extensive)
  have ne: "cstep ((cstep ^^ n) S) \<noteq> (cstep ^^ n) S" using Suc.prems by simp
  have chain: "cstep ((cstep ^^ n) S) \<subseteq> set (submsgs_list xs)"
    using cstep_chain[OF hS, of "Suc n"] by simp
  have fin: "finite (cstep ((cstep ^^ n) S))" using chain by (rule finite_subset) simp
  have "card ((cstep ^^ n) S) \<noteq> card (cstep ((cstep ^^ n) S))"
  proof
    assume eq: "card ((cstep ^^ n) S) = card (cstep ((cstep ^^ n) S))"
    from card_seteq[OF fin sub] eq have "(cstep ^^ n) S = cstep ((cstep ^^ n) S)" by simp
    with ne show False by simp
  qed
  moreover have "card ((cstep ^^ n) S) \<le> card (cstep ((cstep ^^ n) S))"
    by (rule card_mono[OF fin sub])
  ultimately have "card ((cstep ^^ n) S) < card (cstep ((cstep ^^ n) S))" by simp
  with ih show ?case by simp
qed

lemma cstep_eventually_stable:
  assumes hS: "S \<subseteq> set (submsgs_list xs)"
  shows "cstep ((cstep ^^ List.length (submsgs_list xs)) S) = (cstep ^^ List.length (submsgs_list xs)) S"
proof (rule ccontr)
  let ?B = "List.length (submsgs_list xs)"
  assume hne: "cstep ((cstep ^^ ?B) S) \<noteq> (cstep ^^ ?B) S"
  have h1: "card S + (?B + 1) \<le> card ((cstep ^^ (?B + 1)) S)"
  proof (rule cstep_card_growth[OF hS])
    fix i assume hi: "i < ?B + 1"
    show "cstep ((cstep ^^ i) S) \<noteq> (cstep ^^ i) S"
    proof
      assume eq: "cstep ((cstep ^^ i) S) = (cstep ^^ i) S"
      have hprop: "\<And>k. (cstep ^^ k) ((cstep ^^ i) S) = (cstep ^^ i) S"
        by (rule cstep_fixed[OF eq])
      have "i \<le> ?B" using hi by simp
      then have "(cstep ^^ ?B) S = (cstep ^^ ((?B - i) + i)) S" by simp
      also have "\<dots> = (cstep ^^ (?B - i)) ((cstep ^^ i) S)" by (simp add: funpow_add)
      also have "\<dots> = (cstep ^^ i) S" using hprop by simp
      finally have "(cstep ^^ ?B) S = (cstep ^^ i) S" .
      with eq hne show False by simp
    qed
  qed
  have h2: "card ((cstep ^^ (?B + 1)) S) \<le> card (set (submsgs_list xs))"
  proof -
    have sub2: "(cstep ^^ (?B + 1)) S \<subseteq> set (submsgs_list xs)"
      using cstep_chain[OF hS, of "?B + 1"] .
    have fin2: "finite (set (submsgs_list xs))" by simp
    from card_mono[OF fin2 sub2] show ?thesis .
  qed
  have h3: "card (set (submsgs_list xs)) = ?B"
  proof -
    have d: "distinct (submsgs_list xs)" by (simp add: submsgs_list_def)
    from distinct_card[OF d] show ?thesis by simp
  qed
  from h1 h2 h3 show False by simp
qed

lemma breakl_stable: "cstep (set (breakl xs)) = set (breakl xs)"
proof -
  let ?S = "set (remdups xs)"
  let ?B = "List.length (submsgs_list xs)"
  have hS: "?S \<subseteq> set (submsgs_list xs)" by (auto simp: submsgs_list_def submsg_list_self)
  have fx: "cstep ((cstep ^^ ?B) ?S) = (cstep ^^ ?B) ?S"
    by (rule cstep_eventually_stable[OF hS])
  have bl: "set (breakl xs) = (cstep ^^ (?B + 1)) ?S"
  proof -
    have "set (breakl xs) = set (iter_closure (?B + 1) (remdups xs))" by (simp add: breakl_def)
    also have "\<dots> = (cstep ^^ (?B + 1)) (set (remdups xs))" by (rule set_iter_closure)
    finally show ?thesis .
  qed
  have c1: "cstep ((cstep ^^ (?B + 1)) ?S) = (cstep ^^ (?B + 1)) ?S"
  proof -
    have "(cstep ^^ (?B + 1)) ?S = cstep ((cstep ^^ ?B) ?S)"
      by simp
    with fx show ?thesis by simp
  qed
  from bl c1 show ?thesis by simp
qed

lemma cstep_Up1: "MPair m1 m2 \<in> S \<Longrightarrow> m1 \<in> cstep S"
proof -
  assume h: "MPair m1 m2 \<in> S"
  have hstep: "m1 \<in> set (one_step (MPair m1 m2) S)" by (simp add: one_step.simps)
  have "m1 \<in> (\<Union>x\<in>S. set (one_step x S))" using h hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_Up2: "MPair m1 m2 \<in> S \<Longrightarrow> m2 \<in> cstep S"
proof -
  assume h: "MPair m1 m2 \<in> S"
  have hstep: "m2 \<in> set (one_step (MPair m1 m2) S)" by (simp add: one_step.simps)
  have "m2 \<in> (\<Union>x\<in>S. set (one_step x S))" using h hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_Dec: "\<lbrakk> MAEnc m (MK (Kp k)) \<in> S; MK (Ks k) \<in> S \<rbrakk> \<Longrightarrow> m \<in> cstep S"
proof -
  assume h1: "MAEnc m (MK (Kp k)) \<in> S" and h2: "MK (Ks k) \<in> S"
  have hstep: "m \<in> set (one_step (MAEnc m (MK (Kp k))) S)" using h2 by (simp add: one_step.simps)
  have "m \<in> (\<Union>x\<in>S. set (one_step x S))" using h1 hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_Ver: "\<lbrakk> MSig m (MK (Ks k)) \<in> S; MK (Kp k) \<in> S \<rbrakk> \<Longrightarrow> m \<in> cstep S"
proof -
  assume h1: "MSig m (MK (Ks k)) \<in> S" and h2: "MK (Kp k) \<in> S"
  have hstep: "m \<in> set (one_step (MSig m (MK (Ks k))) S)" using h2 by (simp add: one_step.simps)
  have "m \<in> (\<Union>x\<in>S. set (one_step x S))" using h1 hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_SDec: "\<lbrakk> MSEnc m (MK (Ks k)) \<in> S; MK (Ks k) \<in> S \<rbrakk> \<Longrightarrow> m \<in> cstep S"
proof -
  assume h1: "MSEnc m (MK (Ks k)) \<in> S" and h2: "MK (Ks k) \<in> S"
  have hstep: "m \<in> set (one_step (MSEnc m (MK (Ks k))) S)" using h2 by (simp add: one_step.simps)
  have "m \<in> (\<Union>x\<in>S. set (one_step x S))" using h1 hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_Wat1: "MWat m b \<in> S \<Longrightarrow> m \<in> cstep S"
proof -
  assume h: "MWat m b \<in> S"
  have hstep: "m \<in> set (one_step (MWat m b) S)" by (simp add: one_step.simps)
  have "m \<in> (\<Union>x\<in>S. set (one_step x S))" using h hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_Jam:
  "\<lbrakk> MJam (MWat m (MBitm bb)) (MBitm b) \<in> S;
     b = Null \<or> (b \<le> bb \<and> MBitm b \<in> S) \<rbrakk> \<Longrightarrow> m \<in> cstep S"
proof -
  assume h1: "MJam (MWat m (MBitm bb)) (MBitm b) \<in> S"
     and h2: "b = Null \<or> (b \<le> bb \<and> MBitm b \<in> S)"
  have hstep: "m \<in> set (one_step (MJam (MWat m (MBitm bb)) (MBitm b)) S)"
    using h2 by (simp add: one_step.simps)
  have "m \<in> (\<Union>x\<in>S. set (one_step x S))" using h1 hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_Dh1:
  "\<lbrakk> MSEnc m (MModExp (MModExp (MExpg gn) a) b) \<in> S;
     MModExp (MExpg gn) a \<in> S; b \<in> S \<rbrakk> \<Longrightarrow> m \<in> cstep S"
proof -
  assume h1: "MSEnc m (MModExp (MModExp (MExpg gn) a) b) \<in> S"
     and h2: "MModExp (MExpg gn) a \<in> S" and h3: "b \<in> S"
  have hstep: "m \<in> set (one_step (MSEnc m (MModExp (MModExp (MExpg gn) a) b)) S)"
    using h2 h3 by (simp add: one_step.simps)
  have "m \<in> (\<Union>x\<in>S. set (one_step x S))" using h1 hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_Dh2:
  "\<lbrakk> MSEnc m (MModExp (MModExp (MExpg gn) a) b) \<in> S;
     MModExp (MExpg gn) b \<in> S; a \<in> S \<rbrakk> \<Longrightarrow> m \<in> cstep S"
proof -
  assume h1: "MSEnc m (MModExp (MModExp (MExpg gn) a) b) \<in> S"
     and h2: "MModExp (MExpg gn) b \<in> S" and h3: "a \<in> S"
  have hstep: "m \<in> set (one_step (MSEnc m (MModExp (MModExp (MExpg gn) a) b)) S)"
    using h2 h3 by (simp add: one_step.simps)
  have "m \<in> (\<Union>x\<in>S. set (one_step x S))" using h1 hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma cstep_Dh3:
  "\<lbrakk> MSEnc m (MModExp (MModExp (MExpg gn) a) b) \<in> S;
     MExpg gn \<in> S; a \<in> S; b \<in> S \<rbrakk> \<Longrightarrow> m \<in> cstep S"
proof -
  assume h1: "MSEnc m (MModExp (MModExp (MExpg gn) a) b) \<in> S"
     and h2: "MExpg gn \<in> S" and h3: "a \<in> S" and h4: "b \<in> S"
  have hstep: "m \<in> set (one_step (MSEnc m (MModExp (MModExp (MExpg gn) a) b)) S)"
    using h2 h3 h4 by (simp add: one_step.simps)
  have "m \<in> (\<Union>x\<in>S. set (one_step x S))" using h1 hstep by blast
  then show ?thesis by (auto simp: cstep_def)
qed

lemma breakl_complete: "set xs \<turnstile>\<^sub>\<Down> m \<Longrightarrow> m \<in> set (breakl xs)"
proof -
  let ?S = "set (breakl xs)"
  have fx: "cstep ?S = ?S" by (rule breakl_stable)
  have gen: "K \<subseteq> ?S \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m \<Longrightarrow> m \<in> ?S" for K
  proof -
    assume sub: "K \<subseteq> ?S"
    assume d: "K \<turnstile>\<^sub>\<Down> m"
    from d sub show "m \<in> ?S"
    proof (induct rule: breakdown.induct)
      case (Mb_break m)
      with sub show ?case by blast
    next
      case Up_break1
      with cstep_Up1 fx show ?case by blast
    next
      case Up_break2
      with cstep_Up2 fx show ?case by blast
    next
      case Dec_break
      with cstep_Dec fx show ?case by blast
    next
      case Ver_break
      with cstep_Ver fx show ?case by blast
    next
      case SDec_break
      with cstep_SDec fx show ?case by blast
    next
      case Wat1_break
      with cstep_Wat1 fx show ?case by blast
    next
      case Jam_break
      with cstep_Jam fx show ?case by blast
    next
      case Dh_break1
      with cstep_Dh1 fx show ?case by blast
    next
      case Dh_break2
      with cstep_Dh2 fx show ?case by blast
    next
      case Dh_break3
      with cstep_Dh3 fx show ?case by blast
    qed
  qed
  have base: "set xs \<subseteq> ?S" by (rule breakl_extensive)
  assume h: "set xs \<turnstile>\<^sub>\<Down> m"
  from gen[OF base] h show ?thesis by simp
qed

subsubsection \<open> Monotonicity \<close>

text \<open> Monotonicity of the implementation mirrors monotonicity of the declarative relations.
On the build-up side this is @{text buildable_mono}; on the breakdown side @{text breakdown_mono}
is the rule-level statement and @{text breakl_mono} its counterpart for the closure, obtained
from soundness and completeness. \<close>

lemma buildable_mono:
  "ms \<subseteq> ms' \<Longrightarrow> buildable m ms \<Longrightarrow> buildable m ms'"
  by (induct m) (auto dest: subsetD)

lemma filter_buildable_mono:
  "ms \<subseteq> ms' \<Longrightarrow> set (filter_buildable xs ms) \<subseteq> set (filter_buildable xs ms')"
  by (auto simp: filter_buildable_def intro: buildable_mono)

text \<open> On the breakdown side the knowledge that drives the rules (member, unpairing,
decryption, digital verify, watermarking, and jamming) is the set of atomic parts extracted from
the messages the intruder has heard, and that extraction is monotone in the messages. So enlarging
@{text xs} enlarges the set of keys and bitmasks against which the decryption, verification, and
dejamming tests are evaluated, and it cannot invalidate a prefix test such as @{text "b \<le> bb"}
because that test does not depend on the messages at all. \<close>

lemma atomics_mono: "set xs \<subseteq> set xs' \<Longrightarrow> set (atomics xs) \<subseteq> set (atomics xs')"
  by (auto simp add: atomics_def)

text \<open> Both declarative relations are monotone in the intruder's knowledge as well. The build-up
side reduces to @{text buildable_mono}; the breakdown side has no implementation counterpart here,
so it is proved from the rules themselves. \<close>

lemma buildup_mono: "K \<subseteq> K' \<Longrightarrow> K \<turnstile>\<^sub>\<Up> m \<Longrightarrow> K' \<turnstile>\<^sub>\<Up> m"
  by (simp add: buildup_buildable) (blast intro: buildable_mono)

lemma breakdown_mono: "K \<subseteq> K' \<Longrightarrow> K \<turnstile>\<^sub>\<Down> m \<Longrightarrow> K' \<turnstile>\<^sub>\<Down> m"
proof -
  assume sub: "K \<subseteq> K'"
  assume d: "K \<turnstile>\<^sub>\<Down> m"
  from d sub show ?thesis
    by (induct rule: breakdown.induct) (auto intro: breakdown.intros)
qed

text \<open> Monotonicity of the closure in the messages the intruder has heard is now immediate: it
is the composite of soundness, monotonicity of the declarative relation, and completeness. \<close>

lemma breakl_mono: "set xs \<subseteq> set ys \<Longrightarrow> set (breakl xs) \<subseteq> set (breakl ys)"
proof (rule subsetI)
  fix m
  assume hsub: "set xs \<subseteq> set ys" and hm: "m \<in> set (breakl xs)"
  from subsetD[OF breakl_sound hm] have h1: "set xs \<turnstile>\<^sub>\<Down> m" by simp
  from breakdown_mono[OF hsub h1] have h2: "set ys \<turnstile>\<^sub>\<Down> m" .
  from breakl_complete[OF h2] show "m \<in> set (breakl ys)" .
qed

subsubsection \<open> Watermark injectivity and non-forgeability \<close>

text \<open> Watermarking and jamming are injective (facts @{text MWat_inj_eq} and @{text MJam_inj_eq}).
Consequently, for a message that the intruder has not heard (@{text "MWat m b \<notin> ms"}), she can
only build @{text "MWat m b"} if she can already build the bitmask @{text b}: this is the symbolic
content of the non-forgeability discipline (rule Wat2 needs the bitmask). \<close>

lemma MWat_inj_eq: "MWat m b = MWat m' b' \<longleftrightarrow> m = m' \<and> b = b'" by simp
lemma MJam_inj_eq: "MJam m b = MJam m' b' \<longleftrightarrow> m = m' \<and> b = b'" by simp

lemma buildable_MWat_imp:
  "MWat m b \<notin> ms \<Longrightarrow> buildable (MWat m b) ms \<Longrightarrow> buildable b ms"
  by (simp add: buildable.simps)

(*
lemma buildable_MJam_imp:
  "MJam m b \<notin> ms \<Longrightarrow> buildable (MJam m b) ms \<Longrightarrow> buildable b ms"
  by (simp add: buildable.simps)
*)

subsubsection \<open> Jamming-elimination characterisation \<close>

text \<open> The bitmask order realises the prefix test used by the jamming rule: a bitmask @{text b'}
eliminates the jamming of a watermark @{text b} exactly when @{text "b' \<le> b"}, i.e. @{text b'} has
the same number of bitmasks and no more samples (@{text less_eq_Bm_Bm}). @{text Null} is the least
element, so an empty jamming bitmask never blocks recovery. \<close>

lemma less_eq_Bm_Bm: "(Bm x1 y1 \<le> Bm x2 y2) = ((x1 = x2) \<and> y1 \<le> y2)"
  by (simp add: less_eq_dbitmask_def)

lemma less_Bm_Bm: "(Bm x1 y1 < Bm x2 y2) = ((x1 = x2) \<and> y1 < y2)"
  by (simp add: less_dbitmask_def)

lemma Null_le[simp]: "Null \<le> b"
  by (simp add: less_eq_dbitmask_def)

lemma not_Bm_le_Null[simp]: "\<not> (Bm x y \<le> Null)"
  by (simp add: less_eq_dbitmask_def)

lemma le_Null_eq[simp]: "(b \<le> Null) = (b = Null)"
  by (cases b) (simp_all add: less_eq_dbitmask_def)

subsubsection \<open> Replay versus forgery \<close>

text \<open> The breakdown closure @{text breakl} separates the two watermarking capabilities. By
@{text breakl_wat} the intruder always learns the underlying message of a watermarked message
(rule Wat1). By @{text breakl_jam_unknown}, a jammed message whose jamming bitmask is not known is
left untouched, so it does not by itself leak the plaintext. Finally, @{text breakl_jam_known} shows
that once the jamming bitmask @{text b} is known and is a prefix of the watermarking bitmask
@{text bb}, the intruder recovers the plaintext. \<close>

lemma step_once_Wat: "m \<in> set (step_once [MWat m b])"
  by (simp add: step_once_def one_step.simps List.member_def)

lemma breakl_wat[simp]: "m \<in> set (breakl [MWat m b])"
proof -
  have h: "m \<in> set (step_once (remdups [MWat m b]))" by (simp add: step_once_Wat)
  obtain n where bd: "List.length (submsgs_list [MWat m b]) + 1 = Suc n"
    by (cases "List.length (submsgs_list [MWat m b])") auto
  show ?thesis
    unfolding breakl_def bd
    using h step_once_subset_iter_Suc[of "remdups [MWat m b]" n] by auto
qed

lemma step_once_Jam_unknown[simp]:
  "b \<noteq> Null \<Longrightarrow> step_once [MJam m (MBitm b)] = [MJam m (MBitm b)]"
  by (cases m; auto simp: step_once_def one_step.simps List.member_def
           split: dmsg.splits dkey.splits dbitmask.splits)

lemma breakl_jam_unknown:
  "b \<noteq> Null \<Longrightarrow> breakl [MJam m (MBitm b)] = [MJam m (MBitm b)]"
proof -
  assume hb: "b \<noteq> Null"
  have h: "step_once [MJam m (MBitm b)] = [MJam m (MBitm b)]"
    using hb by (cases m; auto simp: step_once_def one_step.simps List.member_def
                    split: dmsg.splits dkey.splits dbitmask.splits)
  obtain n where bd: "List.length (submsgs_list [MJam m (MBitm b)]) + 1 = Suc n"
    by (cases "List.length (submsgs_list [MJam m (MBitm b)])") auto
  show ?thesis
    unfolding breakl_def bd
    using h by (simp add: iter_closure_fix)
qed

lemma breakl_jam_unknown_subset:
  "b \<noteq> Null \<Longrightarrow> set (breakl [MJam m (MBitm b)]) \<subseteq> {MJam m (MBitm b)}"
  by (simp add: breakl_jam_unknown)

lemma MJam_MWat_not_self: "m \<noteq> MJam (MWat m bwm) k"
proof
  assume "m = MJam (MWat m bwm) k"
  then have "size m = 2 + size m + size bwm + size k" by simp
  then show False by linarith
qed

lemma breakl_jam_unknown_leak:
  "b \<noteq> Null \<Longrightarrow>
   MWat m (MBitm bb) \<notin> set (breakl [MJam (MWat m (MBitm bb)) (MBitm b)]) \<and>
   m \<notin> set (breakl [MJam (MWat m (MBitm bb)) (MBitm b)])"
  by (simp add: breakl_jam_unknown MJam_MWat_not_self)

lemma step_once_Jam_known:
  "b \<noteq> Null \<Longrightarrow> b \<le> bb \<Longrightarrow>
   m \<in> set (step_once [MBitm b, MJam (MWat m (MBitm bb)) (MBitm b)])"
  by (simp add: step_once_def one_step.simps List.member_def)

lemma breakl_jam_known:
  "b \<noteq> Null \<Longrightarrow> b \<le> bb \<Longrightarrow>
   m \<in> set (breakl [MBitm b, MJam (MWat m (MBitm bb)) (MBitm b)])"
proof -
  assume hb: "b \<noteq> Null" and hs: "b \<le> bb"
  let ?K = "[MBitm b, MJam (MWat m (MBitm bb)) (MBitm b)]"
  have h: "m \<in> set (step_once (remdups ?K))"
    using hb hs by (simp add: step_once_Jam_known)
  obtain n where bd: "List.length (submsgs_list ?K) + 1 = Suc n"
    by (cases "List.length (submsgs_list ?K)") auto
  show ?thesis
    unfolding breakl_def bd
    using h step_once_subset_iter_Suc[of "remdups ?K" n] by auto
qed

subsection \<open> All instances \<close>

definition "AllAgents = ((enum_class.enum:: ('a::len) dagent list))"
definition "AgentsMsgs as = MAg ` (set as)"
definition "AgentsLst as = map MAg as"
abbreviation "AllAgentsLst \<equiv> AgentsLst AllAgents"
value "(AgentsMsgs AllAgents) :: (2,4,4,2,2,1,1) dmsg set"
value "(AgentsLst AllAgents) :: (2,4,4,2,2,1,1) dmsg list"

definition "AllPKs = map Kp (enum_class.enum:: (('k::len) fsnat list))"
definition "PKsMsgs pks = MK ` (set pks)"
definition "PKsLst pks = map MK pks"
abbreviation "AllPKsLst \<equiv> PKsLst AllPKs"
value "(PKsMsgs AllPKs) :: (2,4,4,2,2,1,1) dmsg set"
value "(PKsLst AllPKs) :: (2,4,4,2,2,1,1) dmsg list"

definition "AllSKs = map Ks (enum_class.enum:: (('k::len) fsnat list))"
definition "SKsMsgs sks = MK ` (set sks)"
definition "SKsLst sks = map MK sks"
abbreviation "AllSKsLst \<equiv> SKsLst AllSKs"

value "(SKsMsgs AllSKs) :: (2,4,4,2,2,1,1) dmsg set"

definition "AllNonces = (enum_class.enum:: ('a::len) dnonce list)"
definition "NoncesMsgs xs = MNon ` (set xs)"
definition "NoncesLst xs = map MNon xs"
abbreviation "AllNoncesLst \<equiv> NoncesLst AllNonces"
value "(NoncesMsgs AllNonces) :: (2,4,4,2,2,1,1) dmsg set"

definition "AllExpGs = (enum_class.enum:: ('a::len) dexpg list)"
definition "ExpGMsgs xs = MExpg ` (set xs)"
definition "ExpGLst xs = map MExpg xs"
abbreviation "AllExpGLst \<equiv> ExpGLst AllExpGs"
value "(ExpGMsgs AllExpGs) :: (2,4,4,2,2,1,1) dmsg set"

definition "AllBitMs = (enum_class.enum:: ('a::len, 'b::len) dbitmask list)"
definition "BitMMsgs xs = MBitm ` (set xs)"
definition "BitMLst xs = map MBitm xs"
abbreviation "AllBitMLst \<equiv> BitMLst AllBitMs"
value "(BitMMsgs AllBitMs) :: (2,4,4,2,2,1,1) dmsg set"

subsection \<open> Signals and Channels \<close>

datatype ('a::len, 'n::len) dsig = ClaimSecret (sag:"'a dagent") (sn: "'n dnonce") (sp: "\<bbbP> ('a dagent)")
  | StartProt "'a dagent" "'a dagent" "'n dnonce" "'n dnonce"
  | EndProt "'a dagent" "'a dagent" "'n dnonce" "'n dnonce"

chantype ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) chan =
  env   :: "'a::{len,typerep} dagent \<times> 'a dagent"
\<comment> \<open> @{text "(src, medium, dst, m)"} Send a message m from src to dst through medium. If the medium is 
  Intruder, it just means to a public network/channel. Otherwise, it is private. \<close>
  send  :: "'a dagent \<times> 'a dagent \<times> 'a dagent \<times> ('a::{len,typerep}, 'n::{len,typerep}, 
    'k::{len,typerep}, 's::{len,typerep}, 'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
\<comment> \<open> @{text "(src, medium, dst, m)"} Send a message m from src to dst through medium. If the medium is 
  Intruder, it just means to a public network/channel. Otherwise, it is private. \<close>
  cjam   :: "('a::{len,typerep}, 'n::{len,typerep}, 'k::{len,typerep}, 's::{len,typerep}, 
    'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
  cdejam :: "('a::{len,typerep}, 'n::{len,typerep}, 'k::{len,typerep}, 's::{len,typerep}, 
    'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
  recv  :: "'a dagent \<times> 'a dagent \<times> 'a dagent \<times> ('a::{len,typerep}, 'n::{len,typerep}, 
    'k::{len,typerep}, 's::{len,typerep}, 'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
  leak  :: "('a::{len,typerep}, 'n::{len,typerep}, 'k::{len,typerep}, 's::{len,typerep}, 
    'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
  sig   :: "('a::{len,typerep}, 'n::{len,typerep}) dsig"
  terminate :: "unit"

print_bnfs

text \<open> Use abbreviation hear and fake for send and recv to avoid renaming later in Intruder \<close>
abbreviation "hear \<equiv> send"
abbreviation "fake \<equiv> recv"
abbreviation "relay \<equiv> recv"

definition send_to_network where
"send_to_network A B m = outp send (A, Intruder, B, m)"

definition send_privately where
"send_privately A B m = outp send (A, A, B, m)"

definition recv_from_network where
"recv_from_network A ms = inp_in recv (set [(Intruder, Intruder, A, m). m \<leftarrow> ms])"

definition recv_privately where
"recv_privately A B ms = inp_in recv (set [(A, A, B, m). m \<leftarrow> ms])"

end
