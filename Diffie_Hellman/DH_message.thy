section \<open> Modelling, verification, and animation of security protocols \<close>
theory DH_message
  imports "../CSP_operators"
          "Datatype_Order_Generator.Order_Generator"
begin

subsection \<open> General definitions \<close>
text \<open> Ideally we should use insort_insert_key from the list theory, but it causes a 
compilation problem when generating the code because it calls set-related functions 
(Set.image and ...) in List.hs. But Set.hs also includes List-related functions. It is 
a cycle. We can break it by definition a new function below. \<close>
context linorder
begin

definition insort_insert_key' :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "insort_insert_key' f x xs =
  (if f x \<in> f ` set xs then xs else insort_key f x xs)"
end

abbreviation "list_union_sort \<equiv> fold (insort_insert_key' (\<lambda>x. x))"
value "insort (MKp (PK Alice)) (sort [g\<^sub>m, MAg Alice])"
value "list_union_sort [g\<^sub>m, MAg Alice, (MKp (PK Alice))] (sort [g\<^sub>m, MAg Alice])"

subsection \<open> Data types \<close>
datatype dagent =  Alice | Bob | Intruder | Server

instantiation dagent :: enum
begin
definition enum_dagent :: "dagent list" where
"enum_dagent = [Alice, Bob, Intruder, Server]"

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

datatype dpkey = PK (pa:dagent)
datatype dskey = SK (sa:dagent)
datatype dkey = Kp (kp:dpkey) | Ks (ks:dskey)

fun inv\<^sub>k where 
"inv\<^sub>k (Kp k) = Ks (SK (pa k))" |
"inv\<^sub>k (Ks k) = Kp (PK (sa k))"

definition "inv\<^sub>p pk = SK (pa pk)"
definition "inv\<^sub>s sk = PK (sa sk)"

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
(* Modular exponentiation: g^e mod p where g is the base, e is the exponent, and p is the modulus *)
(* datatype dexp_base = g *)

datatype dmsg = MAg (ma:dagent)
  | MNon (mn:dnonce)
  | MKp (mkp:dpkey)
  | MKs (mks:dskey)
  | MCmp (mc1:dmsg) (mc2:dmsg)
  | MEnc (mem:dmsg) (mek:dpkey)
  | MSig (msd:dmsg) (msk:dskey)
  | MSEnc (msem:dmsg) (msek:dmsg)
  | MExpg (* (mg: dexp_base) *)
  | MModExp (mmem:dmsg) (mmee:dnonce)

text \<open> Generate linorder for all these types in order to support comparison between dmsg, particularly 
for MCmp to reduce the number of messages that intruder can build because we can treat 
@{text "MCmp a1 a2"} and @{text "MCmp a2 a1"} as the same, and 
@{text "MCmp (MCmp a3 a1) a2"} and @{text "MCmp a2 (MCmp a3 a1)"} also as the same. 
\<close>
derive linorder "dagent"
derive linorder "dnonce"
derive linorder "dpkey"
derive linorder "dskey"
derive linorder "dkey"
derive linorder "dmsg"

text\<open>Concrete syntax for dmsg \<close>
syntax
  "_CompMsg" :: "['a, args] \<Rightarrow> 'a * 'b"  ("(2\<lbrace>_,/ _\<rbrace>\<^sub>m)")
  "_EncryptMsg" :: "['a, 'a] \<Rightarrow> 'a"      ("(2{_}\<^bsub>_\<^esub>)")
  "_SEncryptMsg" :: "['a, 'a] \<Rightarrow> 'a"     ("(2{_}\<^sub>S\<^bsub>_\<^esub>)")
  "_SignMsg" :: "['a, 'a] \<Rightarrow> 'a"         ("(2{_}\<^sub>d\<^bsub>_\<^esub>)")
  "_ModExpMsg" :: "['a, 'a] \<Rightarrow> 'a"       (infixl "^\<^sub>m" 30)
  "_MExpg" :: "'a" ("g\<^sub>m")
translations
  "\<lbrace>w, x, y, z\<rbrace>\<^sub>m" \<rightleftharpoons> "\<lbrace>w, \<lbrace>x, \<lbrace>y, z\<rbrace>\<^sub>m\<rbrace>\<^sub>m\<rbrace>\<^sub>m"
  "\<lbrace>x, y, z\<rbrace>\<^sub>m" \<rightleftharpoons> "\<lbrace>x, \<lbrace>y, z\<rbrace>\<^sub>m\<rbrace>\<^sub>m"
  "\<lbrace>x, y\<rbrace>\<^sub>m" \<rightleftharpoons> "CONST MCmp x y"
  "{m}\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MEnc m k"
  "{m}\<^sub>d\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MSig m k"
  "{m}\<^sub>S\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MSEnc m k"
  "m^\<^sub>me" \<rightleftharpoons> "CONST MModExp m e"
  "g\<^sub>m"  \<rightleftharpoons> "CONST MExpg"

value "{MNon (N Alice)}\<^bsub>PK Alice\<^esub>"
value "{MNon (N Alice)}\<^sub>d\<^bsub>SK Alice\<^esub>"
value "\<lbrace>MNon (N Alice), MKp (PK Bob)\<rbrace>\<^sub>m"
value "g\<^sub>m ^\<^sub>m ((N Alice)) ^\<^sub>m ((N Bob))"

definition "AllAgents = ((enum_class.enum:: (dagent) list))"
definition "AllAgentsMsgs = MAg ` (set AllAgents)"
definition "AllAgentsLst = map MAg AllAgents"

definition "AllPKs = (enum_class.enum:: (dpkey) list)"
definition "AllPKsMsgs = MKp ` (set AllPKs)"
definition "AllPKsLst = map MKp AllPKs"
value "AllPKsMsgs"
value "AllPKsLst"

definition "AllSKs = (enum_class.enum:: (dskey) list)"
definition "AllSKsMsgs = MKs ` (set AllSKs)"
definition "AllSKsLst = map MKs AllSKs"
value "AllSKsMsgs"

definition "AllNonces = (enum_class.enum:: (dnonce) list)"
definition "AllNoncesMsgs = MNon ` (set AllNonces)"
definition "AllNoncesLst = map MNon AllNonces"
value "AllNoncesMsgs"

fun length:: "dmsg \<Rightarrow> nat" where 
"length (MAg _) = 1" |
"length (MNon _) = 1" |
"length (MKp _) = 1" |
"length (MKs _) = 1" |
"length (MCmp m1 m2) = length m1 + length m2" |
"length (MEnc m k) = length m" |
"length (MSig m k) = length m" |
"length (MSEnc m k) = length m" |
"length (MExpg) = 1" |
"length (MModExp m k) = length m"

fun atomic :: "dmsg \<Rightarrow> dmsg list" where
"atomic (MAg m) = [(MAg m)]" |
"atomic (MNon m) = [(MNon m)]" |
"atomic (MKp m) = [(MKp m)]" |
"atomic (MKs m) = [(MKs m)]" |
"atomic (MCmp m1 m2) = list_union_sort (atomic m1) (atomic m2)" |
"atomic (MEnc m k) = atomic m" |
"atomic (MSig m k) = atomic m" |
"atomic (MSEnc m k) = atomic m" |
"atomic (MExpg) = [(MExpg)]" |
"atomic (MModExp m k) = atomic m"

fun dupl :: "dmsg \<Rightarrow> bool" where
"dupl (MAg _) = False" |
"dupl (MNon _) = False" |
"dupl (MKp _) = False" |
"dupl (MKs _) = False" |
"dupl (MCmp m1 m2) = ((dupl m1) \<or> (dupl m2) \<or> (filter (\<lambda>s. List.member (atomic m1) s) (atomic m2) \<noteq> []))" |
"dupl (MEnc m k) = dupl m" |
"dupl (MSig m k) = dupl m" |
"dupl (MSEnc m k) = dupl m" |
"dupl (MExpg) = False" |
"dupl (MModExp m k) = dupl m"

abbreviation "dupl2 m1 m2 \<equiv> (dupl m1) \<or> (dupl m2) \<or> (filter (\<lambda>s. List.member (atomic m1) s) (atomic m2) \<noteq> [])"

text \<open> Create a MCmp from a list of messages \<close>
fun create_cmp :: "dmsg list \<Rightarrow> dmsg option" where
"create_cmp [] = None" |
"create_cmp (x#[y]) = Some (MCmp x y)" |
"create_cmp (x#ys) = (case (create_cmp ys) of 
  None \<Rightarrow> None |
  Some y \<Rightarrow> Some (MCmp x y))
"

value "create_cmp [MNon (N Alice), MAg Bob, MKp (PK Alice), MKp (PK Alice), MKp (PK Alice), MKp (PK Alice)]"

text \<open> Transform a MCmp into a list of sorted messages \<close>
fun mcmp_to_list :: "dmsg \<Rightarrow> dmsg list" where
"mcmp_to_list (MCmp m1 m2) = List.sort (mcmp_to_list m1 @ mcmp_to_list m2)" |
"mcmp_to_list a = [a]"

value "mcmp_to_list (MCmp 
  (MCmp 
      (MSEnc (MCmp (MAg Alice) (MNon (N Bob))) (MKs (SK Alice))) 
      (MAg Alice)
  )
  (MNon (N Alice))
)"

text \<open> @{text "msort"} is to sort the dmsg based on its order, specifically for MCmp because we 
disregard the order in MCmp. So we sort it first and then we can compare two MCmp to see if they 
are equal. We treat @{text "MCmp a1 a2"} and @{text "MCmp a2 a1"} as the same, and 
@{text "MCmp (MCmp a3 a1) a2"} and @{text "MCmp a2 (MCmp a3 a1)"} also as the same.
\<close>
fun msort :: "dmsg \<Rightarrow> dmsg" where
"msort (MAg a) = (MAg a)" |
"msort (MNon a) = (MNon a)" |
"msort (MKp a) = (MKp a)" |
"msort (MKs a) = (MKs a)" |
\<comment> \<open> This is going to transform a MCmp into a sorted MCmp \<close>
"msort (MCmp m1 m2) = (case create_cmp (List.sort (mcmp_to_list (msort m1) @ mcmp_to_list (msort m2))) of
  Some y \<Rightarrow> y | None \<Rightarrow> (MCmp m1 m2))" |
"msort (MEnc m k) = (MEnc (msort m) k) " |
"msort (MSig m k) = (MSig (msort m) k)" |
"msort (MSEnc m k) = (MSEnc (msort m) k)" |
"msort (MExpg) = (MExpg)" |
"msort (MModExp m k) = (MModExp (msort m) k)"

value "msort (MCmp (MCmp (MSEnc (MKp (PK Alice)) (MKs (SK Alice))) (MAg Alice)) (MNon (N Alice)))"
value "msort (MCmp 
  (MCmp 
    (MSEnc (MCmp (MAg Alice) (MNon (N Bob))) (MKs (SK Alice))) 
    (MAg Alice)
  )
  (MNon (N Alice))
)"
value "msort (MCmp 
  (MCmp 
    (MSEnc (MCmp 
              (MAg Alice) 
              (MCmp (MNon (N Intruder)) (MNon (N Bob)))) 
           (MKs (SK Alice))) 
    (MCmp (MAg Intruder) (MCmp (MAg Bob) (MAg Server)))
  )
  (MNon (N Alice))
)"
value "(List.sort (mcmp_to_list (msort (MCmp 
    (MSEnc (MCmp 
              (MAg Alice) 
              (MCmp (MNon (N Intruder)) (MNon (N Bob)))) 
           (MKs (SK Alice))) 
    (MCmp (MAg Intruder) (MCmp (MAg Bob) (MAg Server)))
  ))))"

value "msort (MCmp (MCmp (MKp (PK Alice)) (MKs (SK Alice))) (MAg Alice)) 
  =  msort (MCmp (MCmp (MAg Alice) (MKs (SK Alice))) (MKp (PK Alice))) "

datatype dsig = ClaimSecret (sag:dagent) (sn:dnonce) (sp: "\<bbbP> dagent")
  | StartProt dagent dagent dnonce dnonce
  | EndProt dagent dagent dnonce dnonce

subsection \<open> Message inferences \<close>
definition "extract_dskey xs = map (mks)  (filter is_MKs xs)"
definition "extract_dpkey xs = map (mkp ) (filter is_MKp xs)"
definition "extract_dkeys xs = map (Ks) (extract_dskey xs)"
definition "extract_dkeyp xs = map (Kp) (extract_dpkey xs)"
definition "extract_nonces xs = map (mn ) (filter is_MNon xs)"

text \<open> @{text "break_lst xs ys"} break down a list of messages and ys is the list of messages that 
have been broken down previously. \<close>
fun break_lst::"dmsg list \<Rightarrow> dmsg list \<Rightarrow> dmsg list" where
"break_lst [] ams = ams" |
"break_lst ((MKp k)#xs) ams = (break_lst xs (List.insert (MKp k) ams))" |
"break_lst ((MKs k)#xs) ams = (break_lst xs (List.insert (MKs k) ams))" |
"break_lst ((MAg A)#xs) ams = (break_lst xs (List.insert (MAg A) ams))" |
"break_lst ((MNon A)#xs) ams = (break_lst xs (List.insert (MNon A) ams))" |
\<comment> \<open> A and B might be mutual dependent, such as @{text "\<lbrace>{g\<^sub>m ^\<^sub>m (na)}\<^sub>s\<^bsub>SK A\<^esub> , MKp (PK A)\<rbrace>\<^sub>m"}. 
  We could proceed as follows, but now the @{text "{g\<^sub>m ^\<^sub>m (na)}\<^sub>s\<^bsub>SK A\<^esub>"} would be in the @{text "ams"} 
though it still can be breakdown.
\<close>
(* The right way might be "break_lst (A#(B#xs)) ams" but it is hard to prove it will be terminated *)
"break_lst ((MCmp A B)#xs) ams = (
    break_lst xs (remdups (break_lst [A] ams @ break_lst [B] ams @ ams))
  )" |
\<comment> \<open> We don't consider asymmetric encryption here \<close>
"break_lst ((MEnc A (PK k))#xs) ams = break_lst xs ams" |
"break_lst ((MSig A (SK k))#xs) ams = 
    (if List.member ams (MKp (PK k)) then 
      break_lst (A#xs) (List.insert (MSig A (SK k)) ams)
    else 
      let rams = break_lst xs ams 
      in  if List.member rams (MKp (PK k)) then
          \<comment> \<open> TODO: do we need to re-do it again for xs? It seems so because A may have more info. 
          Current solution is to apply @{text break_lst} twice. \<close>
          break_lst (A#xs) (List.insert (MSig A (SK k)) ams)
        else
          break_lst xs (List.insert (MSig A (SK k)) (ams))
)" |
\<comment> \<open> Particularly, we are looking at the k having a form @{text "((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)"}. 
  @{text "{m}\<^sub>S\<^bsub>((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)\<^esub> "} can be broken if (@{text "(g\<^sub>m ^\<^sub>m a)"} and @{text "b"})
  or (@{text "(g\<^sub>m ^\<^sub>m b)"} and @{text "a"}) in the messages because 
  @{text "((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)"} is equal to @{text "((g\<^sub>m ^\<^sub>m b) ^\<^sub>m a)"}.
\<close>
"break_lst ((MSEnc m k)#xs) ams = (case k of
  ((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b) \<Rightarrow> 
     (if (List.member ams ((g\<^sub>m ^\<^sub>m a)) \<and> List.member ams (MNon b)) \<or> 
         (List.member ams ((g\<^sub>m ^\<^sub>m b)) \<and> List.member ams (MNon a)) \<or> 
         (List.member ams (g\<^sub>m) \<and> List.member ams (MNon a) \<and> List.member ams (MNon b)) then 
          break_lst (m#xs) (List.insert (MSEnc m k) ams)
        else 
          let rams = break_lst xs ams
          in if (List.member rams ((g\<^sub>m ^\<^sub>m a)) \<and> List.member rams (MNon b)) \<or> 
               (List.member rams ((g\<^sub>m ^\<^sub>m b)) \<and> List.member rams (MNon a)) \<or> 
               (List.member rams (g\<^sub>m) \<and> List.member rams (MNon a) \<and> List.member rams (MNon b)) then 
              break_lst (m#xs) (List.insert (MSEnc m k) ams)
            else
              break_lst xs (List.insert (MSEnc m k) (ams))
    ) |
  \<comment> \<open> Otherwise, we won't break it \<close>
  _ \<Rightarrow> break_lst xs (List.insert (MSEnc m k) (ams))
) " |
"break_lst ((MExpg)#xs) ams = break_lst xs (List.insert (MExpg) (ams))" |
\<comment> \<open> We cannot break anything from a^b but the message should be kept \<close>
"break_lst ((a ^\<^sub>m b)#xs) ams = break_lst xs (List.insert (a ^\<^sub>m b) (ams))"

definition "breakl xs = break_lst xs []"
text \<open> Our strategy to deal with @{text "(MCmp A B)"} is the application of breakl twice. \<close>
definition "breakm xs = breakl (breakl xs)"

value "breakl [\<lbrace>{g\<^sub>m ^\<^sub>m (N Bob)}\<^sub>d\<^bsub>SK Alice\<^esub> , MKp (PK Alice)\<rbrace>\<^sub>m]"
value "breakm [\<lbrace>{g\<^sub>m ^\<^sub>m (N Bob)}\<^sub>d\<^bsub>SK Alice\<^esub> , MKp (PK Alice)\<rbrace>\<^sub>m]"
value "breakm [\<lbrace>{g\<^sub>m ^\<^sub>m (N Alice)}\<^sub>d\<^bsub>SK Alice\<^esub> , {MKp (PK Alice)}\<^sub>d\<^bsub>SK Bob\<^esub> \<rbrace>\<^sub>m,
  \<lbrace>MKp (PK Intruder), {MKp (PK Bob)}\<^sub>d\<^bsub>SK Intruder\<^esub> \<rbrace>\<^sub>m]"

value "let knowledge = [
    MNon (N Alice), MKs (SK Bob), MNon (N Bob), g\<^sub>m,
    \<lbrace>{(\<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m)}\<^bsub>PK Bob\<^esub> , (MAg Alice)\<rbrace>\<^sub>m,
    {MKp (PK Alice)}\<^sub>S\<^bsub>((g\<^sub>m ^\<^sub>m (N Alice)) ^\<^sub>m (N Bob))\<^esub>] 
  in breakl knowledge"

value "let knowledge = [
    (g\<^sub>m ^\<^sub>m (N Alice)), \<lbrace>MNon (N Bob), (MAg Alice)\<rbrace>\<^sub>m, 
    {MKp (PK Alice)}\<^sub>S\<^bsub>((g\<^sub>m ^\<^sub>m (N Alice)) ^\<^sub>m (N Bob))\<^esub>] 
  in breakl knowledge"

value "let knowledge = [
    (g\<^sub>m ^\<^sub>m (N Bob)), \<lbrace>MNon (N Bob), (MAg Alice)\<rbrace>\<^sub>m, 
    {MKp (PK Alice)}\<^sub>S\<^bsub>((g\<^sub>m ^\<^sub>m (N Alice)) ^\<^sub>m (N Bob))\<^esub>] 
  in breakl knowledge"

value "let knowledge = [
    (g\<^sub>m ^\<^sub>m (N Bob)), \<lbrace>MNon (N Alice), (MAg Alice)\<rbrace>\<^sub>m, 
    {MKp (PK Alice)}\<^sub>S\<^bsub>((g\<^sub>m ^\<^sub>m (N Alice)) ^\<^sub>m (N Bob))\<^esub>] 
  in breakl knowledge"

text \<open> @{text "pair2 xs ys l"}: pair message once for each element of @{text "xs"} with 
every element of @{text "ys"} if they are different, their length does not exceed the given @{text 
"l"} which denotes the maximum length of a composed message. 
\<close>
fun pair2 :: "dmsg list \<Rightarrow> dmsg list \<Rightarrow> nat \<Rightarrow> dmsg list" where
"pair2 [] ys l = []" |
"pair2 (x#xs) ys l = (let cs = pair2 xs ys l in
  (map (\<lambda>n. msort (MCmp x n)) \<comment> \<open> Sort the components in MCmp \<close>
    (filter 
      \<comment> \<open> they are not the same, length won't exceed l, and they are not private keys  \<close>
      (\<lambda>y. y \<noteq> x \<and> length x + length y \<le> l \<and> \<not> dupl2 x y \<and> \<not> is_MKs x \<and> \<not> is_MKs y) 
    ys)
  ) @ cs)"

value "length \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m"
value "pair2 [MNon (N Server), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] 
             [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] 3"
\<comment> \<open> We expect [] because equal or duplicate cases \<close>
value "pair2 [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] 
             [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] 3"

text \<open> @{text "enc\<^sub>1 xs ks"}: encrypt each element of @{text "xs"} with 
every key of @{text "ks"} \<close>
fun enc\<^sub>1 :: "dmsg list \<Rightarrow> dpkey list \<Rightarrow> dmsg list" where
"enc\<^sub>1 [] pks = []" |
"enc\<^sub>1 (x#xs) pks = (if is_MKs x then enc\<^sub>1 xs pks 
  else (map (\<lambda>k. MEnc x k) pks) @ enc\<^sub>1 xs pks)"

value "enc\<^sub>1 [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] [PK Bob, PK Alice, PK Intruder]"

definition "enc\<^sub>1' xs = (enc\<^sub>1 xs (extract_dpkey xs))"

text \<open> @{text "sig\<^sub>1 xs ks"}: sign each element of @{text "xs"} with 
every key of @{text "ks"} \<close>
fun sig\<^sub>1 :: "dmsg list \<Rightarrow> dskey list \<Rightarrow> dmsg list" where
"sig\<^sub>1 [] sks = []" |
"sig\<^sub>1 (x#xs) sks = (if is_MKs x then sig\<^sub>1 xs sks 
  else (map (\<lambda>k. MSig x k) sks) @ sig\<^sub>1 xs sks)"

value "sig\<^sub>1 [MNon (N Alice), \<lbrace>(MAg Bob), (MNon (N Alice))\<rbrace>\<^sub>m] [SK Server]"

definition "sig\<^sub>1' xs = sig\<^sub>1 xs (extract_dskey xs)"

text \<open> @{text "senc\<^sub>1 xs eks"}: encrypt each element of @{text "xs"} with 
every key of @{text "eks"} (a set of MModExp)  \<close>
fun senc\<^sub>1 :: "dmsg list \<Rightarrow> dmsg list \<Rightarrow> dmsg list" where
"senc\<^sub>1 [] eks = []" |
"senc\<^sub>1 (x#xs) eks = (if is_MKs x then senc\<^sub>1 xs eks 
  else (map (\<lambda>k. MSEnc x k) eks) @ senc\<^sub>1 xs eks)"

definition "senc\<^sub>1' xs = senc\<^sub>1 xs (filter is_MModExp xs)"

value "senc\<^sub>1' [MNon (N Alice), (MAg Bob), (MNon (N Alice)), g\<^sub>m ^\<^sub>m ((N Alice)) ^\<^sub>m ((N Bob))]"

text \<open> Apply @{text "^\<^sub>m"} up to twice, based on @{text "g\<^sub>m"} \<close>
definition mod_exp2 :: "dnonce list \<Rightarrow> dmsg list" where
"mod_exp2 ns = (let mes = (map (\<lambda>n. g\<^sub>m ^\<^sub>m n) ns) 
   in mes @ concat (map (\<lambda>m. (map (\<lambda>n. m ^\<^sub>m n) ns)) mes)
)"

value "mod_exp2 [N Alice, N Bob]"

definition "mod_exp2' ns = (if List.member ns g\<^sub>m then mod_exp2 (extract_nonces ns) else [])"

text \<open> Apply @{text "^\<^sub>m"} up to once to @{text "g\<^sub>m ^\<^sub>m a"} \<close>
fun mod_exp1 :: "dmsg list \<Rightarrow> dnonce list \<Rightarrow> dmsg list" where
"mod_exp1 [] ns = []" |
"mod_exp1 ((g\<^sub>m ^\<^sub>m a)#xs) ns = (map (\<lambda>n. (g\<^sub>m ^\<^sub>m a) ^\<^sub>m n) ns) @ mod_exp1 xs ns" | 
"mod_exp1 (x#xs) ns = mod_exp1 xs ns"

value "mod_exp1 [g\<^sub>m ^\<^sub>m (N Alice)] [N Alice, N Bob]"

definition "mod_exp1' xs = (mod_exp1 xs (extract_nonces xs))"

text \<open> @{text "build1\<^sub>n knows _ _ nc ne l"} where @{text "knows"} is a list of atomic messages;
; @{text "nc"} denotes the number of times of composition;  
@{text "ne"} denotes the number of times of encryption (symmetric this case); 
@{text "l"} denotes the maximum length of a composed message
\<close>
fun build\<^sub>n::"dmsg list \<Rightarrow> dpkey list \<Rightarrow> dskey list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dmsg list" where
\<comment> \<open> Original xs is always in the result \<close>
"build\<^sub>n xs pks sks 0 0 l = xs" |
\<comment> \<open> Original xs is always in the result, composed messages (cs) also are in the result, along with 
new messages built from xs + cs \<close>
"build\<^sub>n xs pks sks (Suc nc) 0 l = (build\<^sub>n (List.union (pair2 xs xs l) xs) pks sks nc 0 l)" | 
"build\<^sub>n xs pks sks 0 (Suc ne) l = (build\<^sub>n (List.union (senc\<^sub>1' xs) xs) pks sks 0 ne l)" |
\<comment> \<open> Original xs + new messages after composition + new messages after encryption \<close>
"build\<^sub>n xs pks sks (Suc nc) (Suc ne) l = (if ne = 0 then
  \<comment> \<open> If only one encryption, we treat it as outermost so composion first \<close>
  (build\<^sub>n (List.union (pair2 xs xs l) xs) pks sks nc (Suc 0) l)
else 
  (List.union 
  \<comment> \<open> New messages after composition \<close>
    (build\<^sub>n (List.union (pair2 xs xs l) xs) pks sks nc (Suc ne) l)
  \<comment> \<open> New messages after encryption \<close>
    (build\<^sub>n (List.union (senc\<^sub>1' xs) xs) pks sks (Suc nc) ne l)
  )
)"

value "let ns = sort [MNon (N Alice), (MAg Bob), MKp (PK Bob)]
  in build\<^sub>n ns (extract_dpkey ns) (extract_dskey ns) 0 0 2"

value "let ns = sort [MNon (N Alice), MKp (PK Bob)]
  in build\<^sub>n ns (extract_dpkey ns) (extract_dskey ns) 1 1 2"

text \<open> We build modular expressions by @{text "^\<^sub>m"} first, then build others from new messages \<close>
definition "build1\<^sub>n ns c e l = (let xs = mod_exp2' ns; ys = mod_exp1' ns; 
    zs = remdups xs@ys@ns; ss = sig\<^sub>1' (zs)
  in (build\<^sub>n (zs@ss) (extract_dpkey ss) (extract_dskey ss) c e l))"

definition "build1\<^sub>n_0 ns = build1\<^sub>n ns 0 1 1"
definition "build1\<^sub>n_1 ns = build1\<^sub>n ns 1 1 3"
definition "build1\<^sub>n_2 ns = build1\<^sub>n ns 1 1 2"
definition "build1\<^sub>n_3 ns = build1\<^sub>n ns 2 1 3"

subsection \<open> Processes \<close>
chantype Chan =
  env :: "dagent \<times> dagent"
\<comment> \<open> Send to public channels, which are controlled by Intruders. In this attack model, it just means
 the destination is @{text "Intruder"} \<close>
  send :: "dagent \<times> dagent \<times> dmsg"
  recv :: "dagent \<times> dagent \<times> dmsg"
\<comment> \<open> For private channels, both neither source nor destination is @{text "Intruder"}  \<close>
  (* send\<^sub>s :: "dagent \<times> dagent \<times> dmsg"
  recv\<^sub>s :: "dagent \<times> dagent \<times> dmsg" *)
  hear :: "dagent \<times> dagent \<times> dmsg"
  fake :: "dagent \<times> dagent \<times> dmsg"
  leak :: "dmsg"
  sig :: "dsig"
  terminate :: "unit"

end
