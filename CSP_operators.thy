section \<open> Extra CSP operators to support verification of security protocols \<close>
theory CSP_operators
  imports "Interaction_Trees.ITree_Extraction"
          "Interaction_Trees.ITree_Deadlock"
          "ITree_UTP.ITree_CSP"

begin

unbundle Z_Relation_Syntax

subsection \<open> CSP processes \<close>
definition outp_choice_from_list :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'b) itree) \<Rightarrow> 'a list \<Rightarrow> ('e, 'b) itree" where
"outp_choice_from_list c P A = Vis (pfun_of_alist (map (\<lambda>x. (build\<^bsub>c\<^esub> x, P x)) A))"

definition outp_choice_from_set :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'a) itree) \<Rightarrow> 'a set \<Rightarrow> _" where
"outp_choice_from_set c P A = Vis (\<lambda> a \<in> build\<^bsub>c\<^esub> ` A \<bullet> P (the (match\<^bsub>c\<^esub> a)))"

lemma outp_choice_from_list_code [code_unfold]:
  "wb_prism c \<Longrightarrow> outp_choice_from_set c P (set xs) = outp_choice_from_list c P xs"
  unfolding outp_choice_from_list_def outp_choice_from_set_def
  by (simp only: set_map [THEN sym] inter_set_filter pabs_set filter_map comp_def, simp add: comp_def)

primrec inter_csp_list :: "(('e, 'a) itree) list \<Rightarrow> ('e, unit) itree" where
"inter_csp_list [] = skip" |
"inter_csp_list (P#Ps) = (do {P;skip} \<interleave> inter_csp_list Ps)"

(* Alternative definition using foldl 
definition inter_csp_list' :: "(('e, 'a) itree) list \<Rightarrow> ('e, unit) itree" where
"inter_csp_list' Px = foldl (\<lambda>q p. (do {p ; skip} \<interleave> q)) skip Px"
*)

definition indexed_inter_csp_list :: "'a list \<Rightarrow> ('a \<Rightarrow> (('e, _) itree)) \<Rightarrow> ('e, unit) itree" ("\<interleave>\<^bsub>_\<^esub> @ _" [55, 56] 56)
  where "indexed_inter_csp_list A Px = inter_csp_list (map Px A)"

primrec seq_csp_list :: "(('e, 'a) htree) list \<Rightarrow> ('e, 'a) htree" where
"seq_csp_list [] s = Ret s" |
"seq_csp_list (P#Ps) s = (P s \<bind> (seq_csp_list Ps))"

definition indexed_seq_csp_list :: "'a list \<Rightarrow> ('a \<Rightarrow> ('e, 'b) htree) \<Rightarrow> ('e, 'b) htree" (";\<^bsub>_\<^esub> @ _" [55, 56] 56)
  where "indexed_seq_csp_list A Ps s = seq_csp_list (map Ps A) s"

end
