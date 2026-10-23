section \<open> Animation of the Diffie-Hellman with digital signatures \<close>
theory DHWJ_config
  imports "ITree_Security.Sec_Messages"
begin
type_synonym max_agents = 2
type_synonym max_pks = 4
type_synonym max_sks = 4
type_synonym max_nonces = 4
type_synonym max_expg = 1
type_synonym max_bitmasks = 3
type_synonym max_bitmask_length = 2

type_synonym dnonce = "max_nonces dnonce"
type_synonym dmsg = "(max_agents, max_nonces, max_pks, max_sks, max_expg, max_bitmasks, max_bitmask_length) dmsg"
type_synonym dagent = "max_agents dagent"
type_synonym dkey = "(max_pks, max_sks) dkey"
type_synonym chan = "(max_agents, max_nonces, max_pks, max_sks, max_expg, max_bitmasks, max_bitmask_length) chan"
type_synonym dbitmask = "(max_bitmasks, max_bitmask_length) dbitmask"

subsection \<open> Configuration and general definitions \<close>
abbreviation "Alice \<equiv> Agent (nmk 0) :: dagent"
abbreviation "Bob \<equiv> Agent (nmk 1) :: dagent"
abbreviation "AllAgents' \<equiv> [Alice, Bob, Intruder] :: dagent list"
abbreviation "AllAgentsButIntruder' \<equiv> [Alice, Bob]"
abbreviation "AllAgentsLst' \<equiv> AgentsLst AllAgents' :: dmsg list"
abbreviation "AllNonces' \<equiv> [nmk 0, nmk 1, nmk 2] :: dnonce list"
abbreviation "AllNoncesLst' \<equiv> NoncesLst AllNonces' :: dmsg list"
abbreviation "AllPKs' \<equiv> [Kp (nmk 0), Kp (nmk 1), Kp (nmk 2)] :: dkey list"
abbreviation "AllPKsLst' \<equiv> PKsLst AllPKs' :: dmsg list"
abbreviation "AllSKs' \<equiv> [Ks (nmk 0), Ks (nmk 1), Ks (nmk 2)] :: dkey list"
abbreviation "AllSKsLst' \<equiv> SKsLst AllSKs' :: dmsg list"
abbreviation "ExpG \<equiv> MExpg (nmk 0) :: dmsg"
(* For this protocol, we use the same bits (nmk 1) for jamming as watermarking *)
abbreviation "AllBitms' \<equiv> [Null, Bm (nmk 0) (nmk 1), Bm (nmk 1) (nmk 1), Bm (nmk 2) (nmk 1)] :: dbitmask list"
abbreviation "AllBitmsLst' \<equiv> BitMLst AllBitms' :: dmsg list"

text \<open> All pairs of agents that form a communication from a source to a destination \<close>
definition "AllOtherAgentsButIntr A = [B. B \<leftarrow> AllAgentsButIntruder', B \<noteq> A]"
definition "AllCommsAgentsButIntr = [(A, B). A \<leftarrow> AllAgentsButIntruder', B \<leftarrow> AllOtherAgentsButIntr A]"
definition "AllOtherAgents A = [B. B \<leftarrow> AllAgents', B \<noteq> A]"

text \<open> Communications from an honest sender to any receiver, including the intruder.
  This is the alphabet the intruder may observe: it also receives messages addressed to itself. \<close>
definition "AllCommsAgentsFromHonest = [(A, B). A \<leftarrow> AllAgentsButIntruder', B \<leftarrow> AllOtherAgents A]"
definition "AllCommsAgents = [(A, B). A \<leftarrow> AllAgents', B \<leftarrow> AllOtherAgents A]"

abbreviation NonceMap :: "dagent \<Zpfun> dnonce"  where 
"NonceMap \<equiv> {Alice \<mapsto> nmk 0, Bob \<mapsto> nmk 1, Intruder \<mapsto> nmk 2}"

abbreviation SKeyMap :: "dagent \<Zpfun> dkey"  where
"SKeyMap \<equiv> {Alice \<mapsto> Ks (nmk 0), Bob \<mapsto> Ks (nmk 1), Intruder \<mapsto> Ks (nmk 2)}"

abbreviation bitmask_map :: "dagent \<Zpfun> dbitmask"  where 
"bitmask_map \<equiv> {Alice \<mapsto> Bm (nmk 0) (nmk 1), Bob \<mapsto> Bm (nmk 1) (nmk 1), Intruder \<mapsto> Bm (nmk 2) (nmk 1)}"

(*
abbreviation PKeyMap :: "dagent \<Zpfun> dkey"  where 
"PKeyMap \<equiv> {Alice \<mapsto> Kp (nmk 0), Bob \<mapsto> Kp (nmk 1), Intruder \<mapsto> Kp (nmk 2), Server \<mapsto> Kp (nmk 3)}"
*)

definition pks :: "dagent \<Rightarrow> dkey" where
"pks a = pk_of_sk (SKeyMap(a))"

abbreviation "MSK A \<equiv> MK (SKeyMap A)"
abbreviation "MPK A \<equiv> MK (pks A)"

definition "AllOtherPKs A = removeAll (MPK A) AllPKsLst'"

text \<open> @{text "Eve1"} for @{text "{Alice \<mapsto> True, Bob \<mapsto> False}"}, 
  @{text "Eve2"} for @{text "{Alice \<mapsto> False, Bob \<mapsto> True}"},
  @{text "Eve3"} for @{text "{Alice \<mapsto> True, Bob \<mapsto> True}"},
  @{text "Eve4"} for @{text "{Alice \<mapsto> False, Bob \<mapsto> False}"},
\<close>
datatype deve = Eve1 | Eve2 | Eve3 | Eve4

text \<open> Different spatial locations of an eavesdropper in terms of jamming ranges of Alice and Bob\<close>
abbreviation intruder_in_range_map :: "deve \<Rightarrow> dagent \<Zpfun> bool"  where 
"intruder_in_range_map eve \<equiv> case eve of 
  Eve1 \<Rightarrow> {Alice \<mapsto> True, Bob \<mapsto> False} |
  Eve2 \<Rightarrow> {Alice \<mapsto> False, Bob \<mapsto> True} |
  Eve3 \<Rightarrow> {Alice \<mapsto> True, Bob \<mapsto> True} |
  Eve4 \<Rightarrow> {Alice \<mapsto> False, Bob \<mapsto> False}
"

definition "mkbma A \<equiv> (MBitm ((bitmask_map(A))))"
abbreviation "bm_or_null_b b A \<equiv> (if b then mkbma A else MBitm Null)"
abbreviation "bm_or_null A eve \<equiv> (if A = Intruder then MBitm Null else bm_or_null_b (intruder_in_range_map eve A) A)"

abbreviation "Secrets_Nonces \<equiv> removeAll (MNon (NonceMap Intruder)) AllNoncesLst'"
abbreviation "Secrets_PKs \<equiv> removeAll (MK (Kp (NonceMap Intruder))) AllPKsLst'"
definition "AllSecrets = ((Secrets_Nonces @ Secrets_PKs @ [mkbma Alice, mkbma Bob]) :: dmsg list)"
(*
abbreviation "Secrets_SKs \<equiv> removeAll (MK (Ks (NonceMap Intruder))) AllSKsLst'"
definition "AllSecrets = ((Secrets_Nonces @ Secrets_PKs @ Secrets_SKs) :: dmsg list)"
*)

value "AllSecrets"
(*
definition InitKnows :: "dmsg list" where 
"InitKnows = AllAgentsLst' @ ExpGLst AllExpGs @ [MNon (NonceMap Intruder), MSK Intruder, MPK Intruder]"
*)
definition InitKnows :: "dmsg list" where 
"InitKnows = AllAgentsLst' @ ExpGLst AllExpGs @ [MNon (NonceMap Intruder), MBitm (bitmask_map(Intruder))]"

value "InitKnows"

end
