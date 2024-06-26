section \<open> Animation of Diffie–Hellman protocol \<close>
theory DH
  imports "DH_message"
          "ITree_Simulation.ITree_Simulation"
          "DH_animation"
begin

text \<open> From diffie-hellman-passive.pi in ProVerif
Diffie-Hellman without signatures, Only resists passive attacks
	1. A -> B : g^x
  2. B -> A : g^y
     A and B compute the key as k = (g^x)^y = (g^y)^x
  3. A -> B : {s}k
    We choose the public key of Alice as the secret s
\<close>

subsection \<open> General definitions \<close>
definition "AllSecrets = removeAll (MNon (N Intruder)) AllNoncesLst @ 
  removeAll (MKp (PK Intruder)) AllPKsLst"

definition InitKnows :: "dmsg list" where 
"InitKnows = AllAgentsLst @ [g\<^sub>m, MNon (N Intruder), MKs (SK Intruder), MKp (PK Intruder)]"

subsection \<open>  DH - Processes \<close>
subsubsection \<open> Alice \<close>

definition PAlice :: "dagent \<Rightarrow> dnonce \<Rightarrow> (Chan, unit) itree" where
"PAlice A na = 
  do {
     \<comment> \<open> Send g^a \<close>
    outp send (A, Intruder, g\<^sub>m ^\<^sub>m (na));
     \<comment> \<open> Receive g^b \<close>
    (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, A, g\<^sub>m ^\<^sub>m (nb) ). 
       nb \<leftarrow> removeAll na AllNonces, nb \<noteq> N Server]);
    \<comment> \<open> MKp (PK A) is chosen as a secret, encrypted with (g^b)^a \<close>
    outp send (A, Intruder, {MKp (PK A)}\<^sub>S\<^bsub>m ^\<^sub>m na\<^esub> );
    outp terminate ()
}
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "A_I_snd_msg A na = (
    \<comment> \<open> g^a \<close>
    [(A, Intruder,  g\<^sub>m ^\<^sub>m (na))] @
      \<comment> \<open> (g^b)^a \<close>
    [(A, Intruder, {MKp (PK A)}\<^sub>S\<^bsub>g\<^sub>m ^\<^sub>m (nb) ^\<^sub>m na\<^esub> ).
      nb \<leftarrow> removeAll na AllNonces, nb \<noteq> N Server]
  )"

value "A_I_snd_msg Alice (N Alice)"

definition "A_I_snd_event A na = [send_C m. m \<leftarrow> A_I_snd_msg A na]"

definition "A_I_rcv_msg A na = (
    \<comment> \<open> g^b \<close>
    [(Intruder, A, g\<^sub>m ^\<^sub>m (nb) ). nb \<leftarrow> removeAll na AllNonces, nb \<noteq> N Server]
  )"

value "A_I_rcv_msg Alice (N Alice)"

definition "A_I_rcv_event A na = [recv_C m. m \<leftarrow> A_I_rcv_msg A na]"

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"
 
subsubsection \<open> Bob \<close>
definition PBob :: "dagent \<Rightarrow> dnonce \<Rightarrow> dagent \<Rightarrow> (Chan, unit) itree" where
"PBob B nb A = 
  do {
     \<comment> \<open> Send g^b \<close>
    outp send (B, Intruder, g\<^sub>m ^\<^sub>m (nb));
     \<comment> \<open> Receive g^a \<close>
    (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, B, g\<^sub>m ^\<^sub>m (na) ). 
       na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server]);
    \<comment> \<open> Recieve an encrypted message using (g^a)^b as the key \<close>
    (_, _, m') \<leftarrow> inp_in recv (set [(Intruder, B, {s}\<^sub>S\<^bsub>(g\<^sub>m ^\<^sub>m (nb)) ^\<^sub>m na\<^esub> ). 
       s \<leftarrow> AllPKsLst, na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server]);
    \<comment> \<open> If B can break the message m' to get the secret, it terminates. Otherwise, deadlock \<close>
    if List.member (breakm [MNon nb, MAg B, g\<^sub>m ^\<^sub>m nb, m, m']) (MKp (PK A)) then 
      outp terminate ()
    else Ret ()
}
"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "B_I_snd_msg B nb = \<comment> \<open> g^a \<close> [(B, Intruder,  g\<^sub>m ^\<^sub>m (nb))]"

value "B_I_snd_msg Bob (N Bob)"

definition "B_I_snd_event B nb = [send_C m. m \<leftarrow> B_I_snd_msg B nb]"

definition "B_I_rcv_msg B nb = (
    \<comment> \<open> g^a \<close>
    [(Intruder, B, g\<^sub>m ^\<^sub>m (na) ). na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server] @
    [(Intruder, B, {s}\<^sub>S\<^bsub>(g\<^sub>m ^\<^sub>m (nb)) ^\<^sub>m na\<^esub>  ). 
      s \<leftarrow> AllPKsLst, na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server]
  )"

value "B_I_rcv_msg Bob (N Bob)"

definition "B_I_rcv_event B nb = [recv_C m. m \<leftarrow> B_I_rcv_msg B nb]"

value "(B_I_rcv_msg Bob (N Bob) @ B_I_snd_msg Bob (N Bob))"

subsubsection \<open> Intruder \<close>
text \<open> @{text "PIntruder I ni k sec "} \<close>
definition PIntruder0:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> (Chan, unit) itree" where
"PIntruder0 I ni k s = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (A, B, m) \<leftarrow> inp_in hear (set (A_I_snd_msg Alice (N Alice) @ B_I_snd_msg Bob (N Bob)));
            Ret (True, breakm (List.insert m knows), sec)}
    \<box> do { inp_in fake (set [(A, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents, B \<noteq> Server, 
              m' \<leftarrow> (build1\<^sub>n_0 (knows))]); 
            Ret (True, knows, sec) }
    \<box> do { outp terminate (); Ret (False, knows, sec) }
    \<box> do { 
          \<comment> \<open> List.member should only be used for code generation, see comments in its definition \<close>
          let leaked = filter (\<lambda>s. List.member knows s) sec
          in 
            do { 
                guard (leaked \<noteq> []);
                inp_in leak (set leaked); Ret (True, knows, sec)
            }
      }
    )
    (ret)
  ); Ret ()
}"

definition "PLeakOnlyOnce secrects = \<interleave>\<^bsub>secrects\<^esub> @ (\<lambda>s. do {outp leak s})"

value "PLeakOnlyOnce AllSecrets"

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "PIntruder1 I ni k s = (
  (PIntruder0 I ni k s) 
  \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s)
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "rename_leak = [(leak_C x, leak_C x). x \<leftarrow> AllSecrets]"

definition "rename_I = 
  [(hear_C x, send_C x). x \<leftarrow> (A_I_snd_msg Alice (N Alice) @ B_I_snd_msg Bob (N Bob))] @
  [(fake_C x, recv_C x). x \<leftarrow> (A_I_rcv_msg Alice (N Alice) @ B_I_rcv_msg Bob (N Bob))] @
  [(terminate_C (), terminate_C ())] @
  rename_leak"

value "rename_I"

definition "PIntruder = rename' (PIntruder1 Intruder (N Intruder) InitKnows AllSecrets) (set rename_I)"

subsubsection \<open> Composition \<close>

definition "Events_A_B_I = (set (
  (A_I_snd_event Alice (N Alice) @ A_I_rcv_event Alice (N Alice)) @ 
  (B_I_snd_event Bob (N Bob) @ B_I_rcv_event Bob (N Bob)) @ 
  terminate_event))"
value "Events_A_B_I"

definition DH_Original where
"DH_Original = 
    (PAlice Alice (N Alice)  \<parallel>\<^bsub> set terminate_event \<^esub> PBob Bob (N Bob) Alice) 
    \<parallel>\<^bsub> Events_A_B_I \<^esub> PIntruder"

animate_sec DH_Original

(* AReach 15 %Terminate%
   AReach 15 %Leak PK Alice%
*)

end
