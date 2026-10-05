section \<open> Animation of the classic Diffie-Hellman without signatures \<close>
theory DH
  imports "ITree_Simulation.ITree_Simulation"
          "ITree_Security.Sec_Animation"
          "DH_config"
begin

text \<open>
Diffie-Hellman without signatures, Only resists passive attacks
	1. A -> B : g^x
  2. B -> A : g^y
     A and B compute the key as k = (g^x)^y = (g^y)^x
  3. A -> B : {s}k
    We choose the public key of Alice as the secret s
\<close>

subsection \<open>  DH - Processes \<close>
subsubsection \<open> Alice \<close>
definition Initiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan, unit) itree" where
"Initiator A na = 
  do {
    (_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents', C \<noteq> A]);
    do {
      \<comment> \<open> Send g^na \<close>
      outp send (A, Intruder, B, ExpG ^\<^sub>m (MNon na));
       \<comment> \<open> Receive the second message from other agents. nb is not known to A. \<close>
      (_, _, _, m) \<leftarrow> inp_in recv (set [(Intruder, Intruder, A, ExpG ^\<^sub>m (MNon nb)). nb \<leftarrow> removeAll na AllNonces']);
      \<comment> \<open> Send Msg3 \<close>
      \<comment> \<open> MKp (PK A) is chosen as a secret, encrypted with (g^b)^a \<close>
      outp send (A, Intruder, B, {MK (pks A)}\<^sup>s\<^bsub>m ^\<^sub>m (MNon na)\<^esub> );
      outp terminate ()
    }
  }
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition A_I_snd_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"A_I_snd_msg A na = (let Bs = removeAll A AllAgents'
  in
    \<comment> \<open> g^a \<close>
    [(A, Intruder, B, ExpG ^\<^sub>m (MNon na)). B \<leftarrow> Bs] @
      \<comment> \<open> (g^b)^a \<close>
    [(A, Intruder, B, {MK (pks A)}\<^sup>s\<^bsub>ExpG ^\<^sub>m (MNon nb) ^\<^sub>m (MNon na)\<^esub> ).
      nb \<leftarrow> removeAll na AllNonces', B \<leftarrow> Bs]
  )"

value "A_I_snd_msg Alice (NonceMap Alice)"

definition A_I_snd_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"A_I_snd_event A na = [send_C m. m \<leftarrow> A_I_snd_msg A na]"

definition A_I_rcv_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where  
"A_I_rcv_msg A na = (
    \<comment> \<open> g^b \<close>
    [(Intruder, Intruder, A, ExpG ^\<^sub>m (MNon nb)). nb \<leftarrow> removeAll na AllNonces']
  )"

value "A_I_rcv_msg Alice (NonceMap Alice)"

definition A_I_rcv_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"A_I_rcv_event A na = [recv_C m. m \<leftarrow> A_I_rcv_msg A na]"

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"
 
subsubsection \<open> Bob \<close>

definition Responder :: "dagent \<Rightarrow> dnonce \<Rightarrow> dagent \<Rightarrow> (chan, unit) itree" where
"Responder B nb A = 
  do {
     \<comment> \<open> Send g^b \<close>
    outp send (B, Intruder, A, ExpG ^\<^sub>m (MNon nb));
     \<comment> \<open> Receive g^a \<close>
    (_, _, _, m) \<leftarrow> inp_in recv (set [(Intruder, Intruder, B, ExpG ^\<^sub>m (MNon na) ). 
       na \<leftarrow> removeAll nb AllNonces']);
    \<comment> \<open> Recieve an encrypted message using (g^a)^b as the key \<close>
    (_, _, _, m') \<leftarrow> inp_in recv (set [(Intruder, Intruder, B, {s}\<^sup>s\<^bsub>(ExpG ^\<^sub>m (MNon nb)) ^\<^sub>m (MNon na)\<^esub> ). 
       s \<leftarrow> AllPKsLst', na \<leftarrow> removeAll nb AllNonces']);
    \<comment> \<open> If B can break the message m' to get the secret, it terminates. Otherwise, deadlock \<close>
    if List.member (breakl [MNon nb, MAg B, ExpG ^\<^sub>m (MNon nb), m, m']) (MK (pks A)) then 
      outp terminate ()
    else Ret ()
}
"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition B_I_snd_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"B_I_snd_msg B nb = (let As = removeAll B AllAgents' in 
   \<comment> \<open> g^a \<close> [(B, Intruder, A, ExpG ^\<^sub>m (MNon nb)). A \<leftarrow> As]
)"

value "B_I_snd_msg Bob (NonceMap Bob)"

definition B_I_snd_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"B_I_snd_event B nb = [send_C m. m \<leftarrow> B_I_snd_msg B nb]"

definition B_I_rcv_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"B_I_rcv_msg B nb = (
    \<comment> \<open> g^a \<close>
    [(Intruder, Intruder, B, ExpG ^\<^sub>m (MNon na) ). na \<leftarrow> removeAll nb AllNonces'] @
    [(Intruder, Intruder, B, {s}\<^sup>s\<^bsub>(ExpG ^\<^sub>m (MNon nb)) ^\<^sub>m (MNon na)\<^esub>  ). 
      s \<leftarrow> AllPKsLst', na \<leftarrow> removeAll nb AllNonces']
  )"

value "B_I_rcv_msg Bob (NonceMap Bob)"

definition B_I_rcv_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"B_I_rcv_event B nb = [recv_C m. m \<leftarrow> B_I_rcv_msg B nb]"

value "(B_I_rcv_msg Bob (NonceMap Bob) @ B_I_snd_msg Bob (NonceMap Bob))"

subsubsection \<open> Intruder \<close>
definition AllPossibleMsgsRecvByAgents :: "dmsg list" where 
"AllPossibleMsgsRecvByAgents = (map last4 (A_I_rcv_msg Alice (NonceMap Alice) @ B_I_rcv_msg Bob (NonceMap Bob)))"

value "AllPossibleMsgsRecvByAgents"

text \<open> @{text "PIntruder I ni k sec "} \<close>
definition PIntruder0:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> (chan, unit) itree" where
"PIntruder0 I ni k s = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (A, I, B, m) \<leftarrow> inp_in hear (set (A_I_snd_msg Alice (NonceMap Alice) @ B_I_snd_msg Bob (NonceMap Bob)));
            Ret (True, breakl (List.insert m knows), sec)}
    \<box> \<^cancel>\<open>do { inp_in fake (set [(A, I, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents', 
              m' \<leftarrow> (build1\<^sub>n_0 (knows))]); 
            Ret (True, knows, sec) }\<close>
      do {  
            inp_in fake (set [(A, I, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents', 
                m' \<leftarrow> (filter_buildable AllPossibleMsgsRecvByAgents (set knows))]); 
            Ret (True, knows, sec) 
      }
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
definition "PIntruder1 I ni k s =
  ((PIntruder0 I ni k s) \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s)
    \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "rename_leak = [(leak_C x, leak_C x). x \<leftarrow> AllSecrets]"

definition "rename_I = 
  [(send_C x, send_C x). x \<leftarrow> (A_I_snd_msg Alice (NonceMap Alice) @ B_I_snd_msg Bob (NonceMap Bob))] @
  [(recv_C x, recv_C x). x \<leftarrow> (A_I_rcv_msg Alice (NonceMap Alice) @ B_I_rcv_msg Bob (NonceMap Bob))] @
  [(terminate_C (), terminate_C ())] @
  rename_leak"

value "rename_I"

text \<open> We use the rename operator here to block all built messages that Alice and Bob are not going 
to receive. This is to reduce unnecessary messages sent to the network, for the sake of animation 
performance. \<close>
definition "PIntruder = rename' (PIntruder1 Intruder (NonceMap Intruder) InitKnows AllSecrets) (set rename_I)"

subsubsection \<open> Composition \<close>

definition "PAlice = Initiator Alice (NonceMap Alice)"
definition "PBob = Responder Bob (NonceMap Bob) Alice"

definition "Events_A_B_I = (set (remdups (
  (A_I_snd_event Alice (NonceMap Alice) @ A_I_rcv_event Alice (NonceMap Alice)) @ 
  (B_I_snd_event Bob (NonceMap Bob) @ B_I_rcv_event Bob (NonceMap Bob)) @ 
  terminate_event)))"
value "Events_A_B_I"

definition DH_Original where
"DH_Original = 
    (PAlice  \<parallel>\<^bsub> set terminate_event \<^esub> PBob) \<parallel>\<^bsub> Events_A_B_I \<^esub> PIntruder"

animate_sec_sound DH_Original

(* AReach 15 %Terminate%
   AReach 15 %Leak PK0%
*)

end
