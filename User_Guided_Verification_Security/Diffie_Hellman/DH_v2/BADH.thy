section \<open> Animation of the Diffie-Hellman with digital signatures \<close>
theory BADH
  imports "ITree_Simulation.ITree_Simulation" 
          "ITree_Security.Sec_Animation"
          "DH_config"
begin

subsection \<open> DH with Digital Signature (BADH) to provide mutual authentication \<close>
(* See the 2003 SIGMA paper *)
text \<open> 
Diffie-Hellman with signatures
Set up: A and B know peer's public keys, but Intruder doesn't know them. 
We add A in the first message so B knows who (A) sends the message.

		A -> B : A, g^x
    B -> A : g^y, B, {(g^x, g^y)}^d_skB
      A and B compute the key as k = (g^x)^y = (g^y)^x
    A -> B : A, {(g^y, g^x)}^d_skA
      The nonce of Alice is chosen as the secret s
\<close>

(* Another version for references.
https://en.wikipedia.org/wiki/Station-to-Station_protocol#Authentication-only_STS *)
(*
  (1) Alice \<rightarrow> Bob : x
  (2) Alice \<leftarrow> Bob : y, SB(y, x)
  (3) Alice \<rightarrow> Bob : SA(x, y)
*)

subsection \<open>  DH - Processes \<close>
subsubsection \<open> Alice \<close>
definition Initiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> dagent \<Rightarrow> (chan, unit) itree" where
"Initiator A na B = 
  do {
    \<^cancel>\<open>(_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents', C \<noteq> A]);\<close>
    do {
      \<comment> \<open> Send a signal to claim na is secret between A and B \<close>
      \<^cancel>\<open>outp sig (ClaimSecret A na (set [B]));\<close>
      \<comment> \<open> Send g^na \<close>
      outp send (A, Intruder, B, \<lbrace>MAg A, ExpG ^\<^sub>m (MNon na)\<rbrace>\<^sub>m);
      \<comment> \<open> Receive the second message from other agents \<close>
      \<comment> \<open> Assume A knows B's public key \<close>
      (_, _, _, m) \<leftarrow> inp_in recv (set [(Intruder, Intruder, A, 
          \<lbrace>ExpG ^\<^sub>m (MNon (NonceMap B)), 
            {\<lbrace>ExpG ^\<^sub>m (MNon na), ExpG ^\<^sub>m (MNon (NonceMap B)) \<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap B)\<^esub> 
          \<rbrace>\<^sub>m). B \<leftarrow> removeAll A AllAgents']);
      let gB = mc1 m
      in 
        do {
          \<comment> \<open> Send message 3 back to B \<close>
          outp send (A, Intruder, B, {\<lbrace>gB, ExpG ^\<^sub>m (MNon na)\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap A)\<^esub> );
          \<comment> \<open> MKp (PK A) is chosen as a secret, encrypted with (g^b)^a \<close>
          outp send (A, Intruder, B, {MK (pks A)}\<^sup>s\<^bsub>gB ^\<^sub>m (MNon na)\<^esub> );
          outp terminate ()
        }
    }
}
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition A_I_snd_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
  "A_I_snd_msg A na = (let Bs = removeAll A AllAgents' in
    \<comment> \<open> g^a \<close>
    [(A, Intruder, B, \<lbrace>MAg A, ExpG ^\<^sub>m (MNon na)\<rbrace>\<^sub>m). B \<leftarrow> Bs] @
      \<comment> \<open> (g^b)^a \<close>
    [(A, Intruder, B, {\<lbrace>ExpG ^\<^sub>m (MNon (NonceMap B)), ExpG ^\<^sub>m (MNon na)\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap A)\<^esub> ).
      B \<leftarrow> Bs] @
    [(A, Intruder, B, {MK (pks A)}\<^sup>s\<^bsub>ExpG ^\<^sub>m (MNon (NonceMap B)) ^\<^sub>m (MNon na)\<^esub> ). B \<leftarrow> Bs ]
  )"

value "buildable ({\<lbrace>ExpG ^\<^sub>m (MNon (NonceMap Bob)), ExpG ^\<^sub>m (MNon (NonceMap Alice))\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap Alice)\<^esub> ) 
  (set (breakl [MNon (NonceMap Alice), ExpG, MAg Alice, ExpG ^\<^sub>m (MNon (NonceMap Bob)), MK ((SKeyMap Alice))]))"

value "A_I_snd_msg Alice (NonceMap Alice)"

definition A_I_snd_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"A_I_snd_event A na = [send_C m. m \<leftarrow> A_I_snd_msg A na]"

definition A_I_rcv_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"A_I_rcv_msg A na = ( let Bs = removeAll A AllAgents' in
    \<comment> \<open> (g^y, {(g^y, g^x)}_skB \<close>
    [(Intruder, Intruder, A, \<lbrace>ExpG ^\<^sub>m (MNon (NonceMap B)), 
      {\<lbrace>ExpG ^\<^sub>m (MNon na), ExpG ^\<^sub>m (MNon (NonceMap B))\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap B)\<^esub> 
    \<rbrace>\<^sub>m). B \<leftarrow> Bs]
  )"

value "A_I_rcv_msg Alice (NonceMap Alice)"

definition A_I_rcv_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"A_I_rcv_event A na = [recv_C m. m \<leftarrow> A_I_rcv_msg A na]"

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"
 
subsubsection \<open> Bob \<close>
value "breakl [MNon (NonceMap Bob), MAg (Bob), ExpG ^\<^sub>m (MNon (NonceMap Bob)), ExpG ^\<^sub>m (MNon (NonceMap Alice)), 
  {MK (Kp (knatmake (0::\<nat>)))}\<^sup>s\<^bsub>(ExpG ^\<^sub>m (MNon (NonceMap Bob))) ^\<^sub>m (MNon (NonceMap Alice))\<^esub> ]"

definition Responder :: "dagent \<Rightarrow> dnonce \<Rightarrow> dagent \<Rightarrow> (chan, unit) itree" where
"Responder B nb A = 
  do {
    \<comment> \<open> Receive g^x\<close>
    (_, _, _, m) \<leftarrow> inp_in recv (set [(Intruder, Intruder, B, \<lbrace>MAg A, ExpG ^\<^sub>m (MNon (NonceMap A))\<rbrace>\<^sub>m). 
       A \<leftarrow> removeAll B AllAgents']);
    \<comment> \<open> Send g^b \<close>
    let A = ma (mc1 m); gA = mc2 m in 
      do {
        outp send (B, Intruder, A, \<lbrace>ExpG ^\<^sub>m (MNon nb), {\<lbrace>gA, ExpG ^\<^sub>m (MNon nb)\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap B)\<^esub> \<rbrace>\<^sub>m);
        \<comment> \<open> Receive (g^b, g^a)_skA \<close>
        (_, _, _, m3) \<leftarrow> inp_in recv (set [(Intruder, Intruder, B, {\<lbrace>ExpG ^\<^sub>m (MNon nb), gA\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap A')\<^esub> ). 
          A' \<leftarrow> removeAll B AllAgents']);
        \<comment> \<open> Recieve an encrypted message using (g^a)^b as the key \<close>
        (_, _, _, m') \<leftarrow> inp_in recv (set [(Intruder, Intruder, B, {s}\<^sup>s\<^bsub>swap_mod_exp (gA ^\<^sub>m (MNon nb))\<^esub> ). 
           s \<leftarrow> AllPKsLst']);
        \<comment> \<open> If B can break the message m' to get the secret, it terminates. Otherwise, deadlock \<close>
        if List.member (breakl [MNon nb, MAg B, ExpG ^\<^sub>m (MNon nb), gA, m']) (MK (pks A)) then 
          outp terminate ()
        else Ret ()
      }
}
"

text \<open> All messages that Bob will send and Intruder can hear  \<close>
definition B_I_snd_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"B_I_snd_msg B nb = (let As = removeAll B AllAgents' in 
  \<comment> \<open> g^b, {(g^a, g^b)_skB} \<close> 
  [(B, Intruder, A, \<lbrace>ExpG ^\<^sub>m (MNon nb), 
    {\<lbrace>ExpG ^\<^sub>m (MNon (NonceMap A)), ExpG ^\<^sub>m (MNon nb)\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap B)\<^esub> \<rbrace>\<^sub>m).  A \<leftarrow> As]
)"

value "B_I_snd_msg Bob (NonceMap Bob)"

definition B_I_snd_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"B_I_snd_event B nb = [send_C m. m \<leftarrow> B_I_snd_msg B nb]"

definition B_I_rcv_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"B_I_rcv_msg B nb = (let As = removeAll B AllAgents' in
    \<comment> \<open> Message 1: (A, g^a) \<close>
    [(Intruder, Intruder, B, \<lbrace>MAg A, ExpG ^\<^sub>m (MNon (NonceMap A))\<rbrace>\<^sub>m ). A \<leftarrow> As] @
    [(Intruder, Intruder, B, {\<lbrace>ExpG ^\<^sub>m (MNon nb), ExpG ^\<^sub>m (MNon (NonceMap A))\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MK (SKeyMap A')\<^esub> ). 
      A \<leftarrow> As, A' \<leftarrow> As] @
    [(Intruder, Intruder, B, {s}\<^sup>s\<^bsub>swap_mod_exp (ExpG ^\<^sub>m (MNon (NonceMap A)) ^\<^sub>m (MNon nb))\<^esub> ). 
      s \<leftarrow> AllPKsLst', A \<leftarrow> As]
  )"

value "B_I_rcv_msg Bob (NonceMap Bob)"

definition B_I_rcv_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"B_I_rcv_event B nb = [recv_C m. m \<leftarrow> B_I_rcv_msg B nb]"

value "(B_I_rcv_msg Bob (N Bob) @ B_I_snd_msg Bob (N Bob))"

subsubsection \<open> Intruder \<close>

definition "AllPossibleMsgsRecvByAgents = map last4 (A_I_rcv_msg Alice (NonceMap Alice) @ B_I_rcv_msg Bob (NonceMap Bob))"

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
    \<box> \<^cancel>\<open>do { inp_in fake (set [(A, I, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents', m' \<leftarrow> (build1\<^sub>n_3 (knows))]); 
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

definition "PAlice = Initiator Alice (NonceMap Alice) Bob"
definition "PBob = Responder Bob (NonceMap Bob) Alice"

definition "Events_A_B_I = (set (remdups (
  (A_I_snd_event Alice (NonceMap Alice) @ A_I_rcv_event Alice (NonceMap Alice)) @ 
  (B_I_snd_event Bob (NonceMap Bob) @ B_I_rcv_event Bob (NonceMap Bob)) @ 
  terminate_event)))"
value "Events_A_B_I"

definition BADH_Signature where
"BADH_Signature = 
    (PAlice  \<parallel>\<^bsub> set terminate_event \<^esub> PBob) \<parallel>\<^bsub> Events_A_B_I \<^esub> PIntruder"

animate_sec BADH_Signature

(* AReach 15 %Terminate%
   AReach 15 %Leak PK0%
*)

end
