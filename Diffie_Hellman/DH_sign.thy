section \<open> Animation of Diffie–Hellman protocol with digital signature \<close>
theory DH_sign
  imports "DH_message"
          "ITree_Simulation.ITree_Simulation"
          "DH_animation"
begin

text \<open> From diffie-hellman-active.pi in ProVerif
(* Diffie-Hellman with signatures
		A -> B : { g^x }skA, pkA    (n0 fresh)
    B -> A : { g^y }skB         (n1 fresh)
      A and B compute the key as k = (g^x)^y = (g^y)^x
    A -> B : { s }k
      The nonce of Alice is chosen as the secret s
*)
\<close>

subsection \<open> General definitions \<close>

definition "AllSecrets = removeAll (MNon (N Intruder)) AllNoncesLst"

definition InitKnows :: "dmsg list" where 
"InitKnows = AllAgentsLst @ (removeAll (MKp (PK Server)) AllPKsLst) @ 
            [g\<^sub>m, MNon (N Intruder), MKs (SK Intruder)]"

value "InitKnows"
subsection \<open>  DH - Processes \<close>
subsubsection \<open> Alice \<close>

definition PAlice :: "dagent \<Rightarrow> dnonce \<Rightarrow> dagent \<Rightarrow> (Chan, unit) itree" where
"PAlice A na B = 
  do {
     \<comment> \<open> Send g^a \<close>
    outp send (A, Intruder, msort \<lbrace>{g\<^sub>m ^\<^sub>m (na)}\<^sub>d\<^bsub>SK A\<^esub> , MKp (PK A)\<rbrace>\<^sub>m);
     \<comment> \<open> Receive g^b \<close>
    (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, A, {g\<^sub>m ^\<^sub>m (nb)}\<^sub>d\<^bsub>SK B\<^esub> ).
       nb \<leftarrow> removeAll na AllNonces, nb \<noteq> N Server]);
    let g_nb = (msd m)
    in do {
      \<comment> \<open> MNon (N A) is chosen as a secret, encrypted with (g^b)^a \<close>
      outp send (A, Intruder, {MNon (N A)}\<^sub>S\<^bsub>g_nb ^\<^sub>m na\<^esub> );
      outp terminate ()
    }
}
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "A_I_snd_msg A na = (
    \<comment> \<open> g^a \<close>
    [(A, Intruder,  msort \<lbrace>{g\<^sub>m ^\<^sub>m (na)}\<^sub>d\<^bsub>SK A\<^esub> , MKp (PK A)\<rbrace>\<^sub>m)] @
    \<comment> \<open> (g^b)^a \<close>
    [(A, Intruder, {MNon (N A)}\<^sub>S\<^bsub>g\<^sub>m ^\<^sub>m (nb) ^\<^sub>m na\<^esub> ).
      nb \<leftarrow> removeAll na AllNonces, nb \<noteq> N Server]
  )"

value "A_I_snd_msg Alice (N Alice)"

definition "A_I_snd_event A na = [send_C m. m \<leftarrow> A_I_snd_msg A na]"

definition "A_I_rcv_msg A na B = (
    \<comment> \<open> g^b \<close>
    [(Intruder, A, {g\<^sub>m ^\<^sub>m (nb)}\<^sub>d\<^bsub>SK B\<^esub> ). 
    nb \<leftarrow> removeAll na AllNonces, nb \<noteq> N Server]
  )"

value "A_I_rcv_msg Alice (N Alice) Bob"

definition "A_I_rcv_event A na B = [recv_C m. m \<leftarrow> A_I_rcv_msg A na B]"

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"

subsubsection \<open> Bob \<close>
definition PBob :: "dagent \<Rightarrow> dnonce \<Rightarrow> dagent \<Rightarrow> (Chan, unit) itree" where
"PBob B nb A = 
  do {
     \<comment> \<open> Receive { g^na }skA, pkA \<close>
    (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, B, msort \<lbrace>{g\<^sub>m ^\<^sub>m (na)}\<^sub>d\<^bsub>skA\<^esub> , pkA\<rbrace>\<^sub>m). 
       na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server,
       skA \<leftarrow> removeAll (SK B) AllSKs, pkA \<leftarrow> removeAll (MKp (PK B)) AllPKsLst]);
    let pkA = mc1 m; m1 = mc2 m; g_na = msd m1
      \<comment> \<open> if skA and pkA are paired \<close>
    in if inv\<^sub>p (mkp pkA) = (msk m1) then do {
        \<comment> \<open> Send g^b \<close>
        outp send (B, Intruder, {g\<^sub>m ^\<^sub>m (nb)}\<^sub>d\<^bsub>SK B\<^esub> );
        \<comment> \<open> Recieve an encrypted message using (g^a)^b as the key \<close>
        (_, _, m2) \<leftarrow> inp_in recv (set [(Intruder, B, msort ({s}\<^sub>S\<^bsub>(g\<^sub>m ^\<^sub>m (nb)) ^\<^sub>m na\<^esub> )). 
           s \<leftarrow> AllNoncesLst, s \<noteq> MNon (N Server), s \<noteq> MNon (nb),
            na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server]);
        \<comment> \<open> If B can break the message m' to get the secret, it terminates. Otherwise, deadlock \<close>
        if List.member (breakm [MNon nb, MAg B, g\<^sub>m ^\<^sub>m nb, g_na, m2]) (MNon (N A)) then 
          outp terminate ()
        else Ret ()
      }
      else do {Ret ()}
}
"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "B_I_snd_msg B nb = \<comment> \<open> g^a \<close> [(B, Intruder, {g\<^sub>m ^\<^sub>m (nb)}\<^sub>d\<^bsub>SK B\<^esub> )]"

value "B_I_snd_msg Bob (N Bob)"

definition "B_I_snd_event B nb = [send_C m. m \<leftarrow> B_I_snd_msg B nb]"

definition "B_I_rcv_msg B nb = (
    \<comment> \<open> g^a \<close>
    [(Intruder, B, msort \<lbrace>{g\<^sub>m ^\<^sub>m (na)}\<^sub>d\<^bsub>skA\<^esub> , pkA\<rbrace>\<^sub>m). 
      na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server,
       skA \<leftarrow> removeAll (SK B) AllSKs, pkA \<leftarrow> removeAll (MKp (PK B)) AllPKsLst] @
    [(Intruder, B, msort ({s}\<^sub>S\<^bsub>(g\<^sub>m ^\<^sub>m (nb)) ^\<^sub>m na\<^esub> )). 
      s \<leftarrow> AllNoncesLst, s \<noteq> MNon (N Server), s \<noteq> MNon (nb),
      na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server]
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
              m' \<leftarrow> (build1\<^sub>n_2 (knows))]);
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

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "PIntruder1 I ni k s = (
  (PIntruder0 I ni k s) 
  \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s)
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "rename_leak = [(leak_C x, leak_C x). x \<leftarrow> AllSecrets]"

definition "rename_I = 
  [(hear_C x, send_C x). x \<leftarrow> (A_I_snd_msg Alice (N Alice) @ B_I_snd_msg Bob (N Bob))] @
  [(fake_C x, recv_C x). x \<leftarrow> (A_I_rcv_msg Alice (N Alice) Bob @ B_I_rcv_msg Bob (N Bob))] @
  [(terminate_C (), terminate_C ())] @
  rename_leak"

value "rename_I"

definition "PIntruder = rename' (PIntruder1 Intruder (N Intruder) (InitKnows) AllSecrets) (set rename_I)"

subsubsection \<open> Composition \<close>

definition "Events_A_B_I = (set (
  (A_I_snd_event Alice (N Alice) @ A_I_rcv_event Alice (N Alice) Bob) @ 
  (B_I_snd_event Bob (N Bob) @ B_I_rcv_event Bob (N Bob)) @ 
  terminate_event))"
value "Events_A_B_I"

definition DH_sign where
"DH_sign = 
    (PAlice Alice (N Alice) Bob  \<parallel>\<^bsub> set terminate_event \<^esub> PBob Bob (N Bob) Alice) 
    \<parallel>\<^bsub> Events_A_B_I \<^esub> PIntruder"

animate_sec DH_sign

(* AReach 15 %Terminate%
   AReach 15 %Leak N Alice%
*)
end
