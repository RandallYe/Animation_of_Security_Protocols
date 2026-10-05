section \<open> Animation of NSPKP (3-message version) including the original and the corrected versions \<close>
theory NSLPK3
  imports "ITree_Simulation.ITree_Simulation"
          "ITree_Security.Sec_Animation"
          "NSPK3_config"
begin

text \<open> Needham Schroeder Public Key Protocol: three-message version
The protocol runs as follows:

    A \<rightarrow> B : { N A , A } K P B {\displaystyle A\rightarrow B:\{N_{A},A\}_{K_{PB}}}

        A {\displaystyle A} chooses a random N A {\displaystyle N_{A}} and sends it to B {\displaystyle B}.

    B \<rightarrow> A : { N A , N B } K P A {\displaystyle B\rightarrow A:\{N_{A},N_{B}\}_{K_{PA}}}

        B {\displaystyle B} chooses a random N B {\displaystyle N_{B}}, and sends it to A {\displaystyle A} along with N A {\displaystyle N_{A}} to prove ability to decrypt with K S B {\displaystyle K_{SB}}.

    A \<rightarrow> B : { N B } K P B {\displaystyle A\rightarrow B:\{N_{B}\}_{K_{PB}}}

        A {\displaystyle A} confirms N B {\displaystyle N_{B}} to B {\displaystyle B}, to prove ability to decrypt with K S A {\displaystyle K_{SA}}.
\<close>
subsection \<open> Needham Schroeder Lowe  - Processes \<close>

subsubsection \<open> Alice \<close>

definition LInitiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan, unit) itree" where
"LInitiator A na = 
      do {
          \<comment> \<open> Receive environment's request to establish authentication with B \<close>
          (_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents', C \<noteq> A]);
          do {
                \<comment> \<open> Send a signal to claim na is secret between A and B \<close>
                outp sig (ClaimSecret A na (set [B]));
                \<comment> \<open> Send Msg1 \<close>
                outp send (A, Intruder, B, {\<lbrace>MNon (na), MAg A\<rbrace>\<^sub>m}\<^sup>a\<^bsub>MK (pks(B))\<^esub> );
                \<comment> \<open> Receive Msg2, A expects an identity from B, not any agent. So A won't accept Bob if
                B is not Bob. \<close>
               (_, _, _, m) \<leftarrow> inp_in recv (set [(Intruder, Intruder, A, {\<lbrace>MNon na, MNon nb, MAg B\<rbrace>\<^sub>m }\<^sup>a\<^bsub>MK (pks(A))\<^esub> ). 
                  nb \<leftarrow> removeAll na AllNonces']);
                \<comment> \<open> (mn (mc2 m)) \<close>
                let nb = (mn (mc1 (mc2 (mem m))))
                in
                  do {
                    outp sig (StartProt A B na nb);
                    \<comment> \<open> Send Msg3 \<close>
                    outp send (A, Intruder, B, {MNon nb}\<^sup>a\<^bsub>MK (pks(B))\<^esub> );
                    outp sig (EndProt A B na nb);
                    outp terminate ()
                  }
          }
  }
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition LA_I_snd_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"LA_I_snd_msg A na = (let Bs = removeAll A AllAgents'
  in
    \<comment> \<open> Msg1 \<close>
    [(A, Intruder, B, {\<lbrace>MNon (na), MAg A\<rbrace>\<^sub>m}\<^sup>a\<^bsub>MK (pks(B))\<^esub> ). B \<leftarrow> Bs] @
      \<comment> \<open> Msg3 \<close>
    [(A, Intruder, B, {MNon nb}\<^sup>a\<^bsub>MK (pks(B))\<^esub> ). B \<leftarrow> Bs, nb \<leftarrow> removeAll na AllNonces']
  )"

value "LA_I_snd_msg Alice (NonceMap(Alice))"

definition LA_I_snd_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"LA_I_snd_event A na = [send_C m. m \<leftarrow> LA_I_snd_msg A na]"

definition LA_I_rcv_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"LA_I_rcv_msg A na = (
    \<comment> \<open> Msg2 \<close>
    [(Intruder, Intruder, A, {\<lbrace>MNon na, MNon nb, MAg B\<rbrace>\<^sub>m }\<^sup>a\<^bsub>MK (pks(A))\<^esub> ). 
      nb \<leftarrow> removeAll na AllNonces', B \<leftarrow> removeAll A AllAgents'
    ]
  )"

value "LA_I_rcv_msg Alice (NonceMap(Alice))"

definition LA_I_rcv_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"LA_I_rcv_event A na = [recv_C m. m \<leftarrow> LA_I_rcv_msg A na]"

definition A_I_sig :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"A_I_sig A na = [sig_C (ClaimSecret A nb (set [B])). 
  nb \<leftarrow> AllNonces', B \<leftarrow> removeAll A AllAgents']"

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"

subsubsection \<open> Bob \<close>
definition LResponder :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan, unit) itree" where
"LResponder B nb = 
      do {
          \<comment> \<open> Receive Msg1 \<close>
          (_, _, _, m) \<leftarrow> inp_in recv (set [(Intruder, Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^sup>a\<^bsub>MK (pks(B))\<^esub> ). 
            A \<leftarrow> removeAll B AllAgents', 
            na \<leftarrow> removeAll nb AllNonces']);
          let A = ma (mc2 (mem m)); na = mn (mc1 (mem m))
          in
            do {  
                  \<comment> \<open> Send a signal to claim nb is secret between A and B \<close>
                  outp sig (ClaimSecret B nb (set [A]));
                  outp sig (StartProt B A na nb);
                  \<comment> \<open> Send Msg2 \<close>
                  outp send (B, Intruder, A, {\<lbrace>MNon na, MNon nb, MAg B\<rbrace>\<^sub>m}\<^sup>a\<^bsub>MK (pks(A))\<^esub> );
                  \<comment> \<open> Receive Msg3 \<close>
                  m3 \<leftarrow> inp_in recv (set [(Intruder, Intruder, B, {(MNon nb)}\<^sup>a\<^bsub>MK (pks(B))\<^esub> )]);
                  outp sig (EndProt B A na nb);
                  outp terminate ()
            }
  }
"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition LB_I_rcv_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"LB_I_rcv_msg B nb = (let As = removeAll B AllAgents'
  in
    \<comment> \<open> Msg1 \<close>
    [(Intruder, Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^sup>a\<^bsub>MK (pks(B))\<^esub> ). 
        A \<leftarrow> As, na \<leftarrow> removeAll nb AllNonces'] @
    \<comment> \<open> Msg3 \<close>
    [(Intruder, Intruder, B, {MNon nb}\<^sup>a\<^bsub>MK (pks(B))\<^esub> )]
  )"

value "LB_I_rcv_msg Bob (NonceMap(Bob))"

definition LB_I_rcv_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"LB_I_rcv_event B nb = [recv_C m. m \<leftarrow> LB_I_rcv_msg B nb]"

definition LB_I_snd_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"LB_I_snd_msg B nb = (let As = removeAll Bob AllAgents'
  in
    \<comment> \<open> Msg2 \<close>
    [(B, Intruder, A, {\<lbrace>MNon na, MNon (nb), MAg B\<rbrace>\<^sub>m }\<^sup>a\<^bsub>MK (pks(A))\<^esub> ). 
      A \<leftarrow> As, na \<leftarrow> removeAll nb AllNonces'
    ]
  )"

value "LB_I_snd_msg Bob (NonceMap(Bob))"
value "(LB_I_rcv_msg Bob (NonceMap(Bob)) @ LB_I_snd_msg Bob (NonceMap(Bob)))"

definition LB_I_snd_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"LB_I_snd_event B nb = [send_C m. m \<leftarrow> LB_I_snd_msg B nb]"

definition "B_I_sig B nb = [sig_C (ClaimSecret B na (set [A])). 
  na \<leftarrow> AllNonces', A \<leftarrow> removeAll B AllAgents']"

subsubsection \<open> Intruder \<close>
definition "AllPossibleMsgsRecvByAgents = map last4 (LA_I_rcv_msg Alice (NonceMap Alice) @ LB_I_rcv_msg Bob (NonceMap Bob))"

value "AllPossibleMsgsRecvByAgents"

definition LPIntruder0:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> (chan, unit) itree" where
"LPIntruder0 I ni k s = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (A, I, B, m) \<leftarrow> inp_in hear (set (LA_I_snd_msg Alice (NonceMap(Alice)) @ LB_I_snd_msg Bob (NonceMap(Bob))));
            \<comment> \<open> Intruder can fake any message (it can infer) to the target \<close>
            Ret (True, breakl (List.insert m knows), sec)}
    \<box> \<^cancel>\<open>do { inp_in fake (set [(A, I, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents', 
          m' \<leftarrow> (buildm (knows))]); Ret (True, knows, sec) }\<close>
      do {  
            inp_in fake (set [(A, I, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents', 
                m' \<leftarrow> (filter_buildable AllPossibleMsgsRecvByAgents (set knows))]); 
            Ret (True, knows, sec) 
      }
    \<box> do { outp terminate (); Ret (False, knows, sec) }
    \<comment> \<open> If an agent claims n is secret and only knows to agent B, which is the intruder. We can remove 
      this nonce in the secret. \<close>
    \<box> do { c \<leftarrow> inp_in sig (set [(ClaimSecret A n (set [B])). A \<leftarrow> removeAll I AllAgents', 
              n \<leftarrow> removeAll ni AllNonces',  B \<leftarrow> AllAgents']);
              (if I \<in> (sp c) then Ret (True, knows, (removeAll (MNon (sn c)) sec)) else Ret (True, knows, sec))
          }
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
definition "LPIntruder1 I ni k s = ((LPIntruder0 I ni k s) \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s) 
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "rename_leak = [(leak_C x, leak_C x). x \<leftarrow> AllSecrets]"

definition "rename_sig I ni = [(sig_C (ClaimSecret A n (set [B])), sig_C (ClaimSecret A n (set [B]))). 
              A \<leftarrow> removeAll I AllAgents', n \<leftarrow> removeAll ni AllNonces',  B \<leftarrow> AllAgents', 
              A \<noteq> B]"

definition "rename_I_L = [(send_C x, send_C x). x \<leftarrow> (LA_I_snd_msg Alice (NonceMap(Alice)) @ LB_I_snd_msg Bob (NonceMap(Bob)))] @
  [(recv_C x, recv_C x). x \<leftarrow> (LA_I_rcv_msg Alice (NonceMap(Alice)) @ LB_I_rcv_msg Bob (NonceMap(Bob)))] @
  [(terminate_C (), terminate_C ())] @
  rename_leak @ rename_sig Intruder (NonceMap(Intruder))"

value "rename_I_L"

definition "LPIntruder = rename' (LPIntruder1 Intruder (NonceMap(Intruder)) InitKnows AllSecrets) (set rename_I_L)"

subsubsection \<open> Composition \<close>
definition "LPAlice = LInitiator Alice (NonceMap(Alice))"
definition "LPBob = LResponder Bob (NonceMap(Bob))"

definition "LEvents_A_B_I = 
  (set (remdups (((LA_I_snd_event Alice (NonceMap(Alice)) 
      @ LA_I_rcv_event Alice (NonceMap(Alice)) 
      @ A_I_sig Alice (NonceMap(Alice))) 
      @ terminate_event 
      @ (LB_I_snd_event Bob (NonceMap(Bob)) 
      @ LB_I_rcv_event Bob (NonceMap(Bob)) 
      @ B_I_sig Bob (NonceMap(Bob))))
)))"

definition NSLPK3 where
"NSLPK3 = (LPAlice \<parallel>\<^bsub> set terminate_event \<^esub> LPBob)  \<parallel>\<^bsub> LEvents_A_B_I \<^esub>  LPIntruder"

animate_sec NSLPK3

(*
Reachability:
  AReach 15 %Terminate%
  AReach 15 %Leak N1%
  RReach 15 %Leak N1%
  AReach 15 %Sig EndProt (A1) (A0) (N0) (N1)% # %Sig StartProt (A0) (A1) (N0) (N1)%
  AReach 15 %Sig EndProt (A0) (A1) (N0) (N1)% # %Sig StartProt (A1) (A0) (N0) (N1)%
*)
end
