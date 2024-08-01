section \<open> Animation of NSPKP (3-message version) including the original and the corrected versions \<close>
theory NSPK3
  imports "NSPK3_message"
          "ITree_Simulation.ITree_Simulation"
          "NSPK3_animation"
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

subsection \<open> General definitions \<close>
definition "AllSecrets = removeAll (MNon (N Intruder)) AllNoncesLst"

definition InitKnows :: "dmsg list" where 
"InitKnows = AllAgentsLst @ AllPKsLst @ [MNon (N Intruder), MKs (SK Intruder)]"

value "InitKnows"

subsection \<open>  Needham Schroeder original - Processes \<close>

subsubsection \<open> Alice \<close>

definition Initiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> (Chan, unit) itree" where
"Initiator A na = 
      do {
          \<comment> \<open> Receive environment's request to establish authentication with B \<close>
          (_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents, C \<noteq> A]);
          do {
                \<comment> \<open> Send a signal to claim na is secret between A and B \<close>
                outp sig (ClaimSecret A na (set [B]));
                \<comment> \<open> Send Msg1 \<close>
                outp send (A, Intruder, {\<lbrace>MNon (na), MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> );
                \<comment> \<open> Receive Msg2 \<close>
               (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, A, {\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). 
                  nb \<leftarrow> removeAll na AllNonces]);
                \<comment> \<open> (mn (mc2 m)) \<close>
                let nb = (mn (mc2 (mem m))) 
                in
                  do {
                    outp sig (StartProt A B na nb);
                    \<comment> \<open> Send Msg3 \<close>
                    outp send (A, Intruder, {MNon nb}\<^bsub>PK B\<^esub> );
                    outp sig (EndProt A B na nb);
                    outp terminate ()
                  }
          }
  }
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "A_I_snd_msg A na = (let Bs = removeAll A AllAgents
  in
    \<comment> \<open> Msg1 \<close>
    [(A, Intruder, {\<lbrace>MNon (N A), MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). B \<leftarrow> Bs] @
      \<comment> \<open> Msg3 \<close>
    [(A, Intruder, {MNon nb}\<^bsub>PK B\<^esub> ). B \<leftarrow> Bs, nb \<leftarrow> removeAll na AllNonces]
  )"

value "A_I_snd_msg Alice (N Alice)"

definition "A_I_snd_event A na = [send_C m. m \<leftarrow> A_I_snd_msg A na]"

definition "A_I_rcv_msg A na = (
    \<comment> \<open> Msg2 \<close>
    [(Intruder, A, {\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). nb \<leftarrow> removeAll na AllNonces
    ]
  )"

value "A_I_rcv_msg Alice (N Alice)"

definition "A_I_rcv_event A na = [recv_C m. m \<leftarrow> A_I_rcv_msg A na]"

definition "A_I_sig A na = [sig_C (ClaimSecret A nb (set [B])). 
  nb \<leftarrow> AllNonces, B \<leftarrow> removeAll A AllAgents]"

(*
definition "rename_A_I = \<lbrace>send x \<mapsto> hear x | x \<in> (set A_I_snd_msg). True\<rbrace> \<union> 
  \<lbrace>recv x \<mapsto> fake x | x \<in> (set A_I_rcv_msg). True\<rbrace>"

definition "rename_A_I' = [(send_C x, hear_C x). x \<leftarrow> (A_I_snd_msg)] @ 
                          [(recv_C x, fake_C x). x \<leftarrow> (A_I_rcv_msg)]"

definition "rename_sig = 
  [(sig_C (ClaimSecret a n {b}), sig_C (ClaimSecret a n {b})). 
    a \<leftarrow> AllAgents, n \<leftarrow> AllNonces, b \<leftarrow> AllAgents]@
  [(sig_C (StartProt a b na nb), sig_C (StartProt a b na nb)). 
    a \<leftarrow> AllAgents, b \<leftarrow> AllAgents, na \<leftarrow> AllNonces, nb \<leftarrow> AllNonces] @
  [(sig_C (EndProt a b na nb), sig_C (StartProt a b na nb)). 
    a \<leftarrow> AllAgents, b \<leftarrow> AllAgents, na \<leftarrow> AllNonces, nb \<leftarrow> AllNonces]"

definition "rename_A_I_nochanged = 
  [(env_C (Alice, x), env_C (Alice, x)). x \<leftarrow> removeAll Alice AllAgents] @ 
  rename_sig @
  [(terminate_C (), terminate_C ())]
"
*)

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"

subsubsection \<open> Bob \<close>
definition Responder :: "dagent \<Rightarrow> dnonce \<Rightarrow> (Chan, unit) itree" where
"Responder B nb = 
      do {
          \<comment> \<open> Receive Msg1 \<close>
          (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). 
            A \<leftarrow> removeAll B AllAgents, 
            na \<leftarrow> removeAll nb AllNonces]);
          let A = ma (mc2 (mem m)); na = mn (mc1 (mem m))
          in
            do {  
                  \<comment> \<open> Send a signal to claim nb is secret between A and B \<close>
                  outp sig (ClaimSecret B nb (set [A]));
                  outp sig (StartProt B A na nb);
                  \<comment> \<open> Send Msg2 \<close>
                  outp send (B, Intruder, {\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m}\<^bsub>PK A\<^esub> );
                  \<comment> \<open> Receive Msg3 \<close>
                  m3 \<leftarrow> inp_in recv (set [(Intruder, B, {(MNon nb)}\<^bsub>PK B\<^esub> )]);
                  outp sig (EndProt B A na nb);
                  outp terminate ()
            }
  }
"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "B_I_rcv_msg B nb = (let As = removeAll B AllAgents
  in
    \<comment> \<open> Msg1 \<close>
    [(Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). 
        A \<leftarrow> As, na \<leftarrow> removeAll nb AllNonces] @
    \<comment> \<open> Msg3 \<close>
    [(Intruder, B, {MNon nb}\<^bsub>PK B\<^esub> )]
  )"

value "B_I_rcv_msg Bob (N Bob)"

definition "B_I_rcv_event B nb = [recv_C m. m \<leftarrow> B_I_rcv_msg B nb]"

definition "B_I_snd_msg B nb = (let As = removeAll Bob AllAgents
  in
    \<comment> \<open> Msg2 \<close>
    [(B, Intruder, {\<lbrace>MNon na, MNon (N B)\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). 
      A \<leftarrow> As, na \<leftarrow> removeAll nb AllNonces
    ]
  )"

value "B_I_snd_msg Bob (N Bob)"
value "(B_I_rcv_msg Bob (N Bob) @ B_I_snd_msg Bob (N Bob))"

definition "B_I_snd_event B nb = [send_C m. m \<leftarrow> B_I_snd_msg B nb]"

definition "B_I_sig B nb = [sig_C (ClaimSecret B na (set [A])). 
  na \<leftarrow> AllNonces, A \<leftarrow> removeAll B AllAgents]"

subsubsection \<open> Intruder \<close>
text \<open> Ideally Intruder can hear all messages on network, but it is not executable.
  @{text "do { ABm \<leftarrow> inp_in hear {(A,B,m) | A B m. True};  Ret ((snd (snd ABm)) # knows)" } 
\<close>

text \<open> @{text "PIntruder I ni k sec "} \<close>
definition PIntruder0:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> (Chan, unit) itree" where
"PIntruder0 I ni k s = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (A, B, m) \<leftarrow> inp_in hear (set (A_I_snd_msg Alice (N Alice) @ B_I_snd_msg Bob (N Bob)));
            \<comment> \<open> Intruder can fake any message (it can infer) to the target \<close>
            Ret (True, breakm (List.insert m knows), sec)}
    \<box> do { inp_in fake (set [(A, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents, 
          m' \<leftarrow> (build\<^sub>n_1 (knows))]); Ret (True, knows, sec) }
    \<box> do { outp terminate (); Ret (False, knows, sec) }
    \<comment> \<open> If an agent claims n is secret and only knows to agent B, which is the intruder. We can remove 
      this nonce in the secret. \<close>
    \<box> do { c \<leftarrow> inp_in sig (set [(ClaimSecret A n (set [B])). A \<leftarrow> removeAll I AllAgents, 
              n \<leftarrow> removeAll ni AllNonces,  B \<leftarrow> AllAgents]);
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

value "PLeakOnlyOnce AllSecrets"

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "PIntruder1 I ni k s = ((PIntruder0 I ni k s) \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s) 
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "rename_leak = [(leak_C x, leak_C x). x \<leftarrow> AllSecrets]"

definition "rename_sig I ni = [(sig_C (ClaimSecret A n (set [B])), sig_C (ClaimSecret A n (set [B]))). 
              A \<leftarrow> removeAll I AllAgents, n \<leftarrow> removeAll ni AllNonces,  B \<leftarrow> AllAgents, 
              A \<noteq> B]"

definition "rename_I = [(hear_C x, send_C x). x \<leftarrow> (A_I_snd_msg Alice (N Alice) @ B_I_snd_msg Bob (N Bob))] @
  [(fake_C x, recv_C x). x \<leftarrow> (A_I_rcv_msg Alice (N Alice) @ B_I_rcv_msg Bob (N Bob))] @
  [(terminate_C (), terminate_C ())] @
  rename_leak @ rename_sig Intruder (N Intruder)"

definition "PIntruder = rename' (PIntruder1 Intruder (N Intruder) InitKnows AllSecrets) (set rename_I)"

subsubsection \<open> Composition \<close>

definition "rename2 = \<lbrace>recv x \<mapsto> fake x | x. True\<rbrace>"
term "(rename' (Initiator Alice (N Alice)) rename1)"
term "\<lbrace>hear x. fst x = Alice\<rbrace>"
term "\<lbrace>hear x \<in> {(Alice, Bob, MAg Alice)}. True\<rbrace>"

definition "PAlice = Initiator Alice (N Alice)"
definition "PBob = Responder Bob (N Bob)"
(*
definition NSPKP_Original where
"NSPKP_Original = 
  (
    PAlice
    \<parallel>\<^bsub> (set (A_I_snd_event Alice (N Alice)  @  A_I_rcv_event Alice (N Alice) 
            @ terminate_event @ A_I_sig Alice (N Alice))) \<^esub>
    PIntruder
  )
  \<parallel>\<^bsub> (set (B_I_snd_event Bob (N Bob) @ B_I_rcv_event Bob (N Bob) 
          @ terminate_event @ B_I_sig Bob (N Bob))) \<^esub>
  PBob
"
*)

definition "Events_A_B_I = 
  (set ((A_I_snd_event Alice (N Alice) 
      @ A_I_rcv_event Alice (N Alice) 
      @ A_I_sig Alice (N Alice)) 
      @ terminate_event 
      @ (B_I_snd_event Bob (N Bob) 
      @ B_I_rcv_event Bob (N Bob) 
      @ B_I_sig Bob (N Bob)))
)"

definition NSPK3 where
"NSPK3 = (PAlice \<parallel>\<^bsub> set terminate_event \<^esub> PBob)  \<parallel>\<^bsub> Events_A_B_I \<^esub>  PIntruder"

(* animate_sec NSPK3 *)

(*
Expected trace: 
  Feasible %Env [Alice] Bob; Sig ClaimSecret Alice (N Alice) (Set [ Bob ]); Send [Alice=>Intruder] {<N Alice, Alice>}_PK Bob; Recv [Bob<=Intruder] {<N Alice, Alice>}_PK Bob; Sig ClaimSecret Bob (N Bob) (Set [ Alice ]); Sig StartProt Bob Alice (N Alice) (N Bob); Send [Bob=>Intruder] {<N Alice, N Bob>}_PK Alice; Recv [Alice<=Intruder] {<N Alice, N Bob>}_PK Alice; Sig StartProt Alice Bob (N Alice) (N Bob); Send [Alice=>Intruder] {N Bob}_PK Bob; Sig EndProt Alice Bob (N Alice) (N Bob); Recv [Bob<=Intruder] {N Bob}_PK Bob; Sig EndProt Bob Alice (N Alice) (N Bob); Terminate%

Attack counterexample trace:
  Feasible %Env [Alice] Intruder; Sig ClaimSecret Alice (N Alice) (Set [ Intruder ]); Send [Alice=>Intruder] {<N Alice, Alice>}_PK Intruder; Recv [Bob<=Intruder] {<N Alice, Alice>}_PK Bob; Sig ClaimSecret Bob (N Bob) (Set [ Alice ]); Sig StartProt Bob Alice (N Alice) (N Bob); Send [Bob=>Intruder] {<N Alice, N Bob>}_PK Alice; Recv [Alice<=Intruder] {<N Alice, N Bob>}_PK Alice; Sig StartProt Alice Intruder (N Alice) (N Bob); Send [Alice=>Intruder] {N Bob}_PK Intruder; Leak N Bob%

Reachability:
  AReach 15 %Terminate%
  AReach 15 %Leak N Bob%
  RReach 15 %Leak N Bob%
  AReach 15 %Sig EndProt Bob Alice (N Alice) (N Bob)% # %Sig StartProt Alice Bob (N Alice) (N Bob)%
  AReach 15 %Sig EndProt Alice Bob (N Alice) (N Bob)% # %Sig StartProt Bob Alice (N Alice) (N Bob)%
*)

subsection \<open> Needham Schroeder Lowe  - Processes \<close>

subsubsection \<open> Alice \<close>

definition LInitiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> (Chan, unit) itree" where
"LInitiator A na = 
      do {
          \<comment> \<open> Receive environment's request to establish authentication with B \<close>
          (_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents, C \<noteq> A]);
          do {
                \<comment> \<open> Send a signal to claim na is secret between A and B \<close>
                outp sig (ClaimSecret A na (set [B]));
                \<comment> \<open> Send Msg1 \<close>
                outp send (A, Intruder, {\<lbrace>MNon (N A), MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> );
                \<comment> \<open> Receive Msg2, A expects an identity from B, not any agent. So A won't accept Bob if
                B is not Bob. \<close>
               (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, A, {\<lbrace>MNon na, MNon nb, MAg B\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). 
                  nb \<leftarrow> removeAll na AllNonces]);
                \<comment> \<open> (mn (mc2 m)) \<close>
                let nb = (mn (mc1 (mc2 (mem m))))
                in
                  do {
                    outp sig (StartProt A B na nb);
                    \<comment> \<open> Send Msg3 \<close>
                    outp send (A, Intruder, {MNon nb}\<^bsub>PK B\<^esub> );
                    outp sig (EndProt A B na nb);
                    outp terminate ()
                  }
          }
  }
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "LA_I_snd_msg A na = (let Bs = removeAll A AllAgents
  in
    \<comment> \<open> Msg1 \<close>
    [(A, Intruder, {\<lbrace>MNon (N A), MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). B \<leftarrow> Bs] @
      \<comment> \<open> Msg3 \<close>
    [(A, Intruder, {MNon nb}\<^bsub>PK B\<^esub> ). B \<leftarrow> Bs, nb \<leftarrow> removeAll na AllNonces]
  )"

value "LA_I_snd_msg Alice (N Alice)"

definition "LA_I_snd_event A na = [send_C m. m \<leftarrow> LA_I_snd_msg A na]"

definition "LA_I_rcv_msg A na = (
    \<comment> \<open> Msg2 \<close>
    [(Intruder, A, {\<lbrace>MNon na, MNon nb, MAg B\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). 
      nb \<leftarrow> removeAll na AllNonces, B \<leftarrow> removeAll A AllAgents
    ]
  )"

value "LA_I_rcv_msg Alice (N Alice)"

definition "LA_I_rcv_event A na = [recv_C m. m \<leftarrow> LA_I_rcv_msg A na]"

subsubsection \<open> Bob \<close>
definition LResponder :: "dagent \<Rightarrow> dnonce \<Rightarrow> (Chan, unit) itree" where
"LResponder B nb = 
      do {
          \<comment> \<open> Receive Msg1 \<close>
          (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). 
            A \<leftarrow> removeAll B AllAgents, 
            na \<leftarrow> removeAll nb AllNonces]);
          let A = ma (mc2 (mem m)); na = mn (mc1 (mem m))
          in
            do {  
                  \<comment> \<open> Send a signal to claim nb is secret between A and B \<close>
                  outp sig (ClaimSecret B nb (set [A]));
                  outp sig (StartProt B A na nb);
                  \<comment> \<open> Send Msg2 \<close>
                  outp send (B, Intruder, {\<lbrace>MNon na, MNon nb, MAg B\<rbrace>\<^sub>m}\<^bsub>PK A\<^esub> );
                  \<comment> \<open> Receive Msg3 \<close>
                  m3 \<leftarrow> inp_in recv (set [(Intruder, B, {(MNon nb)}\<^bsub>PK B\<^esub> )]);
                  outp sig (EndProt B A na nb);
                  outp terminate ()
            }
  }
"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "LB_I_rcv_msg B nb = (let As = removeAll B AllAgents
  in
    \<comment> \<open> Msg1 \<close>
    [(Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). 
        A \<leftarrow> As, na \<leftarrow> removeAll nb AllNonces] @
    \<comment> \<open> Msg3 \<close>
    [(Intruder, B, {MNon nb}\<^bsub>PK B\<^esub> )]
  )"

value "LB_I_rcv_msg Bob (N Bob)"

definition "LB_I_rcv_event B nb = [recv_C m. m \<leftarrow> LB_I_rcv_msg B nb]"

definition "LB_I_snd_msg B nb = (let As = removeAll Bob AllAgents
  in
    \<comment> \<open> Msg2 \<close>
    [(B, Intruder, {\<lbrace>MNon na, MNon (N B), MAg B\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). 
      A \<leftarrow> As, na \<leftarrow> removeAll nb AllNonces
    ]
  )"

value "LB_I_snd_msg Bob (N Bob)"
value "(LB_I_rcv_msg Bob (N Bob) @ LB_I_snd_msg Bob (N Bob))"

definition "LB_I_snd_event B nb = [send_C m. m \<leftarrow> LB_I_snd_msg B nb]"

subsubsection \<open> Intruder \<close>
text \<open> Ideally Intruder can hear all messages on network, but it is not executable.
  @{text "do { ABm \<leftarrow> inp_in hear {(A,B,m) | A B m. True};  Ret ((snd (snd ABm)) # knows)" } 
\<close>
text \<open> @{text "PIntruder I ni k sec "} \<close>
value "build\<^sub>n_2 InitKnows"
definition LPIntruder0:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> (Chan, unit) itree" where
"LPIntruder0 I ni k s = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (A, B, m) \<leftarrow> inp_in hear (set (LA_I_snd_msg Alice (N Alice) @ LB_I_snd_msg Bob (N Bob)));
            \<comment> \<open> Intruder can fake any message (it can infer) to the target \<close>
            \<^cancel>\<open> inp_in fake (set [(A, B, m'). m' \<leftarrow> (build\<^sub>n_1 (atom_msgs' (m # knows)))]); \<close>
            Ret (True, breakm (List.insert m knows), sec)}
    \<box> do { inp_in fake (set [(A, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents, 
          m' \<leftarrow> (build\<^sub>n_2 (knows))]); Ret (True, knows, sec) }
    \<box> do { outp terminate (); Ret (False, knows, sec) }
    \<comment> \<open> If an agent claims n is secret and only knows to agent B, which is the intruder. We can remove 
      this nonce in the secret. \<close>
    \<box> do { c \<leftarrow> inp_in sig (set [(ClaimSecret A n (set [B])). A \<leftarrow> removeAll I AllAgents, 
              n \<leftarrow> removeAll ni AllNonces,  B \<leftarrow> AllAgents]);
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

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "LPIntruder1 I ni k s = ((LPIntruder0 I ni k s) \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s) 
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "rename_I_L = [(hear_C x, send_C x). x \<leftarrow> (LA_I_snd_msg Alice (N Alice) @ LB_I_snd_msg Bob (N Bob))] @
  [(fake_C x, recv_C x). x \<leftarrow> (LA_I_rcv_msg Alice (N Alice) @ LB_I_rcv_msg Bob (N Bob))] @
  [(terminate_C (), terminate_C ())] @
  rename_leak @ rename_sig Intruder (N Intruder)"

value "rename_I_L"

definition "LPIntruder = rename' (LPIntruder1 Intruder (N Intruder) InitKnows AllSecrets) (set rename_I_L)"

subsubsection \<open> Composition \<close>
definition "LPAlice = LInitiator Alice (N Alice)"
definition "LPBob = LResponder Bob (N Bob)"

definition "LEvents_A_B_I = 
  (set ((LA_I_snd_event Alice (N Alice) 
      @ LA_I_rcv_event Alice (N Alice) 
      @ A_I_sig Alice (N Alice)) 
      @ terminate_event 
      @ (LB_I_snd_event Bob (N Bob) 
      @ LB_I_rcv_event Bob (N Bob) 
      @ B_I_sig Bob (N Bob)))
)"

definition NSPKP_Lowe where
"NSPKP_Lowe = (LPAlice \<parallel>\<^bsub> set terminate_event \<^esub> LPBob)  \<parallel>\<^bsub> LEvents_A_B_I \<^esub>  LPIntruder"

animate_sec NSPKP_Lowe

end
