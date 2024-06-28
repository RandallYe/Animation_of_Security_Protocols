section \<open> Animation of NSPKP (7-message version) including the original version \<close>
theory NSPK7
  imports "NSPK7_message"
          "ITree_Simulation.ITree_Simulation"
          "NSPK7_animation"
begin

text \<open> Needham Schroeder Public Key Protocol: seven-message version
The protocol runs as follows:
\begin{enumerate}
    \item  A \<rightarrow> S: (A, B)  : {S knows the  pk(A)  and  pk(B) }
    \item   S \<rightarrow> A: < (pk(B), B) >^s_{sk(S)}  : S signs the message and {\clz assume A and B know  pk(S) }
    \item   A \<rightarrow> B: < (na, A) >{pk(B)}
    \item   B \<rightarrow> S: (B, A)
    \item   S \<rightarrow> B: < (pk(A), A)>^s_{sk(S)}  : S signs the message
    \item   B \<rightarrow> A: < (na, nb) >_{pk(A)}
    \item   A \<rightarrow> B: < nb >_{pk(B)}
 \end{enumerate}
\<close>

subsection \<open> General definitions \<close>
definition "AllSecrets = removeAll (MNon (N Intruder)) AllNoncesLst"

definition InitKnows :: "dmsg list" where 
"InitKnows = AllAgentsLst @ [MNon (N Intruder), MKs (SK Intruder)]"

value "InitKnows"

value "let ret = (let ns = InitKnows in build\<^sub>n ns (extract_dpkey ns) (extract_dskey ns) 1 1 3)
  in (size (ret), ret)"

subsection \<open>  Needham Schroeder original - Processes \<close>
subsubsection \<open> Alice \<close>

definition Initiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> (Chan, unit) itree" where
"Initiator A na = 
      do {
          \<comment> \<open> Receive environment's request to establish authentication with B \<close>
          (_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents, C \<noteq> A, C \<noteq> Server]);
          do {
              \<comment> \<open> Send Msg1 \<close>
              outp send\<^sub>s (A, Server, \<lbrace>MAg A, MAg B\<rbrace>\<^sub>m);
              \<comment> \<open> Receive Msg2 \<close>
              (_, _, m) \<leftarrow> inp_in recv\<^sub>s (set [(Server, A, {\<lbrace>pk, MAg B\<rbrace>\<^sub>m }\<^sub>d\<^bsub>SK Server\<^esub> ). 
                  pk \<leftarrow> AllPKsLst]);
              let pkb = (mkp (mc1 (msd m)))
              in 
                do {
                  \<comment> \<open> Send a signal to claim na is secret between A and B \<close>
                  outp sig (ClaimSecret A na (set [B]));
                  \<comment> \<open> Send Msg3 \<close>
                  outp send (A, Intruder, {\<lbrace>MNon (N A), MAg A\<rbrace>\<^sub>m}\<^bsub>pkb\<^esub> );
                  \<comment> \<open> Receive Msg6 \<close>
                 (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, A, {\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). 
                    nb \<leftarrow> removeAll na AllNonces, nb \<noteq> N Server]);
                  \<comment> \<open> (mn (mc2 m)) \<close>
                  let nb = (mn (mc2 (mem m))) 
                  in
                    do {
                      outp sig (StartProt A B na nb);
                      \<comment> \<open> Send Msg7 \<close>
                      outp send (A, Intruder, {MNon nb}\<^bsub>pkb\<^esub> );
                      outp sig (EndProt A B na nb);
                      outp terminate ()
                    }
                }
          }
  }
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "A_I_snd_msg A na = (let Bs = (filter (\<lambda>a. a \<noteq> A \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg1 \<close>
    [(A, Intruder, {\<lbrace>MNon (N A), MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). B \<leftarrow> Bs] @
      \<comment> \<open> Msg3 \<close>
    [(A, Intruder, {MNon nb}\<^bsub>PK B\<^esub> ). B \<leftarrow> Bs, 
      nb \<leftarrow> (filter (\<lambda>a. a \<noteq> na \<and> a \<noteq> N Server) AllNonces)]
  )"

value "A_I_snd_msg Alice (N Alice)"

definition "A_I_snd_event A na = [send_C m. m \<leftarrow> A_I_snd_msg A na]"

definition "A_I_rcv_msg A na = (
    \<comment> \<open> Msg2 \<close>
    [(Intruder, A, {\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). 
      nb \<leftarrow> (filter (\<lambda>a. a \<noteq> na \<and> a \<noteq> N Server) AllNonces)]
  )"

value "A_I_rcv_msg Alice (N Alice)"

definition "A_I_rcv_event A na = [recv_C m. m \<leftarrow> A_I_rcv_msg A na]"

definition "A_I_sig A na = [sig_C (ClaimSecret A nb (set [B])). 
  nb \<leftarrow> removeAll (N Server) AllNonces, 
  B \<leftarrow> (filter (\<lambda>a. a \<noteq> A \<and> a \<noteq> Server) AllAgents)]"

value "A_I_sig Alice (N Alice)"

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"

definition "A_I_snd_msg_sec A = (let Bs = (filter (\<lambda>a. a \<noteq> A \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg1 \<close>
    [(A, Server, \<lbrace>MAg A, MAg B\<rbrace>\<^sub>m). B \<leftarrow> Bs]
  )"

value "A_I_snd_msg_sec Alice"

definition "A_I_snd_event_sec A = [send\<^sub>s_C m. m \<leftarrow> A_I_snd_msg_sec A]"

definition "A_I_rcv_msg_sec A = (let Bs = (filter (\<lambda>a. a \<noteq> A \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg2 \<close>
    [(Server, A, {\<lbrace>pk, MAg B\<rbrace>\<^sub>m }\<^sub>d\<^bsub>SK Server\<^esub> ). B \<leftarrow> Bs, pk \<leftarrow> AllPKsLst]
  )"

value "A_I_rcv_msg_sec Alice"

definition "A_I_rcv_event_sec A = [recv\<^sub>s_C m. m \<leftarrow> A_I_rcv_msg_sec A]"
 
subsubsection \<open> Bob \<close>
definition Responder :: "dagent \<Rightarrow> dnonce \<Rightarrow> (Chan, unit) itree" where
"Responder B nb = 
      do {
          \<comment> \<open> Receive Msg1 \<close>
          (_, _, m) \<leftarrow> inp_in recv (set [(Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). 
            A \<leftarrow> removeAll B AllAgents, A \<noteq> Server,
            na \<leftarrow> removeAll nb AllNonces, na \<noteq> N Server]);
          let A = ma (mc2 (mem m)); na = mn (mc1 (mem m))
          in
            do {  
              \<comment> \<open> Send Msg3 \<close>
              outp send\<^sub>s (B, Server, \<lbrace>MAg B, MAg A\<rbrace>\<^sub>m);
              \<comment> \<open> Receive Msg4 \<close>
              (_, _, m) \<leftarrow> inp_in recv\<^sub>s (set [(Server, B, {\<lbrace>pka, MAg A\<rbrace>\<^sub>m }\<^sub>d\<^bsub>SK Server\<^esub> ). 
                  pka \<leftarrow> AllPKsLst]);
              let pka = (mkp (mc1 (msd m)))
              in 
                do {
                \<comment> \<open> Send a signal to claim nb is secret between A and B \<close>
                outp sig (ClaimSecret B nb (set [A]));
                outp sig (StartProt B A na nb);
                \<comment> \<open> Send Msg6 \<close>
                outp send (B, Intruder, {\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m}\<^bsub>pka\<^esub> );
                \<comment> \<open> Receive Msg7 \<close>
                m3 \<leftarrow> inp_in recv (set [(Intruder, B, {(MNon nb)}\<^bsub>PK B\<^esub> )]);
                outp sig (EndProt B A na nb);
                outp terminate ()
            }
       }
  }
"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition "B_I_rcv_msg B nb = (let As = (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg1 \<close>
    [(Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^bsub>PK B\<^esub> ). 
        A \<leftarrow> As, na \<leftarrow> (filter (\<lambda>a. a \<noteq> nb \<and> a \<noteq> N Server) AllNonces)] @
    \<comment> \<open> Msg3 \<close>
    [(Intruder, B, {MNon nb}\<^bsub>PK B\<^esub> )]
  )"

value "B_I_rcv_msg Bob (N Bob)"

definition "B_I_rcv_event B nb = [recv_C m. m \<leftarrow> B_I_rcv_msg B nb]"

definition "B_I_snd_msg B nb = (let As = (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg2 \<close>
    [(B, Intruder, {\<lbrace>MNon na, MNon (N B)\<rbrace>\<^sub>m }\<^bsub>PK A\<^esub> ). 
      A \<leftarrow> As, na \<leftarrow> (filter (\<lambda>a. a \<noteq> nb \<and> a \<noteq> N Server) AllNonces)
    ]
  )"

value "B_I_snd_msg Bob (N Bob)"
value "(B_I_rcv_msg Bob (N Bob) @ B_I_snd_msg Bob (N Bob))"

definition "B_I_snd_event B nb = [send_C m. m \<leftarrow> B_I_snd_msg B nb]"

definition "B_I_sig B nb = [sig_C (ClaimSecret B na (set [A])). 
  na \<leftarrow> removeAll (N Server) AllNonces,  
  A \<leftarrow> (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)]"

value "B_I_sig Bob (N Bob)"

definition "B_I_snd_msg_sec B = (let As = (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg3 \<close>
    [(B, Server, \<lbrace>MAg B, MAg A\<rbrace>\<^sub>m). A \<leftarrow> As]
  )"

value "B_I_snd_msg_sec Bob"

definition "B_I_snd_event_sec B = [send\<^sub>s_C m. m \<leftarrow> B_I_snd_msg_sec B]"

definition "B_I_rcv_msg_sec B = (let As = (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg4 \<close>
    [(Server, B, {\<lbrace>pk, MAg A\<rbrace>\<^sub>m }\<^sub>d\<^bsub>SK Server\<^esub> ). A \<leftarrow> As, pk \<leftarrow> AllPKsLst]
  )"

value "B_I_rcv_msg_sec Bob"

definition "B_I_rcv_event_sec B = [recv\<^sub>s_C m. m \<leftarrow> B_I_rcv_msg_sec B]"

subsubsection \<open> Intruder \<close>
text \<open> Ideally Intruder can hear all messages on network, but it is not executable.
  @{text "do { ABm \<leftarrow> inp_in hear {(A,B,m) | A B m. True};  Ret ((snd (snd ABm)) # knows)" } 
\<close>

definition "get_PK_agents I A knows = do {
  outp send\<^sub>s (I, Server, \<lbrace>MAg I, MAg A\<rbrace>\<^sub>m);
  (_, _, m) \<leftarrow> inp_in recv\<^sub>s (set [(Server, I, {\<lbrace>pk, MAg A\<rbrace>\<^sub>m }\<^sub>d\<^bsub>SK Server\<^esub> ). 
      pk \<leftarrow> AllPKsLst]);
  Ret (List.insert (MKp (mkp (mc1 (msd m)))) knows)
}"

abbreviation "agents_not_I_S I \<equiv> (filter (\<lambda>a. a \<noteq> I \<and> a \<noteq> Server) AllAgents)"
definition "get_pk_agents I = ;\<^bsub>agents_not_I_S I\<^esub> @ get_PK_agents I"

value "get_pk_agents Intruder InitKnows"
value "(build\<^sub>n_1 (atom_msgs' (InitKnows)))"

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
              m' \<leftarrow> (build\<^sub>n_1 (knows))]); 
            Ret (True, knows, sec) }
    \<box> do { outp terminate (); Ret (False, knows, sec) }
    \<comment> \<open> If an agent claims n is secret and only knows to agent B, which is the intruder. We can remove 
      this nonce in the secret. \<close>
    \<box> do { c \<leftarrow> inp_in sig (set [(ClaimSecret A n (set [B])). 
              A \<leftarrow> (filter (\<lambda>a. a \<noteq> I \<and> a \<noteq> Server) AllAgents), 
              n \<leftarrow> (filter (\<lambda>a. a \<noteq> ni \<and> a \<noteq> N Server) AllNonces),  
              B \<leftarrow> removeAll Server AllAgents]);
              (if I \<in> (sp c) 
               then Ret (True, knows, (removeAll (MNon (sn c)) sec)) 
               else Ret (True, knows, sec))
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

value "build\<^sub>n_1 (atom_msgs' (InitKnows))"

definition "PLeakOnlyOnce secrects = \<interleave>\<^bsub>secrects\<^esub> @ (\<lambda>s. do {outp leak s})"

value "PLeakOnlyOnce AllSecrets"

term "get_pk_agents Intruder k"
definition "PIntruder1 I ni k s = do {
  knows \<leftarrow> get_pk_agents I k; 
  (PIntruder0 I ni knows s)
}"

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "PIntruder2 I ni k s = (
  (PIntruder1 I ni k s) 
  \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s)
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "rename_leak = [(leak_C x, leak_C x). x \<leftarrow> AllSecrets]"

definition "rename_sig I ni = [(sig_C (ClaimSecret A n (set [B])), sig_C (ClaimSecret A n (set [B]))). 
              A \<leftarrow> removeAll I AllAgents, n \<leftarrow> removeAll ni AllNonces,  B \<leftarrow> AllAgents, 
              A \<noteq> B, A \<noteq> Server, B \<noteq> Server]"

definition "I_snd_msg_sec I = (let Bs = (filter (\<lambda>a. a \<noteq> I \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg1 \<close>
    [(I, Server, \<lbrace>MAg I, MAg B\<rbrace>\<^sub>m). B \<leftarrow> Bs]
  )"


definition "I_snd_event_sec I = [send\<^sub>s_C m. m \<leftarrow> I_snd_msg_sec I]"

definition "I_rcv_msg_sec I = (let Bs = (filter (\<lambda>a. a \<noteq> I \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg2 \<close>
    [(Server, I, {\<lbrace>pk, MAg B\<rbrace>\<^sub>m }\<^sub>d\<^bsub>SK Server\<^esub> ). B \<leftarrow> Bs, pk \<leftarrow> AllPKsLst]
  )"

definition "I_rcv_event_sec I = [recv\<^sub>s_C m. m \<leftarrow> I_rcv_msg_sec I]"

definition "rename_I = 
  [(hear_C x, send_C x). x \<leftarrow> (A_I_snd_msg Alice (N Alice) @ B_I_snd_msg Bob (N Bob))] @
  [(fake_C x, recv_C x). x \<leftarrow> (A_I_rcv_msg Alice (N Alice) @ B_I_rcv_msg Bob (N Bob))] @
  [(terminate_C (), terminate_C ())] @
  rename_leak @ rename_sig Intruder (N Intruder) @
  [(send\<^sub>s_C x, send\<^sub>s_C x). x \<leftarrow> I_snd_msg_sec Intruder] @
  [(recv\<^sub>s_C x, recv\<^sub>s_C x). x \<leftarrow> I_rcv_msg_sec Intruder]"

value "rename_I"

definition "c = (PIntruder2 Intruder (N Intruder) InitKnows AllSecrets)"
definition "PIntruder = rename' (PIntruder2 Intruder (N Intruder) InitKnows AllSecrets) (set rename_I)"

(* animate_sec "PIntruder" *)

subsubsection \<open> Server \<close>

definition PServer0 :: "(Chan, unit) itree" where
"PServer0 = ITree_Iteration.iter (
    do {
      \<comment> \<open> Receive Msg1 or Msg4 \<close>
      (A, _, m) \<leftarrow> inp_in recv\<^sub>s (set [(A, Server, \<lbrace>MAg A, MAg B\<rbrace>\<^sub>m). 
          A \<leftarrow> removeAll Server AllAgents, B \<leftarrow> removeAll Server AllAgents, B \<noteq> A]);
      let B = ma (mc2 m)
      in 
        do {
            \<comment> \<open> Send Msg2 or Msg5 \<close>
            outp send\<^sub>s (Server, A, {\<lbrace>MKp (PK B), MAg B\<rbrace>\<^sub>m}\<^sub>d\<^bsub>SK Server\<^esub> )
        }
  })
"

definition PServer1 where 
"PServer1 = PServer0 \<triangle> (do { outp terminate ()} )"

definition "rename_Server = 
  [(recv\<^sub>s_C x, send\<^sub>s_C x). x \<leftarrow> (A_I_snd_msg_sec Alice @ B_I_snd_msg_sec Bob @ I_snd_msg_sec Intruder)] @
  [(send\<^sub>s_C x, recv\<^sub>s_C x). x \<leftarrow> (A_I_rcv_msg_sec Alice @ B_I_rcv_msg_sec Bob @ I_rcv_msg_sec Intruder)] @
  [(terminate_C (), terminate_C ())]"

definition "PServer = rename' (PServer1) (set rename_Server)"

subsubsection \<open> Composition \<close>

definition "PAlice = Initiator Alice (N Alice)"
definition "PBob = Responder Bob (N Bob)"

definition "Events_A_B_S = (set ((A_I_snd_event_sec Alice @ A_I_rcv_event_sec Alice 
            @ terminate_event @ B_I_snd_event_sec Bob @ B_I_rcv_event_sec Bob)))"
definition "Events_A_B_S_I = (set (
  (A_I_snd_event Alice (N Alice) @ A_I_rcv_event Alice (N Alice) @ A_I_sig Alice (N Alice)) @ 
  (B_I_snd_event Bob (N Bob) @ B_I_rcv_event Bob (N Bob) @ B_I_sig Bob (N Bob)) @ 
  terminate_event @ I_snd_event_sec Intruder @ I_rcv_event_sec Intruder))"
value "Events_A_B_S_I"

definition NSPK7 where
"NSPK7 = 
    ((PAlice \<parallel>\<^bsub> set terminate_event \<^esub> PBob) \<parallel>\<^bsub> Events_A_B_S \<^esub> PServer) 
    \<parallel>\<^bsub> Events_A_B_S_I \<^esub> PIntruder"

animate_sec NSPK7

end