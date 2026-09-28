section \<open> Animation of NSPKP (7-message version) including the original version \<close>
theory NSPK7
  imports "ITree_Simulation.ITree_Simulation" 
          "ITree_Security.Sec_Animation"
          "NSPK7_config"
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

subsection \<open>  Needham Schroeder original - Processes \<close>
subsubsection \<open> Alice \<close>

definition Initiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan, unit) itree" where
"Initiator A na = 
      do {
          \<comment> \<open> Receive environment's request to establish authentication with B \<close>
          (_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents, C \<noteq> A, C \<noteq> Server]);
          do {
              \<comment> \<open> Send Msg1 \<close>
              send_privately A Server (\<lbrace>MAg A, MAg B\<rbrace>\<^sub>m);
              \<comment> \<open> Receive Msg2 \<close>
              (_, _, _, m) \<leftarrow> recv_privately Server A [{\<lbrace>pk, MAg B\<rbrace>\<^sub>m }\<^sup>d\<^bsub>MK (SKeyMap Server)\<^esub> . pk \<leftarrow> AllPKsLst];
              let pkb = mc1 (msd m)
              in 
                do {
                  \<comment> \<open> Send a signal to claim na is secret between A and B \<close>
                  outp sig (ClaimSecret A na (set [B]));
                  \<comment> \<open> Send Msg3 \<close>
                  send_to_network A B ({\<lbrace>MNon (NonceMap A), MAg A\<rbrace>\<^sub>m}\<^sup>a\<^bsub>pkb\<^esub> );
                  \<comment> \<open> Receive Msg6 \<close>
                 (_, _, _, m) \<leftarrow> recv_from_network A [{\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m }\<^sup>a\<^bsub>MK (pks A)\<^esub> . 
                    nb \<leftarrow> removeAll na AllNonces, nb \<noteq> NonceMap Server];
                  \<comment> \<open> (mn (mc2 m)) \<close>
                  let nb = (mn (mc2 (mem m))) 
                  in
                    do {
                      outp sig (StartProt A B na nb);
                      \<comment> \<open> Send Msg7 \<close>
                      send_to_network A B ({MNon nb}\<^sup>a\<^bsub>pkb\<^esub> );
                      outp sig (EndProt A B na nb);
                      outp terminate ()
                    }
                }
          }
  }
"

\<comment> \<open> send (Alice, B, m) \<Rightarrow> hear (Alice, B, m)\<close>
text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition A_I_snd_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"A_I_snd_msg A na = (let Bs = (filter (\<lambda>a. a \<noteq> A \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg3 \<close>
    [(A, Intruder, B, {\<lbrace>MNon (NonceMap A), MAg A\<rbrace>\<^sub>m}\<^sup>a\<^bsub>MK (pks B)\<^esub> ). B \<leftarrow> Bs] @
    \<comment> \<open> Msg7 \<close>
    [(A, Intruder, B, {MNon nb}\<^sup>a\<^bsub>MK (pks B)\<^esub> ). B \<leftarrow> Bs, 
      nb \<leftarrow> (filter (\<lambda>a. a \<noteq> na \<and> a \<noteq> NonceMap Server) AllNonces)]
  )"

value "A_I_snd_msg Alice (NonceMap Alice)"

definition A_I_snd_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"A_I_snd_event A na = [send_C m. m \<leftarrow> A_I_snd_msg A na]"

definition A_I_rcv_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"A_I_rcv_msg A na = (
    \<comment> \<open> Msg6 \<close>
    [(Intruder, Intruder, A, {\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m }\<^sup>a\<^bsub>MK (pks A)\<^esub> ). 
      nb \<leftarrow> (filter (\<lambda>a. a \<noteq> na \<and> a \<noteq> NonceMap Server) AllNonces)]
  )"

value "A_I_rcv_msg Alice (NonceMap Alice)"

definition A_I_rcv_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"A_I_rcv_event A na = [recv_C m. m \<leftarrow> A_I_rcv_msg A na]"

definition A_I_sig :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"A_I_sig A na = [sig_C (ClaimSecret A nb (set [B])). 
  nb \<leftarrow> removeAll (NonceMap Server) AllNonces, 
  B \<leftarrow> (filter (\<lambda>a. a \<noteq> A \<and> a \<noteq> Server) AllAgents)]"

value "A_I_sig Alice (NonceMap Alice)"

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"

definition A_I_snd_msg_sec :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"A_I_snd_msg_sec A = (let Bs = (filter (\<lambda>a. a \<noteq> A \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg1 \<close>
    [(A, A, Server, \<lbrace>MAg A, MAg B\<rbrace>\<^sub>m). B \<leftarrow> Bs]
  )"

value "A_I_snd_msg_sec Alice"

definition A_I_snd_event_sec :: "dagent \<Rightarrow> chan list" where
"A_I_snd_event_sec A = [send_C m. m \<leftarrow> A_I_snd_msg_sec A]"

definition A_I_rcv_msg_sec :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"A_I_rcv_msg_sec A = (let Bs = (filter (\<lambda>a. a \<noteq> A \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg2 \<close>
    [(Server, Server, A, {\<lbrace>pk, MAg B\<rbrace>\<^sub>m }\<^sup>d\<^bsub>MK (SKeyMap Server)\<^esub> ). B \<leftarrow> Bs, pk \<leftarrow> AllPKsLst]
  )"

value "A_I_rcv_msg_sec Alice"

definition A_I_rcv_event_sec :: "dagent \<Rightarrow> chan list" where
"A_I_rcv_event_sec A = [recv_C m. m \<leftarrow> A_I_rcv_msg_sec A]"
 
subsubsection \<open> Bob \<close>
definition Responder :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan, unit) itree" where
"Responder B nb = 
      do {
          \<comment> \<open> Receive Msg1 \<close>
          (_, _, _, m) \<leftarrow> recv_from_network B [{\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^sup>a\<^bsub>MK (pks B)\<^esub> . 
            A \<leftarrow> removeAll B AllAgents, A \<noteq> Server,  
            na \<leftarrow> removeAll nb AllNonces, na \<noteq> NonceMap Server];
          let A = ma (mc2 (mem m)); na = mn (mc1 (mem m))
          in
            do {  
              \<comment> \<open> Send Msg3 \<close>
              send_privately B Server (\<lbrace>MAg B, MAg A\<rbrace>\<^sub>m);
              \<comment> \<open> Receive Msg4 \<close>
              (_, _, _, m) \<leftarrow> recv_privately Server B [{\<lbrace>pka, MAg A\<rbrace>\<^sub>m }\<^sup>d\<^bsub>MSK Server\<^esub> . 
                  pka \<leftarrow> AllPKsLst];
              let pka = (mc1 (msd m))
              in 
                do {
                \<comment> \<open> Send a signal to claim nb is secret between A and B \<close>
                outp sig (ClaimSecret B nb (set [A]));
                outp sig (StartProt B A na nb);
                \<comment> \<open> Send Msg6 \<close>
                send_to_network B A ({\<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m}\<^sup>a\<^bsub>pka\<^esub> );
                \<comment> \<open> Receive Msg7 \<close>
                m3 \<leftarrow> recv_from_network B [{(MNon nb)}\<^sup>a\<^bsub>MPK B\<^esub> ];
                outp sig (EndProt B A na nb);
                outp terminate ()
            }
       }
  }
"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition B_I_rcv_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"B_I_rcv_msg B nb = (let As = (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg1 \<close>
    [(Intruder, Intruder, B, {\<lbrace>MNon na, MAg A\<rbrace>\<^sub>m}\<^sup>a\<^bsub>MPK B\<^esub> ). 
        A \<leftarrow> As, na \<leftarrow> (filter (\<lambda>a. a \<noteq> nb \<and> a \<noteq> NonceMap Server) AllNonces)] @
    \<comment> \<open> Msg3 \<close>
    [(Intruder, Intruder, B, {MNon nb}\<^sup>a\<^bsub>MPK B\<^esub> )]
  )"

value "B_I_rcv_msg Bob (NonceMap Bob)"

definition B_I_rcv_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"B_I_rcv_event B nb = [recv_C m. m \<leftarrow> B_I_rcv_msg B nb]"

definition B_I_snd_msg :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"B_I_snd_msg B nb = (let As = (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg2 \<close>
    [(B, Intruder, A, {\<lbrace>MNon na, MNon (nb)\<rbrace>\<^sub>m }\<^sup>a\<^bsub>MPK A\<^esub> ). 
      A \<leftarrow> As, na \<leftarrow> (filter (\<lambda>a. a \<noteq> nb \<and> a \<noteq> NonceMap Server) AllNonces)
    ]
  )"

value "B_I_snd_msg Bob (NonceMap Bob)"
value "(B_I_rcv_msg Bob (NonceMap Bob) @ B_I_snd_msg Bob (NonceMap Bob))"

definition B_I_snd_event :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"B_I_snd_event B nb = [send_C m. m \<leftarrow> B_I_snd_msg B nb]"

definition B_I_sig :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"B_I_sig B nb = [sig_C (ClaimSecret B na (set [A])). 
  na \<leftarrow> removeAll (NonceMap Server) AllNonces,  
  A \<leftarrow> (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)]"

value "B_I_sig Bob (NonceMap Bob)"

definition B_I_snd_msg_sec :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"B_I_snd_msg_sec B = (let As = (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg3 \<close>
    [(B, B, Server, \<lbrace>MAg B, MAg A\<rbrace>\<^sub>m). A \<leftarrow> As]
  )"

value "B_I_snd_msg_sec Bob"

definition B_I_snd_event_sec :: "dagent \<Rightarrow> chan list" where
"B_I_snd_event_sec B = [send_C m. m \<leftarrow> B_I_snd_msg_sec B]"

definition B_I_rcv_msg_sec :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"B_I_rcv_msg_sec B = (let As = (filter (\<lambda>a. a \<noteq> B \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg4 \<close>
    [(Server, Server, B, {\<lbrace>pk, MAg A\<rbrace>\<^sub>m }\<^sup>d\<^bsub>MSK Server\<^esub> ). A \<leftarrow> As, pk \<leftarrow> AllPKsLst]
  )"

value "B_I_rcv_msg_sec Bob"

definition B_I_rcv_event_sec :: "dagent \<Rightarrow> chan list" where
"B_I_rcv_event_sec B = [recv_C m. m \<leftarrow> B_I_rcv_msg_sec B]"

subsubsection \<open> Intruder \<close>

definition "AllPossibleMsgsRecvByAgents = map last4 (A_I_rcv_msg Alice (NonceMap Alice) @ B_I_rcv_msg Bob (NonceMap Bob))"

value "AllPossibleMsgsRecvByAgents"

text \<open> Intruder might be an agent and also know Server's public keys, 
  and retrieve Alice's and Bob's public keys from the Server. \<close>
definition "get_PK_agents I A knows = do {
  send_privately I Server (\<lbrace>MAg I, MAg A\<rbrace>\<^sub>m);
  (_, _, _, m) \<leftarrow> recv_privately Server I [{\<lbrace>pk, MAg A\<rbrace>\<^sub>m }\<^sup>d\<^bsub>MSK Server\<^esub> . pk \<leftarrow> AllPKsLst];
  Ret (List.insert (mc1 (msd m)) knows)
}"

abbreviation "agents_not_I_S I \<equiv> (filter (\<lambda>a. a \<noteq> I \<and> a \<noteq> Server) AllAgents)"

text \<open> This is an indexed sequential composition \<close>
definition "get_pk_agents I = ;\<^bsub>agents_not_I_S I\<^esub> @ get_PK_agents I"

value "get_pk_agents Intruder InitKnows"

text \<open> @{text "PIntruder I ni k sec "} \<close>
definition PIntruder0:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> (chan, unit) itree" where
"PIntruder0 I ni k s = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (A, I, B, m) \<leftarrow> inp_in hear (set (A_I_snd_msg Alice (NonceMap Alice) @ B_I_snd_msg Bob (NonceMap Bob)));
            Ret (True, breakl (List.insert m knows), sec)
       }
    \<box> \<^cancel>\<open>do { inp_in fake (set [(A, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents, B \<noteq> Server, 
              m' \<leftarrow> (build\<^sub>n_1 (knows))]); 
            Ret (True, knows, sec) }\<close>
      do {  
            inp_in fake (set [(A, I, B, m'). A \<leftarrow> [I], B \<leftarrow> removeAll I AllAgents', 
                m' \<leftarrow> (filter_buildable AllPossibleMsgsRecvByAgents (set knows))]); 
            Ret (True, knows, sec) 
      }
    \<box> do { outp terminate (); Ret (False, knows, sec) }
    \<comment> \<open> If an agent claims n is secret and only knows to agent B, which is the intruder. We can remove 
      this nonce in the secret. \<close>
    \<box> do { c \<leftarrow> inp_in sig (set [(ClaimSecret A n (set [B])). 
              A \<leftarrow> (filter (\<lambda>a. a \<noteq> I \<and> a \<noteq> Server) AllAgents), 
              n \<leftarrow> (filter (\<lambda>a. a \<noteq> ni \<and> a \<noteq> NonceMap Server) AllNonces),  
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

definition PLeakOnlyOnce :: "dmsg list \<Rightarrow> (chan, unit) itree"
where "PLeakOnlyOnce secrects = \<interleave>\<^bsub>secrects\<^esub> @ (\<lambda>s. do {outp leak s})"

value "PLeakOnlyOnce AllSecrets"

text \<open> Initially, the intruder retrieves agents' public keys from Server. \<close>
definition "PIntruder1 I ni k s = do {
  knows \<leftarrow> get_pk_agents I k; 
  (PIntruder0 I ni knows s)
}"

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "PIntruder2 I ni k s = ((PIntruder1 I ni k s) \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s)
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "rename_leak = [(leak_C x, leak_C x). x \<leftarrow> AllSecrets]"

definition rename_sig :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan \<times> chan) list"
  where "rename_sig I ni = [(sig_C (ClaimSecret A n (set [B])), sig_C (ClaimSecret A n (set [B]))). 
              A \<leftarrow> removeAll I AllAgents, n \<leftarrow> removeAll ni AllNonces,  B \<leftarrow> AllAgents, 
              A \<noteq> B, A \<noteq> Server, B \<noteq> Server]"

definition I_snd_msg_sec :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
 "I_snd_msg_sec I = (let Bs = (filter (\<lambda>a. a \<noteq> I \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg1 \<close>
    [(I, I, Server, \<lbrace>MAg I, MAg B\<rbrace>\<^sub>m). B \<leftarrow> Bs]
  )"


definition I_snd_event_sec :: "dagent \<Rightarrow> chan list" where
"I_snd_event_sec I = [send_C m. m \<leftarrow> I_snd_msg_sec I]"

definition I_rcv_msg_sec :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"I_rcv_msg_sec I = (let Bs = (filter (\<lambda>a. a \<noteq> I \<and> a \<noteq> Server) AllAgents)
  in
    \<comment> \<open> Msg2 \<close>
    [(Server, Server, I, {\<lbrace>pk, MAg B\<rbrace>\<^sub>m }\<^sup>d\<^bsub>MSK Server\<^esub> ). B \<leftarrow> Bs, pk \<leftarrow> AllPKsLst]
  )"

definition I_rcv_event_sec :: "dagent \<Rightarrow> chan list" where
"I_rcv_event_sec I = [recv_C m. m \<leftarrow> I_rcv_msg_sec I]"

definition "rename_I = 
  [(send_C x, send_C x). x \<leftarrow> (A_I_snd_msg Alice (NonceMap Alice) @ B_I_snd_msg Bob (NonceMap Bob))] @
  [(recv_C x, recv_C x). x \<leftarrow> (A_I_rcv_msg Alice (NonceMap Alice) @ B_I_rcv_msg Bob (NonceMap Bob))] @
  [(terminate_C (), terminate_C ())] @
  rename_leak @ rename_sig Intruder (NonceMap Intruder) @
  [(send_C x, send_C x). x \<leftarrow> I_snd_msg_sec Intruder] @
  [(recv_C x, recv_C x). x \<leftarrow> I_rcv_msg_sec Intruder]"

value "rename_I"

definition "PIntruder = rename' (PIntruder2 Intruder (NonceMap Intruder) InitKnows AllSecrets) (set rename_I)"

(* animate_sec "PIntruder" *)

subsubsection \<open> Server \<close>
text \<open> Now ITree_Iteration.iter is different from the previous one and we use the previous one.
So we redefine it here. \<close>
abbreviation iter :: "('a, unit) itree \<Rightarrow> ('a, unit) itree" where
"iter PP \<equiv> ITree_Iteration.loop (\<lambda> _. PP) ()"

definition PServer0 :: "(chan, unit) itree" where
"PServer0 = iter (
    do {
      \<comment> \<open> Receive Msg1 or Msg4 \<close>
      (A, A, _, m) \<leftarrow> inp_in recv (set [(A, A, Server, \<lbrace>MAg A, MAg B\<rbrace>\<^sub>m). 
          A \<leftarrow> removeAll Server AllAgents, B \<leftarrow> removeAll Server AllAgents, B \<noteq> A]);
      let B = ma (mc2 m)
      in 
        do {
            \<comment> \<open> Send Msg2 or Msg5 \<close>
            send_privately Server A ({\<lbrace>MPK B, MAg B\<rbrace>\<^sub>m}\<^sup>d\<^bsub>MSK Server\<^esub> )
        }
  })
"

definition PServer1 where 
"PServer1 = PServer0 \<triangle> (do { outp terminate ()} )"

definition "rename_Server = 
  [(recv_C x, send_C x). x \<leftarrow> (A_I_snd_msg_sec Alice @ B_I_snd_msg_sec Bob @ I_snd_msg_sec Intruder)] @
  [(send_C x, recv_C x). x \<leftarrow> (A_I_rcv_msg_sec Alice @ B_I_rcv_msg_sec Bob @ I_rcv_msg_sec Intruder)] @
  [(terminate_C (), terminate_C ())]"

definition "PServer = rename' (PServer1) (set rename_Server)"

subsubsection \<open> Composition \<close>

definition "PAlice = Initiator Alice (NonceMap Alice)"
definition "PBob = Responder Bob (NonceMap Bob)"

definition "Events_A_B_S = (set ((A_I_snd_event_sec Alice @ A_I_rcv_event_sec Alice 
            @ terminate_event @ B_I_snd_event_sec Bob @ B_I_rcv_event_sec Bob)))"
definition "Events_A_B_S_I = (set (remdups (
  (A_I_snd_event Alice (NonceMap Alice) @ A_I_rcv_event Alice (NonceMap Alice) @ A_I_sig Alice (NonceMap Alice)) @ 
  (B_I_snd_event Bob (NonceMap Bob) @ B_I_rcv_event Bob (NonceMap Bob) @ B_I_sig Bob (NonceMap Bob)) @ 
  terminate_event @ I_snd_event_sec Intruder @ I_rcv_event_sec Intruder)))"
value "Events_A_B_S_I"

definition NSPK7 where
"NSPK7 = 
    ((PAlice \<parallel>\<^bsub> set terminate_event \<^esub> PBob) \<parallel>\<^bsub> Events_A_B_S \<^esub> PServer) 
    \<parallel>\<^bsub> Events_A_B_S_I \<^esub> PIntruder"

animate_sec NSPK7

(*
Reachability:
  AReach 25 %Terminate%
  AReach 25 %Leak N1%
  RReach 25 %Leak N1%
  AReach 25 %Sig EndProt (A1) (A0) (N0) (N1)% # %Sig StartProt (A0) (A1) (N0) (N1)%
  AReach 25 %Sig EndProt (A0) (A1) (N0) (N1)% # %Sig StartProt (A1) (A0) (N0) (N1)%
*)
end
