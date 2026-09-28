section \<open> Animation of NSWJ3 (3-message version) including the active and passive attacks \<close>
theory NSWJ3_wbplsec
  imports "ITree_Simulation.ITree_Simulation" 
          "ITree_Security.Sec_Animation"
          "NSWJ3_config"
begin

definition "watjam m bw bj = {{m}\<^sup>w\<^bsub>bw\<^esub> }\<^sup>j\<^bsub>bj\<^esub> "
definition "watjam1 m b = {{m}\<^sup>w\<^bsub>b\<^esub> }\<^sup>j\<^bsub>b\<^esub> "

subsection \<open>  Needham Schroeder Public Key Protocol - active attack \<close>
text \<open> The message 1 that an agent can send \<close>
definition msg1a :: "dagent => dmsg" where 
"msg1a A = MWat (\<lbrace>MNon (NonceMap(A)), MAg A\<rbrace>\<^sub>m) (mkbma A)"

text \<open> The message 2 that an agent can send \<close>
definition "msg2a A = [MWat \<lbrace>MNon (NonceMap(A)), MNon (NonceMap(B))\<rbrace>\<^sub>m (mkbma B). B \<leftarrow> AllOtherAgents' A]"
text \<open> The message 3 that an agent can send with its counterpart's nonce \<close>
definition msg3a :: "dagent \<Rightarrow> dmsg \<Rightarrow> dmsg" where 
"msg3a A nb = MWat nb (mkbma A)"

text \<open> A list of Message 1 an agent B can receive. We assume Intruder's bitmasks are not known to B 
and so B won't receive messages watermarked by Intruder's bitmask. \<close>
definition "msg1b B = [msg1a A. A \<leftarrow> AllOtherAgents B]"
text \<open> The message 2 an agent can send \<close>
definition "msg2b B na nb = MWat \<lbrace>MNon na, MNon nb\<rbrace>\<^sub>m (mkbma B)"

text \<open> These messages are all combinations of possible Msg2 and Msg3 that A sends and the intruder can get. \<close>
text \<open> A list of Message 3 an agent can send \<close>
definition "msg3ab A = [msg3a A (MNon (NonceMap(B))). B \<leftarrow> AllAgents', A \<noteq> B]"
text \<open> A list of Message 2 an agent can send \<close>
definition "msg2ab B = [msg2b B (NonceMap(A)) (NonceMap(B)). A \<leftarrow> AllOtherAgents B]"
text \<open> All the messages that an agent will send \<close>
definition "msgsab A = [msg1a A] @ msg3ab A @ msg2ab A"

text \<open> All the messages that agents (A) will send and its counterpart (B) will jam \<close>
definition "msgsabj eve = [{m}\<^sup>j\<^bsub>b\<^esub> . (A, B) \<leftarrow> AllCommsAgents, m \<leftarrow> msgsab A, b \<leftarrow> [bm_or_null B eve]]"

text \<open> The received messages could be from a legitimate agent or from the intruder (for example, fake messages) \<close>
definition rcv_msg :: "dagent \<Rightarrow> dmsg list \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"rcv_msg A ms = [(B, Intruder, A, m). m \<leftarrow> ms, B \<leftarrow> AllOtherAgents' A]"

text \<open> A jamming process for A or B, but not for Intruder. \<close>
definition jamming :: "dagent \<Rightarrow> dmsg list \<Rightarrow> \<bool> \<Rightarrow> (chan, unit) itree" where
"jamming A ms inrange = do {
  loop (\<lambda>s. 
    do {
      (B, _, A, m) \<leftarrow> inp_in recv (set (rcv_msg A ms));
      outp cjam ({m}\<^sup>j\<^bsub>(bm_or_null_b inrange A)\<^esub> )
    })
  ()
}"

text \<open> A jamming process for Intruder. \<close>
definition jamming_intruder :: "deve \<Rightarrow> (chan, unit) itree" where
"jamming_intruder eve = do {
  loop (\<lambda>s. 
    do {
      \<comment> \<open> What Intruder can hear is what other agents can send \<close>
      (A, _, B, m) \<leftarrow> inp_in hear (set [(A, Intruder, B, m). (A, B) \<leftarrow> AllCommsAgents, m \<leftarrow> msgsab A]); 
      \<comment> \<open> Intruder can hear all jammed m by other agents (B) \<close>                               
      ((outp_choice_from_set cjam (\<lambda>s. skip) (set [{m}\<^sup>j\<^bsub>(bm_or_null B eve)\<^esub> . B \<leftarrow> AllOtherAgents A]))
      \<interleave>
      \<comment> \<open> Intruder also relays the original message m to B \<close>
      (outp relay (A, Intruder, B, m)))
    }
  )
  ()
}"

subsubsection \<open> Alice \<close>

definition Initiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan, unit) itree" where
"Initiator A na = do {
    \<comment> \<open> Receive environment's request to establish authentication with B \<close>
    (_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents', C \<noteq> A]);
    do {
      \<comment> \<open> Send a signal to claim na is secret between A and B \<close>
      outp sig (ClaimSecret A na (set [B]));
      \<comment> \<open> Send Msg1 \<close>
      outp send (A, Intruder, B, msg1a A);
      \<comment> \<open> Receive Msg2 \<close>
      \<comment> \<open> A only receives messages that are jammed using A's jamming bitmask so no dejamming required \<close>
      m \<leftarrow> inp_in cjam (set ([{m}\<^sup>j\<^bsub>mkbma A\<^esub> . m \<leftarrow> msg2a A]));
      let m2 = (mwm (mjm m)); nb = mn (mc2 m2)
      in
        do {
          outp sig (StartProt A B na nb);
          \<comment> \<open> Send Msg3 \<close>
          outp send (A, Intruder, B, msg3a A (MNon nb));
          outp sig (EndProt A B na nb);
          outp terminate ()
        }
    }
}
"

value "Initiator Alice (NonceMap(Alice))"
definition A_snd_msgs :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"A_snd_msgs A = (let Bs = removeAll A AllAgents'
  in
    \<comment> \<open> Msg1 \<close>
    [(A, Intruder, B, msg1a A). B \<leftarrow> Bs] @
      \<comment> \<open> Msg3 \<close>
    [(A, Intruder, B, msg3a A (MNon (NonceMap B))). B \<leftarrow> Bs]
  )"

value "A_snd_msgs Alice"

definition A_snd_events :: "dagent \<Rightarrow> chan list" where 
"A_snd_events A = [send_C m. m \<leftarrow> A_snd_msgs A]"

value "A_snd_events Alice"

definition A_rcv_msgs :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"A_rcv_msgs A = rcv_msg A (msg2a A)"

definition Get_messages :: "(dagent \<times> dagent \<times> dagent \<times> dmsg) list \<Rightarrow> dmsg list" where
"Get_messages ms = remdups (map last4 (ms))"

value "A_rcv_msgs Alice"

definition A_recv_events :: "dagent \<Rightarrow> chan list" where 
"A_recv_events A = [recv_C m. m \<leftarrow> A_rcv_msgs A]"

value "A_recv_events Alice"

definition Alice_jamming_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"Alice_jamming_events A na = [cjam_C {m}\<^sup>j\<^bsub>b\<^esub> . m \<leftarrow> Get_messages (A_rcv_msgs A), b \<leftarrow> [mkbma Alice, MBitm Null]]"

value "Alice_jamming_events Alice (NonceMap Alice)"

definition "PAlice = 
  (par_hidep (Initiator Alice (NonceMap Alice)) (Alice_jamming_events Alice (NonceMap Alice))
    (jamming Alice (Get_messages (A_rcv_msgs Alice)) True))
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

\<^cancel>\<open> animate_sec PAlice \<close>

definition A_I_sig :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"A_I_sig A na = [sig_C (ClaimSecret A nb (set [B])). 
  nb \<leftarrow> AllNonces', B \<leftarrow> removeAll A AllAgents']"

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"

subsubsection \<open> Bob \<close>
definition Responder :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan, unit) itree" where
"Responder B nb = 
      do {
          \<comment> \<open> Receive Msg1 \<close>
          m \<leftarrow> inp_in cjam (set ([{m}\<^sup>j\<^bsub>mkbma B\<^esub> . m \<leftarrow> msg1b B]));
          \<comment> \<open> B is supposed to know participant's bitmask so can reduce the msg1 \<close>
          let m1 = (mwm (mjm m)); A = ma (mc2 m1); na = mn (mc1 m1)
          in
            do {  
                  \<comment> \<open> Send a signal to claim nb is secret between A and B \<close>
                  outp sig (ClaimSecret B nb (set [A]));
                  outp sig (StartProt B A na nb);
                  \<comment> \<open> Send Msg2 \<close>
                  outp send (B, Intruder, A, msg2b B na nb);
                  \<comment> \<open> Receive Msg3 \<close>
                  m \<leftarrow> inp_in cjam (set ([{m}\<^sup>j\<^bsub>mkbma B\<^esub> . m \<leftarrow> [msg3a A (MNon nb)]]));
                  outp sig (EndProt B A na nb);
                  outp terminate ()
            }
  }
"

definition B_snd_msgs :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"B_snd_msgs B nb = (let As = removeAll B AllAgents'
  in
    [(B, Intruder, A, msg2b B (NonceMap A) nb). A \<leftarrow> As]
  )"

value "B_snd_msgs Bob (NonceMap Bob)"

definition B_snd_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"B_snd_events B nb = [send_C m. m \<leftarrow> B_snd_msgs B nb]"

value "B_snd_events Bob (NonceMap Bob)"

definition B_rcv_msgs' :: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list" where
"B_rcv_msgs' B nb = (let As = removeAll B AllAgents'
  in
    msg1b B @ [msg3a A (MNon (nb)). A \<leftarrow> As]
)"

definition B_rcv_msgs :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"B_rcv_msgs B nb = rcv_msg B (B_rcv_msgs' B nb)"

value "B_rcv_msgs Bob (NonceMap Bob)"

definition B_recv_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"B_recv_events B nb = [recv_C m. m \<leftarrow> B_rcv_msgs B nb]"

value "B_recv_events Bob (NonceMap Bob)"

definition Bob_jamming_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"Bob_jamming_events B nb = [cjam_C {m}\<^sup>j\<^bsub>b\<^esub> . 
  m \<leftarrow> B_rcv_msgs' B nb, b \<leftarrow> [mkbma B, MBitm Null]]"

value "Bob_jamming_events Bob (NonceMap(Bob))"

definition "PBob_jamming B nb = (jamming B (B_rcv_msgs' B nb) True)"

definition "PBob = 
  (par_hidep (Responder Bob (NonceMap(Bob))) (Bob_jamming_events Bob (NonceMap Bob)) (PBob_jamming Bob (NonceMap Bob))) 
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

\<^cancel>\<open> animate_sec "PBob" \<close>

definition B_I_sig :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"B_I_sig B nb = [sig_C (ClaimSecret B na (set [A])).
  na \<leftarrow> AllNonces', A \<leftarrow> removeAll B AllAgents']"

subsubsection \<open> Intruder \<close>
text \<open> All the messages the agents can send and receive \<close>
definition "AllRecvMsgs = (A_rcv_msgs Alice @ B_rcv_msgs Bob (NonceMap Bob))"

value "AllRecvMsgs"

definition "AllPossibleMsgsRecvByAgents = map last4 AllRecvMsgs"

value "AllPossibleMsgsRecvByAgents"

text \<open> @{text "sublist xs ys"} gets a sublist from xs of which each element is a member of ys. \<close>
definition sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sublist xs ys = filter (\<lambda>x. List.member ys x) xs"

text \<open> @{text "PIntruder I ni k sec "} \<close>
definition PIntruder0:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> deve \<Rightarrow> (chan, unit) itree" where
"PIntruder0 I ni k s eve = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (m) \<leftarrow> inp_in cjam (set (msgsabj eve));
            \<comment> \<open> Intruder can fake any message (it can infer) to the target \<close>
            Ret (True, breakl (List.insert m knows), sec)
      }
    \<comment> \<open> If we consider an active attack so it can send inferred messages to Alice and Bob from Intruder.
    Though the intruder can send any inferred message, here we only consider watermarked messages 
    using buildw. Indeed, there is no difference because legitimate principals only accept watermarked 
    messages from known principals.\<close>
    \<box> \<^cancel>\<open>do { inp_in fake (set [(I, I, B, m'). 
          B \<leftarrow> AllAgentsButIntruder', m' \<leftarrow> (buildw (knows) 2)]);
          Ret (True, knows, sec)
      }\<close>
      do {  
            inp_in fake (set (sublist 
                [(A, I, B, m'). A \<leftarrow> [I], B \<leftarrow> AllAgentsButIntruder', 
                  m' \<leftarrow> (filter_buildable AllPossibleMsgsRecvByAgents (set knows))] 
                AllRecvMsgs) ); 
            Ret (True, knows, sec) 
      }
    \<box> do { outp terminate (); Ret (False, knows, sec) }
    \<comment> \<open> If an agent claims n is secret and only knows to agent B, which is the intruder. We can remove 
      this nonce in the secret. \<close>
    \<box> do { c \<leftarrow> inp_in sig (set [(ClaimSecret A n (set [B])). A \<leftarrow> AllAgentsButIntruder', 
              n \<leftarrow> removeAll ni AllNonces',  B \<leftarrow> AllAgents', A \<noteq> B]);
              (if I \<in> (sp c) then Ret (True, knows, (removeAll (MNon (sn c)) sec)) else Ret (True, knows, sec))
          }
    \<box> do { 
          \<comment> \<open> List.member should only be used for code generation, see comments in its definition \<close>
          let leaked = list_inter knows sec
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

definition Intruder_jamming_events :: "deve \<Rightarrow> chan list" where
"Intruder_jamming_events eve = [cjam_C mj. mj \<leftarrow> msgsabj eve]"

definition "PIntruder0' I ni k s eve = 
  par_hidep (PIntruder0 I ni k s eve) (Intruder_jamming_events eve) (jamming_intruder eve)"

\<^cancel>\<open> definition "Q = PIntruder0' Intruder (NonceMap(Intruder)) InitKnows AllSecrets"
animate_sec Q \<close>

definition "PLeakOnlyOnce secrects = \<interleave>\<^bsub>secrects\<^esub> @ (\<lambda>s. do {outp leak s})"

(* value "PLeakOnlyOnce AllSecrets" *)

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "PIntruder1 I ni k s eve = ((PIntruder0' I ni k s eve) \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s) 
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "PIntruder eve = (PIntruder1 Intruder (NonceMap(Intruder)) InitKnows AllSecrets eve)"

subsubsection \<open> Composition \<close>
text \<open> All messages that agents can fake. \<close>
definition All_msgs :: "(dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"All_msgs = [(A, Intruder, B, m). A \<leftarrow> AllAgents', B \<leftarrow> AllAgents', B \<noteq> A, m \<leftarrow> msgsab A]"

text \<open> All messages that I can fake. \<close>
definition All_msgs_I :: "(dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"All_msgs_I = [(Intruder, Intruder, A, m). A \<leftarrow> AllAgentsButIntruder', m \<leftarrow> msgsab A]"

definition evt_msgs_snd :: "chan list" where 
"evt_msgs_snd = [send_C m. m \<leftarrow> List.union All_msgs  All_msgs_I]"

definition evt_msgs_recv :: "chan list" where 
"evt_msgs_recv = [recv_C m. m \<leftarrow> List.union All_msgs All_msgs_I]"

definition "Events_A_B_I = 
  (set (remdups (A_snd_events Alice @ A_recv_events Alice @
      B_snd_events Bob (NonceMap Bob) @ B_recv_events Bob (NonceMap Bob)
      @ (A_I_sig Alice (NonceMap(Alice)))
      @ terminate_event 
      @ (B_I_sig Bob (NonceMap(Bob))) 
      @ evt_msgs_snd @ evt_msgs_recv))
)"

value "Events_A_B_I"

(*
definition  OtherEvents :: "chan list" where 
"OtherEvents = [ recv_C (Intruder, Intruder, A, m). A \<leftarrow> AllAgentsButIntruder', m \<leftarrow> AllPossibleMsgsRecvByAgents]"
*)
                                                           
(*
text \<open> Also include all possible messages that the intruder can infer to fake. \<close>
definition AllKnows :: "dmsg list" where 
"AllKnows = AllNoncesLst' @ AllAgentsLst' @ AllBitmsLst'"

definition "All_I_Fake = buildw AllKnows 2"
value All_I_Fake

definition "Events_I_Fake = set ([recv_C (Intruder, Intruder, B, m). 
  B \<leftarrow> AllAgentsButIntruder', m \<leftarrow> All_I_Fake])"
*)
(*
definition "P = (PIntruder Eve3)"
animate_sec P
*)

definition NSWJ3_active where
"NSWJ3_active eve = (PAlice \<parallel>\<^bsub> set terminate_event \<^esub> PBob) \<parallel>\<^bsub> Events_A_B_I\<^esub> (PIntruder eve)"

\<comment> \<open> The only purpose of this unnecesssary abbreviation is to call (Eve1 = Eve2) in order to generate 
code for equal_deve, which is used by animation later on web interface. \<close>
abbreviation "NSWJ3_active' eve \<equiv> if Eve1 = Eve2 then NSWJ3_active eve else NSWJ3_active eve"

definition "NSWJ3_active_eve1 = NSWJ3_active' Eve1"
definition "NSWJ3_active_eve2 = NSWJ3_active' Eve2"
definition "NSWJ3_active_eve3 = NSWJ3_active' Eve3"
definition "NSWJ3_active_eve4 = NSWJ3_active' Eve4"
animate_sec NSWJ3_active_eve1

(*
Reachability:
  AReach 15 %Terminate%
  AReach 15 %Leak N1%
  RReach 15 %Leak N1%
  AReach 15 %Sig EndProt (A1) (A0) (N0) (N1)% # %Sig StartProt (A0) (A1) (N0) (N1)% 
  AReach 15 %Sig EndProt (A0) (A1) (N0) (N1)% # %Sig StartProt (A1) (A0) (N0) (N1)%
*)

subsection \<open>  Needham Schroeder Public Key Protocol - passive attack \<close>
definition PIntruder0_passive:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> deve \<Rightarrow> (chan, unit) itree" where
"PIntruder0_passive I ni k s eve = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (m) \<leftarrow> inp_in cjam (set (msgsabj eve));
            \<comment> \<open> Intruder can fake any message (it can infer) to the target \<close>
            Ret (True, breakl (List.insert m knows), sec)
      }
    \<comment> \<open> If we consider a passive attack so it cannot send inferred messages to Alice and Bob from Intruder.\<close>
    \<^cancel>\<open>\<box> do { inp_in fake (set [(I, I, B, m'). 
          B \<leftarrow> AllAgentsButIntruder', m' \<leftarrow> (buildw (knows) 2)]);
          Ret (True, knows, sec)
      }\<close>
    \<box> do { outp terminate (); Ret (False, knows, sec) }
    \<comment> \<open> If an agent claims n is secret and only knows to agent B, which is the intruder. We can remove 
      this nonce in the secret. \<close>
    \<box> do { c \<leftarrow> inp_in sig (set [(ClaimSecret A n (set [B])). A \<leftarrow> AllAgentsButIntruder', 
              n \<leftarrow> removeAll ni AllNonces',  B \<leftarrow> AllAgents', A \<noteq> B]);
              (if I \<in> (sp c) then Ret (True, knows, (removeAll (MNon (sn c)) sec)) else Ret (True, knows, sec))
          }
    \<box> do { 
          \<comment> \<open> List.member should only be used for code generation, see comments in its definition \<close>
          let leaked = list_inter knows sec
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

definition "PIntruder0_passive' I ni k s eve = 
  par_hidep (PIntruder0_passive I ni k s eve) (Intruder_jamming_events eve) (jamming_intruder eve)"

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "PIntruder1_passive I ni k s eve = ((PIntruder0_passive' I ni k s eve) \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s) 
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "PIntruder_passive eve = (PIntruder1_passive Intruder (NonceMap(Intruder)) InitKnows AllSecrets eve)"

subsubsection \<open> Composition \<close>

definition NSWJ3_passive where
"NSWJ3_passive eve = (PAlice \<parallel>\<^bsub> set terminate_event \<^esub> PBob) \<parallel>\<^bsub> Events_A_B_I \<^esub> (PIntruder_passive eve)"

text\<open> The previous @{text "animate_sec"} needs to be commented out because only one such command  
in a file is allow. \<close>
definition "NSWJ3_passive_eve1 = NSWJ3_passive Eve1"
definition "NSWJ3_passive_eve2 = NSWJ3_passive Eve2"
definition "NSWJ3_passive_eve3 = NSWJ3_passive Eve3"
definition "NSWJ3_passive_eve4 = NSWJ3_passive Eve4"
animate_sec NSWJ3_passive_eve4

end
