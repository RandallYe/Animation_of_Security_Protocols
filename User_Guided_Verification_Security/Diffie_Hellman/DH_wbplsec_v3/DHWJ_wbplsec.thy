section \<open> Animation of the classic Diffie-Hellman that is based on WBPLSec \<close>
theory DHWJ_wbplsec
  imports "ITree_Simulation.ITree_Simulation"
          "ITree_Security.Sec_Animation"
          "DHWJ_config"
begin

definition "watjam m bw bj = {{m}\<^sup>w\<^bsub>bw\<^esub> }\<^sup>j\<^bsub>bj\<^esub> "
definition "watjam1 m b = {{m}\<^sup>w\<^bsub>b\<^esub> }\<^sup>j\<^bsub>b\<^esub> "

text \<open>
Diffie-Hellman without signatures, Only resists passive attacks
	1. A -> B : g^x
  2. B -> A : g^y
     A and B compute the key as k = (g^x)^y = (g^y)^x
  3. A -> B : {s}k
    We choose the public key of Alice as the secret s
  4. B -> A : {s}k
    B sends back the secret s to A
\<close>

subsection \<open>  DH - Processes \<close>

subsubsection \<open> Messages \<close>
text \<open> The message 1 or 2 (g^x or g^y) that an agent can send \<close>
definition msg12_agent_send :: "dagent => dmsg" where 
"msg12_agent_send A = (ExpG ^\<^sub>m (MNon (NonceMap(A))))"

text \<open> The watermarked message 1 or 2 (g^x or g^y) that an agent can send \<close>
definition wm_msg12_agent_send :: "dagent => dmsg" where 
"wm_msg12_agent_send A = MWat (msg12_agent_send A) (mkbma A)"

text \<open> All messages 1 and 2 that other agents can receive \<close>
definition "all_msg12_agent_recv A = [msg12_agent_send B. B \<leftarrow> AllOtherAgents A]"
definition "all_wm_msg12_agent_recv A = [wm_msg12_agent_send B. B \<leftarrow> AllOtherAgents A]"

value "all_wm_msg12_agent_recv Alice"

text \<open> The message 3 that an agent can send \<close>
definition msg3_agent_send :: "dagent => dnonce \<Rightarrow> dmsg \<Rightarrow> dmsg" where 
"msg3_agent_send A na gy = {MK (pks A)}\<^sup>s\<^bsub>gy ^\<^sub>m (MNon na)\<^esub> "

text \<open> The watermarked message 3 that an agent can send \<close>
definition wm_msg3_agent_send :: "dagent => dnonce \<Rightarrow> dmsg \<Rightarrow> dmsg" where 
"wm_msg3_agent_send A na gy = MWat (msg3_agent_send A na gy) (mkbma A)"

text \<open> All the message 3 that an agent can send \<close>
definition "all_msg3_agent_send A = [msg3_agent_send A na gy. na \<leftarrow> [(NonceMap(A))], gy \<leftarrow> all_msg12_agent_recv A]"

text \<open> All the watermarked message 3 that an agent can send \<close>
definition "all_wm_msg3_agent_send A = [wm_msg3_agent_send A na gy. na \<leftarrow> [(NonceMap(A))], gy \<leftarrow> all_msg12_agent_recv A]"

text \<open> The message 4 that an agent can send \<close>
definition msg4_agent_send :: "dmsg => dnonce \<Rightarrow> dmsg \<Rightarrow> dmsg" where 
"msg4_agent_send mpk nb gx = {mpk}\<^sup>s\<^bsub>gx ^\<^sub>m (MNon nb)\<^esub> "

text \<open> The watermarked message 4 that an agent can send \<close>
definition wm_msg4_agent_send :: "dagent \<Rightarrow> dmsg => dnonce \<Rightarrow> dmsg \<Rightarrow> dmsg" where 
"wm_msg4_agent_send B mpk nb gx = MWat (msg4_agent_send mpk nb gx) (mkbma B)"

text \<open> All the message 4 that an agent can send \<close>
definition "all_msg4_agent_send B = [msg4_agent_send mpk nb gx. 
  mpk \<leftarrow> AllOtherPKs B, nb \<leftarrow> [(NonceMap(B))], gx \<leftarrow> all_msg12_agent_recv B]"

text \<open> All the watermarked message 4 that an agent can send \<close>
definition "all_wm_msg4_agent_send B = [wm_msg4_agent_send B mpk nb gx. 
  mpk \<leftarrow> AllOtherPKs B, nb \<leftarrow> [(NonceMap(B))], gx \<leftarrow> all_msg12_agent_recv B]"

text \<open> All the messages (1, 2, 3, and 4) that an agent can send \<close>
definition all_msg123_agent_send :: "dagent \<Rightarrow> dmsg list" where
"all_msg123_agent_send A = [msg12_agent_send A] @ all_msg3_agent_send A @ all_msg4_agent_send A"

definition "all_wm_msg123_agent_send A = [wm_msg12_agent_send A] @ all_wm_msg3_agent_send A 
  @ all_wm_msg4_agent_send A"

value "all_wm_msg123_agent_send Alice"

text \<open> All the messages that agents (A) will send and its counterpart (B) will jam \<close>
definition "all_jm_wm_msg123_agent_send eve = [{m}\<^sup>j\<^bsub>b\<^esub> . (A, B) \<leftarrow> AllCommsAgentsButIntr, 
    m \<leftarrow> all_wm_msg123_agent_send A, b \<leftarrow> [bm_or_null B eve]]"

value "AllCommsAgentsButIntr"
value "all_jm_wm_msg123_agent_send Eve1"

text \<open> All the message 3 that an agent can receive \<close>
definition "all_wm_msg3_agent_recv B = [
    MWat ({MPK A}\<^sup>s\<^bsub>(msg12_agent_send B) ^\<^sub>m (MNon (NonceMap (A)))\<^esub> ) (mkbma A). A \<leftarrow> AllOtherAgents B
    \<^cancel>\<open>s \<leftarrow> AllOtherPKs B, na \<leftarrow> removeAll nb AllNonces', A \<leftarrow> AllOtherAgents B\<close>
]"

text \<open> All the message 4 that an agent can receive \<close>
definition "all_wm_msg4_agent_recv A = [
    MWat ({MPK B}\<^sup>s\<^bsub>(msg12_agent_send A) ^\<^sub>m (MNon (NonceMap (C)))\<^esub> ) (mkbma C). B \<leftarrow> AllAgents', 
    C \<leftarrow> AllOtherAgents A
]"

value "all_wm_msg4_agent_recv Alice"

text \<open> The received messages could be from a legitimate agent or from the intruder (for example, fake messages) \<close>
definition rcv_msg :: "dagent \<Rightarrow> dmsg list \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"rcv_msg A ms = [(B, Intruder, A, m). m \<leftarrow> ms, B \<leftarrow> AllOtherAgents A]"

text \<open> Get messages from channel events. \<close>
definition get_messages :: "(dagent \<times> dagent \<times> dagent \<times> dmsg) list \<Rightarrow> dmsg list" where
"get_messages ms = remdups (map last4 (ms))"

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
      (A, _, B, m) \<leftarrow> inp_in hear (set [(A, Intruder, B, m). (A, B) \<leftarrow> AllCommsAgentsButIntr, 
        m \<leftarrow> all_wm_msg123_agent_send A]); 
      \<comment> \<open> Intruder can hear all jammed m by other agents (B) \<close>                               
      ((outp_choice_from_set cjam (\<lambda>s. skip) (set [{m}\<^sup>j\<^bsub>(bm_or_null B eve)\<^esub> . B \<leftarrow> AllOtherAgentsButIntr A]))
      \<interleave>
      \<comment> \<open> Intruder also relays the original message m to B \<close>
      (outp relay (A, Intruder, B, m)))
    }
  )
  ()
}"

subsubsection \<open> Alice \<close>
definition Initiator :: "dagent \<Rightarrow> dnonce \<Rightarrow> (chan, unit) itree" where
"Initiator A na = 
  do {
    (_, B) \<leftarrow> inp_in env (set [(A, C). C \<leftarrow> AllAgents', C \<noteq> A]);
    do {
      \<comment> \<open> Send g^na \<close>
      outp send (A, Intruder, B, wm_msg12_agent_send A);
       \<comment> \<open> Receive g^nb \<close>
      m \<leftarrow> inp_in cjam (set ([{m}\<^sup>j\<^bsub>mkbma A\<^esub> . m \<leftarrow> all_wm_msg12_agent_recv A]));
      let gy = (mwm (mjm m))
      in
        do {
          \<comment> \<open> For signal here, we can recover n from g^n. But Intruder cannot learn n from g^n. \<close>
          outp sig (StartProt A B na (mn (mmek gy)));
          \<comment> \<open> Send Msg3 \<close>
          \<comment> \<open> MKp (PK A) is chosen as a secret, encrypted with (g^b)^a and where g^b = gy \<close>
          outp send (A, Intruder, B, wm_msg3_agent_send A na gy);
          \<comment> \<open> Recieve an encrypted message using (g^a)^b as the key \<close>
          m4' \<leftarrow> inp_in cjam (set ([{m4}\<^sup>j\<^bsub>mkbma A\<^esub> . m4 \<leftarrow> all_wm_msg4_agent_recv A]));
          let m4 = (mwm (mjm m4')); m4m = msem m4
          in 
            \<comment> \<open>If the swap of the key (g^x^y) is equal to (g^y^x), then we can decrypt it to get its 
              clear message m4m \<close>
            if (swap_mod_exp (msek m4)) = (gy ^\<^sub>m (MNon na)) then
              if m4m = MPK A then
                do {
                  outp sig (EndProt A B na (mn (mmek gy)));
                  outp terminate ()
                }
              else 
                Ret ()
            else 
              Ret ()
        }
    }
  }
"

value "Initiator Alice (NonceMap(Alice))"

text \<open> All messages that Alice will send and Intruder can hear  \<close>
definition A_snd_msgs :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"A_snd_msgs A na = (let Bs = removeAll A AllAgents'
  in
    \<comment> \<open> Msg1 \<close>
    [(A, Intruder, B, wm_msg12_agent_send A). B \<leftarrow> Bs] @
    \<comment> \<open> Msg3 \<close>
    [(A, Intruder, B, wm_msg3_agent_send A na gy). B \<leftarrow> Bs, gy \<leftarrow> [msg12_agent_send B]]
  )"

value "A_snd_msgs Alice (NonceMap(Alice))"

definition A_snd_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"A_snd_events A na = [send_C m. m \<leftarrow> A_snd_msgs A na]"

value "A_snd_events Alice (NonceMap(Alice))"

definition A_rcv_msgs :: "dagent \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"A_rcv_msgs A = rcv_msg A (all_wm_msg12_agent_recv A @ all_wm_msg4_agent_recv A)"

value "A_rcv_msgs Alice"

definition A_recv_events :: "dagent \<Rightarrow> chan list" where 
"A_recv_events A = [recv_C m. m \<leftarrow> A_rcv_msgs A]"

value "A_recv_events Alice"

definition Alice_jamming_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"Alice_jamming_events A na = [cjam_C {m}\<^sup>j\<^bsub>b\<^esub> . 
  m \<leftarrow> get_messages (A_rcv_msgs A), b \<leftarrow> [mkbma A, MBitm Null]]"

value "Alice_jamming_events Alice (NonceMap Alice)"

text \<open> The process of Alice is a parallel composition of its initiator and a jamming process with 
the jamming events hidden. The exception is used to terminate the process by the terminate event.
\<close>
definition "PAlice = 
  (par_hidep (Initiator Alice (NonceMap Alice)) 
    (Alice_jamming_events Alice (NonceMap Alice))
    (jamming Alice (get_messages (A_rcv_msgs Alice)) True)
  ) \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

(* animate_sec PAlice *)

definition "terminate_rename = [(terminate_C (), terminate_C ())]"
definition "terminate_event = [terminate_C ()]"
 
subsubsection \<open> Bob \<close>

definition Responder :: "dagent \<Rightarrow> dnonce \<Rightarrow> dagent \<Rightarrow> (chan, unit) itree" where
"Responder B nb A = 
  do {
     \<comment> \<open> Send g^nb \<close>
    outp send (B, Intruder, A, wm_msg12_agent_send B);
     \<comment> \<open> Receive g^na \<close>
    m1 \<leftarrow> inp_in cjam (set ([{m}\<^sup>j\<^bsub>mkbma B\<^esub> . m \<leftarrow> all_wm_msg12_agent_recv B]));
    let gx = (mwm (mjm m1))
    in
      do {
        outp sig (StartProt B A (mn (mmek gx)) nb);
        \<comment> \<open> Recieve an encrypted message using (g^a)^b as the key \<close>
        m3' \<leftarrow> inp_in cjam (set ([{m3}\<^sup>j\<^bsub>mkbma B\<^esub> . m3 \<leftarrow> all_wm_msg3_agent_recv B]));
        let m3 = (mwm (mjm m3')); m3m = msem m3
        in 
          do {
            \<comment> \<open> If B can break the message m' to get the secret, so the session key works. 
                The protocol terminates. Otherwise, deadlock (due to the later exception). \<close>
            \<^cancel>\<open>if List.member (breakl [MNon nb, MAg B, ExpG ^\<^sub>m (MNon nb), gx, m3]) 
                 (MPK A) then\<close>
            \<comment> \<open>If the swap of the key (g^y^x) is equal to (g^x^y), then we can decrypt it to get its 
              clear message m3m \<close>
            if (swap_mod_exp (msek m3)) = (gx ^\<^sub>m (MNon nb)) then
              do {
                outp send (B, Intruder, A, wm_msg4_agent_send B m3m nb gx);
                outp sig (EndProt B A (mn (mmek gx)) nb);
                outp terminate ()
              }
            else 
              Ret ()
          }
      }
  }
"

definition B_snd_msgs :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where 
"B_snd_msgs B nb = (let As = removeAll B AllAgents'
  in
    [(B, Intruder, A, wm_msg12_agent_send B). A \<leftarrow> As] @ 
    [(B, Intruder, A, m4). A \<leftarrow> As, m4 \<leftarrow> all_wm_msg4_agent_send B]
  )"

value "B_snd_msgs Bob (NonceMap Bob)"

definition B_snd_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"B_snd_events B nb = [send_C m. m \<leftarrow> B_snd_msgs B nb]"

value "B_snd_events Bob (NonceMap Bob)"

definition B_rcv_msgs :: "dagent \<Rightarrow> dnonce \<Rightarrow> (dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"B_rcv_msgs B nb = rcv_msg B (all_wm_msg12_agent_recv B @ all_wm_msg3_agent_recv B)"

value "B_rcv_msgs Bob (NonceMap Bob)"

definition B_recv_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where 
"B_recv_events B nb = [recv_C m. m \<leftarrow> B_rcv_msgs B nb]"

value "B_recv_events Bob (NonceMap Bob)"

definition Bob_jamming_events :: "dagent \<Rightarrow> dnonce \<Rightarrow> chan list" where
"Bob_jamming_events B nb = [cjam_C {m}\<^sup>j\<^bsub>b\<^esub> . 
  m \<leftarrow> get_messages (B_rcv_msgs B nb), b \<leftarrow> [mkbma B, MBitm Null]]"

value "Bob_jamming_events Bob (NonceMap(Bob))"

definition "PBob_jamming B nb = (jamming B (get_messages (B_rcv_msgs B nb)) True)"

definition "PBob = 
  (par_hidep (Responder Bob (NonceMap Bob) Alice) 
      (Bob_jamming_events Bob (NonceMap Bob)) 
      (PBob_jamming Bob (NonceMap Bob))) 
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

(* animate_sec PBob *)

subsubsection \<open> Intruder \<close>
text \<open> All the messages the agents can send and receive \<close>
definition "AllRecvMsgs = (A_rcv_msgs Alice @ B_rcv_msgs Bob (NonceMap Bob))"

value "AllRecvMsgs"

definition "AllPossibleMsgsRecvByAgents = remdups (map last4 AllRecvMsgs)"

value "AllPossibleMsgsRecvByAgents"

text \<open> @{text "sublist xs ys"} gets a sublist from xs of which each element is a member of ys. \<close>
definition sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sublist xs ys = filter (\<lambda>x. List.member ys x) xs"

definition PIntruder0:: "dagent \<Rightarrow> dnonce \<Rightarrow> dmsg list \<Rightarrow> dmsg list \<Rightarrow> deve \<Rightarrow> (chan, unit) itree" where
"PIntruder0 I ni k s eve = do {
  ret \<leftarrow> Ret (True, k, s) ;
  (iterate (\<lambda>(con, knows, sec). con)
    (\<lambda> (con, knows, sec). 
       do { 
            \<comment> \<open> Intruder can hear anything Alice and Bob can send \<close>
            (m) \<leftarrow> inp_in cjam (set (all_jm_wm_msg123_agent_send eve));
            \<comment> \<open> Intruder can fake any message (it can infer) to the target \<close>
            Ret (True, breakl (List.insert m knows), sec)
      }
    \<comment> \<open> If we consider an active attack so it can send inferred messages to Alice and Bob from Intruder.
    Though the intruder can send any inferred message, here we only consider watermarked messages 
    using buildw. Indeed, there is no difference because legitimate principals only accept watermarked 
    messages from known principals.\<close>
    \<box> do {  
            inp_in fake (set (sublist 
                [(A, I, B, m'). A \<leftarrow> [I], B \<leftarrow> AllAgentsButIntruder', 
                  m' \<leftarrow> (filter_buildable AllPossibleMsgsRecvByAgents (set knows))] 
                AllRecvMsgs) ); 
            Ret (True, knows, sec) 
      }
    \<box> do { outp terminate (); Ret (False, knows, sec) }
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
"Intruder_jamming_events eve = [cjam_C mj. mj \<leftarrow> all_jm_wm_msg123_agent_send eve]"

value "Intruder_jamming_events Eve1"

definition "PIntruder0' I ni k s eve = 
  par_hidep (PIntruder0 I ni k s eve) (Intruder_jamming_events eve) (jamming_intruder eve)"

definition "PLeakOnlyOnce secrects = \<interleave>\<^bsub>secrects\<^esub> @ (\<lambda>s. do {outp leak s})"

(* value "PLeakOnlyOnce AllSecrets" *)

text \<open> We use the exception operator to terminate PIntruder. \<close>
definition "PIntruder1 I ni k s eve = ((PIntruder0' I ni k s eve) \<parallel>\<^bsub> set (map leak_C s) \<^esub> PLeakOnlyOnce s) 
  \<lbrakk> (set [terminate_C ()]) \<Zrres> skip"

definition "PIntruder eve = (PIntruder1 Intruder (NonceMap(Intruder)) InitKnows AllSecrets eve)"

definition "PIntruderEve1 = PIntruder Eve3"

(* animate_sec PIntruderEve1 *)

subsubsection \<open> Composition \<close>
text \<open> All messages that agents can fake. \<close>
definition All_msgs :: "(dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"All_msgs = [(A, Intruder, B, m). A \<leftarrow> AllAgents', B \<leftarrow> AllAgents', B \<noteq> A, m \<leftarrow> all_wm_msg123_agent_send A]"

text \<open> All messages that I can fake. \<close>
definition All_msgs_I :: "(dagent \<times> dagent \<times> dagent \<times> dmsg) list" where
"All_msgs_I = [(Intruder, Intruder, A, m). A \<leftarrow> AllAgentsButIntruder', m \<leftarrow> all_wm_msg123_agent_send A]"

definition evt_msgs_snd :: "chan list" where 
"evt_msgs_snd = [send_C m. m \<leftarrow> List.union All_msgs  All_msgs_I]"

definition evt_msgs_recv :: "chan list" where 
"evt_msgs_recv = [recv_C m. m \<leftarrow> List.union All_msgs All_msgs_I]"

definition "Events_A_B_I = (set (remdups 
  (     A_snd_events Alice (NonceMap(Alice))
      @ A_recv_events Alice 
      @ B_snd_events Bob (NonceMap Bob) 
      @ B_recv_events Bob (NonceMap Bob)
      @ terminate_event 
      @ evt_msgs_snd @ evt_msgs_recv)
    )
  )"

value "Events_A_B_I"

definition DHWJ_active where                         
"DHWJ_active eve = (PAlice \<parallel>\<^bsub> set terminate_event \<^esub> PBob) \<parallel>\<^bsub> Events_A_B_I\<^esub> (PIntruder eve)"

\<comment> \<open> The only purpose of this unnecesssary abbreviation is to call (Eve1 = Eve2) in order to generate 
code for equal_deve, which is used by animation later on web interface. \<close>
abbreviation "DHWJ_active' eve \<equiv> 
  if Eve1 = Eve2 then DHWJ_active eve else DHWJ_active eve"

definition "DHWJ_active_eve1 = DHWJ_active' Eve1"
definition "DHWJ_active_eve2 = DHWJ_active' Eve2"
definition "DHWJ_active_eve3 = DHWJ_active' Eve3"
definition "DHWJ_active_eve4 = DHWJ_active' Eve4"
animate_sec DHWJ_active_eve4

(* AReach 15 %Terminate%
   AReach 15 %Leak PK0%
   AReach 15 %Sig EndProt (A1) (A0) (N0) (N1)% # %Sig StartProt (A0) (A1) (N0) (N1)%
   AReach 15 %Sig EndProt (A0) (A1) (N0) (N1)% # %Sig StartProt (A1) (A0) (N0) (N1)%
*)

(* 

*)

end
