# User-Guided Verification of Security Protocols via Sound Animation

This folder contains the Isabelle/HOL theories from which sound animators for security protocols are generated, together with the generated Haskell animators. Everything here belongs to the repository [Animation_of_Security_Protocols](../README.md); see the [top-level README](../README.md) for the overview and the papers.

- [What's included in the repo?](#whats-included-in-the-repo)
  - [Early stage (first user-guided sound framework)](#early-stage-first-user-guided-sound-framework)
  - [Second stage (generic and general framework)](#second-stage-generic-and-general-framework)
    - [Web interface](#web-interface)
  - [Third stage (proven soundness)](#third-stage-proven-soundness)
- [How to load theories in Isabelle/HOL and generate Haskell code?](#how-to-load-theories-in-isabellehol-and-generate-haskell-code)
- [Illustrations](#illustrations)
  - [Bounded exploration](#bounded-exploration)
  - [Manual exploration](#manual-exploration)
  - [Checking secrecy](#checking-secrecy)
  - [Checking authenticity](#checking-authenticity)
  - [Bounded verdicts](#bounded-verdicts)

# What's included in the repo?
The folder structure is shown below.

```
├── CSP_operators.thy
├── Diffie_Hellman
│   ├── DH_v1
│   │   ├── Animator_DH
│   │   ├── Animator_DH_sign
│   │   ├── DH.thy
│   │   ├── DH_animation.thy
│   │   ├── DH_message.thy
│   │   └── DH_sign.thy
│   ├── DH_v2
│   │   ├── BADH.thy
│   │   ├── DH.thy
│   │   └── DH_config.thy
│   └── DH_wbplsec_v3
│       ├── DHWJ_config.thy
│       └── DHWJ_wbplsec.thy
├── FSNat.thy
├── NSPKP
│   ├── NSPK3
│   │   ├── Animator_NSLPK3
│   │   ├── Animator_NSPK3
│   │   ├── NSPK3.thy
│   │   ├── NSPK3_animation.thy
│   │   └── NSPK3_message.thy
│   ├── NSPK3_v2
│   │   ├── NSLPK3.thy
│   │   ├── NSPK3.thy
│   │   └── NSPK3_config.thy
│   ├── NSPK3_wbplsec_v3
│   │   ├── NSWJ3_config.thy
│   │   ├── NSWJ3_wbplsec.thy
│   │   └── wbpls.drawio
│   ├── NSPK7
│   │   ├── Animator
│   │   ├── NSPK7.thy
│   │   ├── NSPK7_animation.thy
│   │   └── NSPK7_message.thy
│   └── NSPK7_v2
│       ├── NSPK7.thy
│       └── NSPK7_config.thy
├── ROOT
├── Sec_Animation.thy
└── Sec_Messages.thy
```

In general, this folder contains Isabelle/HOL theories to be used to automatically generate Haskell code for sound animation to verify security protocols. The web application lives in the sibling folder [`animation-web-ui`](../animation-web-ui/README.md).

Now, the folder contains several variants of the Needham-Schroeder Public Key Protocol (NSPK) and the Diffie–Hellman Key Exchange Protocol (DH) using the framework we are developing. These examples were developed in different stages.

## Early stage (first user-guided sound framework)
The theoretical background is presented in our SEFM2024 paper: ["User-Guided Verification of Security Protocols via Sound Animation"](https://doi.org/10.1007/978-3-031-77382-2_3).

The two variants of DH (the classic DH and DH based on digital signature) and three variants of NSPK (NSPK3, NSLPK3, and NSPK7).
+ [DH](./Diffie_Hellman/DH_v1/DH.thy)
+ [DH based on digital signature](./Diffie_Hellman/DH_v1/DH_sign.thy)
+ [NSPK3](./NSPKP/NSPK3/NSPK3.thy)
+ [NSLPK3](./NSPKP/NSPK3/NSPK3.thy)
+ [NSPK7](./NSPKP/NSPK7)

In each folder, we have one theory for the message definitions, one for animation, and one for the protocol. We also deposit the generated Haskell code inside each folder, so users do not have to re-generate them using Isabelle/HOL.

Additionally, [CSP_operators.thy](./CSP_operators.thy) contains CSP operators and processes used in the animation.

## Second stage (generic and general framework)
The theoretical background is presented in our ICFEM2025 paper: ["Formal Verification of Physical Layer Security Protocols for Next-Generation Communication Networks"](https://doi.org/10.1007/978-981-95-4213-0_1).

In general, this framework supports the following features in a same framework.
+ Parametric messages by customisable number of entities: agents, nonces, (public and private) keys, modular exponentiation bases, and bit masks,
+ Synchronous and asynchronous encryption and decryption
+ Digital signature
+ Modular exponentiation
+ A physical layer security (PLS) based on watermarking and jamming

General theories in the framework include
+ [CSP_operators.thy](./CSP_operators.thy): CSP operators and processes
+ [FSNat.thy](./FSNat.thy): finite set of natural numbers
+ [Sec_Messages.thy](./Sec_Messages.thy): message types and definitions
+ [Sec_Animation.thy](./Sec_Animation.thy): animation terminal interface, or lightweight model checker

The two variants of DH (the classic DH and DH based on digital signature) and three variants of NSPK (NSPK3, NSLPK3, and NSPK7) have been extended in this new framework, and new theory files are shown below.
+ [DH](./Diffie_Hellman/DH_v2/DH.thy)
+ [DH based on digital signature](./Diffie_Hellman/DH_v2/BADH.thy)
+ [NSPK3](./NSPKP/NSPK3_v2/NSPK3.thy)
+ [NSLPK3](./NSPKP/NSPK3_v2/NSLPK3.thy)
+ [NSPK7](./NSPKP/NSPK7_v2)

Additionally, we modelled and verified one variant of NSPK3 (NSWJ3) and one variant of DH (DHWJ) based on the PLS.
+ [DHWJ](./Diffie_Hellman/DH_wbplsec_v3/DHWJ_wbplsec.thy)
+ [NSWJ3](./NSPKP/NSPK3_wbplsec_v3/NSWJ3_wbplsec.thy)

We found DHWJ and NSWJ3 preserve confidentiality and authenticity if the PLS is properly set up (to ensure eavesdroppers within the jamming ranges of legitimate receivers, for example, through visible light communication, VLC, and reconfigurable intelligent interface, RIS, to restrict spatially within walls or direct signals) though the original NSPK3 and classic DH are subject to the man-in-the-middle attack. Our work suggests PLS can be integrated with the traditional cryptography to provide flexible and lightweight security.

### Web interface
This is under the folder [`animation-web-ui`](../animation-web-ui/README.md), which is developed using the Yesod web framework based on Haskell. See its [README](../animation-web-ui/README.md) for the setup and deployment instructions and for how its stored event trees are built from the proved exploration.

## Third stage (proven soundness)
The first two stages search the event space with hand-written Haskell functions (`simulate_cnt` and `explore_tree_cnt`) that are only trusted, not proved: nothing rules out a search that silently misses a branch of the event tree. This stage, the work on the `Soundness` branch, replaces that trusted search by a search that is defined and proved in Isabelle/HOL, so that a bounded verification result is a statement about the model rather than about the implementation of a search.

The sound exploration is in [Sec_Animation.thy](./Sec_Animation.thy):
+ `explore n mx t P` returns, for a bound of `n` visible events and `mx` internal steps, *all* traces of an ITree; it is executable and its Haskell rendering is obtained from these definitions by the code generator.
+ `btr` is the inductive characterisation of the same traces, with `explore_iff_btr` connecting the two.
+ The theorem `explore_sound` states that every explored trace is a genuine trace of the ITree, witnessed by the operational semantics `trace_to`, and respects the bound; `explore_complete` states that every genuine trace of bounded length is explored once the internal-step bound is large enough. The search therefore neither invents nor misses a trace.
+ `feasible` and `reaches` decide whether a given trace is feasible and whether a set of events can be reached under a monitor; `reaches_sound` states that a reported trace really exists in the model.
+ `checks n mx P pred` filters the exploration by a property of traces, so its result is the set of counterexamples and its verdict is the emptiness of that set. `checks_sound` guarantees that no counterexample is spurious and `checks_complete` that none is missed within the bounds. The security-relevant checks are `check_leak`, `check_leak_msg`, `check_sig`, `check_terminate`, `check_corr`, `check_corr_violation` and `check_authenticity`. Authenticity is a correspondence check on the participants, not just on the kind of signal: `matches_start` relates a completed run `EndProt s d ns nd` of two honest agents to the counterpart's earlier `StartProt d s ns nd`, and `check_auth_violation` generalises that to any such relation.
+ `state_kind` (with `skind = SContinues | STerminated | SDeadlocked | SDivergent`) classifies how a run ends, replacing the deadlock, termination and divergence reporting of the hand-written explorer. It follows a trace with an explicit fuel bound `(length tr + 1) * (mx + 1)` so that it is structurally recursive; the equations extracted to Haskell are `follow_fuel_code` and `stop_kind_code`.
+ The new Isar command `animate_sec_sound` runs this proved exploration, for example `animate_sec_sound NSPK3` in [NSPK3.thy](./NSPKP/NSPK3_v2/NSPK3.thy), alongside the first-stage `animate_sec`.

The intruder's message breakdown in [Sec_Messages.thy](./Sec_Messages.thy) is now the closure `breakl`, whose soundness and completeness are proved: `breakl_sound` (it derives only messages derivable by the breakdown rules), `breakl_complete` (it derives every derivable message), plus `breakl_extensive`, `breakl_stable` and `breakl_mono`. The protocols call `breakl` in place of the trusted `breakm`.

In short, the third stage keeps the two earlier frameworks but makes the automation they rely on, and not only the protocol models, something that has been proved correct in Isabelle/HOL.

# How to load theories in Isabelle/HOL and generate Haskell code?
[SETUP.md](./SETUP.md) records how to install the Isabelle/HOL and GHC environments; the Web UI environment is in the [animation-web-ui README](../animation-web-ui/README.md).

- Open Isabelle/jEdit

```
$   /path/to/Tools/Isabelle2025-CyPhyAssure/bin/isabelle jedit \
     -d /path/to/Animation_of_Security_Protocols/User_Guided_Verification_Security \
     -l ITree_UTP &
```

- Load the theory for a protocol such as [NSPK3.thy](./NSPKP/NSPK3/NSPK3.thy) to Isabelle/HOL

- Navigate to a line starting with `animate_sec` such as `animate_sec NSPK3`, and check the log on the "Output" tab (usually on the bottom of Isabell). Usually, it will show the log below

```
See theory exports 
Compiling animation... 
See theory exports 
Start animation
```
- This means the code generation succeeded. Now you can click "Start animation" to launch the animator and start the animation

The third stage adds the sound variant of the command, `animate_sec_sound` (for example `animate_sec_sound NSPK3` in [NSPK3.thy](./NSPKP/NSPK3_v2/NSPK3.thy)), which runs the proved bounded exploration and its checks automatically, and can also step through the animation manually one event at a time; see [Illustrations](#illustrations).

# Illustrations

The illustrations below come from the sound interface of the third stage: `animate_sec_sound` first asks for the bounds and then what to do, and every trace it prints is a trace of the search proved sound and complete in [Sec_Animation.thy](./Sec_Animation.thy). The web interface in [`animation-web-ui`](../animation-web-ui/README.md) drives the same search. Long trace lines are wrapped here to fit the page; the interface prints each trace on a single line.

## Bounded exploration

With a visible-event bound of `2` and an internal-step bound of `2`, option 1 enumerates all the traces within those bounds:

```
Sound bounded exploration / checking (search extracted from Isabelle/HOL)
Visible-event bound n (bound on the number of visible events or trace length) [3]: 2
Internal-step bound mx (bound on internal steps between visible events) [3]: 2
Which check? (5 steps through the animation manually)
  1) enumerate all traces within the bounds
  2) secrecy: traces containing a Leak event
  3) completion: traces containing a Terminate event
  4) authenticity: a completed run whose counterpart never started it
  5) manual exploration: choose one event at a time
Check [1]: 1
*** 17 traces within the bounds ***
  []
  [Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg Intruder)) (MK (Kp (Nmk (Nat 1))))))),
    Env_C (Agent (Nmk (Nat 0)),Agent (Nmk (Nat 1)))]
  [Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg Intruder)) (MK (Kp (Nmk (Nat 1))))))),
    Env_C (Agent (Nmk (Nat 0)),Intruder)]
  [Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg Intruder)) (MK (Kp (Nmk (Nat 1))))))),
    Sig_C (ClaimSecret (Agent (Nmk (Nat 1))) (Nmk (Nat 1)) (Set [Intruder]))]
```

(All 17 traces are printed; the first four are shown here.)

## Manual exploration

Option 5 is the step-by-step animation: at every state the enabled events are listed and the user chooses one by its number, and `q` stops. With bounds `4` and `3`:

```
Check [1]: 5
Events:
  (1) Env_C (Agent (Nmk (Nat 0)),Agent (Nmk (Nat 1)))
  (2) Env_C (Agent (Nmk (Nat 0)),Intruder)
  (3) Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg (Agent (Nmk (Nat 0))))) (MK (Kp (Nmk (Nat 1)))))))
  (4) Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg Intruder)) (MK (Kp (Nmk (Nat 1)))))))
[Choose: 1-4, q to quit]: 2
Chosen: Env_C (Agent (Nmk (Nat 0)),Intruder)
Events:
  (1) Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg (Agent (Nmk (Nat 0))))) (MK (Kp (Nmk (Nat 1)))))))
  (2) Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg Intruder)) (MK (Kp (Nmk (Nat 1)))))))
  (3) Sig_C (ClaimSecret (Agent (Nmk (Nat 0))) (Nmk (Nat 0)) (Set [Intruder]))
[Choose: 1-3, q to quit]: 2
Chosen: Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
  MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg Intruder)) (MK (Kp (Nmk (Nat 1)))))))
Events:
  (1) Sig_C (ClaimSecret (Agent (Nmk (Nat 1))) (Nmk (Nat 1)) (Set [Intruder]))
  (2) Sig_C (ClaimSecret (Agent (Nmk (Nat 0))) (Nmk (Nat 0)) (Set [Intruder]))
[Choose: 1-2, q to quit]: q
Manual exploration terminated.
Trace: [Env_C (Agent (Nmk (Nat 0)),Intruder),Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
  MAEnc (MPair (MNon (Nmk (Nat 2))) (MAg Intruder)) (MK (Kp (Nmk (Nat 1)))))))]
```

The user's answers are shown after the prompts. A run can also end by itself, in which case the interface reports `Terminated.`, `Deadlocked.` or `Divergent (internal-step budget exhausted).` before printing the trace.

## Checking secrecy

With bounds `12` and `5`, option 2 finds the classic NSPK3 man-in-the-middle attack, in which the intruder runs the protocol with both agents and learns agent 1's nonce. Five counterexamples are found and all of them are printed; the first is:

```
Check [1]: 2
*** 5 Leak counterexample(s) found ***
  [Env_C (Agent (Nmk (Nat 0)),Intruder),
    Sig_C (ClaimSecret (Agent (Nmk (Nat 0))) (Nmk (Nat 0)) (Set [Intruder])),
    Send_C (Agent (Nmk (Nat 0)),(Intruder,(Intruder,
    MAEnc (MPair (MNon (Nmk (Nat 0))) (MAg (Agent (Nmk (Nat 0))))) (MK (Kp (Nmk (Nat 2))))))),
    Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 0))) (MAg (Agent (Nmk (Nat 0))))) (MK (Kp (Nmk (Nat 1))))))),
    Sig_C (ClaimSecret (Agent (Nmk (Nat 1))) (Nmk (Nat 1)) (Set [Agent (Nmk (Nat 0))])),
    Sig_C (StartProt (Agent (Nmk (Nat 1))) (Agent (Nmk (Nat 0))) (Nmk (Nat 0)) (Nmk (Nat 1))),
    Send_C (Agent (Nmk (Nat 1)),(Intruder,(Agent (Nmk (Nat 0)),
    MAEnc (MPair (MNon (Nmk (Nat 0))) (MNon (Nmk (Nat 1)))) (MK (Kp (Nmk (Nat 0))))))),
    Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 0)),
    MAEnc (MPair (MNon (Nmk (Nat 0))) (MNon (Nmk (Nat 1)))) (MK (Kp (Nmk (Nat 0))))))),
    Sig_C (StartProt (Agent (Nmk (Nat 0))) Intruder (Nmk (Nat 0)) (Nmk (Nat 1))),
    Send_C (Agent (Nmk (Nat 0)),(Intruder,(Intruder,
    MAEnc (MNon (Nmk (Nat 1))) (MK (Kp (Nmk (Nat 2))))))),Recv_C (Intruder,(Intruder,
    (Agent (Nmk (Nat 1)),MAEnc (MNon (Nmk (Nat 1))) (MK (Kp (Nmk (Nat 1))))))),
    Leak_C (MNon (Nmk (Nat 1)))]
```

## Checking authenticity

Option 4 looks for the failure that the `AReach ... # ...` specifications in the theories describe: an honest agent completing a run whose counterpart never started the same session. With bounds `15` and `100`, NSPK3 has eleven such counterexamples; the first is the classic man-in-the-middle, in which agent 1 finishes a session with agent 0 although agent 0 started a session with the intruder instead:

```
Check [1]: 4
*** 11 authenticity counterexample(s) found ***
  [Env_C (Agent (Nmk (Nat 0)),Intruder),
    Sig_C (ClaimSecret (Agent (Nmk (Nat 0))) (Nmk (Nat 0)) (Set [Intruder])),
    Send_C (Agent (Nmk (Nat 0)),(Intruder,(Intruder,
    MAEnc (MPair (MNon (Nmk (Nat 0))) (MAg (Agent (Nmk (Nat 0))))) (MK (Kp (Nmk (Nat 2))))))),
    Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 1)),
    MAEnc (MPair (MNon (Nmk (Nat 0))) (MAg (Agent (Nmk (Nat 0))))) (MK (Kp (Nmk (Nat 1))))))),
    Sig_C (ClaimSecret (Agent (Nmk (Nat 1))) (Nmk (Nat 1)) (Set [Agent (Nmk (Nat 0))])),
    Sig_C (StartProt (Agent (Nmk (Nat 1))) (Agent (Nmk (Nat 0))) (Nmk (Nat 0)) (Nmk (Nat 1))),
    Send_C (Agent (Nmk (Nat 1)),(Intruder,(Agent (Nmk (Nat 0)),
    MAEnc (MPair (MNon (Nmk (Nat 0))) (MNon (Nmk (Nat 1)))) (MK (Kp (Nmk (Nat 0))))))),
    Recv_C (Intruder,(Intruder,(Agent (Nmk (Nat 0)),
    MAEnc (MPair (MNon (Nmk (Nat 0))) (MNon (Nmk (Nat 1)))) (MK (Kp (Nmk (Nat 0))))))),
    Sig_C (StartProt (Agent (Nmk (Nat 0))) Intruder (Nmk (Nat 0)) (Nmk (Nat 1))),
    Send_C (Agent (Nmk (Nat 0)),(Intruder,(Intruder,
    MAEnc (MNon (Nmk (Nat 1))) (MK (Kp (Nmk (Nat 2))))))),Recv_C (Intruder,(Intruder,
    (Agent (Nmk (Nat 1)),MAEnc (MNon (Nmk (Nat 1))) (MK (Kp (Nmk (Nat 1))))))),
    Leak_C (MNon (Nmk (Nat 1))),
    Sig_C (EndProt (Agent (Nmk (Nat 0))) Intruder (Nmk (Nat 0)) (Nmk (Nat 1))),
    Sig_C (EndProt (Agent (Nmk (Nat 1))) (Agent (Nmk (Nat 0))) (Nmk (Nat 0)) (Nmk (Nat 1)))]
```

(All eleven are printed; the first is shown here. The same check on NSLPK3, Lowe's fix, reports no authenticity counterexample at these bounds.)

## Bounded verdicts

A check that reports nothing is a *bounded* negative result: there is no counterexample within the bounds, but one may still exist beyond them. With bounds `12` and `5`:

```
Check [1]: 3
No Terminate counterexample within the bounds.
```
