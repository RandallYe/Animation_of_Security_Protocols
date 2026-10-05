# User-Guided Verification of Security Protocols via Sound Animation

This folder contains the Isabelle/HOL theories from which sound animators for security protocols are generated, together with the generated Haskell animators. Everything here belongs to the repository [Animation_of_Security_Protocols](../README.md); see the [top-level README](../README.md) for the overview and the papers.

- [What's included in the repo?](#whats-included-in-the-repo)
  - [Early stage (first user-guided sound framework)](#early-stage-first-user-guided-sound-framework)
  - [Second stage (generic and general framework)](#second-stage-generic-and-general-framework)
    - [Web interface](#web-interface)
  - [Third stage (proven soundness)](#third-stage-proven-soundness)
- [How to load theories in Isabelle/HOL and generate Haskell code?](#how-to-load-theories-in-isabellehol-and-generate-haskell-code)
- [How to run animators](#how-to-run-animators)
- [Illustrations](#illustrations)
  - [Manual exploration](#manual-exploration)
  - [User-guided verification (manual + automatic)](#user-guided-verification-manual--automatic)

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
+ `checks n mx P pred` filters the exploration by a property of traces, so its result is the set of counterexamples and its verdict is the emptiness of that set. `checks_sound` guarantees that no counterexample is spurious and `checks_complete` that none is missed within the bounds. The security-relevant checks are `check_leak`, `check_leak_msg`, `check_sig`, `check_terminate`, `check_corr`, `check_corr_violation` and `check_authenticity` (secrecy and authenticity are phrased as the presence or absence of a monitor event before a reachability event).
+ `state_kind` (with `skind = SContinues | STerminated | SDeadlocked | SDivergent`) classifies how a run ends, replacing the deadlock, termination and divergence reporting of the hand-written explorer. It follows a trace with an explicit fuel bound `(length tr + 1) * (mx + 1)` so that it is structurally recursive; the equations extracted to Haskell are `follow_fuel_code` and `stop_kind_code`.
+ The new Isar command `animate_sec_sound` runs this proved exploration, for example `animate_sec_sound NSPK3` in [NSPK3.thy](./NSPKP/NSPK3_v2/NSPK3.thy), alongside the first-stage `animate_sec`.

The intruder's message breakdown in [Sec_Messages.thy](./Sec_Messages.thy) is now the closure `breakl`, whose soundness and completeness are proved: `breakl_sound` (it derives only messages derivable by the breakdown rules), `breakl_complete` (it derives every derivable message), plus `breakl_extensive`, `breakl_stable` and `breakl_mono`. The protocols call `breakl` in place of the trusted `breakm`.

In short, the third stage keeps the two earlier frameworks but makes the automation they rely on, and not only the protocol models, something that has been proved correct in Isabelle/HOL.

# How to load theories in Isabelle/HOL and generate Haskell code?
[SETUP.md](./SETUP.md) records how to install the Isabelle/HOL and GHC environments; the Web UI environment is in the [animation-web-ui README](../animation-web-ui/README.md).

- Step 1: install the patched Isabelle/HOL from the [Isabelle/UTP website](https://isabelle-utp.york.ac.uk/download) to get it ready for the development using Isabelle/UTP
- Step 2: run `$ ./bin/isabelle jedit -l Z_Machines` inside the installed Isabelle/HOL
- Step 3: load the theory for the protocols such as [NSPK3.thy](./NSPKP/NSPK3/NSPK3.thy) to Isabelle/HOL
- Step 4: navigate to a line starting with `animate_sec` such as `animate_sec NSPK3`, and check the log on the "Output" tab (usually on the bottom of Isabell). Usually, it will show the log below
```
See theory exports 
Compiling animation... 
See theory exports 
Start animation
```
- Step 5: this means the code generation succeeded. Now you can click "Start animation" to launch the animator and start the animation

The third stage adds the sound variant of the command, `animate_sec_sound` (for example `animate_sec_sound NSPK3` in [NSPK3.thy](./NSPKP/NSPK3_v2/NSPK3.thy)), which explores the animation soundly and automatically rather than interacting with it manually.

# How to run animators
Alternatively, you don't need the Isabelle/HOL to just run the animator. You need the [GHC](https://www.haskell.org/ghc/) compiler to compile Haskell code.

The folder if its name starts with "Animator", this folder contains the Haskell code for the animation. You can compile it using the `ghc` command, or debug it using the `ghci` command, shown below.

```
$ ghc Simulation.hs
$ ghci Simulation.hs
$ ./Simulation
```

# Illustrations

## Manual exploration

```
Starting ITree Animation...
Events:
 (1) Env [Alice] Bob;
 (2) Env [Alice] Intruder;
 (3) Recv [Bob<=Intruder] {<N Intruder, Alice>}_PK Bob;
 (4) Recv [Bob<=Intruder] {<N Intruder, Intruder>}_PK Bob;

[Choose: 1-4]: 1
Env_C (Alice,Bob)
Events:
 (1) Recv [Bob<=Intruder] {<N Intruder, Alice>}_PK Bob;
 (2) Recv [Bob<=Intruder] {<N Intruder, Intruder>}_PK Bob;
 (3) Sig ClaimSecret Alice (N Alice) (Set [ Bob ]);

[Choose: 1-3]: 3
Sig_C (ClaimSecret Alice (N Alice) (Set [Bob]))
Events:
 (1) Send [Alice=>Intruder] {<N Alice, Alice>}_PK Bob;
 (2) Recv [Bob<=Intruder] {<N Intruder, Alice>}_PK Bob;
 (3) Recv [Bob<=Intruder] {<N Intruder, Intruder>}_PK Bob;

[Choose: 1-3]: 1
Send_C (Alice,(Intruder,MEnc (MCmp (MNon (N Alice)) (MAg Alice)) (PK Bob)))
Events:
 (1) Recv [Bob<=Intruder] {<N Alice, Alice>}_PK Bob;
 (2) Recv [Bob<=Intruder] {<N Intruder, Alice>}_PK Bob;
 (3) Recv [Bob<=Intruder] {<N Intruder, Intruder>}_PK Bob;

[Choose: 1-3]: 1
Recv_C (Intruder,(Bob,MEnc (MCmp (MNon (N Alice)) (MAg Alice)) (PK Bob)))
Events:
 (1) Sig ClaimSecret Bob (N Bob) (Set [ Alice ]);

[Choose: 1-1]:
Sig_C (ClaimSecret Bob (N Bob) (Set [Alice]))
Events:
 (1) Sig StartProt Bob Alice (N Alice) (N Bob);

[Choose: 1-1]:
Sig_C (StartProt Bob Alice (N Alice) (N Bob))
Events:
 (1) Send [Bob=>Intruder] {<N Alice, N Bob>}_PK Alice;

[Choose: 1-1]:
Send_C (Bob,(Intruder,MEnc (MCmp (MNon (N Alice)) (MNon (N Bob))) (PK Alice)))
Events:
 (1) Recv [Alice<=Intruder] {<N Alice, N Bob>}_PK Alice;

[Choose: 1-1]:
Recv_C (Intruder,(Alice,MEnc (MCmp (MNon (N Alice)) (MNon (N Bob))) (PK Alice)))
Events:
 (1) Sig StartProt Alice Bob (N Alice) (N Bob);

[Choose: 1-1]:
Sig_C (StartProt Alice Bob (N Alice) (N Bob))
Events:
 (1) Send [Alice=>Intruder] {N Bob}_PK Bob;

[Choose: 1-1]:
Send_C (Alice,(Intruder,MEnc (MNon (N Bob)) (PK Bob)))
Events:
 (1) Sig EndProt Alice Bob (N Alice) (N Bob);
 (2) Recv [Bob<=Intruder] {N Bob}_PK Bob;

[Choose: 1-2]: 1
Sig_C (EndProt Alice Bob (N Alice) (N Bob))
Events:
 (1) Recv [Bob<=Intruder] {N Bob}_PK Bob;

[Choose: 1-1]: 1
Recv_C (Intruder,(Bob,MEnc (MNon (N Bob)) (PK Bob)))
Events:
 (1) Sig EndProt Bob Alice (N Alice) (N Bob);

[Choose: 1-1]:
Sig_C (EndProt Bob Alice (N Alice) (N Bob))
Events:
 (1) Terminate;

[Choose: 1-1]:
Terminate_C ()
Successfully Terminated: ()
Trace: [Env [Alice] Bob, 
    Sig ClaimSecret Alice (N Alice) (Set [ Bob ]), 
    Send [Alice=>Intruder] {<N Alice, Alice>}_PK Bob, 
    Recv [Bob<=Intruder] {<N Alice, Alice>}_PK Bob, 
    Sig ClaimSecret Bob (N Bob) (Set [ Alice ]), 
    Sig StartProt Bob Alice (N Alice) (N Bob), 
    Send [Bob=>Intruder] {<N Alice, N Bob>}_PK Alice, 
    Recv [Alice<=Intruder] {<N Alice, N Bob>}_PK Alice, 
    Sig StartProt Alice Bob (N Alice) (N Bob), 
    Send [Alice=>Intruder] {N Bob}_PK Bob, 
    Sig EndProt Alice Bob (N Alice) (N Bob), 
    Recv [Bob<=Intruder] {N Bob}_PK Bob, 
    Sig EndProt Bob Alice (N Alice) (N Bob), 
    Terminate, 
]
```

## User-guided verification (manual + automatic)

```
Starting ITree Animation...
Events:
 (1) Env [Alice] Bob;
 (2) Env [Alice] Intruder;
 (3) Recv [Bob<=Intruder] {<N Intruder, Alice>}_PK Bob;
 (4) Recv [Bob<=Intruder] {<N Intruder, Intruder>}_PK Bob;

[Choose: 1-4]: 2
Env_C (Alice,Intruder)
Events:
 (1) Recv [Bob<=Intruder] {<N Intruder, Alice>}_PK Bob;
 (2) Recv [Bob<=Intruder] {<N Intruder, Intruder>}_PK Bob;
 (3) Sig ClaimSecret Alice (N Alice) (Set [ Intruder ]);

[Choose: 1-3]: 3
Sig_C (ClaimSecret Alice (N Alice) (Set [Intruder]))
Events:
 (1) Send [Alice=>Intruder] {<N Alice, Alice>}_PK Intruder;
 (2) Recv [Bob<=Intruder] {<N Intruder, Alice>}_PK Bob;
 (3) Recv [Bob<=Intruder] {<N Intruder, Intruder>}_PK Bob;

[Choose: 1-3]: AReach 15 %Leak N Bob%
AReach 15,  %Leak N Bob%
Reachability by Auto: 15
  Events for reachability check: ["Leak N Bob"]
  Events for monitor: []
..........................................................................................
*** These events ["Leak N Bob"] are reached! ***
Trace: [Env [Alice] Intruder, 
    Sig ClaimSecret Alice (N Alice) (Set [ Intruder ]),
    Send [Alice=>Intruder] {<N Alice, Alice>}_PK Intruder, 
    Recv [Bob<=Intruder] {<N Alice, Alice>}_PK Bob, 
    Sig ClaimSecret Bob (N Bob) (Set [ Alice ]), 
    Sig StartProt Bob Alice (N Alice) (N Bob), 
    Send [Bob=>Intruder] {<N Alice, N Bob>}_PK Alice, 
    Recv [Alice<=Intruder] {<N Alice, N Bob>}_PK Alice, 
    Sig StartProt Alice Intruder (N Alice) (N Bob), 
    Send [Alice=>Intruder] {N Bob}_PK Intruder, 
]
```
