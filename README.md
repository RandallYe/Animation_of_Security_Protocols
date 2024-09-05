**User-Guided Verification of Security Protocols via Sound Animation**

This repository contains our work to use sound animation (automatically generated from Isabelle/HOL) to verify security protocols.

- [What's included in the repo?](#whats-included-in-the-repo)
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
│   ├── Animator_DH
│   ├── Animator_DH_sign
│   ├── DH.thy
│   ├── DH_animation.thy
│   ├── DH_message.thy
│   └── DH_sign.thy
├── LICENSE
├── NSPK
│   ├── NSPK3
│   │   ├── Animator_NSLPK3
│   │   ├── Animator_NSPK3
│   │   ├── NSPK3.thy
│   │   ├── NSPK3_animation.thy
│   │   └── NSPK3_message.thy
│   └── NSPK7
│   │   ├── Animator
│       ├── NSPK7.thy
│       ├── NSPK7_animation.thy
│       └── NSPK7_message.thy
```

In general, this repository contains Isabelle/HOL theories to animate the Needham-Schroeder Public Key Protocol and the Diffie–Hellman Key Exchange Protocol using the framework we are developing. In each folder, we have one theory for the message definitions, one for animation, and one for the protocol. We also deposit the generated Haskell code inside each folder, so users do not have to re-generate them using Isabelle/HOL.

Additionally, [CSP_operators.thy](./CSP_operators.thy) contains CSP operators and processes used in the animation. 

# How to load theories in Isabelle/HOL and generate Haskell code?
- Step 1: install the patched Isabelle/HOL from the [Isabelle/UTP website](https://isabelle-utp.york.ac.uk/download) to get it ready for the development using Isabelle/UTP
- Step 2: run `$ ./bin/isabelle jedit -l Z_Machines` inside the installed Isabelle/HOL
- Step 3: load the theory for the protocols such as [NSPK3.thy](./NSPK/NSPK3/NSPK3.thy) to Isabelle/HOL
- Step 4: navigate to a line starting with `animate_sec` such as ` animate_sec NSPK3`, and check the log on the "Output" tab (usually on the bottom of Isabell). Usually, it will show the log below
```
See theory exports 
Compiling animation... 
See theory exports 
Start animation
```
- Step 5: this means the code generation succeeded. Now you can click "Start animation" to launch the animator and start the animation

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

