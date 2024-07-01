**User-Guided Verification of Security Protocols via Sound Animation**

This repository contains our work to use sound animation (automatically generated from Isabelle/HOL) to verify security protocols.

- [What's included in the repo?](#whats-included-in-the-repo)
- [How to load theories in Isabelle/HOL and generate Haskell code?](#how-to-load-theories-in-isabellehol-and-generate-haskell-code)
- [How to run animators](#how-to-run-animators)


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

