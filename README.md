**User-Guided Verification of Security Protocols via Sound Animation**

This repository contains our work on using sound animation — automatically generated from Isabelle/HOL — to verify security protocols. It holds the Isabelle/HOL theories and the generated Haskell animators for several Needham-Schroeder Public Key (NSPK) and Diffie–Hellman (DH) protocol variants, plus the web application used to drive the animation.

Two papers describe the theory behind this repository:

- **SEFM 2024**: ["User-Guided Verification of Security Protocols via Sound Animation"](https://doi.org/10.1007/978-3-031-77382-2_3) — the first user-guided sound framework.
- **ICFEM 2025**: ["Formal Verification of Physical Layer Security Protocols for Next-Generation Communication Networks"](https://doi.org/10.1007/978-981-95-4213-0_1) — the generic framework, including a physical layer security (PLS) based on watermarking and jamming.

The repository contains two components, each documented by its own README:

- [`User_Guided_Verification_Security`](./User_Guided_Verification_Security/README.md): the Isabelle/HOL theories, the protocol variants, and the generated animators, together with the setup instructions for loading the theories in Isabelle/HOL, generating Haskell code, and running the animators.
- [`animation-web-ui`](./animation-web-ui/README.md): the animation web interface, implemented with the Yesod web framework in Haskell.
