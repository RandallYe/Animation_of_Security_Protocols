# Development environment setup

Notes on setting up the Isabelle/HOL and GHC development environment for this folder. The Web UI and PlantUML server setup is in the [`animation-web-ui` README](../animation-web-ui/README.md). The notes were originally kept next to the theories in the older `Protocols/` checkout; the paths below are for this repository.

## Isabelle/HOL

1. Download `Isabelle2025-CyPhyAssure` from [Isabelle/UTP](https://isabelle-utp.york.ac.uk/download).
2. Start Isabelle/jEdit with this folder on the load path:
   ```
   /path/to/Tools/Isabelle2025-CyPhyAssure/bin/isabelle jedit \
     -d /path/to/Animation_of_Security_Protocols/User_Guided_Verification_Security \
     -l ITree_UTP &
   ```
   Replace `/path/to` with the paths on your machine.
3. Install texlive as well.
4. In the Isabelle installation, comment out the call to `prism_chanrep_proofs` in `compile_chantype`, in
   `/path/to/Tools/Isabelle2025-CyPhyAssure/src/CyPhyAssure/Optics/Channel_Type.ML`, so that the `chantyperep_instance` step is the last one performed.

   ```diff
   diff --git a/Channel_Type.ML b/Channel_Type.ML
   index b7c4f3f..ff803fe 100644
   --- a/Channel_Type.ML
   +++ b/Channel_Type.ML
   @@ -206,9 +206,9 @@ fun compile_chantype ((raw_tvars, name), raw_chans) thy =
      in
      (make_chantype (map (fst o snd) raw_tvars) sorts name raw_chans #>
      (* Generate chantyperep instance *)
   -  chantyperep_instance (map (fst o snd) raw_tvars) tvars sorts name raw_chans #>
   +  chantyperep_instance (map (fst o snd) raw_tvars) tvars sorts name raw_chans (* #>
      (* Generate representations for each prism (channel) *)
   -  prism_chanrep_proofs (name, raw_chans)) thy
   +  prism_chanrep_proofs (name, raw_chans)*) ) thy
      end

    End;
   ```

   The change works around a failure of the prism representation proofs: without it, loading the
   `chantype` declaration at [Sec_Messages.thy:1887](./Sec_Messages.thy#L1887) fails with

   ```
   Tactic failed
   The error(s) above occurred for the goal statement:
   has_chanrep send
   ```

## GHC and the animators

5. Install GHC using [ghcup](https://www.haskell.org/ghcup/).
6. Install the libraries into `.ghc`:

   ```
   $ cabal install --lib pretty-show random
   ```
   Without them, compiling `Simulate.hs` fails:

   ```
   Simulate.hs:15:1: error: [GHC-87110]
       Could not find module 'Text.Show.Pretty'.
       Use -v to see a list of the files searched for.
      |
   15 | import Text.Show.Pretty;
      | ^^^^^^^^^^^^^^^^^^^^^^^^

   Simulate.hs:27:1: error: [GHC-87110]
       Could not find module 'System.Random.Stateful'.
       Use -v to see a list of the files searched for.
      |
   27 | import System.Random.Stateful;
      |
   ```
7. If linking fails for want of GMP:
   ```
   /usr/bin/x86_64-linux-gnu-ld.bfd: cannot find -lgmp: No such file or directory
   collect2: error: ld returned 1 exit status
   `gcc' failed in phase `Linker'. (Exit code: 1)
   ```

Then install `libgmp-dev`

   ```
   $ sudo apt update
   $ sudo apt install libgmp-dev
   ```

8. Also install `text`:
   ```
   $ cabal install text --lib
   ```
