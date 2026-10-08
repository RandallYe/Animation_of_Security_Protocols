# Regenerating the animator packages from Isabelle

The three vendored packages under `src/` (`nspk3-animator`, `nswj3-animator`,
`dhwj-animator`) contain Haskell generated from the Isabelle/HOL theories plus
two hand-written modules:

* `Simulate.hs` — quoted verbatim from `generate_file` in
  `User_Guided_Verification_Security/Sec_Animation.thy`
* `*_Animate.hs` — the small wrapper that the Yesod handlers import

They are **not** produced by `stack build`; they have to be regenerated from
Isabelle whenever the theories change.  This file records the procedure.

## Automated

`./regen-animators.sh` does the whole procedure for all three families:

```
./regen-animators.sh            # generate + install + verify (the default)
./regen-animators.sh generate   # Isabelle -> Haskell only
./regen-animators.sh install    # patch + copy into src/*-animator/src
./regen-animators.sh verify     # typecheck each package with GHC 9.2.8
./regen-animators.sh --pkg nswj3            # one family
./regen-animators.sh --help
```

It is modelled on `User_Guided_Verification_Security/Check_Automation/run_check.sh`:
the scratch session and a cached Isabelle user home live in
`animation-web-ui/regeneration/regen-work/` (git-ignored), which is seeded from `~/.isabelle`
on the first run so the expensive interaction-tree heaps are reused.  The
sections below describe what it does and how to do it by hand.

As of the sound-exploration work, a regenerated package also contains
`Sec_Animation.hs`, which exports the Isabelle-proved bounded exploration and
its checks:

```
explore, budget_hit, checks, feasible, reaches,
is_leak, is_sig, is_start, is_end, is_terminate,
check_leak, check_leak_msg, check_sig, check_terminate,
check_corr, check_corr_violation, check_authenticity
```

`*_Animate.hs` re-exports these, so handlers can use the proved search instead
of the hand-written `explore_tree_cnt`.

## 1. Export the modules

Create a throw-away session that imports the protocol theories and exports both
the models and the proved search.  For NSPK3/NSLPK3 the session is:

```
# regen/ROOT
session "ExportAnimator" in "src" = "ITree_Security" +
  options [document = false, timeout = 3600]
  sessions
    "ITree_Simulation"
  theories
    NSPK3_config
    NSPK3
    NSLPK3
    Export
```

with `src/` holding copies of `NSPK3_config.thy`, `NSPK3.thy`, `NSLPK3.thy`
taken from `User_Guided_Verification_Security/NSPKP/NSPK3_v2/`, **with their
`animate_sec` / `animate_sec_sound` command lines removed** (the commands export
and run a terminal driver, which we do not want here).  `src/Export.thy` is:

```isabelle
theory Export
  imports NSPK3 NSLPK3
begin

ML \<open>
let
  val ctx = @{context}
  val thy = Proof_Context.theory_of ctx
  val cs = map (Code.read_const thy)
    ["NSPK3", "NSLPK3", "explore", "budget_hit", "feasible", "reaches", "checks",
     "check_leak", "check_leak_msg", "check_sig", "check_terminate", "check_corr",
     "check_corr_violation", "check_authenticity",
     (* not reachable from the check_* definitions, but imported by the wrappers *)
     "is_start", "is_end", "state_kind"]
  val out = Path.explode "<absolute path>/out"
  val _ = Code_Target.export_code true cs
    [((("Haskell", ""), SOME ({physical = true}, (out, Position.none))),
      (Token.explode (Thy_Header.get_keywords' ctx) Position.none "string_classes"))]
    (Named_Target.theory_init thy)
in () end
\<close>

end
```

Build it:

```
USER_HOME=$PWD/.isabelle-home \
  ~/Tools/Isabelle2025-CyPhyAssure/bin/isabelle build \
  -d regen -d User_Guided_Verification_Security -o document=false ExportAnimator
```

Note the constant names are the **Isabelle** names (`NSPK3`, `NSLPK3`); the code
generator lower-cases the first letter to obtain the Haskell names `nSPK3`,
`nSLPK3`.

The list must also contain `is_start`, `is_end` and `state_kind`: they are *not*
reachable from the `check_*` definitions, but `NSPK3_Animate.hs` imports
`is_start`/`is_end`, and every wrapper uses `state_kind` — with `Skind`,
`follow_fuel` and `stop_kind`, which come along with it — to label the leaves of
the tree.  Omitting them yields a `Sec_Animation.hs` that the hand-written
wrappers cannot compile against.

Everything else is the list used by `sound_simulate` in `Sec_Animation.thy`, so
keep the two in step when that list changes — `budget_hit`, for instance, is the
predicate the sound driver uses to warn that the internal-step budget cut the
exploration short.

The same session shape works for the other two packages: import
`NSWJ3_wbplsec` (with `NSWJ3_config`) or `DHWJ_wbplsec` (with `DHWJ_config`) and
export `NSWJ3_active_eve1..4` / `DHWJ_active_eve1..4` instead of `NSPK3`,
`NSLPK3`.

If the repository's `ITree_Security` session is not already built, it is easier
to define a local one in the throw-away ROOT — pointing at the same theory
directory — than to build it through
`User_Guided_Verification_Security/ROOT`, which also pulls in the AFP
`Datatype_Order_Generator` session:

```
session "ITree_Security" in "../User_Guided_Verification_Security" = "ITree_UTP" +
  options [document = false, timeout = 7200]
  theories
    FSNat
    CSP_operators
    Sec_Messages
    Sec_Animation
```

and then build with just `-d regen`.

## 2. Assemble the package

```
# generated modules
cp out/*.hs animation-web-ui/src/nspk3-animator/src/
# hand-written simulator, taken from the theory's generate_file block
extract Simulate.hs  -> animation-web-ui/src/nspk3-animator/src/Simulate.hs
```

Two small adaptations are currently required:

1. **`Data.Bits`.** The current generator emits
   `import Data.Bits ((.&.), (.|.), (.^.));` in every module.  `(.^.)` only
   exists from `base-4.17` onwards, but this project's `stack.yaml` pins
   `lts-20.26` (GHC 9.2.8, `base-4.16`).  The operator is imported but never
   used, so drop it:

   ```
   sed -i 's/import Data.Bits ((\.\&\.), (\.|\.), (\.\^\.));/import Data.Bits ((.\&.), (.|.));/' src/*.hs
   ```

   (Upgrading the resolver to GHC >= 9.6 would remove the need for this patch.)

2. **`NSPK3_Animate.hs`.**  Remove the unused `Pfun` constructors from the
   `Interaction_Trees` import — the current generator keeps `Pfun` in
   `Interaction_Trees` (as this export does), so the import is simply
   unnecessary.

## 3. Verify

The package must typecheck with the snapshot's GHC, not the system one:

```
PKGDB=~/.stack/snapshots/x86_64-linux/*/9.2.8/pkgdb
~/.ghcup/ghc/9.2.8/bin/ghc -fno-code -package-db $PKGDB \
  -package pretty-show -package random -package text \
  animation-web-ui/src/nspk3-animator/src/NSPK3_Animate.hs
```

`stack build` needs a writable `~/.stack`; use `stack build nspk3-animator`
where that is available.

Check that the package exports the proved search and that the channel equality
instance came along (it is needed by `explore`):

```
grep -c '^explore ::'      animation-web-ui/src/nspk3-animator/src/Sec_Animation.hs
grep -c 'Eq (Chan'         animation-web-ui/src/nspk3-animator/src/Sec_Messages.hs
```

## Status

All three animator packages are regenerated from the current toolchain and build
with the web UI's GHC 9.2.8:

| package | models | sound tree builder |
|---|---|---|
| `nspk3-animator` | NSPK3, NSLPK3 | `explore_tree_NSPK3`, `explore_tree_NSLPK3` |
| `nswj3-animator` | NSWJ3 (Eve1..Eve4) | `explore_tree_NSWJ3` |
| `dhwj-animator` | DHWJ (Eve1..Eve4) | `explore_tree_DHWJ` |

For each one it was checked that the root-to-node paths of the built tree are
exactly the traces of `explore`:

```
NSPK3   n=5 mx=3   225 traces   226 nodes   equal
NSLPK3  n=6 mx=3   436 traces   437 nodes   equal
NSWJ3 Eve1 n=4 mx=3   8 traces     9 nodes   equal
DHWJ  Eve1 n=4 mx=3 183 traces   184 nodes   equal
```

### Per-animator notes

* **Extra constants for `app/Main.hs`.**  The demo executable of
  `nswj3-animator` uses `nSWJ3_active_eve1` and that of `dhwj-animator` uses
  `dHWJ_active_eve4`, so those definitions have to be in the export list
  (`NSWJ3_active_eve1..4`, `DHWJ_active_eve1..4`); exporting only the `*_active`
  function is not enough, since the code generator prunes everything the
  exported constants do not mention.
* **`equal_deve` is gone.**  The older generated `NSWJ3_config`/`DHWJ_config`
  modules exported `equal_deve`, which the hand-written wrappers used for an
  orphan `instance Eq Deve`, and which the handlers imported (without using it).
  The current generator does not produce it, so the wrappers now say
  `{-# LANGUAGE StandaloneDeriving #-}` + `deriving instance Eq Deve`, and
  `Handler/AnimateNSWJ3.hs` / `Handler/AnimateDHWJ.hs` import only `Deve(..)`.
* **`{}` and `Data.Bits`.**  The `Data.Bits ((.^.), ...)` patch described above
  applies to every regenerated package, and the wrappers need
  `nat_of_integer` / `secSetToList` exported from `Sec_Animation` and the local
  `Set` module respectively (they are re-exported by each `*_Animate` wrapper so
  the handlers do not have to disambiguate the four `Arith`/`Set` modules).

## Filling the database with the sound exploration

The database is kept: it is built once and then serves any number of concurrent
sessions, whereas an on-demand exploration is slow.  What changes is only *which*
explorer fills it.  `explore_tree_NSPK3` and `explore_tree_NSLPK3` in
`NSPK3_Animate.hs` no longer call the hand-written `explore_tree_cnt`; they build
the event tree from the traces of the proved bounded exploration:

```haskell
explore_tree_NSPK3 steps tau_steps = soundTree (soundTraces nSPK3 steps tau_steps)

soundTraces p steps tau_steps =
  filter (not . null)
    (secSetToList (explore (nat_of_integer (fromIntegral steps))
                           (nat_of_integer (fromIntegral tau_steps))
                           (nat_of_integer (fromIntegral tau_steps)) p))

soundTree trs = ETNode (TEP 0 0 Root) (soundForest 1 trs)

soundForest d trs =
  [ ETNode (TEP d i (EChan (head (head g)))) (soundForest (d + 1) (map tail g))
  | (i, g) <- zip [1..] groups ]
  where
    groups = List.groupBy (\x y -> show (head x) == show (head y))
               (List.sortBy (\x y -> compare (show (head x)) (show (head y)))
                  (filter (not . null) trs))
```

The handler is untouched: `initInsertEventTreeToDB` still calls
`explore_tree_NSPK3 depth internal_depth` and flattens the result into the
`NSPK3Trees` rows, manual navigation still walks the rows by parent, and the
automatic check still DFS-es the stored tree.  The only difference is that the
stored tree is now exactly the proved exploration.  This was checked directly:
the root-to-node paths of the built tree equal the traces of `explore` (at
`steps = 5, tau_steps = 3`: 225 traces, 226 nodes including the root, identical
path sets).

Node positions are assigned canonically -- `TEP depth number event`, the number
being the sibling's position in the order of the shown events -- because the
trace set, unlike the pfun alist, has no intrinsic order.

### Per-protocol bounds (measured)

`event-tree-depth` is the visible-event bound `n` (the tree depth) and
`event-tree-internal-depth` is the internal-step (`Sil`) budget `mx`, which is
reset after every visible event.  The cost is driven by how many traces the
model has, and that differs by orders of magnitude between protocols, so the
the bounds are set here, uniformly for every protocol:

```yaml
event-tree-depth: 15            # fallback defaults
event-tree-internal-depth: 100

event-tree-bounds:              # protocol -> [depth, internal-depth]
  nspk3: [15, 100]
  nslpk3: [15, 100]
  nswj3: [15, 100]
  dhwj: [15, 100]
```

The bounds are now uniform, 15 visible events and 100 internal steps for every
protocol; a smaller `mx` can cut the exploration short, and the interface then
warns and asks for a larger value.  The measurements below explain why `mx` is
cheap and depth is not.

`Settings.hs` reads the map into `appEventTreeBounds :: Map Text (Int, Int)` and
`Handler/Common.hs` exposes

```haskell
getEventTreeDepthFor :: Text -> Handler (Int, Int)
```

which falls back to the two defaults when a protocol has no entry.  Each handler
passes its own tag, e.g. `getEventTreeDepthFor "nswj3"` in `AnimateNSWJ3.hs`.

Measured single explorations (GHC 9.2.8, `-O0`):

| model | n | mx | traces | time |
|---|---|---|---|---|
| nspk3 | 20 | 100 | 14 214 | ~95 s (saturates at n = 15) |
| nslpk3 | 20 | 100 | 14 162 | ~98 s (saturates) |
| nswj3 | 20 | 100 | -- | **does not finish in 25 minutes** |
| nswj3 | 12 | 5 | 6 919 | ~157 s |
| nswj3 | 10 | 5 | 2 329 | ~18 s |
| dhwj | 20 | 100 | 16 694 | ~292 s |
| dhwj | 12 | 5 | 10 966 | ~75 s |

Two conclusions.

* **Only the depth costs.**  For every model measured, `mx = 3` and `mx = 100`
  give identical trace sets at the same depth (NSWJ3 at 12/3 and 12/5 are both
  6 919 traces, ~151 s vs ~157 s), because the exploration stops as soon as it
  reaches a visible event.  `mx` still matters for *completeness*: `mx = 0`
  collapses NSPK3's exploration to 11 traces.
* **Saturation is model-specific.**  NSPK3 and NSLPK3 saturate, so extra depth
  is free for them; DHWJ is nearly saturated by n = 12; NSWJ3 keeps growing, so
  its depth must be capped.  Hence the per-protocol bounds.

To re-measure a protocol:

```haskell
-- bounds.hs: ghc -O0 -i<animator-src> bounds.hs -- then ./bounds <n> <mx>
import Prelude
import qualified Prelude as P
import System.Environment (getArgs)
import Control.Exception (evaluate)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import NSPK3_Animate (explore, secSetToList)
import NSPK3 (nSPK3)
import Arith (nat_of_integer)

main :: P.IO ()
main = do
  (n : mx : _) <- map read P.<$> getArgs
  t0 <- getCurrentTime
  let k = P.length (secSetToList (explore (nat_of_integer n) (nat_of_integer mx)
                                          (nat_of_integer mx) nSPK3))
  _ <- evaluate k
  t1 <- getCurrentTime
  P.putStrLn (P.show k P.++ " traces in " P.++ P.show (diffUTCTime t1 t0))
```

A fresh database build costs one exploration, so the **first** visit to a page
pays the time in the table above; afterwards the stored tree serves every
session.  The app logs `initInsertEventTreeToDB` at startup, so the real build
time with a production `-O2` build can be read off there.

### Leaf labels: the proved `state_kind` oracle

The proved traces record visible events only, so on their own they cannot say
whether a run finished, deadlocked or diverged.  `Sec_Animation.thy` therefore
defines a small oracle:

```isabelle
datatype skind = SContinues | STerminated | SDeadlocked | SDivergent

fun follow_fuel :: "nat => nat => nat => ('e,'s) itree => 'e list => ('e,'s) itree"
fun stop_kind   :: "nat => ('e,'s) itree => skind"
definition state_kind :: "nat => ('e,'s) itree => 'e list => skind"
```

`follow_fuel` follows a trace, spending at most `mx` internal steps between
visible events (the fuel bound `(length tr + 1) * (mx + 1)` always suffices, so
the definition is structurally recursive); `stop_kind` then classifies the state
that was reached.  The equations are the ones of the hand-written explorer:
empty domain means `SDeadlocked`, an exhausted internal budget `SDivergent`, a
`Ret` `STerminated`, anything else `SContinues`.  `state_kind_Terminated`,
`state_kind_Deadlocked` and `state_kind_Divergent` record the base cases.

The code generator cannot match on `nat` (it is an opaque type), so the extracted
Haskell uses the arithmetic equations `follow_fuel_code` and `stop_kind_code`
with `declare ... [code del]` on the pattern equations -- the same trick as for
`explore`.

Each `*_Animate` wrapper uses it to append a label node to every node whose run
stops there:

```haskell
kindChildren = case state_kind (nat_of_integer (fromIntegral tau)) p prefix of
  SContinues  -> []
  STerminated -> [ETNode (TEP (d + 1) 0 Terminated) []]
  SDeadlocked -> [ETNode (TEP (d + 1) 0 Deadlocked) []]
  SDivergent  -> [ETNode (TEP (d + 1) 0 Divergent) []]
```

so the stored tree again offers `Deadlocked`, `Terminated` and `Divergent` as
selectable events, and the automatic check can look for them.  Verified on
NSPK3, where the labels appear exactly where runs stop:

| n | mx | nodes | labels | visible paths vs proved traces |
|---|---|---|---|---|
| 5 | 3 | 226 | none (no run stops that early) | 225 = 225 |
| 10 | 5 | 4160 | 119 `Deadlocked` | 4040 = 4040 |
| 12 | 5 | 9490 | 519 `Deadlocked` | 8970 = 8970 |

The visible-event paths are unaffected by the labels, so the soundness of the
stored traces is unchanged.

#### Atomic builds and the completion marker

The rows of a tree and a `TreeBuilt` marker are written by a single `runDB`, and
`runDB` goes through `runSqlPool`, which wraps the whole action in one
transaction (`runSqlPoolNoTransaction` is the opt-out) -- so a build that fails
part-way leaves nothing behind.  Completeness is decided by the **marker**, not
by the presence of the ROOT row: a table with rows but no marker (built by an
older version, or left over from an interrupted build) is wiped and rebuilt.

Verified on a copy of a database whose NSPK3 tree predated the oracle: on
startup the stale tree was detected and rebuilt -- 14 214 -> 17 350 rows, now
with 519 `Deadlocked` and 2 617 `Terminated` label nodes -- and a `tree_built`
row appeared for each protocol that finished, while `GET /session` still
answered in 3.6 ms.

### Bounded verdicts, per-protocol locks and the startup preload

Three things make the bounded nature of a check explicit and keep the one-off
tree construction out of the request path.

* **Bounded verdict.**  `Handler/Common.hs` has
  `boundedVerdict depth internalDepth nCounterexamples budgetExhausted`,
  appended by every `autoFormHandler` to the message shown after a check: *"No
  safety violation found within 12 visible steps and 5 internal steps -- a
  bounded result: a violation may still exist beyond these bounds."* (or *"N
  counterexample(s) found within ..."*).  `budgetExhausted` comes from
  `budget_hit`, the Isabelle-proved predicate (re-exported by each animator as
  `budgetExhaustedNSPK3` / `budgetExhaustedNSLPK3` / `budgetExhausted`) that says
  whether the internal-step budget cut the exploration short.  When it is true
  the message gains *"WARNING: the internal-step budget (mx = ...) was exhausted
  and the search was cut short ..."*, so a bounded result is never silently
  reported as if it were exhaustive.  `budget_hit` is a pure traversal of the
  model -- measured at `n = 15, mx = 100`: NSPK3 0.9 s, NSWJ3 0.01 s, DHWJ 6.0 s
  -- much cheaper than the full exploration, but not free, so
  `Handler.Common.ensureBudgetHit` memoises it in
  `appBudgetHit :: MVar (Map Text Bool)`, keyed by protocol/eavesdropper tag, for
  the lifetime of the process: the first check of a protocol pays the cost and
  the rest are instant.

* **Per-protocol locks.**  `App` carries
  `appTreeBuildLocks :: Map Text (MVar ())`, one lock per protocol, created in
  `makeFoundation`; `withTreeBuildLock protocol` serialises the construction of
  that protocol's tree.  A slow NSWJ3 build therefore no longer blocks an
  unrelated NSPK3 build.  Every build re-checks its table *inside* the lock, so
  concurrent builders cannot insert the same tree twice (which would violate the
  unique index on the event id).

* **Startup preload.**  `makeFoundation` forks
  `Handler.TreeBuild.preloadEventTrees` when `event-tree-preload` is true
  (the default; `config/test-settings.yml` sets it to false so the test suite
  does not explore for minutes).  It builds every table that is still empty,
  using Yesod's unsafe handler runner so the existing `Handler`-based builders
  can be reused unchanged.  Pages are served immediately while it runs: with a
  scratch database it was observed building NSPK3 (17 350 rows, including the
  new leaf labels) and then NSLPK3, while `GET /session` answered in
  milliseconds.

The handlers keep their synchronous path as a **fallback**: a request that finds
a table empty calls the same `ensureEventTree`, which waits on that protocol's
lock and re-checks — so if the preload has not reached a protocol yet, the page
still gets its tree rather than an error.
