#! /usr/bin/env bash
#
# run_check.sh — check each protocol using the generated animator 
# record the time taken by each check.
#
# It reports, for each protocol and eavesdropper
# location, whether secrecy holds and whether authenticity holds for Alice and
# for Bob.  The checks are the ones *proved in Isabelle/HOL* and exported by the
# code generator (`Sec_Animation.thy`):
#
#   secrecy     = check_leak                 (no leak event reachable within bound)
#   auth-alice  = check_auth_violation with matches_start and an end predicate
#                 "Alice completes" — i.e. EndProt Alice _ must be preceded by
#                 StartProt _ Alice.  EndProt's FIRST argument is the agent that
#                 completes the run, which is how the protocol theories emit it.
#   auth-bob    = the same with Bob.
#
# Stages (any may be run separately):
#
#   ./run_check.sh generate    Isabelle -> Haskell, one package per family
#   ./run_check.sh build       stack build each generated runner
#   ./run_check.sh run         run every cell, timing each
#   ./run_check.sh all         generate + build + run        (default)
#   ./run_check.sh dry-run     show the grid and bounds, run nothing
#
# Outputs (written next to the script unless overridden):
#   check-results.csv     protocol,model,property,verdict,seconds
#   check-results.md      the same rendered as a Markdown table
#   check-work/logs/*.log per-stage and per-cell logs
#
# Requirements: Isabelle/HOL 2025 (CyPhyAssure session chain), stack + GHC
# (LTS 23.0 / GHC 9.8), and a checkout of Animation_of_Security_Protocols.
#
set -euo pipefail

# --------------------------------------------------------------------------
# Configuration — override through the environment
# --------------------------------------------------------------------------
ARTEFACT=${ARTEFACT:-"$HOME/workspace/Animation_of_Security_Protocols"}
ISABELLE=${ISABELLE:-"$HOME/Tools/Isabelle2025-CyPhyAssure/bin/isabelle"}
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${WORK:-"$HERE/check-work"}
CSV=${CSV:-"$HERE/check-results.csv"}
MD=${MD:-"$HERE/check-results.md"}

THEORIES="$ARTEFACT/User_Guided_Verification_Security"

# Exploration bounds "visible-events internal-steps", per protocol.
# These are the bounds these experiments report.  They are NOT the bounds
# currently configured for the browser interface in
# animation-web-ui/config/settings.yml (where nswj3/dhwj are 12/5, because the
# browser builds a persistent event tree and does not finish at 20/100), and
# the paper's Section 7 also needs to agree with whatever is chosen here.
# Reconcile the three before publishing the numbers.
declare -A BOUNDS=(
  [nspk3]="15 100"
  [nswj3]="15 100"
  [dhwj]="15 100"
  [dh]="15 100"
)

# Isabelle constants to export, per family (models only; the proved checks and
# the properties are added by the generated Export theories).
declare -A MODELS=(
  [nspk3]="NSPK3"
  [nswj3]="NSWJ3_active_eve1 NSWJ3_active_eve2 NSWJ3_active_eve3 NSWJ3_active_eve4 NSWJ3_passive_eve1 NSWJ3_passive_eve2 NSWJ3_passive_eve3 NSWJ3_passive_eve4"
  [dhwj]="DHWJ_active_eve1 DHWJ_active_eve2 DHWJ_active_eve3 DHWJ_active_eve4"
  [dh]="DH_Original"
)
declare -A SRC_DIR=(
  [nspk3]="NSPKP/NSPK3_v2"
  [nswj3]="NSPKP/NSPK3_wbplsec_v3"
  [dhwj]="Diffie_Hellman/DH_wbplsec_v3"
  [dh]="Diffie_Hellman/DH_v2"
)
declare -A SRC_FILES=(
  [nspk3]="NSPK3_config.thy NSPK3.thy NSLPK3.thy"
  [nswj3]="NSWJ3_config.thy NSWJ3_wbplsec.thy"
  [dhwj]="DHWJ_config.thy DHWJ_wbplsec.thy"
  [dh]="DH_config.thy DH.thy"
)
declare -A SRC_THEORY=(   # theory imported by the generated theory
  [nspk3]="NSPK3"
  [nswj3]="NSWJ3_wbplsec"
  [dhwj]="DHWJ_wbplsec"
  [dh]="DH"
)
declare -A SRC_MODULE=(   # generated module holding the models
  [nspk3]="NSPK3.hs"
  [nswj3]="NSWJ3_wbplsec.hs"
  [dhwj]="DHWJ_wbplsec.hs"
  [dh]="DH.hs"
)
FAMILIES=(nspk3 nswj3 dhwj dh)
PROPERTIES=(secrecy auth-alice auth-bob)
CHECK_CONSTS="explore checks check_leak check_leak_msg check_auth_violation matches_start auth_alice auth_bob secrecy"

# A representative subset for --fast: one configuration per family, chosen to
# exercise both a holds and a violated verdict, so the whole
# generate -> build -> run pipeline can be smoke-tested quickly.
declare -A FAST_MODELS=(
  [nspk3]="NSPK3"
  [nswj3]="NSWJ3_active_eve1"
  [dhwj]="DHWJ_active_eve1"
  [dh]="DH_Original"
)

# Defaults, overridden by the command line (see the argument parser at the end).
MODE=all
FAST=0
TIMEOUT_SET=0
CELL_TIMEOUT=${CELL_TIMEOUT:-900}   # seconds per cell; 0 disables the timeout
GHC_OPT=-O2

# --------------------------------------------------------------------------
usage() {
  cat >&2 <<USAGE
usage: $0 [--fast] [--timeout SECONDS] [generate|build|run|all|dry-run]

  generate           Isabelle -> Haskell, one package per family
  build              stack build each generated runner
  run                run every cell and record the verdict and time
  all                generate + build + run                     (default)
  dry-run            print the grid and bounds, run nothing

  --fast             representative subset (one configuration per family,
                     covering a holds and a violated verdict) and -O1
  --timeout SECONDS  per-cell wall-clock limit (default 900; 0 disables)
USAGE
}

log()  { printf '\033[1m==> %s\033[0m\n' "$*" >&2; }
warn() { printf '\033[31mWARNING: %s\033[0m\n' "$*" >&2; }
die()  { printf '\033[31mERROR: %s\033[0m\n' "$*" >&2; exit 1; }

hs_name() { printf '%s%s' "$(printf '%s' "${1:0:1}" | tr 'A-Z' 'a-z')" "${1:1}"; }

# --------------------------------------------------------------------------
# Stage 1 — Isabelle export
# --------------------------------------------------------------------------
generate_family() {
  local fam="$1" src="$THEORIES/${SRC_DIR[$1]}" dir="$WORK/regen/$1"
  local theory="${SRC_THEORY[$1]}" t

  log "generate: $fam"
  rm -rf "$dir"; mkdir -p "$dir/src" "$dir/out"

  for t in ${SRC_FILES[$1]}; do
    [ -f "$src/$t" ] || die "missing theory: $src/$t"
    # strip the interactive `animate_sec`/`animate_sec_sound` commands
    # Delete only lines that are exactly the command; lines that merely contain
    # it (inside \<^cancel> blocks or (* *) comments) are inert and may carry a
    # closing \<close> that must be preserved.
    sed -E '/^[[:space:]]*animate_sec(_sound)?([[:space:]]+[^[:space:]]+)?[[:space:]]*$/d' "$src/$t" > "$dir/src/$t"
  done

  # properties, defined on top of the proved checks
  cat > "$dir/src/Check.thy" <<EOF
theory Check 
  imports $theory
begin

text \<open>Check properties, on top of the proved checks of Sec_Animation.thy.
  A run is completed by the first argument of EndProt (the protocol theories
  emit it that way) and matches_start requires the counterpart's StartProt. \<close>

definition "is_end_alice e \<equiv>
  (case e of sig_C (EndProt s d _ _) \<Rightarrow> s = Alice \<and> is_honest d | _ \<Rightarrow> False)"
definition "is_end_bob e \<equiv>
  (case e of sig_C (EndProt s d _ _) \<Rightarrow> s = Bob \<and> is_honest d | _ \<Rightarrow> False)"

definition "auth_alice n mx (P::(chan, unit) itree) \<equiv>
  check_auth_violation n mx P matches_start is_end_alice"
definition "auth_bob n mx (P::(chan, unit) itree) \<equiv>
  check_auth_violation n mx P matches_start is_end_bob"
definition "secrecy n mx (P::(chan, unit) itree) \<equiv> check_leak n mx P"

end
EOF

  cat > "$dir/src/Export.thy" <<EOF
theory Export
  imports Check 
begin

text \<open>Check export run $(date +%s%N)-$$.\<close>

ML \<open>
let
  val ctx = @{context}
  val thy = Proof_Context.theory_of ctx
  val cs = map (Code.read_const thy)
    (space_explode " " "${MODELS[$1]}" @ space_explode " " "$CHECK_CONSTS")
  val out = Path.explode "${dir}/out"
  val _ = Code_Target.export_code true cs
    [((("Haskell", ""), SOME ({physical = true}, (out, Position.none))),
      (Token.explode (Thy_Header.get_keywords' ctx) Position.none "string_classes"))]
    (Named_Target.theory_init thy)
in () end
\<close>

end
EOF

  cat > "$dir/ROOT" <<EOF
session "CheckExport_$fam" in "src" = "ITree_Security" +
  options [document = false, timeout = 3600]
  sessions "ITree_Simulation"
  theories
    ${SRC_FILES[$1]//.thy/}
    Check 
    Export
EOF

  ( cd "$dir" && USER_HOME="$WORK/.isabelle-home" \
      "$ISABELLE" build -d . -d "$THEORIES" -o document=false "CheckExport_$fam" ) \
      > "$WORK/logs/generate-$fam.log" 2>&1 \
    || { warn "Isabelle build failed for $fam — see $WORK/logs/generate-$fam.log"; return 1; }

  log "  exported $(ls "$dir/out"/*.hs 2>/dev/null | wc -l) modules"
}

# --------------------------------------------------------------------------
# Stage 2 — assemble a standalone runner per family and build it
# --------------------------------------------------------------------------
build_family() {
  local fam="$1"
  local dir="$WORK/build/$fam" regen="$WORK/regen/$fam"
  local modfile="$regen/out/${SRC_MODULE[$1]}"
  log "build: $fam"
  rm -rf "$dir"; mkdir -p "$dir/src"
  cp "$regen/out"/*.hs "$dir/src/" 2>/dev/null || die "no generated modules for $fam"

  # Pin the concrete model type once, taken from the generated module, so the
  # runner stays generic over the family's channel instantiation.
  local first hs sig
  first=$(printf '%s' "${MODELS[$1]}" | awk '{print $1}')
  hs=$(hs_name "$first")
  sig=$(sed -n "/^$hs ::/,/;/p" "$modfile" \
        | sed "1s/^$hs[[:space:]]*::[[:space:]]*//" \
        | tr '\n' ' ' | sed 's/;[[:space:]]*$//' | tr -s ' ')
  [ -n "$sig" ] || die "could not read the type of $hs from $modfile"

  # dispatch clauses
  local clauses="" m h
  for m in ${MODELS[$1]}; do
    h=$(hs_name "$m")
    clauses+="    \"$h\" -> Just <$> cell prop nn mm $h"$'\n'
  done

  cat > "$dir/src/Main.hs" <<EOF
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Prelude
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Control.Exception (evaluate)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import qualified Set
import Arith (Nat, nat_of_integer)
import Check (secrecy, auth_alice, auth_bob)
import ${SRC_THEORY[$1]}
-- the qualified type in the cell signature below needs these in scope
import Interaction_Trees
import Sec_Messages
import Numeral_Type

-- | The generated Set module exports its constructors but no emptiness test.
isEmptySet :: Set.Set a -> Bool
isEmptySet (Set.Set xs)  = null xs
isEmptySet (Set.Coset _) = False

-- | Run one proved check on one model and return its verdict and elapsed time.
cell :: String -> Nat -> Nat -> $sig -> IO (String, Double)
cell prop nn mm p = do
  t0 <- getCurrentTime
  let res = case prop of
              "secrecy"    -> secrecy nn mm p
              "auth-alice" -> auth_alice nn mm p
              "auth-bob"   -> auth_bob nn mm p
              _            -> error ("unknown property: " ++ prop)
      verdict = if isEmptySet res then "holds" else "violated"
  _ <- evaluate verdict        -- force the search before stopping the clock
  t1 <- getCurrentTime
  return (verdict, realToFrac (diffUTCTime t1 t0))

dispatch :: String -> String -> Nat -> Nat -> IO (Maybe (String, Double))
dispatch prop model nn mm = case model of
$clauses    _ -> return Nothing

main :: IO ()
main = do
  args <- getArgs
  case args of
    [prop, model, n, mx] -> do
      r <- dispatch prop model (nat_of_integer (read n)) (nat_of_integer (read mx))
      case r of
        Nothing -> putStrLn ("unknown model: " ++ model) >> exitFailure
        Just (verdict, secs) ->
          putStrLn (model ++ "," ++ prop ++ "," ++ verdict ++ "," ++ show secs)
    _ -> putStrLn "usage: check <secrecy|auth-alice|auth-bob> <model> <n> <mx>"
         >> exitFailure
EOF

  cat > "$dir/package.yaml" <<EOF
name: check-$fam
version: "0.1.0"
dependencies:
  - base
  - containers
  - text
  - random
  - time
executables:
  check:
    main: Main.hs
    source-dirs: src
    ghc-options: [$GHC_OPT]
EOF

  cat > "$dir/stack.yaml" <<EOF
resolver: lts-23.0
packages: [.]
EOF

  ( cd "$dir" && stack build --copy-bins --local-bin-path . ) \
      > "$WORK/logs/build-$fam.log" 2>&1 \
    || { warn "stack build failed for $fam — see $WORK/logs/build-$fam.log"; return 1; }
  log "  built $dir/check"
}

# --------------------------------------------------------------------------
# Stage 3 — run every cell and record the time
# --------------------------------------------------------------------------
run_cell() {
  local fam="$1" model="$2" prop="$3" n="$4" mx="$5"
  local bin="$WORK/build/$fam/check" log="$WORK/logs/cell-$fam-$model-$prop.log"
  local t0 t1 secs verdict rc
  t0=$(date +%s.%N)
  if [ "$CELL_TIMEOUT" -gt 0 ]; then
    timeout "$CELL_TIMEOUT" "$bin" "$prop" "$model" "$n" "$mx" > "$log" 2>&1
  else
    "$bin" "$prop" "$model" "$n" "$mx" > "$log" 2>&1
  fi
  rc=$?
  t1=$(date +%s.%N)
  case "$rc" in
    0)   verdict=$(tail -n1 "$log" | cut -d, -f3) ;;
    124) verdict="timeout" ;;
    *)   verdict="error" ;;
  esac
  secs=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.2f", b-a}')
  printf '%s,%s,%s,%s,%s\n' "$fam" "$model" "$prop" "$verdict" "$secs" >> "$CSV"
  printf '  %-30s %-11s %-9s %6ss\n' "$model" "$prop" "$verdict" "$secs" >&2
}

render_md() {
  {
    echo "# Check — reproduced $(date -u '+%Y-%m-%d %H:%M UTC')"
    echo
    echo "Bounds (visible events / internal steps): ${BOUNDS[*]}"
    echo
    echo "| Protocol | Model | Secrecy | Auth (Alice) | Auth (Bob) |"
    echo "|---|---|---|---|---|"
    awk -F, 'NR>1{k=$1 SUBSEP $2; v[k SUBSEP $3]=$4;
                if(!(k in seen)){seen[k]=1; ord[++n]=k}}
      END{for(i=1;i<=n;i++){split(ord[i],a,SUBSEP);
        printf "| %s | %s | %s | %s | %s |\n", a[1], a[2],
          (v[ord[i] SUBSEP "secrecy"]=="holds"?"●":"○"),
          (v[ord[i] SUBSEP "auth-alice"]=="holds"?"●":"○"),
          (v[ord[i] SUBSEP "auth-bob"]=="holds"?"●":"○")}}' "$CSV"
  } > "$MD"
  log "wrote $CSV and $MD"
}

run_all() {
  : > "$CSV"; echo "protocol,model,property,verdict,seconds" >> "$CSV"
  local fam isa hs prop n mx list
  for fam in "${FAMILIES[@]}"; do
    read -r n mx <<< "${BOUNDS[$fam]}"
    if [ "$FAST" = 1 ]; then list=${FAST_MODELS[$fam]}; else list=${MODELS[$fam]}; fi
    for isa in $list; do
      hs=$(hs_name "$isa")
      for prop in "${PROPERTIES[@]}"; do
        run_cell "$fam" "$hs" "$prop" "$n" "$mx"
      done
    done
  done
  render_md
}

# --------------------------------------------------------------------------
# --------------------------------------------------------------------------
# Command line
# --------------------------------------------------------------------------
while [ $# -gt 0 ]; do
  case "$1" in
    --fast)      FAST=1 ;;
    --timeout)   shift; TIMEOUT_SET=1; CELL_TIMEOUT="${1:?--timeout needs a value}" ;;
    --timeout=*) TIMEOUT_SET=1; CELL_TIMEOUT="${1#*=}" ;;
    generate|build|run|all|dry-run) MODE="$1" ;;
    -h|--help)   MODE=help ;;
    *)           die "unknown argument: $1" ;;
  esac
  shift
done

if [ "$FAST" = 1 ]; then
  [ "$TIMEOUT_SET" = 1 ] || CELL_TIMEOUT=180
  GHC_OPT=-O1
fi

mkdir -p "$WORK/logs" "$WORK/regen" "$WORK/build"
[ -d "$ARTEFACT" ] || die "artefact not found at $ARTEFACT (set ARTEFACT=...)"
[ -x "$ISABELLE" ] || warn "Isabelle not executable at $ISABELLE (set ISABELLE=...)"

case "$MODE" in
  generate) for f in "${FAMILIES[@]}"; do generate_family "$f"; done ;;
  build)    for f in "${FAMILIES[@]}"; do build_family "$f"; done ;;
  run)      run_all ;;
  all)      for f in "${FAMILIES[@]}"; do generate_family "$f"; done
            for f in "${FAMILIES[@]}"; do build_family "$f"; done
            run_all ;;
  dry-run)  echo "fast: $FAST   per-cell timeout: ${CELL_TIMEOUT}s   GHC: ${GHC_OPT}"
            echo "bounds:"; for k in "${FAMILIES[@]}"; do echo "  $k: ${BOUNDS[$k]}"; done
            echo "grid:"
            for k in "${FAMILIES[@]}"; do
              if [ "$FAST" = 1 ]; then list=${FAST_MODELS[$k]}; else list=${MODELS[$k]}; fi
              for m in $list; do echo "  $k $(hs_name "$m")"; done
            done ;;
  help)     usage ;;
  *)        die "usage: $0 [--fast] [--timeout SECONDS] [generate|build|run|all|dry-run]" ;;
esac
