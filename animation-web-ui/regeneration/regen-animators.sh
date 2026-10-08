#!/usr/bin/env bash
#
# regen-animators.sh — regenerate the animator packages from the Isabelle/HOL
# theories and copy the result into animation-web-ui/src/*-animator/src/.
#
# The three vendored packages (nspk3-animator, nswj3-animator, dhwj-animator)
# contain Haskell generated from User_Guided_Verification_Security/.  They are
# NOT produced by `stack build`, so they have to be refreshed whenever the
# theories change.  This script automates the procedure documented in
# animation-web-ui/REGEN_ANIMATORS.md; it follows the same shape as
# User_Guided_Verification_Security/Check_Automation/run_check.sh.
#
# Stages (any may be run separately):
#
#   ./regen-animators.sh generate   Isabelle -> Haskell, one session per family
#   ./regen-animators.sh install    patch, copy into the packages, refresh Simulate.hs
#   ./regen-animators.sh verify     typecheck each package with GHC 9.2.8
#   ./regen-animators.sh all        generate + install + verify          (default)
#
# Options:
#   --pkg nspk3|nswj3|dhwj   restrict to these families (repeatable)
#   --jobs N                 Isabelle build jobs (default: nproc)
#   --clean                  delete the scratch directory first (forces a full
#                            rebuild, including the cached Isabelle heaps)
#   -h, --help               this text
#
# Environment:
#   ARTEFACT       checkout root        (default: parent of this script's directory)
#   ISABELLE       isabelle executable  (default: ~/Tools/Isabelle2025-CyPhyAssure/bin/isabelle)
#   WORK           scratch directory    (default: <this dir>/regen-work)
#   USER_HOME_DIR  Isabelle user home   (default: $WORK/.isabelle-home)
#   GHC_9_2_8      GHC 9.2.8 executable (default: ~/.ghcup/ghc/9.2.8/bin/ghc)
#
# The Isabelle user home is kept out of ~/.isabelle and seeded from it on the
# first run, so the expensive interaction-tree heaps are reused and only
# ITree_Security (about a minute) is built; later runs reuse the cache in $WORK.
# After installing, run `stack build` in animation-web-ui/.
#
set -euo pipefail

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ARTEFACT=${ARTEFACT:-"$(cd "$HERE/.." && pwd)"}
ISABELLE=${ISABELLE:-"$HOME/Tools/Isabelle2025-CyPhyAssure/bin/isabelle"}
WORK=${WORK:-"$HERE/regen-work"}
USER_HOME_DIR=${USER_HOME_DIR:-"$WORK/.isabelle-home"}

THEORIES="$ARTEFACT/User_Guided_Verification_Security"
DEST_ROOT="$HERE/src"
REGEN="$WORK/regen"

FAMILIES=(nspk3 nswj3 dhwj)
declare -A SRC_DIR SRC_FILES SRC_IMPORTS MODELS SESSION DEST WRAPPER
SRC_DIR=(
  [nspk3]="NSPKP/NSPK3_v2"
  [nswj3]="NSPKP/NSPK3_wbplsec_v3"
  [dhwj]="Diffie_Hellman/DH_wbplsec_v3"
)
SRC_FILES=(
  [nspk3]="NSPK3_config.thy NSPK3.thy NSLPK3.thy"
  [nswj3]="NSWJ3_config.thy NSWJ3_wbplsec.thy"
  [dhwj]="DHWJ_config.thy DHWJ_wbplsec.thy"
)
# the theory the generated Export theory imports
SRC_IMPORTS=(
  [nspk3]="NSPK3 NSLPK3"
  [nswj3]="NSWJ3_wbplsec"
  [dhwj]="DHWJ_wbplsec"
)
# Isabelle constants to export: the models plus the proved search below
MODELS=(
  [nspk3]="NSPK3 NSLPK3"
  [nswj3]="NSWJ3_active_eve1 NSWJ3_active_eve2 NSWJ3_active_eve3 NSWJ3_active_eve4"
  [dhwj]="DHWJ_active_eve1 DHWJ_active_eve2 DHWJ_active_eve3 DHWJ_active_eve4"
)
SESSION=(
  [nspk3]="ExportNSPK3"
  [nswj3]="ExportNSWJ3"
  [dhwj]="ExportDHWJ"
)
DEST=(
  [nspk3]="$DEST_ROOT/nspk3-animator/src"
  [nswj3]="$DEST_ROOT/nswj3-animator/src"
  [dhwj]="$DEST_ROOT/dhwj-animator/src"
)
WRAPPER=(
  [nspk3]="NSPK3_Animate.hs"
  [nswj3]="NSWJ3_Animate.hs"
  [dhwj]="DHWJ_Animate.hs"
)

# The proved bounded exploration and its checks, exported into every package.
# Keep in step with `sound_simulate` in Sec_Animation.thy (the models replace
# its `model` argument) plus the predicates the hand-written wrappers import;
# see REGEN_ANIMATORS.md.
SEARCH_CONSTS="explore budget_hit feasible reaches checks check_leak check_leak_msg \
check_sig check_terminate check_corr check_corr_violation check_authenticity \
is_start is_end state_kind"

# Defaults, overridden by the command line (see the argument parser at the end).
MODE=all
CLEAN=0
JOBS=$( (command -v nproc >/dev/null && nproc) || echo 2)
SELECTED=()

# --------------------------------------------------------------------------
usage() {
  cat >&2 <<USAGE
usage: $0 [--pkg nspk3|nswj3|dhwj]... [--jobs N] [--clean] [generate|install|verify|all]

  generate   Isabelle -> Haskell, one export session per family
  install    patch, copy into animation-web-ui/src/*-animator/src, refresh Simulate.hs
  verify     typecheck each package with the project's GHC 9.2.8
  all        generate + install + verify                              (default)

  --pkg NAME only this family (repeatable; default: nspk3 nswj3 dhwj)
  --jobs N   Isabelle build jobs (default: $(nproc 2>/dev/null || echo 2))
  --clean    delete \$WORK first, forcing a full rebuild
  -h,--help  this text
USAGE
}

log()  { printf '\033[1m==> %s\033[0m\n' "$*" >&2; }
warn() { printf '\033[31mWARNING: %s\033[0m\n' "$*" >&2; }
die()  { printf '\033[31mERROR: %s\033[0m\n' "$*" >&2; exit 1; }

# --------------------------------------------------------------------------
# Isabelle plumbing
# --------------------------------------------------------------------------
write_root() {
  local fam t
  {
    cat <<EOF
session "ITree_Security" in "$THEORIES" = "ITree_UTP" +
  options [document = false, timeout = 3600]
  theories
    FSNat
    CSP_operators
    Sec_Messages
    Sec_Animation
EOF
    for fam in "${FAMILIES[@]}"; do
      cat <<EOF

session "${SESSION[$fam]}" in "$fam" = "ITree_Security" +
  options [document = false, timeout = 3600]
  sessions
    "ITree_Simulation"
  theories
EOF
      for t in ${SRC_FILES[$fam]}; do printf '    %s\n' "${t%.thy}"; done
      printf '    Export\n'
    done
  } > "$REGEN/ROOT"
}

generate_family() {
  local fam="$1" src="$THEORIES/${SRC_DIR[$1]}" dir="$REGEN/$1" t
  log "generate: $fam"
  rm -rf "$dir" "$REGEN/out-$fam"
  mkdir -p "$dir" "$REGEN/out-$fam"

  for t in ${SRC_FILES[$fam]}; do
    [ -f "$src/$t" ] || die "missing theory: $src/$t"
    # Strip the interactive animate_sec / animate_sec_sound commands: they
    # export code and then run a terminal driver, which we do not want here.
    # Delete only lines that are exactly the command; the ones inside
    # \<^cancel> blocks or (* *) comments are inert, and a line such as
    #   animate_sec_sound Q \<close>
    # carries the cartouche's closing \<close>, which must be preserved.
    sed -E '/^[[:space:]]*animate_sec(_sound)?([[:space:]]+[^[:space:]]+)?[[:space:]]*$/d' \
      "$src/$t" > "$dir/$t"
  done

  cat > "$dir/Export.thy" <<EOF
theory Export
  imports ${SRC_IMPORTS[$fam]}
begin

text \<open>Generated by regen-animators.sh; do not edit. \<close>

ML \<open>
let
  val ctx = @{context}
  val thy = Proof_Context.theory_of ctx
  val cs = map (Code.read_const thy)
    (space_explode " " "${MODELS[$fam]}" @ space_explode " " "$SEARCH_CONSTS")
  val out = Path.explode "$REGEN/out-$fam"
  val _ = Code_Target.export_code true cs
    [((("Haskell", ""), SOME ({physical = true}, (out, Position.none))),
      (Token.explode (Thy_Header.get_keywords' ctx) Position.none "string_classes"))]
    (Named_Target.theory_init thy)
in () end
\<close>

end
EOF
}

ensure_user_home() {
  local ihome="$USER_HOME_DIR/.isabelle/Isabelle2025"
  if [ ! -d "$ihome/heaps" ] && [ -d "$HOME/.isabelle/Isabelle2025/heaps" ]; then
    log "seeding the Isabelle user home from ~/.isabelle (one-off)"
    mkdir -p "$ihome"
    cp -a "$HOME/.isabelle/Isabelle2025/heaps" "$ihome/heaps"
  fi
}

run_isabelle() {
  local -a sessions=()
  local fam
  for fam in "${FAMILIES[@]}"; do sessions+=("${SESSION[$fam]}"); done
  log "isabelle build: ${sessions[*]} (jobs: $JOBS)"
  USER_HOME="$USER_HOME_DIR" "$ISABELLE" build -b -j"$JOBS" \
    -d "$REGEN" -o document=false "${sessions[@]}" \
    > "$WORK/logs/generate.log" 2>&1 \
    || { warn "Isabelle build failed — see $WORK/logs/generate.log"; tail -25 "$WORK/logs/generate.log" >&2; return 1; }
}

# --------------------------------------------------------------------------
# Assembling the packages
# --------------------------------------------------------------------------
patch_data_bits() {
  local dir="$1"
  # The current generator emits `import Data.Bits ((.&.), (.|.), (.^.));` in
  # every module.  (.^.) only exists from base-4.17 on, but this project pins
  # lts-20.26 / GHC 9.2.8 / base-4.16, and the operator is never used, so drop
  # it.  Upgrading the resolver would remove the need for this patch.
  sed -i 's/import Data\.Bits ((\.\&\.), (\.|\.), (\.\^\.));/import Data.Bits ((.\&.), (.|.));/' \
    "$dir"/*.hs
}

refresh_simulate() {
  local dest="$1" tmp
  tmp=$(mktemp)
  awk '/Simulate\.hs\\<close> = \\<open>/ {flag=1; next}
       flag && /^\\<close>$/ {exit}
       flag {print}' "$THEORIES/Sec_Animation.thy" > "$tmp"
  [ -s "$tmp" ] || { rm -f "$tmp"; die "could not extract Simulate.hs from Sec_Animation.thy"; }
  # the packaged file has no trailing newline; keep it byte-identical
  printf '%s' "$(cat "$tmp")" > "$dest/Simulate.hs"
  rm -f "$tmp"
}

install_family() {
  local fam="$1" out="$REGEN/out-$fam" dest="${DEST[$fam]}"
  [ -d "$out" ] || die "nothing generated for $fam (run 'generate' first)"
  [ -d "$dest" ] || die "missing destination: $dest"
  log "install: $fam -> $dest ($(ls "$out"/*.hs | wc -l) modules)"
  patch_data_bits "$out"
  cp -f "$out"/*.hs "$dest/"
  refresh_simulate "$dest"
}

# --------------------------------------------------------------------------
# Verification with the project's GHC
# --------------------------------------------------------------------------
find_ghc() {
  if [ -n "${GHC_9_2_8:-}" ] && [ -x "$GHC_9_2_8" ]; then printf '%s' "$GHC_9_2_8"; return; fi
  if [ -x "$HOME/.ghcup/ghc/9.2.8/bin/ghc" ]; then printf '%s' "$HOME/.ghcup/ghc/9.2.8/bin/ghc"; return; fi
  command -v ghc-9.2.8 2>/dev/null || true
}

find_pkgdb() {
  ls -d "$HOME"/.stack/snapshots/*/*/9.2.8/pkgdb 2>/dev/null | head -1 || true
}

verify_family() {
  local fam="$1" dest="${DEST[$fam]}"
  log "verify: $fam"
  "$GHC" -fno-code -outputdir "$WORK/verify/$fam" -package-db "$PKGDB" \
    -package pretty-show -package random -package text \
    -i"$dest" "$dest/${WRAPPER[$fam]}" \
    > "$WORK/logs/verify-$fam.log" 2>&1 \
    || { warn "typecheck failed for $fam — see $WORK/logs/verify-$fam.log"; tail -20 "$WORK/logs/verify-$fam.log" >&2; return 1; }
}

# --------------------------------------------------------------------------
# Command line
# --------------------------------------------------------------------------
while [ $# -gt 0 ]; do
  case "$1" in
    --pkg)     shift; SELECTED+=("${1:?--pkg needs a value}") ;;
    --pkg=*)   SELECTED+=("${1#*=}") ;;
    --jobs)    shift; JOBS="${1:?--jobs needs a value}" ;;
    --jobs=*)  JOBS="${1#*=}" ;;
    --clean)   CLEAN=1 ;;
    generate|install|verify|all) MODE="$1" ;;
    -h|--help) MODE=help ;;
    *)         die "unknown argument: $1 (try --help)" ;;
  esac
  shift
done

if [ "$MODE" = help ]; then usage; exit 0; fi

# apply --pkg
if [ ${#SELECTED[@]} -gt 0 ]; then
  for p in "${SELECTED[@]}"; do
    for fam in "${FAMILIES[@]}"; do
      if [ "$p" = "$fam" ]; then continue 2; fi
    done
    die "unknown package: $p (choose from: ${FAMILIES[*]})"
  done
  FAMILIES=("${SELECTED[@]}")
fi

[ -d "$ARTEFACT/User_Guided_Verification_Security" ] || die "theories not found under $ARTEFACT"
[ -d "$DEST_ROOT" ] || die "animation-web-ui/src not found under $HERE"
[ -x "$ISABELLE" ] || warn "Isabelle is not executable at $ISABELLE (set ISABELLE=...)"

if [ "$CLEAN" = 1 ]; then log "cleaning $WORK"; rm -rf "$WORK"; fi

mkdir -p "$WORK/logs" "$REGEN" "$WORK/verify"
ensure_user_home
write_root

# --------------------------------------------------------------------------
# Run
# --------------------------------------------------------------------------
case "$MODE" in
  generate)
    for fam in "${FAMILIES[@]}"; do generate_family "$fam"; done
    run_isabelle
    ;;
  install)
    for fam in "${FAMILIES[@]}"; do install_family "$fam"; done
    ;;
  verify)
    GHC=$(find_ghc); PKGDB=$(find_pkgdb)
    [ -n "$GHC" ]   || die "GHC 9.2.8 not found (set GHC_9_2_8=...)"
    [ -n "$PKGDB" ] || die "stack snapshot package db for GHC 9.2.8 not found (run 'stack build' first)"
    for fam in "${FAMILIES[@]}"; do verify_family "$fam"; done
    log "all packages typecheck"
    ;;
  all)
    for fam in "${FAMILIES[@]}"; do generate_family "$fam"; done
    run_isabelle
    for fam in "${FAMILIES[@]}"; do install_family "$fam"; done
    if GHC=$(find_ghc) && PKGDB=$(find_pkgdb) && [ -n "$GHC" ] && [ -n "$PKGDB" ]; then
      for fam in "${FAMILIES[@]}"; do verify_family "$fam"; done
      log "all packages typecheck"
    else
      warn "skipping verification: GHC 9.2.8 or the stack snapshot db was not found"
    fi
    log "changed files under animation-web-ui/src:"
    git -C "$ARTEFACT" status --short -- animation-web-ui/src | sed 's/^/  /' >&2
    log "now run: (cd $HERE && stack --system-ghc build)"
    ;;
  *) die "unknown mode: $MODE (try --help)" ;;
esac
