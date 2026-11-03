#!/usr/bin/env bash
# Shared helpers for the QRH Comparator kit. Source this from every script:
#     . "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
# It defines variables and functions and creates the work directories. Droplet only.

set -euo pipefail

KIT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# These scripts are for the droplet. On Joey's own computer everything goes through remote.sh.
if [ ! -f "$HOME/.qrh-droplet" ]; then
  echo "This script runs on the droplet, as the user created by scripts/00_system_setup.sh." >&2
  echo "From your own computer use:  scripts/remote.sh run $(basename "$0") ..." >&2
  exit 2
fi

# shellcheck source=../PINS.env
. "$KIT_DIR/PINS.env"

# All state lives under QRH_WORK (default ~/qrh-work). The kit directory itself stays read-only.
QRH_WORK="${QRH_WORK:-$HOME/qrh-work}"
# One spelling of the path everywhere (no trailing slash, no //): the receipt compares the job
# that ran with the command it expects, character for character.
mkdir -p "$QRH_WORK"
QRH_WORK="$(cd "$QRH_WORK" && pwd)"
TOOLS="$QRH_WORK/tools"
LOGS="$QRH_WORK/logs"
RECEIPT="$QRH_WORK/receipt"
OAI_DIR="$QRH_WORK/openai-math"
OAI_LEAN="$OAI_DIR/lean"
COMPARATOR_DIR="$TOOLS/comparator"
COMPARATOR_BIN="$COMPARATOR_DIR/.lake/build/bin/comparator"
LEAN4EXPORT_BIN="$COMPARATOR_DIR/.lake/packages/lean4export/.lake/build/bin/lean4export"
LANDRUN_BIN="$TOOLS/bin/landrun"
MAIN_LABEL="qrh-main"
DIRICHLET_LABEL="qrh-dirichlet"

mkdir -p "$TOOLS/bin" "$LOGS" "$RECEIPT"
case ":$PATH:" in
  *":$TOOLS/bin:"*) ;;
  *) PATH="$TOOLS/bin:$HOME/.elan/bin:$PATH" ;;
esac
export PATH

# Two development switches. Using either one makes the run INVALID as a certification;
# 07_receipt.sh refuses to print PASS when they were used. They exist so the kit itself can be
# exercised on machines without Landlock or systemd. Never set them on the droplet.
#   QRH_DEV_NO_SANDBOX=1       accept a landrun that does not enforce
#   QRH_NO_SYSTEMD=1           run without systemd-run (no AF_UNIX restriction)
QRH_MATHLIB_FROM_SOURCE="${QRH_MATHLIB_FROM_SOURCE:-0}"
QRH_DEV_NO_SANDBOX="${QRH_DEV_NO_SANDBOX:-0}"
QRH_NO_SYSTEMD="${QRH_NO_SYSTEMD:-0}"
export QRH_WORK QRH_MATHLIB_FROM_SOURCE QRH_DEV_NO_SANDBOX QRH_NO_SYSTEMD

ts() { date -u +%Y-%m-%dT%H:%M:%SZ; }
log() { printf '[%s] %s\n' "$(ts)" "$*" | tee -a "$LOGS/kit.log"; }
ok() { log "OK    $*"; }
warn() { log "WARN  $*"; }
die() { log "FAIL  $*"; exit 1; }

# fact KEY VALUE: append one fact for the receipt (last value for a key wins).
fact() { printf '%s\t%s\t%s\n' "$(ts)" "$1" "$2" >>"$RECEIPT/facts.tsv"; }
# fact_get KEY: print the latest value recorded for KEY (empty if none).
fact_get() {
  [ -f "$RECEIPT/facts.tsv" ] || return 0
  awk -F '\t' -v k="$1" '$2 == k { v = $3 } END { if (v != "") print v }' "$RECEIPT/facts.tsv"
}

# deviation TEXT: record anything done differently from the scripted protocol.
deviation() {
  printf -- '- %s  %s\n' "$(ts)" "$*" >>"$RECEIPT/DEVIATIONS.md"
  log "DEVIATION recorded: $*"
}

sha256_of() { sha256sum "$1" | awk '{print $1}'; }

# check_sha FILE EXPECTED LABEL: stop if the file is not the one that was audited.
check_sha() {
  local got
  [ -f "$1" ] || die "$3: missing file $1"
  got="$(sha256_of "$1")"
  [ "$got" = "$2" ] || die "$3: sha256 mismatch for $1 (got $got, pinned $2)"
  ok "$3 matches its pinned sha256"
}

# begin_phase N: a phase that starts again is not done until it finishes again.
begin_phase() { rm -f "$RECEIPT/phase_$1.ok"; }
mark_phase() { ts >"$RECEIPT/phase_$1.ok"; fact "phase_$1" "ok"; }
# phase_command N: the command that runs phase N, in the form the protocol uses.
phase_command() {
  case "$1" in
    1) echo "scripts/01_preflight.sh" ;;
    2) echo "scripts/detach.sh toolchain 02_toolchain.sh" ;;
    3) echo "scripts/detach.sh selftest 03_selftest.sh" ;;
    4) echo "scripts/detach.sh fetch 04_fetch.sh" ;;
    5) echo "scripts/detach.sh deps 05_deps.sh" ;;
    6) echo "scripts/06_run_comparator.sh" ;;
    7) echo "scripts/07_receipt.sh" ;;
    8) echo "scripts/detach.sh bridge 08_bridge.sh" ;;
  esac
}
# require_phase N: stop unless phase N has completed.
require_phase() {
  [ -f "$RECEIPT/phase_$1.ok" ] || die "phase $1 has not completed; run it first: $(phase_command "$1")"
}

require_not_root() {
  if [ "$(id -u)" = "0" ]; then
    die "do not run this as root (Comparator's guarantees assume an unprivileged user). Run scripts/00_system_setup.sh as root once, then log in as the unprivileged user it creates."
  fi
}

need_cmd() { command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"; }

have_user_systemd() {
  command -v systemd-run >/dev/null 2>&1 || return 1
  if [ -z "${XDG_RUNTIME_DIR:-}" ] && [ -d "/run/user/$(id -u)" ]; then
    XDG_RUNTIME_DIR="/run/user/$(id -u)"
    export XDG_RUNTIME_DIR
  fi
  systemctl --user show-environment >/dev/null 2>&1
}

boot_id() { cat /proc/sys/kernel/random/boot_id 2>/dev/null || echo unknown; }

# job_running LABEL: is the detached job with this label still running?
job_running() {
  local unitf="$LOGS/$1.unit" u
  [ -f "$unitf" ] || return 1
  u="$(cat "$unitf")"
  case "$u" in
    pid:*) kill -0 "${u#pid:}" 2>/dev/null ;;
    *) have_user_systemd && systemctl --user is-active --quiet "$u" 2>/dev/null ;;
  esac
}

# --- the kit itself ---------------------------------------------------------------------------

# kit_changes: list kit files that differ from the shipped manifest (empty output = unmodified).
kit_changes() {
  local m="$KIT_DIR/KIT_MANIFEST.sha256"
  [ -f "$m" ] || { echo "KIT_MANIFEST.sha256 is missing"; return 0; }
  (
    cd "$KIT_DIR"
    find . -type f ! -name KIT_MANIFEST.sha256 ! -path './results/*' ! -name .qrh_host ! -name '._*' \
      ! -path './.claude/settings.local.json' -print0 |
      LC_ALL=C sort -z | xargs -0 sha256sum
  ) | awk '
    side == "old" { old[$2] = $1; next }
    { if (!($2 in old)) print "added: " $2; else if (old[$2] != $1) print "modified: " $2; delete old[$2] }
    END { for (k in old) print "removed: " k }
  ' side=old "$m" side=new -
}

# --- the OpenAI checkout ----------------------------------------------------------------------

# verify_oai_tree: the OpenAI checkout is exactly the audited commit, with no local changes.
# (git is safe here: the sandbox cannot write to this repository's .git, and .lake is ignored.)
verify_oai_tree() {
  local head tree dirty
  [ -d "$OAI_DIR/.git" ] || die "no OpenAI checkout at $OAI_DIR; run phase 4 first: $(phase_command 4)"
  head="$(git -C "$OAI_DIR" rev-parse HEAD)"
  [ "$head" = "$OAI_COMMIT" ] || die "OpenAI checkout is at $head, pinned $OAI_COMMIT"
  tree="$(git -C "$OAI_DIR" rev-parse "HEAD:lean/OAI/NumberTheory/DirichletL")"
  [ "$tree" = "$OAI_TREE_DIRICHLETL" ] || die "proof directory tree is $tree, pinned $OAI_TREE_DIRICHLETL"
  ok "OpenAI checkout is at the pinned commit and the proof directory has the pinned tree hash"
  check_sha "$OAI_LEAN/ComparatorChallenges/QuasiRiemannHypothesis.lean" "$SHA_CHALLENGE_LEAN" "challenge statement"
  check_sha "$OAI_LEAN/$OAI_CONFIG" "$SHA_CHALLENGE_JSON" "Comparator configuration"
  check_sha "$OAI_LEAN/ComparatorChallenges/DirichletSevenEighths.lean" "$SHA_CHALLENGE_DIRICHLET_LEAN" "second challenge statement (Dirichlet)"
  check_sha "$OAI_LEAN/$OAI_CONFIG_DIRICHLET" "$SHA_CHALLENGE_DIRICHLET_JSON" "second Comparator configuration (Dirichlet)"
  check_sha "$OAI_LEAN/lakefile.lean" "$SHA_LAKEFILE" "lakefile"
  check_sha "$OAI_LEAN/lake-manifest.json" "$SHA_MANIFEST" "dependency manifest"
  check_sha "$OAI_LEAN/lean-toolchain" "$SHA_TOOLCHAIN_FILE" "toolchain file"
  check_sha "$OAI_LEAN/patches/PrimeNumberTheoremAnd-lean4341.patch" "$SHA_PATCH_PNT" "PrimeNumberTheoremAnd patch"
  check_sha "$OAI_LEAN/patches/rellich-kondrachov-lean4341.patch" "$SHA_PATCH_RELLICH" "rellich-kondrachov patch"
  check_sha "$OAI_LEAN/OAI/NumberTheory/DirichletL/Nonvanishing.lean" "$SHA_SOLUTION_ENTRY" "solution entry module"
  dirty="$(git -C "$OAI_DIR" status --porcelain --untracked-files=all | head -n 20 || true)"
  [ -z "$dirty" ] || die "the OpenAI checkout has local changes (it must stay untouched):
$dirty"
  ok "OpenAI checkout has no local changes"
}

# cold_tree_check: nothing of the challenge, the solution, or the two third-party libraries the
# solution imports may have been compiled yet. (Comparator's README, assumption 2.)
cold_tree_check() {
  local d found
  for d in "$OAI_LEAN/.lake/build" "$OAI_LEAN/.lake/packages/PrimeNumberTheoremAnd/.lake/build" \
    "$OAI_LEAN/.lake/packages/rellich-kondrachov/.lake/build"; do
    [ -d "$d" ] || continue
    found="$(find "$d" -type f -print -quit)"
    [ -z "$found" ] || die "found build output ($found) before the Comparator run. The tree is not cold; see docs/PROTOCOL.md, \"Re-runs\""
  done
}

# closure_check ROOT ENTRY MODULES LINES DIGEST LABEL OUT_PREFIX
# Re-measure a source closure and compare it with the audited numbers. Flags must be empty.
closure_check() {
  local root="$1" entry="$2" want_n="$3" want_lines="$4" want_digest="$5" label="$6" out="$7" got
  python3 -I "$KIT_DIR/scripts/closure_scan.py" "$root" "$entry" --json "$out.json" --list "$out.txt" >/dev/null \
    || die "$label: source scan failed"
  got="$(python3 -I -c '
import json, sys
d = json.load(open(sys.argv[1]))
print(d["project_modules"], d["project_lines"], d["closure_digest"], sum(d["flag_counts"].values()))' "$out.json")"
  # shellcheck disable=SC2086
  set -- $got
  [ "$1" = "$want_n" ] || die "$label: $1 source files in the import closure, audited $want_n"
  [ "$2" = "$want_lines" ] || die "$label: $2 lines in the import closure, audited $want_lines"
  [ "$3" = "$want_digest" ] || die "$label: closure digest $3 differs from the audited $want_digest"
  [ "$4" = "0" ] || die "$label: the static scan flagged $4 construct(s); see $out.json"
  ok "$label: $want_n files, $want_lines lines, digest matches the audit, no flagged constructs"
}

# --- dependencies: records that need no git afterwards ----------------------------------------
# After the solution has been compiled, nothing under .lake is trusted any more, and no program
# that interprets files there (git above all) may run outside the sandbox. Everything below
# only hashes bytes.

# lakefiles_listing: sha256 of each dependency's Lake configuration file, sorted.
lakefiles_listing() {
  (cd "$OAI_LEAN/.lake/packages" && find . -mindepth 2 -maxdepth 2 \( -name lakefile.lean -o -name lakefile.toml \) -print0 |
    LC_ALL=C sort -z | xargs -0 -r sha256sum)
}

# snapshot_compiled OUTFILE: sha256 of every file the dependencies have under .lake/build/lib
# (compiled modules in all their parts), sorted by path. Lake's .trace notes are left out.
snapshot_compiled() {
  local out="$1"
  (
    cd "$OAI_LEAN/.lake/packages"
    find . -path '*/.lake/build/lib/*' -type f ! -name '*.trace' -print0 |
      xargs -0 -r -n 64 -P "$(nproc)" sha256sum
  ) | LC_ALL=C sort -k 2 >"$out"
}

# snapshot_listed LISTFILE OUTFILE: re-hash exactly the paths named in an earlier snapshot.
# A file that has gone missing simply has no line in OUTFILE, so the two files then differ.
snapshot_listed() {
  (
    cd "$OAI_LEAN/.lake/packages"
    awk '{ print $2 }' "$1" | tr '\n' '\0' | xargs -0 -r -n 64 -P "$(nproc)" sha256sum 2>/dev/null || true
  ) | LC_ALL=C sort -k 2 >"$2"
}

# compare_snapshots OLD NEW: print "modified deleted added" counts.
compare_snapshots() {
  awk '
    side == "old" { old[$2] = $1; next }
    { if ($2 in old) { if (old[$2] != $1) modified++; delete old[$2] } else added++ }
    END { deleted = 0; for (k in old) deleted++; printf "%d %d %d\n", modified + 0, deleted, added + 0 }
  ' side=old "$1" side=new "$2"
}

# trusted_inputs_unchanged: compare what the run trusted with the records made at the end of
# phase 5. Prints one line per problem; prints nothing if all is as recorded. Uses no git.
trusted_inputs_unchanged() {
  local m d a tmp="$RECEIPT/.verify.$$"
  if [ -f "$RECEIPT/deps_compiled.sha256" ]; then
    snapshot_compiled "$tmp.compiled"
    read -r m d a <<<"$(compare_snapshots "$RECEIPT/deps_compiled.sha256" "$tmp.compiled")"
    if [ "$m" != "0" ] || [ "$d" != "0" ]; then echo "compiled dependency files: $m modified, $d deleted since phase 5"; fi
    echo "$a" >"$RECEIPT/deps_added.count"
  else
    echo "the phase-5 record of compiled dependency files is missing"
  fi
  if [ -f "$RECEIPT/mathlib_sources.sha256" ]; then
    snapshot_listed "$RECEIPT/mathlib_sources.sha256" "$tmp.src"
    if ! cmp -s "$RECEIPT/mathlib_sources.sha256" "$tmp.src"; then echo "Mathlib source files changed since phase 5"; fi
  else
    echo "the phase-5 record of Mathlib's source files is missing"
  fi
  if [ "$(lakefiles_listing | sha256sum | awk '{print $1}')" != "$DEPS_LAKEFILES_DIGEST" ]; then
    echo "the dependencies' Lake configuration files changed"
  fi
  rm -f "$tmp.compiled" "$tmp.src"
}

# --- the checker's binaries -------------------------------------------------------------------

# tools_unchanged: the three checker binaries are the ones built and hashed in phase 2.
# Prints one line per problem.
tools_unchanged() {
  local name bin
  for name in comparator lean4export landrun; do
    case "$name" in
      comparator) bin="$COMPARATOR_BIN" ;;
      lean4export) bin="$LEAN4EXPORT_BIN" ;;
      landrun) bin="$LANDRUN_BIN" ;;
    esac
    if [ ! -x "$bin" ]; then
      echo "$name binary is missing"
    elif [ "$(sha256_of "$bin")" != "$(fact_get "${name}_sha256")" ]; then
      echo "$name binary differs from the one built in phase 2"
    fi
  done
}

# --- sandbox probes, by behaviour -------------------------------------------------------------
# The systemd properties of every Comparator launch. RestrictAddressFamilies is what Comparator's
# README asks for; SystemCallArchitectures=native is what systemd's manual says to combine it
# with, so that the restriction cannot be sidestepped through the 32-bit system-call interface;
# OOMPolicy=continue only makes sure an exit code is recorded if the kernel kills a process.
# LimitSTACK: the kernel replay follows the proof's dependencies recursively, and a long enough
# chain of them would overflow the usual 8 MiB stack at the very end of a run that took hours.
# Stack is only used when needed; a Mathlib-scale run behaved identically with this limit.
UNIT_PROPS=(-p "RestrictAddressFamilies=~AF_UNIX" -p "SystemCallArchitectures=native" -p "OOMPolicy=continue" -p "LimitSTACK=1G")
UNIT_PROPS_TEXT="RestrictAddressFamilies=~AF_UNIX SystemCallArchitectures=native OOMPolicy=continue LimitSTACK=1G"

# af_unix_state: can THIS process create an AF_UNIX socket? Prints allowed, denied or unknown.
af_unix_state() {
  python3 -I -c '
import socket
try:
    socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    print("allowed")
except OSError:
    print("denied")
' 2>/dev/null || echo unknown
}

# decided_case: prints one line if an attempt of the main run has already settled the question
# (Comparator rejected the proof, or accepted it in a cold run); prints nothing otherwise.
decided_case() { python3 -I "$KIT_DIR/scripts/receipt.py" --decided "$QRH_WORK"; }

# sandbox_probes: (a) landrun, with the flags Comparator passes, lets a process write inside an
# allowed directory and not outside it; (b) a systemd user unit with the properties of the real
# run cannot create an AF_UNIX socket, and one without them can. Sets PROBE_FAILURES and records
# the boot the probes were made in.
sandbox_probes() {
  local probe="$QRH_WORK/sandbox-probe" flags py tcp_py tcp_outside tcp_inside
  PROBE_FAILURES=0
  rm -rf "$probe"
  mkdir -p "$probe/allowed"
  flags=(--best-effort --ro / --rw /dev -ldd -add-exec --rwx "$probe/allowed")
  if "$LANDRUN_BIN" "${flags[@]}" -- /bin/sh -c "echo inside > '$probe/allowed/in.txt'" >/dev/null 2>&1 && [ -f "$probe/allowed/in.txt" ]; then
    ok "sandbox: write inside the allowed directory succeeded"
  else
    log "FAIL  sandbox: could not write inside the allowed directory (landrun is not working)"
    PROBE_FAILURES=$((PROBE_FAILURES + 1))
  fi
  "$LANDRUN_BIN" "${flags[@]}" -- /bin/sh -c "echo outside > '$probe/out.txt'" >/dev/null 2>&1 || true
  if [ -e "$probe/out.txt" ]; then
    fact sandbox_enforcing "no"
    if [ "$QRH_DEV_NO_SANDBOX" = "1" ]; then
      warn "sandbox: a write OUTSIDE the allowed directory succeeded; continuing only because QRH_DEV_NO_SANDBOX=1"
      deviation "sandbox does not enforce on this machine (QRH_DEV_NO_SANDBOX=1). INVALID as a certification."
      fact invalidating_override "QRH_DEV_NO_SANDBOX"
    else
      log "FAIL  sandbox: a write OUTSIDE the allowed directory succeeded. Landlock is not enforcing; do not continue"
      PROBE_FAILURES=$((PROBE_FAILURES + 1))
    fi
  else
    ok "sandbox: write outside the allowed directory was denied"
    fact sandbox_enforcing "yes"
  fi

  # Informational: is outbound TCP blocked inside the sandbox? (Landlock ABI 4+, kernel 6.7+.)
  tcp_py='
import socket
try:
    socket.create_connection(("1.1.1.1", 443), timeout=8).close()
    print("open")
except PermissionError:
    print("denied")
except Exception:
    print("unreachable")
'
  tcp_outside="$(python3 -c "$tcp_py" 2>/dev/null || echo unreachable)"
  tcp_inside="$("$LANDRUN_BIN" "${flags[@]}" -- python3 -c "$tcp_py" 2>/dev/null || echo error)"
  case "$tcp_outside/$tcp_inside" in
    */denied) ok "sandbox: outbound TCP is denied inside the sandbox"; fact sandbox_tcp "blocked" ;;
    open/open) warn "sandbox: outbound TCP is NOT blocked inside the sandbox (older Landlock). File-system rules still apply"; fact sandbox_tcp "open" ;;
    *) warn "sandbox: could not tell whether TCP is blocked (outside: $tcp_outside, inside: $tcp_inside)"; fact sandbox_tcp "untested" ;;
  esac
  rm -rf "$probe"

  py='import socket; socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)'
  if [ "$QRH_NO_SYSTEMD" = "1" ]; then
    warn "AF_UNIX restriction not tested (QRH_NO_SYSTEMD=1)"
    fact af_unix_restricted "no"
    fact invalidating_override "QRH_NO_SYSTEMD"
  else
    have_user_systemd || die "no systemd user manager (see docs/TROUBLESHOOTING.md)"
    if systemd-run --user --wait --collect --quiet -- python3 -c "$py" >/dev/null 2>&1; then
      ok "AF_UNIX control: without the restriction a UNIX socket can be created"
    else
      log "FAIL  AF_UNIX control: could not create a UNIX socket even without the restriction (the test is not informative)"
      PROBE_FAILURES=$((PROBE_FAILURES + 1))
    fi
    if systemd-run --user --wait --collect --quiet "${UNIT_PROPS[@]}" -- python3 -c "$py" >/dev/null 2>&1; then
      log "FAIL  AF_UNIX: socket creation succeeded under the run's unit properties; the restriction is not in force"
      fact af_unix_restricted "no"
      PROBE_FAILURES=$((PROBE_FAILURES + 1))
    else
      ok "AF_UNIX: socket creation is denied under the run's unit properties"
      fact af_unix_restricted "yes"
    fi
  fi
  fact probes_boot_id "$(boot_id)"
}

# archive_attempt LABEL: move the files of the current attempt aside (NAME.x -> NAME.x.N).
# Prints N.
archive_attempt() {
  local label="$1" n=1 f
  while [ -e "$LOGS/$label.log.$n" ] || [ -e "$LOGS/$label.exit.$n" ] || [ -e "$LOGS/$label.job.sh.$n" ] || [ -e "$LOGS/$label.start.$n" ]; do n=$((n + 1)); done
  for f in job.sh log exit start end time unit mem.tsv mempeak type; do
    if [ -e "$LOGS/$label.$f" ]; then mv "$LOGS/$label.$f" "$LOGS/$label.$f.$n"; fi
  done
  echo "$n"
}
