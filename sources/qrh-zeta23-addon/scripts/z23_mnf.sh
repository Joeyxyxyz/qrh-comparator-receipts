#!/usr/bin/env bash
# QRH zeta23 add-on, step B2: put the MNF.RH library, its counting vocabulary and the restatement
# of zeta23's Theorems A–D over MNF's definitions on top of the zeta23 tree that Comparator has
# just checked, and start a second Comparator run on it (challenge MNFChallenges/Restated.json,
# solution MNF.RH.Zeta23Restated), through the main kit's launcher, label zeta23-mnf.
#
#   scripts/z23_mnf.sh                 adds the files, generates the challenge, starts the run
#   scripts/z23_mnf_status.sh --wait 540
#   scripts/z23_mnf_report.sh          afterwards
#
# This run is WARM with respect to the Zeta23 library by design (the oleans Comparator built in
# the zeta23-main run are reused, exactly as the MNF add-on reused OpenAI's tree); it is cold
# with respect to MNF/ and MNFChallenges/, which have never been compiled in this tree. The
# zeta23 checkout is changed in three ways, all recorded by hash: MNF/ and MNFChallenges/ added,
# MNF_AuditB2.lean added, and one lean_lib stanza appended to lakefile.toml.
ADDON_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
KIT="${QRH_KIT_DIR:-/opt/qrh-kit}"
[ -f "$KIT/scripts/lib.sh" ] || { echo "main kit not found at $KIT (set QRH_KIT_DIR)" >&2; exit 2; }
export QRH_WORK="${QRH_Z23_WORK:-$HOME/qrh-zeta23-work}"
# shellcheck source=/opt/qrh-kit/scripts/lib.sh
. "$KIT/scripts/lib.sh"
# shellcheck source=../PINS-zeta23.env
. "$ADDON_DIR/PINS-zeta23.env"
require_not_root
need_cmd python3

LABEL="zeta23-mnf"
MAIN="zeta23-main"
Z23="$QRH_WORK/formal-math/$Z23_SUBDIR"
MNFWORK="$QRH_WORK/mnf"
mkdir -p "$MNFWORK"
mnf_fact() { printf '%s\t%s\t%s\n' "$(ts)" "$1" "$2" >>"$RECEIPT/facts.tsv"; }

log "== zeta23 + MNF: prepare the second run =="
problems="$(cd "$ADDON_DIR" && sha256sum --quiet -c MANIFEST.sha256 2>&1 | grep -v ': OK$' || true)"
[ -z "$problems" ] || die "the add-on differs from its manifest: $(echo "$problems" | head -3 | tr '\n' ' ')"
ok "add-on matches its manifest"

# The first run must have been accepted and reported.
[ -f "$LOGS/$MAIN.exit" ] || die "no finished $MAIN run in $QRH_WORK; run scripts/z23_prepare.sh and wait for it first"
[ "$(cat "$LOGS/$MAIN.exit")" = "0" ] || die "the $MAIN run did not exit 0; the MNF layer is only judged on an accepted tree"
[ "$(fact_get verdict)" = "PASS" ] || die "the $MAIN receipt is not PASS (recorded: $(fact_get verdict)); run scripts/z23_report.sh first"
if job_running "$LABEL"; then die "$LABEL is already running; see scripts/z23_mnf_status.sh"; fi
if [ -e "$LOGS/$LABEL.start" ] || [ -e "$LOGS/$LABEL.exit" ]; then
  die "an attempt of $LABEL already exists in $QRH_WORK; report it with scripts/z23_mnf_report.sh"
fi
[ -f "$Z23/.lake/build/lib/lean/Solution.olean" ] || die "the zeta23 tree has no compiled Solution; the first run's build output is missing"

# What the first run trusted must still be as pinned (bytes only).
for pair in "Challenge.lean:$SHA_Z23_CHALLENGE" "ChallengeDeps.lean:$SHA_Z23_CHALLENGEDEPS" "$Z23_CONFIG:$SHA_Z23_CONFIG" \
  "lake-manifest.json:$SHA_Z23_MANIFEST" "lean-toolchain:$SHA_Z23_TOOLCHAIN_FILE"; do
  check_sha "$Z23/${pair%%:*}" "${pair#*:}" "zeta23 ${pair%%:*}"
done

# The MNF layer: the three library files are byte-identical to the MNF add-on v2's (pinned here),
# the two new files are this add-on's.
mkdir -p "$Z23/MNF/RH" "$Z23/MNFChallenges"
for f in Core Gap Hypotheses Counting Zeta23Restated; do
  cp "$ADDON_DIR/MNF/RH/$f.lean" "$Z23/MNF/RH/$f.lean"
done
cp "$ADDON_DIR/MNFChallenges/theorem_list.txt" "$Z23/MNFChallenges/theorem_list.txt"
check_sha "$Z23/MNF/RH/Core.lean" "$SHA_MNF_CORE" "MNF/RH/Core.lean (as in the MNF add-on v2)"
check_sha "$Z23/MNF/RH/Gap.lean" "$SHA_MNF_GAP" "MNF/RH/Gap.lean (as in the MNF add-on v2)"
check_sha "$Z23/MNF/RH/Hypotheses.lean" "$SHA_MNF_HYPOTHESES" "MNF/RH/Hypotheses.lean (as in the MNF add-on v2)"
if ! grep -q '^name = "MNF"$' "$Z23/lakefile.toml"; then
  cat "$ADDON_DIR/lakefile_append.toml" >>"$Z23/lakefile.toml"
fi
(cd "$Z23" && python3 -I "$ADDON_DIR/scripts/z23_gen_challenge.py") || die "generating the challenge failed"
found="$(find "$Z23/.lake/build/lib/lean/MNF" "$Z23/.lake/build/lib/lean/MNFChallenges" -type f -print -quit 2>/dev/null || true)"
[ -z "$found" ] || die "found compiled MNF files ($found) before the run: the MNF layer is not cold in this tree"
(cd "$Z23" && sha256sum MNF/RH/*.lean MNFChallenges/*.lean MNFChallenges/Restated.json MNFChallenges/theorem_list.txt MNF_AuditB2.lean lakefile.toml) >"$MNFWORK/mnf_sha256.txt"
mnf_fact mnf_files_sha256 "$(sha256_of "$MNFWORK/mnf_sha256.txt")"
mnf_fact mnf_lakefile_after_sha256 "$(sha256_of "$Z23/lakefile.toml")"
mnf_fact mnf_theorems "$(python3 -I -c 'import json,sys;print(len(json.load(open(sys.argv[1]))["theorem_names"]))' "$Z23/MNFChallenges/Restated.json")"
mnf_fact mnf_definitions "$(cat "$Z23"/MNFChallenges/*.lean | grep -cE '^(noncomputable )?def ')"
ok "MNF layer in place: $(fact_get mnf_theorems) theorems, $(fact_get mnf_definitions) definitions, challenge MNFChallenges/Restated.json (no definition holes, NanoDa enabled)"

sandbox_probes
[ "$PROBE_FAILURES" = "0" ] || die "the sandbox probes failed; do not run"
mnf_fact "probes_boot_id_$LABEL" "$(boot_id)"
log "starting Comparator on the MNF layer (MNFChallenges/Restated.json, solution MNF.RH.Zeta23Restated), warm with respect to Zeta23, kernels: Lean + NanoDa"
QRH_WORK="$QRH_WORK" "$KIT/scripts/run_comparator.sh" --label "$LABEL" --dir "$Z23" --config MNFChallenges/Restated.json --run-type warm --detach ||
  die "the run could not be started (see above)"
for _ in $(seq 1 20); do [ -e "$LOGS/$LABEL.start" ] && break; sleep 1; done
cat <<EOF

[zeta23+MNF] The run is detached (minutes: Mathlib and Zeta23 are compiled; only the MNF layer and
             the challenge are built). Watch it with
                 $ADDON_DIR/scripts/z23_mnf_status.sh --wait 540
             When it says STATE=finished, run
                 $ADDON_DIR/scripts/z23_mnf_report.sh
EOF
