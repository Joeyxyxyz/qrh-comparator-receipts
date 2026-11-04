#!/usr/bin/env bash
# QRH zeta23 add-on v3, step B3 (second run, label zeta23-density-v3): put the density layer on top of the zeta23 tree that Comparator
# checked (zeta23-main, PASS) and start a Comparator run on it through the main kit's launcher,
# label zeta23-density, challenge MNFChallengesD/Density.json, solution MNF.RH.DensityAll.
#
#   scripts/z23_density.sh                  adds the files, generates the challenge, starts the run
#   scripts/z23_density_status.sh --wait 540
#   scripts/z23_density_report.sh           afterwards
#
# The layer: the five MNF.RH files of step B2 (byte-identical, pinned), MNF/RH/GapDensity.lean
# (add-on v3's file, docstrings revised), MNF/RH/Density.lean, MNF/RH/Strip.lean,
# MNF/Extension/InjectionEjection.lean, Zeta23/Superlinear.lean, Zeta23/OffLine.lean,
# Zeta23/BohrLandau.lean (carries two `sorry` lemmas, NOT in the claim set), Zeta23/MNFBridge.lean,
# Zeta23/BL/{DPMV,DPMVexp,JensenDisc}.lean, and the top module MNF/RH/DensityAll.lean.
# The run is WARM with respect to the Zeta23 library (compiled by the accepted zeta23-main run) and,
# where step B2 ran in this tree, with respect to its five MNF.RH files; it is cold for every module
# this add-on introduces, which the script checks. The checkout is changed only by adding files and
# appending lean_lib stanzas to lakefile.toml; everything is recorded by hash.
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

LABEL="$D_LABEL"
MAIN="zeta23-main"
Z23="$QRH_WORK/formal-math/$Z23_SUBDIR"
DWORK="$QRH_WORK/$D_WORKDIR"
mkdir -p "$DWORK"
d_fact() { printf '%s\t%s\t%s\n' "$(ts)" "$1" "$2" >>"$RECEIPT/facts.tsv"; }

log "== zeta23 + density layer: prepare the run =="
problems="$(cd "$ADDON_DIR" && sha256sum --quiet -c MANIFEST.sha256 2>&1 | grep -v ': OK$' || true)"
[ -z "$problems" ] || die "the add-on differs from its manifest: $(echo "$problems" | head -3 | tr '\n' ' ')"
ok "add-on matches its manifest"

[ -f "$LOGS/$MAIN.exit" ] || die "no finished $MAIN run in $QRH_WORK; run the zeta23 add-on's scripts/z23_prepare.sh first"
[ "$(cat "$LOGS/$MAIN.exit")" = "0" ] || die "the $MAIN run did not exit 0; the layer is only judged on an accepted tree"
[ "$(fact_get verdict)" = "PASS" ] || die "the $MAIN receipt is not PASS (recorded: $(fact_get verdict))"
if job_running "$LABEL"; then die "$LABEL is already running; see scripts/z23_density_status.sh"; fi
if [ -e "$LOGS/$LABEL.start" ] || [ -e "$LOGS/$LABEL.exit" ]; then
  die "an attempt of $LABEL already exists in $QRH_WORK; report it with scripts/z23_density_report.sh"
fi
[ -f "$Z23/.lake/build/lib/lean/Solution.olean" ] || die "the zeta23 tree has no compiled Solution; the first run's build output is missing"
[ -x "$TOOLS/bin/nanoda_bin" ] || die "NanoDa is not built in this tree ($TOOLS/bin/nanoda_bin); the pinned configuration enables it (install cargo and rebuild the zeta23 add-on's tools first)"
d_fact "nanoda_bin_sha256_$LABEL" "$(sha256_of "$TOOLS/bin/nanoda_bin")"

for pair in "Challenge.lean:$SHA_Z23_CHALLENGE" "ChallengeDeps.lean:$SHA_Z23_CHALLENGEDEPS" "$Z23_CONFIG:$SHA_Z23_CONFIG" \
  "lake-manifest.json:$SHA_Z23_MANIFEST" "lean-toolchain:$SHA_Z23_TOOLCHAIN_FILE"; do
  check_sha "$Z23/${pair%%:*}" "${pair#*:}" "zeta23 ${pair%%:*}"
done

# the layer's files
mkdir -p "$Z23/MNF/RH" "$Z23/MNF/Extension" "$Z23/Zeta23/BL" "$Z23/MNFChallengesD"
for f in Core Gap Hypotheses Counting Zeta23Restated GapDensity Density Strip DensityPartial DensityAll; do
  cp "$ADDON_DIR/MNF/RH/$f.lean" "$Z23/MNF/RH/$f.lean"
done
cp "$ADDON_DIR/MNF/Extension/InjectionEjection.lean" "$Z23/MNF/Extension/InjectionEjection.lean"
for f in Superlinear OffLine BohrLandau MNFBridge; do cp "$ADDON_DIR/Zeta23/$f.lean" "$Z23/Zeta23/$f.lean"; done
for f in DPMV DPMVexp JensenDisc BohrLandauPartial; do cp "$ADDON_DIR/Zeta23/BL/$f.lean" "$Z23/Zeta23/BL/$f.lean"; done
check_sha "$Z23/MNF/RH/Core.lean" "$SHA_MNF_CORE" "MNF/RH/Core.lean (as in the MNF add-on v2 and step B2)"
check_sha "$Z23/MNF/RH/Gap.lean" "$SHA_MNF_GAP" "MNF/RH/Gap.lean (as in the MNF add-on v2 and step B2)"
check_sha "$Z23/MNF/RH/Hypotheses.lean" "$SHA_MNF_HYPOTHESES" "MNF/RH/Hypotheses.lean (as in the MNF add-on v2 and step B2)"
check_sha "$Z23/MNF/RH/Counting.lean" "$SHA_MNF_COUNTING" "MNF/RH/Counting.lean (as in step B2)"
check_sha "$Z23/MNF/RH/Zeta23Restated.lean" "$SHA_MNF_RESTATED" "MNF/RH/Zeta23Restated.lean (as in step B2)"
for name in MNF MNFChallenges MNFChallengesD; do
  if ! grep -q "^name = \"$name\"\$" "$Z23/lakefile.toml"; then
    python3 -I - "$ADDON_DIR/lakefile_append.toml" "$name" >>"$Z23/lakefile.toml" <<'PY'
import re, sys
txt = open(sys.argv[1]).read()
for stanza in re.split(r"\n(?=\[\[lean_lib\]\])", txt):
    if f'name = "{sys.argv[2]}"' in stanza:
        s = stanza[stanza.index("[[lean_lib]]"):]
        print("\n" + s.rstrip() + "\n", end="")
PY
  fi
done
(cd "$Z23" && python3 -I "$ADDON_DIR/scripts/z23_gen_density_challenge.py") || die "generating the challenge failed"

# cold for everything v3 introduces; the v2 modules may already be compiled (v2's run), which is recorded
B="$Z23/.lake/build/lib/lean"
for m in Zeta23/BL/BohrLandauPartial MNF/RH/DensityPartial MNFChallengesD/BohrLandau MNFChallengesD/BohrLandauPartial MNFChallengesD/DensityPartial; do
  [ ! -e "$B/$m.olean" ] || die "found a compiled $m before the run: the v3 layer is not cold in this tree"
done
warm=""; for m in MNF/RH/GapDensity MNF/RH/Density MNF/RH/Strip MNF/Extension/InjectionEjection Zeta23/Superlinear Zeta23/OffLine Zeta23/BohrLandau Zeta23/MNFBridge Zeta23/BL/DPMV Zeta23/BL/DPMVexp Zeta23/BL/JensenDisc; do [ -e "$B/$m.olean" ] && warm="$warm $m"; done
if [ -n "$warm" ]; then d_fact density_v2_files "compiled earlier in this tree (v2 run):$warm"; else d_fact density_v2_files "not compiled before this run"; fi
if [ -e "$B/MNF/RH/Core.olean" ]; then d_fact density_b2_files "compiled earlier in this tree (step B2): warm for Core, Gap, Hypotheses, Counting, Zeta23Restated"; else d_fact density_b2_files "not compiled before this run"; fi
(cd "$Z23" && sha256sum MNF/RH/*.lean MNF/Extension/*.lean Zeta23/Superlinear.lean Zeta23/OffLine.lean Zeta23/BohrLandau.lean Zeta23/MNFBridge.lean Zeta23/BL/*.lean MNFChallengesD/*.lean MNFChallengesD/Density.json "$D_AUDIT" lakefile.toml) >"$DWORK/density_sha256.txt"
d_fact density_files_sha256 "$(sha256_of "$DWORK/density_sha256.txt")"
d_fact density_lakefile_after_sha256 "$(sha256_of "$Z23/lakefile.toml")"
d_fact density_theorems "$(python3 -I -c 'import json,sys;print(len(json.load(open(sys.argv[1]))["theorem_names"]))' "$Z23/$D_CONFIG")"
d_fact density_definitions "$(cat "$Z23"/MNFChallengesD/*.lean | grep -cE '^(noncomputable )?def ')"
d_fact density_sorries_outside_claims "Zeta23/BohrLandau.lean: meanSquare_strip, rightHalfBound_of_meanSquare (not in the claim set)"
ok "density layer in place: $(fact_get density_theorems) theorems, $(fact_get density_definitions) definitions, challenge $D_CONFIG (no definition holes, NanoDa enabled)"

sandbox_probes
[ "$PROBE_FAILURES" = "0" ] || die "the sandbox probes failed; do not run"
d_fact "probes_boot_id_$LABEL" "$(boot_id)"
log "starting Comparator on the density layer ($D_CONFIG, solution $D_SOLUTION_MODULE), warm with respect to Zeta23, kernels: Lean + NanoDa"
QRH_WORK="$QRH_WORK" "$KIT/scripts/run_comparator.sh" --label "$LABEL" --dir "$Z23" --config "$D_CONFIG" --run-type warm --detach ||
  die "the run could not be started (see above)"
for _ in $(seq 1 20); do [ -e "$LOGS/$LABEL.start" ] && break; sleep 1; done
cat <<MSG

[zeta23+density] The run is detached (minutes: Mathlib and Zeta23 are compiled; the layer and the
                 challenge are built, exported and replayed). Watch it with
                     $ADDON_DIR/scripts/z23_density_status.sh --wait 540
                 When it says STATE=finished, run
                     $ADDON_DIR/scripts/z23_density_report.sh
MSG
