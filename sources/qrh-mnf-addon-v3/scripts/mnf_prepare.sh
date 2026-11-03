#!/usr/bin/env bash
# QRH MNF add-on, step 1: put the MNF.RH library on top of the tree Comparator checked and start
# a Comparator run on it (challenge MNFChallenges/RH.json, solution MNF.RH.Unconditional).
#
# Version 3 of the add-on: the v2 library plus Counting, Reduction, Schrodinger (with the Sturm–
# Liouville theorem) and GapDensity; a challenge with no definition holes. Runs only after the main kit reached PASS. Never touches the verified tree: it works on a full
# copy, $QRH_WORK/mnf-tree, so the receipt in $QRH_WORK/receipt keeps describing an unmodified
# tree. In the copy it adds MNF/, MNFChallenges/ and two lean_lib lines at the end of
# lakefile.lean (lakefile_append.lean), nothing else. Comparator then builds the challenge and
# the solution itself, inside its sandbox, and judges them.
#
#   scripts/mnf_prepare.sh            copies the tree (a few minutes), starts the run, returns
#   scripts/mnf_status.sh             to watch it
#   scripts/mnf_report.sh             afterwards
ADDON_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
KIT="${QRH_KIT_DIR:-/opt/qrh-kit}"
[ -f "$KIT/scripts/lib.sh" ] || { echo "main kit not found at $KIT (set QRH_KIT_DIR)" >&2; exit 2; }
# shellcheck source=/opt/qrh-kit/scripts/lib.sh
. "$KIT/scripts/lib.sh"
require_not_root
need_cmd python3
need_cmd sha256sum

LABEL="mnf-library-v3"
TREE="$QRH_WORK/mnf-tree"
# The add-on (v3) keeps its own logs and facts under $QRH_WORK/mnf-v3, so neither the main receipt nor
# the earlier add-on runs ($QRH_WORK/mnf, mnf-v2) are touched, and the main receipt
# nor the v1 add-on's $QRH_WORK/mnf is touched, and the main receipt
# ($QRH_WORK/receipt, sealed at phase 7) is never appended to. The kit's run_comparator.sh is
# pointed at that directory; it finds the tools through a link.
MNFWORK="$QRH_WORK/mnf-v3"
mkdir -p "$MNFWORK/logs" "$MNFWORK/receipt"
ln -sfn "$TOOLS" "$MNFWORK/tools"
LOGS="$MNFWORK/logs"
mnf_fact() { printf '%s\t%s\t%s\n' "$(ts)" "$1" "$2" >>"$MNFWORK/receipt/facts.tsv"; }

log "== MNF library v3: prepare =="
verdict="$(fact_get verdict)"
[ "$verdict" = "PASS" ] || die "the library run only means something after a PASS of the main kit (recorded verdict: ${verdict:-none})"
require_phase 7

# The add-on itself must be what was shipped.
problems="$(cd "$ADDON_DIR" && sha256sum --quiet -c MANIFEST.sha256 2>&1 | grep -v ': OK$' || true)"
[ -z "$problems" ] || die "the add-on differs from its manifest: $(echo "$problems" | head -3 | tr '\n' ' ')"
extra="$(cd "$ADDON_DIR" && find . -type f ! -name MANIFEST.sha256 ! -path './.claude/settings.local.json' ! -name '._*' | sed 's|^\./||' | LC_ALL=C sort | comm -23 - <(awk '{print $2}' MANIFEST.sha256 | LC_ALL=C sort))"
[ -z "$extra" ] || die "files in the add-on that are not in its manifest: $(echo "$extra" | head -3 | tr '\n' ' ')"
ok "add-on matches its manifest"

if job_running "$LABEL"; then die "$LABEL is already running; see scripts/status.sh $LABEL"; fi

# The verified tree, as Comparator left it.
verify_oai_tree
[ -f "$OAI_LEAN/.lake/build/lib/lean/$(echo "$OAI_SOLUTION_MODULE" | tr . /).olean" ] ||
  die "the compiled form of $OAI_SOLUTION_MODULE is not in $OAI_LEAN/.lake/build"

# A fresh copy every time this step runs: the copy is disposable, the original is not.
if [ -d "$TREE" ]; then
  log "removing the previous copy $TREE"
  rm -rf "$TREE"
fi
log "copying the verified tree to $TREE (this is the slow part: several GB)"
cp -a "$OAI_LEAN" "$TREE"
# Nothing of the copy is a git repository of ours to verify; drop the pointer so no script
# mistakes it for the original.
rm -rf "$TREE/.git"

cp -r "$ADDON_DIR/MNF" "$TREE/MNF"
cp -r "$ADDON_DIR/SturmLiouville" "$TREE/SturmLiouville"
cp -r "$ADDON_DIR/MNFChallenges" "$TREE/MNFChallenges"
cp "$ADDON_DIR/MNF_Audit.lean" "$TREE/MNF_Audit.lean"
cat "$ADDON_DIR/lakefile_append.lean" >>"$TREE/lakefile.lean"
chmod -R u+w "$TREE/MNF" "$TREE/SturmLiouville" "$TREE/MNFChallenges" "$TREE/MNF_Audit.lean" "$TREE/lakefile.lean"
date -u +%Y-%m-%dT%H:%M:%SZ >"$TREE/.mnf-prepared"

# Record what was added, by hash.
(cd "$ADDON_DIR" && sha256sum MNF/RH/*.lean SturmLiouville/*.lean MNFChallenges/*.lean MNFChallenges/RH.json MNF_Audit.lean lakefile_append.lean) >"$MNFWORK/library_sha256.txt"
sha256sum "$TREE/lakefile.lean" | awk '{print $1}' >"$MNFWORK/lakefile_after_sha256.txt"
mnf_fact mnf_library_files "$(sha256sum "$MNFWORK/library_sha256.txt" | awk '{print $1}')"
mnf_fact mnf_tree "$TREE"
mnf_fact mnf_prepared "$(cat "$TREE/.mnf-prepared")"
mnf_fact main_verdict "$verdict"
ok "tree copied; MNF/, SturmLiouville/, MNFChallenges/ and MNF_Audit.lean added; lakefile.lean extended by $(wc -l <"$ADDON_DIR/lakefile_append.lean") lines"

log "starting Comparator on the library (challenge MNFChallenges/RH.json, solution MNF.RH.Unconditional)"
QRH_WORK="$MNFWORK" "$KIT/scripts/run_comparator.sh" --label "$LABEL" --dir "$TREE" --config MNFChallenges/RH.json --detach
cat <<EOF

[mnf] The run is detached. It builds the challenge and the solution (minutes to an hour: the
      challenge imports all of Mathlib), exports both, and checks them. Watch it with
          $ADDON_DIR/scripts/mnf_status.sh --wait 540
      When it says STATE=finished, run
          $ADDON_DIR/scripts/mnf_report.sh
EOF
