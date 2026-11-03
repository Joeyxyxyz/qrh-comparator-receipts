#!/usr/bin/env bash
# QRH MNF add-on, step 2: after the Comparator run on the library has finished, audit the
# library (axiom reports and printed statements, with plain `lean` in a landrun sandbox, against
# the tree Comparator built in $QRH_WORK/mnf-tree) and write the report.
#
#   scripts/mnf_report.sh
#
# Writes  $QRH_WORK/mnf/MNF_LIBRARY.md     the report
#         $QRH_WORK/mnf/audit.out          lean's output for MNF_Audit.lean
#         $QRH_WORK/qrh-mnf-receipt.tar.gz  the report, the run's log and exit code, the hashes
# Prints  MNF_LIBRARY=ACCEPTED | MNF_LIBRARY=REJECTED | MNF_LIBRARY=INCOMPLETE  as its last line.
ADDON_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
KIT="${QRH_KIT_DIR:-/opt/qrh-kit}"
[ -f "$KIT/scripts/lib.sh" ] || { echo "main kit not found at $KIT (set QRH_KIT_DIR)" >&2; exit 2; }
# shellcheck source=/opt/qrh-kit/scripts/lib.sh
. "$KIT/scripts/lib.sh"
require_not_root
need_cmd python3

LABEL="mnf-library-v3"
TREE="$QRH_WORK/mnf-tree"
MNFWORK="$QRH_WORK/mnf-v3"
MNFDIR="$MNFWORK"
LOGS="$MNFWORK/logs"
mkdir -p "$MNFDIR"
rm -f "$MNFDIR/MNF_LIBRARY.md"
mnf_fact() { printf '%s\t%s\t%s\n' "$(ts)" "$1" "$2" >>"$MNFWORK/receipt/facts.tsv"; }

log "== MNF library v3: report =="
[ -f "$TREE/.mnf-prepared" ] || die "no prepared tree at $TREE; run scripts/mnf_prepare.sh first"
if job_running "$LABEL"; then die "$LABEL is still running; see scripts/mnf_status.sh"; fi
[ -f "$LOGS/$LABEL.exit" ] || die "no exit code for $LABEL; the run never finished (see scripts/mnf_status.sh)"

# Audit compile: the library's own #print axioms and #check, sandboxed, no lake.
lean_prefix="$(cd "$QRH_WORK" && elan run "$OAI_TOOLCHAIN" lean --print-prefix)"
[ -x "$lean_prefix/bin/lean" ] || die "cannot find the Lean toolchain"
lp="$TREE/.lake/build/lib/lean"
for d in "$TREE"/.lake/packages/*/.lake/build/lib/lean; do
  if [ -d "$d" ]; then lp="$lp:$d"; fi
done
rc_audit=0
if [ -f "$TREE/.lake/build/lib/lean/MNF/RH/Unconditional.olean" ]; then
  log "auditing the library (sandboxed lean on MNF_Audit.lean)"
  (cd "$TREE" && LEAN_PATH="$lp" "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec \
      --env LEAN_PATH --env HOME --rox "$lean_prefix" -- "$lean_prefix/bin/lean" MNF_Audit.lean) \
      >"$MNFDIR/audit.out" 2>&1 || rc_audit=$?
else
  echo "MNF.RH.Unconditional was not compiled by the Comparator run; no audit possible" >"$MNFDIR/audit.out"
  rc_audit=1
fi

rc=0
python3 -I "$ADDON_DIR/scripts/mnf_check.py" \
  --label "$LABEL" --logs "$LOGS" --mnfdir "$MNFDIR" --tree "$TREE" --addon "$ADDON_DIR" \
  --audit-rc "$rc_audit" --receipt "$RECEIPT" --mnf-receipt "$MNFWORK/receipt" >"$MNFDIR/check.out" || rc=$?
cat "$MNFDIR/check.out"
result="$(tail -1 "$MNFDIR/check.out")"
mnf_fact mnf_library "$result"
tar -czf "$QRH_WORK/qrh-mnf-v3-receipt.tar.gz" -C "$QRH_WORK" --exclude=mnf-v3/tools mnf-v3 2>/dev/null || true
log "report: $MNFDIR/MNF_LIBRARY.md (also in $QRH_WORK/qrh-mnf-v3-receipt.tar.gz)"
echo "$result"
[ "$rc" = "0" ]
