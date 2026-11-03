#!/usr/bin/env bash
# QRH zeta23 add-on, step B2 report: after the zeta23-mnf run has ended, audit the MNF layer
# (plain `lean` in a landrun sandbox on MNF_AuditB2.lean: #print axioms and #check for every
# theorem the challenge names) and write the report.
#
#   scripts/z23_mnf_report.sh
#
# Writes  $QRH_WORK/mnf/MNF_ZETA23.md         the report
#         $QRH_WORK/mnf/audit.out             lean's output for MNF_AuditB2.lean
#         $QRH_WORK/qrh-zeta23-mnf-receipt.tar.gz   mnf/ + the run's logs + receipt facts
#         /tmp/qrh-zeta23-mnf-receipt.tar.gz   a world-readable copy
# Prints  MNF_ZETA23=ACCEPTED | REJECTED | INCOMPLETE  as its last line.
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
Z23="$QRH_WORK/formal-math/$Z23_SUBDIR"
MNFWORK="$QRH_WORK/mnf"
mkdir -p "$MNFWORK"
rm -f "$MNFWORK/MNF_ZETA23.md"
mnf_fact() { printf '%s\t%s\t%s\n' "$(ts)" "$1" "$2" >>"$RECEIPT/facts.tsv"; }

log "== zeta23 + MNF: report =="
if job_running "$LABEL"; then die "$LABEL is still running; see scripts/z23_mnf_status.sh"; fi
[ -f "$LOGS/$LABEL.exit" ] || die "no exit code for $LABEL; the run never finished (see scripts/z23_mnf_status.sh)"

# the files the run used must be as recorded (bytes only)
if (cd "$Z23" && sha256sum --quiet -c "$MNFWORK/mnf_sha256.txt" >/dev/null 2>&1); then mnf_fact mnf_files_after "unchanged"; else mnf_fact mnf_files_after "CHANGED"; fi
for pair in "Challenge.lean:$SHA_Z23_CHALLENGE" "ChallengeDeps.lean:$SHA_Z23_CHALLENGEDEPS" "$Z23_CONFIG:$SHA_Z23_CONFIG"; do
  [ "$(sha256_of "$Z23/${pair%%:*}")" = "${pair#*:}" ] || mnf_fact mnf_files_after "CHANGED (${pair%%:*})"
done

# audit compile: sandboxed lean, no lake
lean_prefix="$(fact_get lean_prefix)"
lp="$Z23/.lake/build/lib/lean"
for d in "$Z23"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && lp="$lp:$d"; done
rc_audit=0
if [ -f "$Z23/.lake/build/lib/lean/MNF/RH/Zeta23Restated.olean" ]; then
  log "auditing the MNF layer (sandboxed lean on MNF_AuditB2.lean)"
  (cd "$Z23" && LEAN_PATH="$lp" "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec \
      --env LEAN_PATH --env HOME --rox "$lean_prefix" -- "$lean_prefix/bin/lean" MNF_AuditB2.lean) \
      >"$MNFWORK/audit.out" 2>&1 || rc_audit=$?
else
  echo "MNF.RH.Zeta23Restated was not compiled by the Comparator run; no audit possible" >"$MNFWORK/audit.out"
  rc_audit=1
fi

rc=0
python3 -I "$ADDON_DIR/scripts/z23_mnf_check.py" --label "$LABEL" --logs "$LOGS" --mnfdir "$MNFWORK" --tree "$Z23" \
  --audit-rc "$rc_audit" --receipt "$RECEIPT" >"$MNFWORK/check.out" || rc=$?
cat "$MNFWORK/check.out"
result="$(tail -1 "$MNFWORK/check.out")"
mnf_fact mnf_zeta23 "$result"
tar -czf "$QRH_WORK/qrh-zeta23-mnf-receipt.tar.gz" -C "$QRH_WORK" mnf "logs/$LABEL.log" "logs/$LABEL.exit" "logs/$LABEL.start" "logs/$LABEL.end" "logs/$LABEL.time" "logs/$LABEL.job.sh" "logs/$LABEL.type" "logs/$LABEL.unit" receipt/facts.tsv 2>/dev/null || true
cp "$QRH_WORK/qrh-zeta23-mnf-receipt.tar.gz" /tmp/qrh-zeta23-mnf-receipt.tar.gz 2>/dev/null && chmod a+r /tmp/qrh-zeta23-mnf-receipt.tar.gz 2>/dev/null || true
log "report: $MNFWORK/MNF_ZETA23.md (also in $QRH_WORK/qrh-zeta23-mnf-receipt.tar.gz, copy in /tmp)"
echo "$result"
[ "$rc" = "0" ]
