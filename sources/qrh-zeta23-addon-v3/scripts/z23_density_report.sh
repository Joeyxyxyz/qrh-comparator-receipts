#!/usr/bin/env bash
# QRH zeta23 add-on v2, step B3 report: after the zeta23-density run has ended, audit the layer
# (plain `lean` in a landrun sandbox on MNF_AuditDensity.lean: #print axioms and #check for every
# theorem the challenge names) and write the report.
#
#   scripts/z23_density_report.sh
#
# Writes  $QRH_WORK/density/MNF_DENSITY.md            the report
#         $QRH_WORK/density/audit.out                 lean's output for MNF_AuditDensity.lean
#         $QRH_WORK/qrh-zeta23-density-receipt.tar.gz density/ + the run's logs + receipt facts
#         "/tmp/$D_BUNDLE"      a world-readable copy
# Prints  MNF_DENSITY=ACCEPTED | REJECTED | INCOMPLETE  as its last line.
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
Z23="$QRH_WORK/formal-math/$Z23_SUBDIR"
DWORK="$QRH_WORK/$D_WORKDIR"
mkdir -p "$DWORK"
rm -f "$DWORK/MNF_DENSITY.md"
d_fact() { printf '%s\t%s\t%s\n' "$(ts)" "$1" "$2" >>"$RECEIPT/facts.tsv"; }

log "== zeta23 + density layer: report =="
if job_running "$LABEL"; then die "$LABEL is still running; see scripts/z23_density_status.sh"; fi
[ -f "$LOGS/$LABEL.exit" ] || die "no exit code for $LABEL; the run never finished (see scripts/z23_density_status.sh)"

if (cd "$Z23" && sha256sum --quiet -c "$DWORK/density_sha256.txt" >/dev/null 2>&1); then d_fact density_files_after "unchanged"; else d_fact density_files_after "CHANGED"; fi
for pair in "Challenge.lean:$SHA_Z23_CHALLENGE" "ChallengeDeps.lean:$SHA_Z23_CHALLENGEDEPS" "$Z23_CONFIG:$SHA_Z23_CONFIG"; do
  [ "$(sha256_of "$Z23/${pair%%:*}")" = "${pair#*:}" ] || d_fact density_files_after "CHANGED (${pair%%:*})"
done

lean_prefix="$(fact_get lean_prefix)"
lp="$Z23/.lake/build/lib/lean"
for d in "$Z23"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && lp="$lp:$d"; done
rc_audit=0
if [ -f "$Z23/.lake/build/lib/lean/MNF/RH/DensityAll.olean" ]; then
  log "auditing the density layer (sandboxed lean on $D_AUDIT)"
  (cd "$Z23" && LEAN_PATH="$lp" "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec \
      --env LEAN_PATH --env HOME --rox "$lean_prefix" -- "$lean_prefix/bin/lean" "$D_AUDIT") \
      >"$DWORK/audit.out" 2>&1 || rc_audit=$?
else
  echo "$D_SOLUTION_MODULE was not compiled by the Comparator run; no audit possible" >"$DWORK/audit.out"
  rc_audit=1
fi

rc=0
python3 -I "$ADDON_DIR/scripts/z23_density_check.py" --label "$LABEL" --logs "$LOGS" --ddir "$DWORK" --tree "$Z23" \
  --config "$D_CONFIG" --audit-rc "$rc_audit" --receipt "$RECEIPT" >"$DWORK/check.out" || rc=$?
cat "$DWORK/check.out"
result="$(tail -1 "$DWORK/check.out")"
d_fact density_result "$result"
tar -czf "$QRH_WORK/$D_BUNDLE" -C "$QRH_WORK" "$D_WORKDIR" "logs/$LABEL.log" "logs/$LABEL.exit" "logs/$LABEL.start" "logs/$LABEL.end" "logs/$LABEL.time" "logs/$LABEL.job.sh" "logs/$LABEL.type" "logs/$LABEL.unit" receipt/facts.tsv 2>/dev/null || true
cp "$QRH_WORK/$D_BUNDLE" "/tmp/$D_BUNDLE" 2>/dev/null && chmod a+r "/tmp/$D_BUNDLE" 2>/dev/null || true
log "report: $DWORK/MNF_DENSITY.md (also in $QRH_WORK/$D_BUNDLE, copy in /tmp)"
echo "$result"
[ "$rc" = "0" ]
