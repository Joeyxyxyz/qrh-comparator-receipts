#!/usr/bin/env bash
# QRH zeta23 add-on, step 2: after the Comparator run has ended, re-check that what the run trusted
# is as it was (bytes only, no git: nothing under .lake is trusted after the solution was built),
# print the axiom reports of the 17 statements with plain `lean` in a landrun sandbox, and write
# the receipt.
#
#   scripts/z23_report.sh
#
# Writes  $QRH_WORK/receipt/RECEIPT-zeta23.md   the receipt        (QRH_WORK = ~/qrh-zeta23-work)
#         $QRH_WORK/receipt/receipt.json        the same, as data
#         $QRH_WORK/receipt/audit.out           lean's output for scripts/PrintAxioms.lean
#         $QRH_WORK/qrh-zeta23-receipt.tar.gz   receipt + logs + dependency records
#         /tmp/qrh-zeta23-receipt.tar.gz        a world-readable copy, for reading from another account
# Prints  VERDICT=PASS | REJECTED | ERROR | INVALID | INCOMPLETE  as its last line.
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

LABEL="zeta23-main"
FM_DIR="$QRH_WORK/formal-math"
Z23="$FM_DIR/$Z23_SUBDIR"

log "== zeta23: report =="
if job_running "$LABEL"; then
  fact main_state "running"
  log "the run is still going; the receipt will say INCOMPLETE"
elif [ -f "$LOGS/$LABEL.exit" ]; then
  fact main_state "finished"
  log "checking that what the run trusted is as it was (bytes only)"
  problems=""
  for pair in "Challenge.lean:$SHA_Z23_CHALLENGE" "ChallengeDeps.lean:$SHA_Z23_CHALLENGEDEPS" "$Z23_CONFIG:$SHA_Z23_CONFIG" \
    "lakefile.toml:$SHA_Z23_LAKEFILE" "lake-manifest.json:$SHA_Z23_MANIFEST" "lean-toolchain:$SHA_Z23_TOOLCHAIN_FILE" \
    "Challenge/XiPrime.lean:$SHA_Z23_CHALLENGE_XIPRIME" "ChallengeDeps/XiPrime.lean:$SHA_Z23_CHALLENGEDEPS_XIPRIME"; do
    f="${pair%%:*}"; want="${pair#*:}"
    if [ ! -f "$Z23/$f" ]; then problems="$problems;$f missing"
    elif [ "$(sha256_of "$Z23/$f")" != "$want" ]; then problems="$problems;$f changed"; fi
  done
  cfg="$(fact_get config_used)"
  if [ -n "$cfg" ] && [ "$(sha256_of "$Z23/$cfg" 2>/dev/null)" != "$(fact_get config_used_sha256)" ]; then problems="$problems;$cfg changed"; fi
  if [ -z "$problems" ]; then fact trusted_files_after "unchanged"; else fact trusted_files_after "${problems#;}"; fi
  # compiled dependencies: re-hash exactly the recorded paths
  if [ -f "$RECEIPT/deps_compiled.sha256" ]; then
    tmp="$RECEIPT/.verify.$$"
    (cd "$Z23/.lake/packages" && awk '{ print $2 }' "$RECEIPT/deps_compiled.sha256" | tr '\n' '\0' | xargs -0 -r -n 64 -P "$(nproc)" sha256sum 2>/dev/null || true) | LC_ALL=C sort -k 2 >"$tmp"
    read -r m d a <<<"$(compare_snapshots "$RECEIPT/deps_compiled.sha256" "$tmp")"
    if [ "$m" = "0" ] && [ "$d" = "0" ]; then
      fact deps_after "unchanged"
    else
      awk 'side == "old" { old[$2] = $1; next } { if ($2 in old) { if (old[$2] != $1) print "modified " $2; delete old[$2] } } END { for (k in old) print "deleted " k }' side=old "$RECEIPT/deps_compiled.sha256" side=new "$tmp" >"$RECEIPT/deps_modified.txt"
      fact deps_after "$m modified, $d deleted (receipt/deps_modified.txt)"
    fi
    rm -f "$tmp"
    (cd "$Z23/.lake/packages" && find . -mindepth 2 -maxdepth 2 \( -name lakefile.lean -o -name lakefile.toml \) -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum) >"$RECEIPT/.lakefiles.$$"
    if [ "$(sha256_of "$RECEIPT/.lakefiles.$$")" = "$(fact_get dep_lakefiles_digest)" ]; then fact dep_lakefiles_after "unchanged"; else fact dep_lakefiles_after "CHANGED"; fi
    rm -f "$RECEIPT/.lakefiles.$$"
  else
    fact deps_after "no record"
  fi
  # the checker's binaries
  t=""
  for pair in "comparator:$COMPARATOR_BIN" "lean4export:$LEAN4EXPORT_BIN" "landrun:$LANDRUN_BIN"; do
    n="${pair%%:*}"; b="${pair#*:}"
    if [ ! -x "$b" ]; then t="$t;$n missing"; elif [ "$(sha256_of "$b")" != "$(fact_get "${n}_sha256")" ]; then t="$t;$n differs"; fi
  done
  if [ "$(fact_get nanoda_enabled)" = "yes" ]; then
    if [ "$(sha256_of "$TOOLS/bin/nanoda_bin" 2>/dev/null)" != "$(fact_get nanoda_sha256)" ]; then t="$t;nanoda differs"; fi
  fi
  if [ -z "$t" ]; then fact tools_after "unchanged"; else fact tools_after "${t#;}"; fi
  fact addon_after "$(cd "$ADDON_DIR" && sha256sum --quiet -c MANIFEST.sha256 >/dev/null 2>&1 && echo unmodified || echo CHANGED)"

  # the audit: the project's own #print axioms file, with plain lean, sandboxed, read-only
  if [ -f "$Z23/scripts/PrintAxioms.lean" ] && [ -f "$Z23/.lake/build/lib/lean/Solution.olean" ]; then
    lean_prefix="$(fact_get lean_prefix)"
    lp="$Z23/.lake/build/lib/lean"
    for d in "$Z23"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && lp="$lp:$d"; done
    log "auditing the 17 statements (sandboxed lean on scripts/PrintAxioms.lean)"
    rc_audit=0
    (cd "$Z23" && LEAN_PATH="$lp" "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec \
        --env LEAN_PATH --env HOME --rox "$lean_prefix" -- "$lean_prefix/bin/lean" scripts/PrintAxioms.lean) \
        >"$RECEIPT/audit.out" 2>&1 || rc_audit=$?
    fact audit_rc "$rc_audit"
  else
    echo "no audit: Solution was not compiled, or scripts/PrintAxioms.lean is absent" >"$RECEIPT/audit.out"
    fact audit_rc "skipped"
  fi
elif [ -f "$LOGS/$LABEL.unit" ] || [ -f "$LOGS/$LABEL.start" ]; then
  fact main_state "lost"
else
  fact main_state "not-started"
fi

cp "$ADDON_DIR/PINS-zeta23.env" "$RECEIPT/PINS-zeta23.env"
python3 -I "$ADDON_DIR/scripts/z23_receipt.py" "$QRH_WORK" "$ADDON_DIR" >"$RECEIPT/receipt.out" || die "could not build the receipt"
verdict="$(sed -n 's/^VERDICT=//p' "$RECEIPT/receipt.out" | tail -n 1)"
fact verdict "$verdict"
sed '$d' "$RECEIPT/receipt.out"
tarball="$QRH_WORK/qrh-zeta23-receipt.tar.gz"
tar -czf "$tarball" -C "$QRH_WORK" receipt logs 2>/dev/null || true
cp "$tarball" /tmp/qrh-zeta23-receipt.tar.gz 2>/dev/null && chmod a+r /tmp/qrh-zeta23-receipt.tar.gz 2>/dev/null || true
log "receipt: $RECEIPT/RECEIPT-zeta23.md   bundle: $tarball (copy in /tmp)"
echo "VERDICT=$verdict"
