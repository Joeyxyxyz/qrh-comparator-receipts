#!/usr/bin/env bash
# Phase 7. Verdict and receipt. Changes nothing in the OpenAI tree; safe to run at any time and
# more than once. Prints the receipt and ends with a line VERDICT=...
#
#   PASS         Comparator accepted in a cold run and every condition of the protocol held.
#   PROVISIONAL  Comparator accepted in a warm run. Not a certification.
#   INVALID      Comparator accepted but a condition did not hold. Not a certification.
#   REJECTED     Comparator decided against the proof.
#   ERROR        The run ended without a decision. Says nothing about the proof.
#   INCOMPLETE   Not finished, or not started.
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root
need_cmd python3

label="$MAIN_LABEL"
if job_running "$label"; then
  fact main_state "running"
  log "the main run is still going; the receipt will say INCOMPLETE"
elif [ -f "$LOGS/$label.exit" ]; then
  fact main_state "finished"
  log "== receipt: checking that what the run trusted is as it was =="
  # From here on nothing under .lake is trusted, so nothing below runs git or any other
  # program that interprets files there. Bytes are hashed and compared, nothing else.
  if (verify_oai_tree) >/dev/null 2>&1; then
    fact tree_verified_after "yes"
  else
    fact tree_verified_after "no"
    warn "the OpenAI checkout no longer verifies against the pins"
  fi
  problems="$(trusted_inputs_unchanged | tr '\n' ';' | sed 's/;$//')"
  fact trusted_inputs_after "${problems:-unchanged}"
  [ -z "$problems" ] || warn "$problems"
  fact deps_added_during_run "$(cat "$RECEIPT/deps_added.count" 2>/dev/null || echo unknown)"
  if (closure_check "$OAI_LEAN" "$OAI_SOLUTION_MODULE" "$CLOSURE_MODULES" "$CLOSURE_LINES" "$CLOSURE_DIGEST" "proof source closure" "$RECEIPT/closure" &&
    closure_check "$OAI_LEAN/.lake/packages/PrimeNumberTheoremAnd" "$PNT_ENTRY" "$PNT_CLOSURE_MODULES" "$PNT_CLOSURE_LINES" "$PNT_CLOSURE_DIGEST" "PrimeNumberTheoremAnd files" "$RECEIPT/closure_pnt" &&
    closure_check "$OAI_LEAN/.lake/packages/rellich-kondrachov" "$RELLICH_ENTRY" "$RELLICH_CLOSURE_MODULES" "$RELLICH_CLOSURE_LINES" "$RELLICH_CLOSURE_DIGEST" "rellich-kondrachov files" "$RECEIPT/closure_rellich") >/dev/null 2>&1; then
    fact closures_after "unchanged"
  else
    fact closures_after "CHANGED"
    warn "the proof's source files no longer match the audited digests"
  fi
  problems="$(tools_unchanged | tr '\n' ';' | sed 's/;$//')"
  fact tools_after "${problems:-unchanged}"
  problems="$(kit_changes | tr '\n' ';' | sed 's/;$//')"
  fact kit_after "${problems:-unmodified}"
  fact after_checks_attempt "$(cat "$LOGS/$label.start" 2>/dev/null || echo unknown)"
elif [ -f "$LOGS/$label.unit" ] || [ -f "$LOGS/$label.start" ]; then
  fact main_state "lost"
else
  fact main_state "not-started"
fi

cp "$KIT_DIR/PINS.env" "$RECEIPT/PINS.env"
python3 -I "$KIT_DIR/scripts/receipt.py" "$QRH_WORK" "$KIT_DIR" >"$RECEIPT/receipt.out" || die "could not build the receipt"
verdict="$(sed -n 's/^VERDICT=//p' "$RECEIPT/receipt.out" | tail -n 1)"
fact verdict "$verdict"
rm -f "$RECEIPT/phase_7.ok"
if [ "$verdict" = "PASS" ]; then mark_phase 7; fi

sed '$d' "$RECEIPT/receipt.out"
tarball="$QRH_WORK/qrh-receipt.tar.gz"
# (tar may complain that a log changed while it was being read if a job is still running)
tar -czf "$tarball" -C "$QRH_WORK" receipt logs 2>/dev/null || true
log "receipt: $RECEIPT/RECEIPT.md   bundle with all logs: $tarball"
case "$verdict" in
  PASS) log "Next: scripts/detach.sh bridge 08_bridge.sh   (compiles the MNF bridge on top of the checked theorem)" ;;
  PROVISIONAL) log "A warm accept does not certify. To certify: scripts/reset_tree.sh \"why\", phase 5, then scripts/06_run_comparator.sh" ;;
  ERROR) log "No decision was reached. See docs/TROUBLESHOOTING.md, \"Phase 6\", before doing anything else" ;;
  REJECTED | INVALID) log "Stop here and report the receipt as it stands" ;;
esac
echo "VERDICT=$verdict"
