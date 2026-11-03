#!/usr/bin/env bash
# Where does the protocol stand? Read-only. Run this first in any new session: every phase
# leaves a marker on disk, so nothing depends on anyone's memory of an earlier session.
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

echo "kit      $KIT_DIR"
echo "work     $QRH_WORK"
echo "user     $(id -un)$([ "$(id -u)" = "0" ] && echo '  <-- root: only phase 0 (system setup) runs as root')"
[ ! -f "$HOME/.qrh-local" ] || echo "machine  Joey's own computer (set up like the droplet; nothing bills)"
changes="$(kit_changes | head -n 5 || true)"
if [ -n "$changes" ]; then echo "KIT FILES DIFFER FROM THE SHIPPED ONES (stop and tell Joey):"; echo "$changes" | sed 's/^/         /'; fi
echo
names=("1|preflight|scripts/01_preflight.sh"
  "2|checker toolchain|scripts/detach.sh toolchain 02_toolchain.sh"
  "3|controls|scripts/detach.sh selftest 03_selftest.sh"
  "4|fetch and verify|scripts/detach.sh fetch 04_fetch.sh"
  "5|dependencies|scripts/detach.sh deps 05_deps.sh"
  "6|Comparator run started|scripts/06_run_comparator.sh"
  "7|receipt says PASS|scripts/07_receipt.sh"
  "8|MNF bridge|scripts/detach.sh bridge 08_bridge.sh")
next=""
for row in "${names[@]}"; do
  IFS='|' read -r n title cmd <<<"$row"
  if [ -f "$RECEIPT/phase_$n.ok" ]; then
    printf '  phase %s  %-24s done %s\n' "$n" "$title" "$(cut -c1-20 "$RECEIPT/phase_$n.ok")"
  else
    printf '  phase %s  %-24s -\n' "$n" "$title"
    if [ -z "$next" ]; then next="$cmd"; fi
  fi
done
echo
running=""
for u in "$LOGS"/*.unit; do
  [ -e "$u" ] || continue
  l="$(basename "$u" .unit)"
  if job_running "$l"; then running="$running $l"; fi
done
v="$(fact_get verdict)"
if [ -n "$running" ]; then
  echo "running now:$running"
  echo "next: wait for it. Poll with: scripts/status.sh LABEL --wait 540"
elif [ -e "$LOGS/$MAIN_LABEL.start" ] && [ ! -e "$LOGS/$MAIN_LABEL.exit" ]; then
  echo "running now: nothing. The main run ended without an exit code."
  if [ "$v" = "ERROR" ]; then
    echo "next: docs/TROUBLESHOOTING.md, \"Phase 6\", then tell Joey. A new attempt needs his say-so and starts with scripts/reset_tree.sh"
  else
    echo "next: scripts/07_receipt.sh (it will say ERROR)"
  fi
elif [ -e "$LOGS/$MAIN_LABEL.exit" ] && [ ! -f "$RECEIPT/phase_7.ok" ]; then
  echo "running now: nothing. The main run has finished with exit code $(cat "$LOGS/$MAIN_LABEL.exit")."
  case "$v" in
    "" | INCOMPLETE) echo "next: scripts/07_receipt.sh" ;;
    PROVISIONAL) echo "recorded verdict: PROVISIONAL (a warm accept). To certify: scripts/reset_tree.sh \"why\", phase 5, phase 6" ;;
    ERROR) echo "recorded verdict: ERROR (no decision). next: docs/TROUBLESHOOTING.md, \"Phase 6\", then tell Joey. A new attempt needs his say-so and starts with scripts/reset_tree.sh" ;;
    *) echo "recorded verdict: $v. next: report the receipt to Joey ($RECEIPT/RECEIPT.md); do not re-run" ;;
  esac
else
  echo "running now: nothing"
  if [ -n "$next" ]; then echo "next: $next"; else echo "next: nothing; all phases are done. Report to Joey"; fi
fi
if [ -n "$v" ]; then echo "last recorded verdict: $v   ($RECEIPT/RECEIPT.md)"; fi
if [ -s "$RECEIPT/DEVIATIONS.md" ]; then echo "deviations recorded: $(wc -l <"$RECEIPT/DEVIATIONS.md" | tr -d ' ') (scripts/show.sh deviations)"; fi
exit 0
