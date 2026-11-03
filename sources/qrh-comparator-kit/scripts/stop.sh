#!/usr/bin/env bash
# Stop a detached job (the Comparator run by default). Use only when the protocol says to:
# stopping the main run means the attempt is over and the next one is a re-run.
#
#   stop.sh [LABEL]
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root

label="${1:-$MAIN_LABEL}"
unitf="$LOGS/$label.unit"
[ -f "$unitf" ] || die "$label was never started"
if ! job_running "$label"; then
  log "$label is not running; nothing to stop"
  exit 0
fi
u="$(cat "$unitf")"
case "$u" in
  pid:*)
    pid="${u#pid:}"
    # the job was started with setsid, so its process group id is its pid
    kill -TERM -- "-$pid" 2>/dev/null || kill -TERM "$pid" 2>/dev/null || true
    sleep 3
    kill -KILL -- "-$pid" 2>/dev/null || true
    ;;
  *)
    systemctl --user stop "$u" || true
    ;;
esac
sleep 1
if job_running "$label"; then
  die "$label is still running after the stop request"
fi
deviation "$label: stopped by scripts/stop.sh before it finished"
log "$label stopped"
