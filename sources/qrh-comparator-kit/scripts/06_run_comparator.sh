#!/usr/bin/env bash
# Phase 6. Start the real Comparator run. It detaches at once; follow it with scripts/status.sh.
#
#   06_run_comparator.sh                  the certifying run: a cold tree, nothing compiled before.
#                                         After an attempt that ended without a decision, run
#                                         scripts/reset_tree.sh and phase 5 first; then this again.
#   06_run_comparator.sh --stack SIZE     the same, with a stack limit other than the kit's 1G
#                                         (e.g. 8G). Only if a run ended with "deep recursion" or a
#                                         stack overflow, and only with Joey's say-so.
#   06_run_comparator.sh --warm           NOT a certification: go again in the tree as the last
#                                         attempt left it, reusing what the sandbox compiled. A
#                                         quick way to learn whether a fix (more memory, more
#                                         stack) works. An accept from a warm run is reported as
#                                         PROVISIONAL. Needs Joey's say-so.
#   06_run_comparator.sh --dirichlet      optional, after a PASS: OpenAI's statement for Dirichlet
#                                         L-functions, with the proof files already compiled.
#                                         Always warm, so its result is PROVISIONAL at best.
#
# Why warm runs do not certify: docs/PROTOCOL.md, "Re-runs".
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root
need_cmd python3

usage="usage: 06_run_comparator.sh [--warm | --dirichlet] [--stack SIZE]"
mode="cold"
while [ "$#" -gt 0 ]; do
  case "$1" in
    --warm) mode="warm"; shift ;;
    --dirichlet) mode="dirichlet"; shift ;;
    --stack)
      case "${2:-}" in "" | *[!0-9KMG]* | [KMG]*) die "$usage   (SIZE is a number followed by K, M or G, like 8G)" ;; esac
      export QRH_STACK_LIMIT="$2"
      shift 2
      ;;
    *) die "$usage" ;;
  esac
done

require_phase 3
require_phase 4
require_phase 5

label="$MAIN_LABEL"
[ "$mode" = "dirichlet" ] && label="$DIRICHLET_LABEL"
if job_running "$MAIN_LABEL" || job_running "$DIRICHLET_LABEL"; then die "a Comparator run is still going; see scripts/status.sh"; fi

# What became of the last attempt at the main run, if there was one? The phase-6 marker is
# written by a run when it starts and removed by a reset, so it tells whether this tree has been
# used, also when a launch that did not complete has already set the earlier attempt's files aside.
last="none"
if [ -e "$LOGS/$MAIN_LABEL.start" ]; then
  last="$(python3 -I "$KIT_DIR/scripts/receipt.py" --classify "$QRH_WORK" "$MAIN_LABEL")"
elif [ -f "$RECEIPT/phase_6.ok" ]; then
  last="an earlier attempt, whose files have been set aside"
fi

# before_any_launch: checks every launch needs, cold or warm.
before_any_launch() {
  local problems
  problems="$(kit_changes)"
  [ -z "$problems" ] || die "the kit's files differ from the shipped ones:
$problems"
  problems="$(tools_unchanged)"
  [ -z "$problems" ] || die "$problems"
  [ "$(fact_get landrun_static)" = "yes" ] || die "landrun was not confirmed to be a static binary; run phase 2 again: $(phase_command 2)"
  verify_oai_tree
  # The sandbox and the socket restriction are proved again now, in this boot of the machine.
  sandbox_probes
  [ "$PROBE_FAILURES" = "0" ] || die "the sandbox probes failed; do not run (see above)"
  # Recorded for this run by name; the job records the boot it really runs in, and the receipt
  # requires the two to be the same.
  fact "probes_boot_id_$label" "$(boot_id)"
  fact "launch_cpus_$label" "$(nproc)"
  fact "launch_mem_gb_$label" "$(awk '/MemTotal/ {printf "%d", $2/1048576}' /proc/meminfo)"
  fact "launch_swap_gb_$label" "$(awk '/SwapTotal/ {printf "%d", $2/1048576}' /proc/meminfo)"
  fact qrh_work "$QRH_WORK"
}

# A case that Comparator has settled (a rejection, or an accept in a cold run) is not run again.
if [ "$mode" != "dirichlet" ]; then
  decided="$(decided_case)"
  [ -z "$decided" ] || die "this case is decided: $decided. It is not run again; report scripts/07_receipt.sh"
fi

run_type="warm"
case "$mode" in
  cold)
    case "$last" in
      none) ;;
      ACCEPTED) die "the last attempt was accepted in a warm run. To certify, start cold: scripts/reset_tree.sh \"why\", then phase 5, then this script" ;;
      *) die "this tree has already been used by an attempt that ended without a decision ($last). For the certifying run start cold: scripts/reset_tree.sh \"why\", then phase 5, then this script. (A warm run, --warm, is a diagnostic only.)" ;;
    esac
    log "== Comparator run (cold): $OAI_CONFIG =="
    before_any_launch
    cold_tree_check
    problems="$(trusted_inputs_unchanged)"
    [ -z "$problems" ] || die "$problems (phase 5 must be repeated)"
    run_type="cold"
    config="$OAI_CONFIG"
    ;;
  warm)
    case "$last" in
      none) die "--warm continues after an earlier attempt; there has been none" ;;
      ACCEPTED) die "the last attempt was already accepted in a warm run; another warm run adds nothing. To certify, start cold: scripts/reset_tree.sh \"why\", then phase 5, then this script without --warm" ;;
    esac
    log "== Comparator run (WARM, diagnostic only): $OAI_CONFIG =="
    before_any_launch
    deviation "a WARM attempt of the main run was started: files compiled by an earlier attempt were reused. Its result cannot certify (docs/PROTOCOL.md, Re-runs)"
    config="$OAI_CONFIG"
    ;;
  dirichlet)
    [ "$last" = "ACCEPTED" ] || die "--dirichlet is an optional extra after the main run has been accepted"
    log "== Comparator run (optional second statement, warm): $OAI_CONFIG_DIRICHLET =="
    before_any_launch
    config="$OAI_CONFIG_DIRICHLET"
    ;;
esac

# The job itself records, when it really starts, that an attempt began, of which kind, and (for
# the main run) the phase-6 marker. So nothing about the run depends on this terminal surviving
# the next few seconds, and a launch that fails leaves no trace that would count as an attempt.
if [ "$mode" != "dirichlet" ]; then rm -f "$RECEIPT/phase_7.ok" "$RECEIPT/phase_8.ok"; fi
QRH_CALLED_BY_06=1 "$KIT_DIR/scripts/run_comparator.sh" --label "$label" --dir "$OAI_LEAN" --config "$config" --run-type "$run_type" --detach ||
  die "the run could not be started (see above). Nothing was started and nothing counts as an attempt; fix the cause and call this script again"
for _ in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do
  [ -e "$LOGS/$label.start" ] && break
  sleep 1
done
[ -e "$LOGS/$label.start" ] || warn "the unit was started but has not reported in after 20 seconds; look at scripts/status.sh $label"
log "The run is on its own now. It builds 2,943 proof files, exports, and replays the proof in the kernel: expect hours."
log "Poll with: scripts/status.sh $label --wait 540     When it has ended: scripts/07_receipt.sh"
