#!/usr/bin/env bash
# Throw away everything that has been compiled or downloaded inside the OpenAI checkout, so that
# the next attempt starts cold. The source checkout, the checker toolchain and the controls stay.
# The logs of earlier attempts are kept (renamed with a numeric suffix) and stay in the receipt.
#
#   scripts/reset_tree.sh "why"          e.g.  scripts/reset_tree.sh "out of memory in step 5, droplet resized"
#
# Afterwards: phase 5 again, then phase 6.
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root
[ "$#" -ge 1 ] && [ -n "$1" ] || die "usage: reset_tree.sh \"why\"   (one sentence; it goes into the receipt)"
need_cmd python3

# A case that Comparator has settled is not run again, so there is nothing to reset for.
decided="$(decided_case)"
[ -z "$decided" ] || die "this case is decided: $decided. It is not run again, and after a PASS the compiled tree is what the bridge phase needs. Report scripts/07_receipt.sh"

for l in "$MAIN_LABEL" "$DIRICHLET_LABEL" deps; do
  if job_running "$l"; then die "$l is still running; stop it first (scripts/stop.sh $l)"; fi
done
for l in "$MAIN_LABEL" "$DIRICHLET_LABEL"; do
  if [ -e "$LOGS/$l.start" ] || [ -e "$LOGS/$l.log" ] || [ -e "$LOGS/$l.job.sh" ]; then
    n="$(archive_attempt "$l")"
    log "$l: earlier attempt kept with suffix .$n"
  fi
done
log "== reset: removing every compiled and downloaded file under $OAI_LEAN/.lake =="
rm -rf "$OAI_LEAN/.lake"
rm -f "$RECEIPT"/phase_5.ok "$RECEIPT"/phase_6.ok "$RECEIPT"/phase_7.ok "$RECEIPT"/phase_8.ok \
  "$RECEIPT"/deps_compiled.sha256 "$RECEIPT"/mathlib_sources.sha256 "$RECEIPT"/dep_lakefiles.sha256 "$RECEIPT"/deps_added.count
deviation "tree reset to cold: $*"
verify_oai_tree
log "done. Next: $(phase_command 5), then $(phase_command 6)"
