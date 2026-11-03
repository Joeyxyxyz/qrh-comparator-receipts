#!/usr/bin/env bash
# Record something that was done outside the scripted protocol, in one sentence. It goes into
# the receipt under "Deviations". If you had to improvise, this is how the reader finds out.
#
#   scripts/note.sh "ran 'lake update' a second time after a network error on the first"
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
[ "$#" -ge 1 ] && [ -n "$1" ] || die "usage: note.sh \"what was done differently, and why\""
deviation "operator note: $*"
