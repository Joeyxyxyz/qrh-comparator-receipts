#!/usr/bin/env bash
# Phase 8. Only after a PASS: compile the MNF bridge on top of the theorem Comparator checked.
#
#   step A  bridge/MNF_Bridge78.lean                 the bridge with the 7/8 theorem as a hypothesis;
#                                                    imports Mathlib only.
#   step B  bridge/MNF_Bridge78_Unconditional.lean   imports step A and OpenAI's proof, and removes
#                                                    the hypothesis.
#
# Both compiles run the way Comparator's own builds do: inside a landrun sandbox, in a systemd
# unit that may not open AF_UNIX sockets (scripts/detach.sh gives this phase that unit, and the
# phase refuses to run anywhere else). Step A may write to $QRH_WORK/bridge, where its compiled
# file goes; step B may write nowhere. Nothing is written into the OpenAI tree, and neither lake
# nor git is run there: after the proof has been compiled, its build directory is only ever read
# by sandboxed processes.
#
# Takes a few minutes. Run it detached:   scripts/detach.sh bridge 08_bridge.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root
need_cmd python3
begin_phase 8
# Whatever an earlier run of this phase reported no longer stands.
rm -f "$RECEIPT/BRIDGE.md" "$RECEIPT/bridge.out"
fact bridge "not finished"

verdict="$(fact_get verdict)"
[ "$verdict" = "PASS" ] || die "the bridge only means something after a PASS (recorded verdict: ${verdict:-none}). Run scripts/07_receipt.sh first"
require_phase 7

log "== MNF bridge =="
afu="$(af_unix_state)"
if [ "$afu" = "denied" ]; then
  ok "this phase runs in a unit that may not open AF_UNIX sockets"
elif [ "$QRH_NO_SYSTEMD" = "1" ]; then
  warn "AF_UNIX sockets are $afu here (QRH_NO_SYSTEMD=1): the bridge compiles are sandboxed by landrun only"
  deviation "bridge phase run without the AF_UNIX restriction (QRH_NO_SYSTEMD=1)"
else
  die "AF_UNIX sockets are $afu here. This phase must run in its restricted unit: start it with scripts/detach.sh bridge 08_bridge.sh (never directly), logged in over SSH as this user"
fi
problems="$(kit_changes)"
[ -z "$problems" ] || die "the kit differs from its manifest: $(echo "$problems" | head -5 | tr '\n' ' ')"
check_sha "$KIT_DIR/bridge/MNF_Bridge78.lean" "$SHA_BRIDGE_COND" "bridge (conditional file)"
check_sha "$KIT_DIR/bridge/MNF_Bridge78_Unconditional.lean" "$SHA_BRIDGE_UNCOND" "bridge (unconditional file)"
check_sha "$KIT_DIR/bridge/expected_statements.txt" "$SHA_BRIDGE_EXPECTED" "bridge (expected statements)"
verify_oai_tree
problems="$(tools_unchanged)"
[ -z "$problems" ] || die "$problems"

work="$QRH_WORK/bridge"
rm -rf "$work"
mkdir -p "$work"
cp "$KIT_DIR/bridge/MNF_Bridge78.lean" "$KIT_DIR/bridge/MNF_Bridge78_Unconditional.lean" "$work/"
chmod u+w "$work"/*.lean

# The Lean toolchain's own directory, asked for from a neutral place.
lean_prefix="$(cd "$QRH_WORK" && elan run "$OAI_TOOLCHAIN" lean --print-prefix)"
[ -x "$lean_prefix/bin/lean" ] || die "cannot find the Lean toolchain"

# Where compiled modules live: the bridge's own directory first, then the project, then each
# dependency. (This is the list `lake env` would compute; lake itself is not run.)
[ -f "$OAI_LEAN/.lake/build/lib/lean/$(echo "$OAI_SOLUTION_MODULE" | tr . /).olean" ] ||
  die "the compiled form of $OAI_SOLUTION_MODULE is not in $OAI_LEAN/.lake/build; the bridge needs the tree Comparator built"
lp="$work:$OAI_LEAN/.lake/build/lib/lean"
for d in "$OAI_LEAN"/.lake/packages/*/.lake/build/lib/lean; do
  if [ -d "$d" ]; then lp="$lp:$d"; fi
done

# sandboxed_lean WRITABLE_DIR LEAN_ARGS...   (WRITABLE_DIR may be empty: then nothing is writable)
sandboxed_lean() {
  local writable="$1"
  shift
  local grant=()
  if [ -n "$writable" ]; then grant=(--rwx "$writable"); fi
  LEAN_PATH="$lp" "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec \
    --env LEAN_PATH --env HOME ${grant[@]+"${grant[@]}"} --rox "$lean_prefix" -- "$lean_prefix/bin/lean" "$@"
}

rc_a=0
log "step A: compiling the conditional bridge (Mathlib only), sandboxed"
(cd "$work" && sandboxed_lean "$work" -o "$work/MNF_Bridge78.olean" MNF_Bridge78.lean) >"$LOGS/bridge_cond.out" 2>&1 || rc_a=$?
rc_b=0
if [ "$rc_a" = "0" ] && [ -f "$work/MNF_Bridge78.olean" ]; then
  log "step B: compiling the unconditional layer against OpenAI's checked theorem, sandboxed"
  (cd "$work" && sandboxed_lean "" MNF_Bridge78_Unconditional.lean) >"$LOGS/bridge_uncond.out" 2>&1 || rc_b=$?
else
  echo "step A failed; step B was not attempted" >"$LOGS/bridge_uncond.out"
  rc_b=1
fi

# The checker reads the kit's own pinned copies of the sources, not the ones in the work folder.
rc=0
python3 -I "$KIT_DIR/scripts/bridge_check.py" \
  "$KIT_DIR/bridge/MNF_Bridge78.lean" "$LOGS/bridge_cond.out" "$rc_a" \
  "$KIT_DIR/bridge/MNF_Bridge78_Unconditional.lean" "$LOGS/bridge_uncond.out" "$rc_b" \
  "$KIT_DIR/bridge/expected_statements.txt" "$RECEIPT/BRIDGE.md" >"$RECEIPT/bridge.out" || rc=$?
sed '$d' "$RECEIPT/bridge.out"

if [ "$rc" = "0" ]; then
  fact bridge "ok"
  mark_phase 8
else
  fact bridge "FAILED"
fi
tar -czf "$QRH_WORK/qrh-receipt.tar.gz" -C "$QRH_WORK" receipt logs 2>/dev/null || true
if [ "$rc" = "0" ]; then
  log "bridge report: $RECEIPT/BRIDGE.md (also in $QRH_WORK/qrh-receipt.tar.gz)"
  echo "BRIDGE=OK"
else
  log "bridge check failed; see $RECEIPT/BRIDGE.md, $LOGS/bridge_cond.out and $LOGS/bridge_uncond.out. This does not affect the Comparator verdict"
  echo "BRIDGE=FAILED"
  exit 1
fi
