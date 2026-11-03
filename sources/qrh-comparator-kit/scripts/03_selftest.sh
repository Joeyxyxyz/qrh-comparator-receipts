#!/usr/bin/env bash
# Phase 3. Controls. Before trusting a PASS on the real theorem, show on this machine that
#   (a) the sandbox denies what it should deny, and the socket restriction is in force;
#   (b) Comparator, launched exactly as the real run will be, accepts a correct proof and
#       REJECTS a wrong statement, an extra axiom and a sorry, each for the right reason;
#   (c) a proof file that tries to write outside its sandbox while Comparator compiles it fails
#       to do so;
#   (d) Comparator's own regression projects (in its repository at the pinned commit) end as its
#       authors expect, each for the reason recorded in controls/upstream_expected.tsv.
# A checker that cannot fail proves nothing, so any control failing stops the protocol.
#
# Takes a few minutes. Run it detached:   scripts/detach.sh selftest 03_selftest.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root
require_phase 2
need_cmd python3
begin_phase 3

log "== self-test (controls) =="
failures=0
failed_names=""
bad() { log "FAIL  $*"; failures=$((failures + 1)); }

problems="$(tools_unchanged)"
[ -z "$problems" ] || die "$problems (run phase 2 again: $(phase_command 2))"

# --- (a) sandbox and socket restriction, tested by behaviour ------------------------------------
sandbox_probes
failures=$((failures + PROBE_FAILURES))

# --- (b), (c), (d) Comparator controls -----------------------------------------------------------
controls_root="$QRH_WORK/controls"
rm -rf "$controls_root"
mkdir -p "$controls_root"
n_accept=0
n_reject=0

# run_control LABEL DIR EXPECTED_EXIT TEXT_THE_OUTPUT_MUST_CONTAIN
run_control() {
  local label="$1" dir="$2" expected_rc="$3" expected_msg="$4" rc=0 out
  printf '%s\n' "$OAI_TOOLCHAIN" >"$dir/lean-toolchain"
  "$KIT_DIR/scripts/run_comparator.sh" --label "$label" --dir "$dir" --config config.json >"$LOGS/$label.launch" 2>&1 || rc=$?
  out="$LOGS/$label.log"
  if [ ! -f "$out" ]; then
    bad "$label: Comparator did not run: $(tail -n 2 "$LOGS/$label.launch" | tr '\n' ' ' | cut -c1-300)"
    failed_names="$failed_names $label"
    fact "$label" "FAILED (did not run)"
    return 0
  fi
  if [ "$rc" != "$expected_rc" ] || ! grep -qF -- "$expected_msg" "$out"; then
    bad "$label: expected exit $expected_rc and \"$expected_msg\"; got exit $rc. Last lines of its output:"
    grep -av '^Exporting ' "$out" | tail -n 5 | cut -c1-300 | sed 's/^/        /' | tee -a "$LOGS/kit.log" || true
    failed_names="$failed_names $label"
    fact "$label" "FAILED (exit $rc, expected $expected_rc with \"$expected_msg\")"
    return 0
  fi
  if [ "$rc" = "0" ]; then n_accept=$((n_accept + 1)); else n_reject=$((n_reject + 1)); fi
  ok "$label: exit $rc as expected, output contains \"$expected_msg\""
  fact "$label" "ok (exit $rc)"
}

json_field() { python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])" "$1" "$2"; }

# (b) and (c): the kit's own controls
for c in pass wrong_statement extra_axiom sorry_proof sandbox_write; do
  cp -r "$KIT_DIR/controls/$c" "$controls_root/$c"
  chmod -R u+w "$controls_root/$c"
  run_control "control-$c" "$controls_root/$c" \
    "$(json_field "$controls_root/$c/expected.json" exit_code)" \
    "$(json_field "$controls_root/$c/expected.json" must_contain)"
done

# (c) what the sandbox_write control managed to write while it was being compiled
sw="$controls_root/sandbox_write"
if [ ! -f "$sw/.lake/qrh_probe_inside" ]; then
  bad "control-sandbox_write: its compile-time code left no trace inside .lake, so the test shows nothing"
  failed_names="$failed_names control-sandbox_write"
elif [ -e "$sw/qrh_probe_project" ] || [ -e "$controls_root/sandbox_write.outside" ]; then
  fact sandbox_holds_in_comparator "no"
  if [ "$QRH_DEV_NO_SANDBOX" = "1" ]; then
    warn "control-sandbox_write: the proof file wrote OUTSIDE .lake while Comparator compiled it; continuing only because QRH_DEV_NO_SANDBOX=1"
    fact invalidating_override "QRH_DEV_NO_SANDBOX"
  else
    bad "control-sandbox_write: the proof file wrote OUTSIDE .lake while Comparator compiled it. Comparator's sandbox does not hold here; do not continue"
    failed_names="$failed_names control-sandbox_write"
  fi
else
  ok "control-sandbox_write: while Comparator compiled it, the proof file could write inside .lake and nowhere else"
  fact sandbox_holds_in_comparator "yes"
fi

# (d) Comparator's own regression projects, same launch path. Projects that need the optional
# nanoda kernel are skipped: this kit does not install nanoda and the real run does not use it.
upstream="$COMPARATOR_DIR/tests/projects"
[ -d "$upstream" ] || die "Comparator's test projects are missing at $upstream"
expected_table="$KIT_DIR/controls/upstream_expected.tsv"
n_skipped=0
seen=""
for src in "$upstream"/*/; do
  name="$(basename "$src")"
  [ -f "$src/config.json" ] && [ -f "$src/test.json" ] || continue
  if python3 -I -c "
import json, sys
c = json.load(open(sys.argv[1]))
sys.exit(0 if (c.get('enable_nanoda') or c.get('external_kernels')) else 1)" "$src/config.json"; then
    n_skipped=$((n_skipped + 1))
    continue
  fi
  row="$(awk -F '\t' -v n="$name" '$1 == n { print $2 "\t" $3 }' "$expected_table")"
  if [ -z "$row" ]; then
    bad "upstream-$name: this project is not in controls/upstream_expected.tsv (Comparator's suite is not the audited one)"
    failed_names="$failed_names upstream-$name"
    continue
  fi
  want_rc="${row%%$'\t'*}"
  want_msg="${row#*$'\t'}"
  [ "$(json_field "$src/test.json" exit_code)" = "$want_rc" ] || bad "upstream-$name: Comparator's own test.json expects a different exit code than the kit's table"
  dst="$controls_root/upstream-$name"
  cp -r "$src" "$dst"
  chmod -R u+w "$dst"
  if [ ! -f "$dst/lakefile.toml" ] && [ ! -f "$dst/lakefile.lean" ]; then
    # the default lakefile Comparator's own test runner generates
    printf 'name = "comparatortest"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "Solution"\n\n[[lean_lib]]\nname = "Challenge"\n' >"$dst/lakefile.toml"
  fi
  run_control "upstream-$name" "$dst" "$want_rc" "$want_msg"
  seen="$seen $name"
done
while IFS=$'\t' read -r name _rest; do
  case "$name" in "" | \#*) continue ;; esac
  case " $seen " in *" $name "*) ;; *) bad "upstream-$name is in the kit's table but was not found in Comparator's suite" ;; esac
done <"$expected_table"
fact upstream_controls_skipped_nanoda "$n_skipped"

fact controls_accepted "$n_accept"
fact controls_rejected "$n_reject"
fact selftest_failures "$failures"
fact selftest_boot_id "$(boot_id)"
if [ "$failures" -gt 0 ]; then
  log "self-test: $failures failure(s):$failed_names"
  log "Stop here and report; do not run the real check. Each control's output is in $LOGS/<name>.log"
  exit 1
fi
if [ "$n_accept" != "$CONTROLS_ACCEPT" ] || [ "$n_reject" != "$CONTROLS_REJECT" ]; then
  die "self-test: $n_accept controls accepted and $n_reject rejected; the kit expects exactly $CONTROLS_ACCEPT and $CONTROLS_REJECT"
fi
mark_phase 3
log "self-test passed: the sandbox denies, and Comparator accepted $n_accept correct and rejected $n_reject incorrect control projects ($n_skipped nanoda-only projects skipped)"
