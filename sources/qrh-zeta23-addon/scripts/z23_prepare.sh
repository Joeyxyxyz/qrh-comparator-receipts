#!/usr/bin/env bash
# QRH zeta23 add-on, step 1: set up a separate work directory, the checker at the tags that match
# zeta23's toolchain, a pinned checkout of anthropics/formal-math, and Mathlib's prebuilt cache;
# prove the sandbox again; then start one COLD Comparator run of zeta23/comparator.json through
# the main kit's launcher (run_comparator.sh: systemd user unit with AF_UNIX denied, landrun for
# the build and export steps). Returns at once after the launch.
#
#   scripts/z23_prepare.sh            (20–60 minutes before the launch: downloads and builds)
#   scripts/z23_status.sh --wait 540  to watch the run (hours: the Zeta23 library is built from source)
#   scripts/z23_report.sh             afterwards
#
# Everything lives under $HOME/qrh-zeta23-work. The main kit's ~/qrh-work (OpenAI's tree and the
# PASS receipt) and the MNF add-ons' ~/qrh-work/mnf* are never touched; only the kit's static
# landrun binary is copied from there, and checked by hash.
ADDON_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
KIT="${QRH_KIT_DIR:-/opt/qrh-kit}"
[ -f "$KIT/scripts/lib.sh" ] || { echo "main kit not found at $KIT (set QRH_KIT_DIR)" >&2; exit 2; }
export QRH_WORK="${QRH_Z23_WORK:-$HOME/qrh-zeta23-work}"
# shellcheck source=/opt/qrh-kit/scripts/lib.sh
. "$KIT/scripts/lib.sh"
# shellcheck source=../PINS-zeta23.env
. "$ADDON_DIR/PINS-zeta23.env"
require_not_root
need_cmd git
need_cmd curl
need_cmd python3
need_cmd sha256sum
need_cmd readelf

LABEL="zeta23-main"
FM_DIR="$QRH_WORK/formal-math"
Z23="$FM_DIR/$Z23_SUBDIR"
MAIN_WORK="$HOME/qrh-work"

log "== zeta23: prepare (work directory $QRH_WORK) =="

# --- the add-on itself must be what was shipped ----------------------------------------------
problems="$(cd "$ADDON_DIR" && sha256sum --quiet -c MANIFEST.sha256 2>&1 | grep -v ': OK$' || true)"
[ -z "$problems" ] || die "the add-on differs from its manifest: $(echo "$problems" | head -3 | tr '\n' ' ')"
extra="$(cd "$ADDON_DIR" && find . -type f ! -name MANIFEST.sha256 ! -path './.claude/settings.local.json' ! -name '._*' | sed 's|^\./||' | LC_ALL=C sort | comm -23 - <(awk '{print $2}' MANIFEST.sha256 | LC_ALL=C sort))"
[ -z "$extra" ] || die "files in the add-on that are not in its manifest: $(echo "$extra" | head -3 | tr '\n' ' ')"
ok "add-on matches its manifest"
fact addon_manifest_sha256 "$(sha256_of "$ADDON_DIR/MANIFEST.sha256")"

# --- one cold attempt per work directory --------------------------------------------------------
if job_running "$LABEL"; then die "$LABEL is already running; see scripts/z23_status.sh"; fi
if [ -e "$LOGS/$LABEL.start" ] || [ -e "$LOGS/$LABEL.exit" ]; then
  die "an attempt of $LABEL already exists in $QRH_WORK (a cold run is made once). Report it with scripts/z23_report.sh; for a new attempt use another work directory: QRH_Z23_WORK=... scripts/z23_prepare.sh"
fi

# --- context: the main kit's verdict, if its receipt is here (recorded, not required) ----------
if [ -f "$MAIN_WORK/receipt/facts.tsv" ]; then
  fact main_kit_verdict "$(awk -F '\t' '$2 == "verdict" { v = $3 } END { print v }' "$MAIN_WORK/receipt/facts.tsv")"
fi

# --- Lean toolchain: the one zeta23 names ---------------------------------------------------------
need_cmd elan
tc="${Z23_TOOLCHAIN#leanprover/lean4:}"
if ! elan toolchain list | grep -F -- "$tc" >/dev/null; then
  log "installing Lean toolchain $Z23_TOOLCHAIN"
  elan toolchain install "$Z23_TOOLCHAIN"
fi
lean_version="$(elan run "$Z23_TOOLCHAIN" lean --version)"
ok "$lean_version"
fact lean_version "$lean_version"
lean_prefix="$(elan run "$Z23_TOOLCHAIN" lean --print-prefix)"
fact lean_prefix "$lean_prefix"
tc_checked=0
for pair in "bin/lean:$SHA_LEAN_RC2_BIN_LEAN" "bin/lake:$SHA_LEAN_RC2_BIN_LAKE" \
  "lib/lean/libleanshared.so:$SHA_LEAN_RC2_LIBLEANSHARED" "lib/lean/libleanshared_1.so:$SHA_LEAN_RC2_LIBLEANSHARED_1" \
  "lib/lean/libleanshared_2.so:$SHA_LEAN_RC2_LIBLEANSHARED_2" "lib/lean/libInit_shared.so:$SHA_LEAN_RC2_LIBINIT_SHARED" \
  "lib/lean/libLake_shared.so:$SHA_LEAN_RC2_LIBLAKE_SHARED"; do
  f="${pair%%:*}"; want="${pair#*:}"
  [ -f "$lean_prefix/$f" ] || die "Lean toolchain file missing: $lean_prefix/$f"
  got="$(sha256_of "$lean_prefix/$f")"
  fact "lean_sha256_$(basename "$f")" "$got"
  if [ -n "$want" ]; then
    [ "$got" = "$want" ] || die "Lean toolchain: $f has sha256 $got, pinned $want"
    tc_checked=$((tc_checked + 1))
  fi
done
if [ "$tc_checked" = "7" ]; then
  fact lean_toolchain_verified "yes (7 files match the pinned sha256 of the v4.33.0-rc2 release)"
  ok "Lean toolchain binaries match the pins"
else
  fact lean_toolchain_verified "recorded only ($tc_checked of 7 pinned)"
  deviation "Lean toolchain binaries recorded by hash but only $tc_checked of 7 were pinned"
fi

# --- landrun: the main kit's static binary, by copy and hash -------------------------------------
if [ -x "$LANDRUN_BIN" ] && [ "$(sha256_of "$LANDRUN_BIN")" = "$Z23_KIT_LANDRUN_SHA256" ]; then
  ok "landrun already in place (sha256 matches the main kit's)"
elif [ -x "$MAIN_WORK/tools/bin/landrun" ] && [ "$(sha256_of "$MAIN_WORK/tools/bin/landrun")" = "$Z23_KIT_LANDRUN_SHA256" ]; then
  cp "$MAIN_WORK/tools/bin/landrun" "$LANDRUN_BIN"
  chmod 755 "$LANDRUN_BIN"
  ok "landrun copied from the main kit (sha256 $Z23_KIT_LANDRUN_SHA256)"
else
  need_cmd go
  log "building landrun at $Z23_LANDRUN_COMMIT (static)"
  GOTOOLCHAIN="go$GO_VERSION" CGO_ENABLED=0 GOFLAGS=-modcacherw GOBIN="$TOOLS/bin" GOPATH="$TOOLS/gopath" \
    go install "${LANDRUN_MODULE}@${Z23_LANDRUN_COMMIT}"
  deviation "landrun rebuilt here rather than copied from the main kit (its sha256 is recorded)"
fi
if readelf -l "$LANDRUN_BIN" 2>/dev/null | grep -q 'INTERP\|DYNAMIC'; then die "landrun is dynamically linked; do not continue"; fi
fact landrun_static "yes"
fact landrun_commit "$Z23_LANDRUN_COMMIT"
fact landrun_sha256 "$(sha256_of "$LANDRUN_BIN")"
fact landrun_version "$("$LANDRUN_BIN" --version 2>&1 | head -n 1)"

# --- Comparator and lean4export at their v4.33.0-rc2 tags ----------------------------------------
if [ ! -d "$COMPARATOR_DIR/.git" ]; then git clone --quiet "$Z23_COMPARATOR_REPO" "$COMPARATOR_DIR"; fi
git -C "$COMPARATOR_DIR" fetch --quiet --tags origin
tag_commit="$(git -C "$COMPARATOR_DIR" rev-parse "${Z23_COMPARATOR_TAG}^{commit}")"
[ "$tag_commit" = "$Z23_COMPARATOR_COMMIT" ] || die "Comparator tag $Z23_COMPARATOR_TAG now points at $tag_commit, pinned $Z23_COMPARATOR_COMMIT"
git -C "$COMPARATOR_DIR" checkout --quiet --force --detach "$Z23_COMPARATOR_COMMIT"
[ "$(tr -d '[:space:]' <"$COMPARATOR_DIR/lean-toolchain")" = "$Z23_TOOLCHAIN" ] || die "Comparator's own lean-toolchain is not $Z23_TOOLCHAIN"
if [ -x "$COMPARATOR_BIN" ] && [ -x "$LEAN4EXPORT_BIN" ] && [ "$(fact_get comparator_commit)" = "$Z23_COMPARATOR_COMMIT" ]; then
  ok "Comparator and lean4export already built"
else
  log "building Comparator and lean4export with $Z23_TOOLCHAIN (minutes)"
  if ! (cd "$COMPARATOR_DIR" && lake build lean4export comparator) >"$LOGS/toolchain_build.log" 2>&1; then
    tail -n 30 "$LOGS/toolchain_build.log" | cut -c1-300 | sed 's/^/        /'
    die "building Comparator failed (full output in $LOGS/toolchain_build.log)"
  fi
fi
[ -x "$COMPARATOR_BIN" ] || die "Comparator binary was not built"
[ -x "$LEAN4EXPORT_BIN" ] || die "lean4export binary was not built"
l4e_commit="$(git -C "$COMPARATOR_DIR/.lake/packages/lean4export" rev-parse HEAD)"
[ "$l4e_commit" = "$Z23_LEAN4EXPORT_COMMIT" ] || die "lean4export is at $l4e_commit, pinned $Z23_LEAN4EXPORT_COMMIT"
[ -z "$(git -C "$COMPARATOR_DIR" status --porcelain | head -n 1 || true)" ] || die "unexpected changes in the Comparator checkout"
fact comparator_commit "$Z23_COMPARATOR_COMMIT"
fact comparator_build_toolchain "$Z23_TOOLCHAIN"
fact lean4export_commit "$l4e_commit"
fact comparator_sha256 "$(sha256_of "$COMPARATOR_BIN")"
fact lean4export_sha256 "$(sha256_of "$LEAN4EXPORT_BIN")"
ok "Comparator $Z23_COMPARATOR_TAG and lean4export $l4e_commit built with their own toolchain"

# --- NanoDa, the second kernel zeta23's configuration asks for (only if cargo is installed) -------
nanoda="no"
if command -v cargo >/dev/null 2>&1; then
  if [ -x "$TOOLS/bin/nanoda_bin" ] && [ "$(fact_get nanoda_commit)" = "$Z23_NANODA_COMMIT" ]; then
    ok "nanoda already built"
  else
    log "building nanoda at $Z23_NANODA_COMMIT (cargo, minutes)"
    if [ ! -d "$TOOLS/nanoda/.git" ]; then git clone --quiet "$Z23_NANODA_REPO" "$TOOLS/nanoda"; fi
    git -C "$TOOLS/nanoda" fetch --quiet origin "$Z23_NANODA_COMMIT"
    git -C "$TOOLS/nanoda" checkout --quiet --force --detach "$Z23_NANODA_COMMIT"
    (cd "$TOOLS/nanoda" && cargo build --release --locked) >"$LOGS/nanoda_build.log" 2>&1 || die "building nanoda failed (see $LOGS/nanoda_build.log)"
    cp "$TOOLS/nanoda/target/release/nanoda_bin" "$TOOLS/bin/nanoda_bin"
    chmod 755 "$TOOLS/bin/nanoda_bin"
  fi
  fact nanoda_commit "$Z23_NANODA_COMMIT"
  fact nanoda_sha256 "$(sha256_of "$TOOLS/bin/nanoda_bin")"
  fact rustc_version "$(rustc --version 2>/dev/null || echo unknown)"
  nanoda="yes"
  ok "nanoda_bin in $TOOLS/bin (Comparator finds it on PATH)"
else
  warn "cargo is not installed: the NanoDa kernel will not be run; the Lean kernel alone judges the proof"
fi
fact nanoda_enabled "$nanoda"

# --- the artifact under test: anthropics/formal-math at the pinned commit -------------------------
if [ ! -d "$FM_DIR/.git" ]; then
  log "cloning $FM_REPO"
  git clone --quiet "$FM_REPO" "$FM_DIR"
fi
git -C "$FM_DIR" fetch --quiet origin "$FM_COMMIT"
git -C "$FM_DIR" checkout --quiet --force --detach "$FM_COMMIT"
[ "$(git -C "$FM_DIR" rev-parse HEAD)" = "$FM_COMMIT" ] || die "formal-math checkout is not at $FM_COMMIT"
[ -d "$Z23" ] || die "no $Z23_SUBDIR directory in the checkout"
check_sha "$Z23/Challenge.lean" "$SHA_Z23_CHALLENGE" "zeta23 challenge statements (Challenge.lean)"
check_sha "$Z23/ChallengeDeps.lean" "$SHA_Z23_CHALLENGEDEPS" "zeta23 definitions (ChallengeDeps.lean)"
check_sha "$Z23/$Z23_CONFIG" "$SHA_Z23_CONFIG" "zeta23 Comparator configuration"
check_sha "$Z23/$Z23_CONFIG_XIPRIME" "$SHA_Z23_CONFIG_XIPRIME" "zeta23 second configuration (xiprime)"
check_sha "$Z23/lakefile.toml" "$SHA_Z23_LAKEFILE" "zeta23 lakefile"
check_sha "$Z23/lake-manifest.json" "$SHA_Z23_MANIFEST" "zeta23 dependency manifest"
check_sha "$Z23/lean-toolchain" "$SHA_Z23_TOOLCHAIN_FILE" "zeta23 toolchain file"
check_sha "$Z23/Challenge/XiPrime.lean" "$SHA_Z23_CHALLENGE_XIPRIME" "zeta23 second challenge (xiprime)"
check_sha "$Z23/ChallengeDeps/XiPrime.lean" "$SHA_Z23_CHALLENGEDEPS_XIPRIME" "zeta23 second definitions (xiprime)"
[ "$(tr -d '[:space:]' <"$Z23/lean-toolchain")" = "$Z23_TOOLCHAIN" ] || die "zeta23's lean-toolchain is not $Z23_TOOLCHAIN"
dirty="$(git -C "$FM_DIR" status --porcelain --untracked-files=all | head -n 20 || true)"
[ -z "$dirty" ] || die "the formal-math checkout has local changes:
$dirty"
ok "formal-math checkout is at $FM_COMMIT with no local changes; the nine trusted files match their pins"
fact fm_commit "$FM_COMMIT"
fact z23_sources_files "$(find "$Z23/Zeta23" -name '*.lean' | wc -l)"
fact z23_sources_lines "$(find "$Z23/Zeta23" -name '*.lean' -print0 | xargs -0 cat | wc -l)"
python3 -I - "$Z23/$Z23_CONFIG" "$Z23_THEOREM_COUNT" <<'PY' || die "the configuration is not the expected one"
import json, sys
c = json.load(open(sys.argv[1]))
assert c["challenge_module"] == "Challenge" and c["solution_module"] == "Solution", "modules"
assert len(c["theorem_names"]) == int(sys.argv[2]), f"{len(c['theorem_names'])} theorem names"
assert not c.get("definition_names"), "definition holes"
assert set(c["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}, "axioms"
assert c.get("enable_nanoda") is True, "enable_nanoda"
print("config:", len(c["theorem_names"]), "theorems, no definition holes, three standard axioms, nanoda enabled")
PY

# The configuration the run uses: the pinned one when NanoDa is available, otherwise a copy of
# it with enable_nanoda set to false (Comparator aborts if the kernel it is asked for is absent).
config="$Z23_CONFIG"
if [ "$nanoda" = "no" ]; then
  config="comparator-leankernel.json"
  python3 -I - "$Z23/$Z23_CONFIG" "$Z23/$config" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
c["enable_nanoda"] = False
open(sys.argv[2], "w").write(json.dumps(c, indent=2) + "\n")
PY
  deviation "NanoDa not run (cargo not installed): Comparator was given $config, a copy of $Z23_CONFIG with enable_nanoda=false; the Lean kernel alone judged the proof"
fi
fact config_used "$config"
fact config_used_sha256 "$(sha256_of "$Z23/$config")"

# --- dependencies: Mathlib's prebuilt cache for the pinned commit (allowed before the run) ---------
log "fetching Mathlib and its prebuilt cache for $Z23_MATHLIB_COMMIT (this is the slow download)"
(cd "$Z23" && lake exe cache get) >"$LOGS/cache_get.log" 2>&1 || { tail -n 20 "$LOGS/cache_get.log"; die "lake exe cache get failed (see $LOGS/cache_get.log)"; }
ml="$(git -C "$Z23/.lake/packages/mathlib" rev-parse HEAD)"
[ "$ml" = "$Z23_MATHLIB_COMMIT" ] || die "Mathlib checkout is at $ml, pinned $Z23_MATHLIB_COMMIT"
fact mathlib_commit "$ml"
n_oleans="$(find "$Z23/.lake/packages/mathlib/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l)"
[ "$n_oleans" -gt 5000 ] || die "the Mathlib cache looks incomplete ($n_oleans .olean files)"
fact mathlib_oleans "$n_oleans"
# Records that need no git afterwards: the dependencies' Lake files and every compiled file.
(cd "$Z23/.lake/packages" && find . -mindepth 2 -maxdepth 2 \( -name lakefile.lean -o -name lakefile.toml \) -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum) >"$RECEIPT/dep_lakefiles.sha256"
fact dep_lakefiles_digest "$(sha256_of "$RECEIPT/dep_lakefiles.sha256")"
# Lake's own bookkeeping sidecars (.trace, .hash: a few bytes each, rewritten by Lake when it
# re-verifies a module it did not rebuild) are left out; every .olean/.ilean/.c and other build
# product is recorded.
log "recording the compiled dependency files by hash ($n_oleans oleans and their parts)"
(cd "$Z23/.lake/packages" && find . -path '*/.lake/build/lib/*' -type f ! -name '*.trace' ! -name '*.hash' -print0 | xargs -0 -r -n 64 -P "$(nproc)" sha256sum) | LC_ALL=C sort -k 2 >"$RECEIPT/deps_compiled.sha256"
fact deps_compiled_files "$(wc -l <"$RECEIPT/deps_compiled.sha256")"
ok "dependencies ready: Mathlib $ml, $n_oleans compiled modules"

# --- cold: nothing of the challenge, the solution or the Zeta23 library compiled yet -----------
found="$(find "$Z23/.lake/build" -type f -print -quit 2>/dev/null || true)"
[ -z "$found" ] || die "found build output ($found) before the Comparator run: the tree is not cold"
ok "the tree is cold: no build output under $Z23_SUBDIR/.lake/build"

# --- the sandbox and the socket restriction, proved again in this boot ---------------------------
sandbox_probes
[ "$PROBE_FAILURES" = "0" ] || die "the sandbox probes failed; do not run"
fact "probes_boot_id_$LABEL" "$(boot_id)"
fact "launch_cpus_$LABEL" "$(nproc)"
fact "launch_mem_gb_$LABEL" "$(awk '/MemTotal/ {printf "%d", $2/1048576}' /proc/meminfo)"
fact "launch_swap_gb_$LABEL" "$(awk '/SwapTotal/ {printf "%d", $2/1048576}' /proc/meminfo)"
fact qrh_work "$QRH_WORK"
fact z23_dir "$Z23"

# --- launch -----------------------------------------------------------------------------------
log "starting Comparator on zeta23 ($config, challenge $Z23_CHALLENGE_MODULE, solution $Z23_SOLUTION_MODULE), cold, kernels: Lean$( [ "$nanoda" = yes ] && echo ' + NanoDa')"
QRH_WORK="$QRH_WORK" "$KIT/scripts/run_comparator.sh" --label "$LABEL" --dir "$Z23" --config "$config" --run-type cold --detach ||
  die "the run could not be started (see above); nothing counts as an attempt"
for _ in $(seq 1 20); do [ -e "$LOGS/$LABEL.start" ] && break; sleep 1; done
[ -e "$LOGS/$LABEL.start" ] || warn "the unit was started but has not reported in after 20 seconds; look at scripts/z23_status.sh"
cat <<EOF

[zeta23] The run is detached. It builds the challenge (Mathlib only: minutes), then the solution,
         which compiles the whole Zeta23 library from source ($(fact_get z23_sources_files) files, $(fact_get z23_sources_lines) lines: hours),
         exports both, compares, and replays in the kernel$( [ "$nanoda" = yes ] && echo 's'). Watch it with
             $ADDON_DIR/scripts/z23_status.sh --wait 540
         When it says STATE=finished, run
             $ADDON_DIR/scripts/z23_report.sh
EOF
