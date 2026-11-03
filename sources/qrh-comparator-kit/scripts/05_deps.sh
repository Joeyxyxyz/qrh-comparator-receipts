#!/usr/bin/env bash
# Phase 5. Resolve OpenAI's dependencies exactly as their README says (lake update, then the
# Mathlib cache), and check the result against the pins. This runs OpenAI's lakefile, which
# Comparator's model treats as trusted input; it does NOT compile the challenge, the solution,
# or anything the solution imports outside Mathlib. That happens only inside Comparator's sandbox.
#
# Takes 10 to 30 minutes. Run it detached:   scripts/detach.sh deps 05_deps.sh
#
#   05_deps.sh                         the default: download Mathlib's prebuilt cache
#   05_deps.sh --mathlib-from-source   do not download it; Comparator then compiles Mathlib itself
#                                      inside the sandbox (hours longer, one trusted party fewer)
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root
require_phase 4
case "${1:-}" in
  "") ;;
  --mathlib-from-source) QRH_MATHLIB_FROM_SOURCE=1 ;;
  *) die "usage: 05_deps.sh [--mathlib-from-source]" ;;
esac
need_cmd git
need_cmd python3
need_cmd lake
if [ -e "$LOGS/$MAIN_LABEL.start" ] || job_running "$MAIN_LABEL"; then
  die "the Comparator run has already been started in this tree. Phase 5 belongs before it; to begin again use scripts/reset_tree.sh"
fi
begin_phase 5

log "== dependencies =="
verify_oai_tree
cd "$OAI_LEAN" || die "cannot enter $OAI_LEAN"

pkgs="$OAI_LEAN/.lake/packages"
cold_tree_check

run_logged() {
  # run_logged LOGFILE CMD...: run quietly, show the tail and stop on failure
  local logf="$1"
  shift
  if ! "$@" >"$logf" 2>&1; then
    tail -n 25 "$logf" | cut -c1-300 | sed 's/^/        /'
    die "command failed: $* (full output in $logf)"
  fi
}

# Mathlib's own hook would start a cache download in the middle of `lake update`. It is switched
# off so that the two steps of OpenAI's README run, and are logged, one after the other.
export MATHLIB_NO_CACHE_ON_UPDATE=1
log "lake update (clones 42 packages and applies OpenAI's compatibility patches)"
run_logged "$LOGS/lake_update.log" lake update
if [ "$QRH_MATHLIB_FROM_SOURCE" = "1" ]; then
  log "skipping Mathlib's prebuilt cache (--mathlib-from-source): Comparator will compile Mathlib in the sandbox"
  found="$(find "$pkgs" -path '*/.lake/build/lib/*' -type f -print -quit)"
  [ -z "$found" ] || die "--mathlib-from-source, but compiled dependency files are already present ($found), left by an earlier cache download. Start from a clean tree: scripts/reset_tree.sh"
  fact mathlib_build "compiled from source inside the sandbox"
else
  log "lake exe cache get (downloads Mathlib's prebuilt files)"
  run_logged "$LOGS/cache_get.log" lake exe cache get
  tail -n 3 "$LOGS/cache_get.log" | cut -c1-200 | sed 's/^/        /'
  fact mathlib_build "prebuilt cache (lake exe cache get)"
fi
grep -a "compatibility patch" "$LOGS/lake_update.log" | sed 's/^/        /' | tail -n 30 || true

# --- the resolved dependency set is the one OpenAI committed ------------------------------------
check_sha "$OAI_LEAN/lake-manifest.json" "$SHA_MANIFEST" "dependency manifest after lake update (no drift)"
verify_oai_tree

python3 -I - "$OAI_LEAN" "$RECEIPT/packages.tsv" <<'PY' || die "a package is not at the revision the manifest names (see above)"
import json, subprocess, sys
root, out = sys.argv[1], sys.argv[2]
manifest = json.load(open(f"{root}/lake-manifest.json"))
bad = 0
rows = []
for p in manifest["packages"]:
    name, rev = p["name"], p.get("rev", "")
    # the manifest writes names with special characters as «name»; the directory has no guillemets
    d = f"{root}/.lake/packages/{name.replace(chr(0xAB), '').replace(chr(0xBB), '')}"
    try:
        head = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
    except Exception as e:
        head = f"ERROR {e}"
    status = "ok" if head == rev else "MISMATCH"
    bad += status != "ok"
    rows.append(f"{name}\t{rev}\t{head}\t{status}\t{p.get('url', '')}")
    if status != "ok":
        print(f"        {name}: manifest {rev}, checkout {head}")
open(out, "w").write("\n".join(rows) + "\n")
print(f"        {len(rows)} packages checked against the manifest, {bad} mismatch(es)")
sys.exit(1 if bad else 0)
PY
ok "every package is at the revision named in the manifest"

pkg_head() { git -C "$pkgs/$1" rev-parse HEAD; }
[ "$(pkg_head mathlib)" = "$MATHLIB_COMMIT" ] || die "Mathlib is not at the pinned commit"
[ "$(pkg_head PrimeNumberTheoremAnd)" = "$PNT_COMMIT" ] || die "PrimeNumberTheoremAnd is not at the pinned commit"
[ "$(pkg_head rellich-kondrachov)" = "$RELLICH_COMMIT" ] || die "rellich-kondrachov is not at the pinned commit"
ok "Mathlib, PrimeNumberTheoremAnd and rellich-kondrachov are at their pinned commits"

# Lake configuration files are code. The set that was read when the kit was written is pinned.
lakefiles_listing >"$RECEIPT/dep_lakefiles.sha256"
lf_n="$(wc -l <"$RECEIPT/dep_lakefiles.sha256" | tr -d ' ')"
lf_digest="$(sha256_of "$RECEIPT/dep_lakefiles.sha256")"
[ "$lf_n" = "$DEPS_LAKEFILES_COUNT" ] || die "$lf_n dependency lakefiles found, audited $DEPS_LAKEFILES_COUNT"
[ "$lf_digest" = "$DEPS_LAKEFILES_DIGEST" ] || die "the dependencies' Lake configuration files differ from the audited set (digest $lf_digest)"
ok "the $lf_n dependency Lake configuration files are the audited ones"
fact deps_lakefiles_digest "$lf_digest"

# Mathlib itself is not patched: its source must be exactly the upstream commit.
dirty="$(git -C "$pkgs/mathlib" status --porcelain | head -n 5 || true)"
[ -z "$dirty" ] || die "Mathlib's source differs from the pinned commit:
$dirty"
ok "Mathlib's source is unmodified"
# Record a checksum of every tracked Mathlib file now, while git can still be trusted here.
# After the proof has been compiled, the comparison is made with sha256sum alone.
(cd "$pkgs" && git -C mathlib ls-files -z | sed -z 's|^|./mathlib/|' | xargs -0 -r -n 64 -P "$(nproc)" sha256sum) |
  LC_ALL=C sort -k 2 >"$RECEIPT/mathlib_sources.sha256"
fact mathlib_source_files "$(wc -l <"$RECEIPT/mathlib_sources.sha256" | tr -d ' ')"
fact mathlib_sources_digest "$(sha256_of "$RECEIPT/mathlib_sources.sha256")"

# OpenAI's patches are in place on the two third-party libraries the proof imports ...
for pair in "PrimeNumberTheoremAnd:PrimeNumberTheoremAnd-lean4341.patch" "rellich-kondrachov:rellich-kondrachov-lean4341.patch"; do
  p="${pair%%:*}"
  f="${pair#*:}"
  git -C "$pkgs/$p" apply --check --reverse "$OAI_LEAN/patches/$f" 2>/dev/null || die "$p: OpenAI's patch $f is not applied cleanly"
done
ok "OpenAI's compatibility patches are applied to PrimeNumberTheoremAnd and rellich-kondrachov"

# ... and the files the proof actually imports from them are byte-identical to the audited ones.
closure_check "$pkgs/PrimeNumberTheoremAnd" "$PNT_ENTRY" "$PNT_CLOSURE_MODULES" "$PNT_CLOSURE_LINES" "$PNT_CLOSURE_DIGEST" \
  "PrimeNumberTheoremAnd files used by the proof" "$RECEIPT/closure_pnt"
closure_check "$pkgs/rellich-kondrachov" "$RELLICH_ENTRY" "$RELLICH_CLOSURE_MODULES" "$RELLICH_CLOSURE_LINES" "$RELLICH_CLOSURE_DIGEST" \
  "rellich-kondrachov files used by the proof" "$RECEIPT/closure_rellich"

cold_tree_check
ok "nothing of the challenge or the solution has been compiled yet (cold tree)"

# --- is the Mathlib cache complete? --------------------------------------------------------------
# If it is not, lake would recompile part of Mathlib during the run and overwrite cached files.
# That is not wrong, but it takes hours and the receipt could no longer say that the compiled
# dependencies stayed untouched. So it is settled here, before the hours are spent.
if [ "$QRH_MATHLIB_FROM_SOURCE" = "1" ]; then
  fact mathlib_cache_complete "not used"
else
  if lake build --no-build Mathlib >"$LOGS/mathlib_no_build.log" 2>&1; then
    ok "the Mathlib cache is complete: no Mathlib file needs compiling"
    fact mathlib_cache_complete "yes"
  else
    fact mathlib_cache_complete "no"
    head -n 12 "$LOGS/mathlib_no_build.log" | cut -c1-300 | sed 's/^/        /' || true
    die "lake reports that Mathlib is not fully up to date after the cache download (above; full output in $LOGS/mathlib_no_build.log). Ask Joey: either retry later, or start from a clean tree (scripts/reset_tree.sh) and use 05_deps.sh --mathlib-from-source"
  fi
fi

# --- records of what the run will trust, for comparison afterwards ------------------------------
snapshot_compiled "$RECEIPT/deps_compiled.sha256"
n_compiled="$(wc -l <"$RECEIPT/deps_compiled.sha256" | tr -d ' ')"
digest="$(sha256_of "$RECEIPT/deps_compiled.sha256")"
fact deps_compiled_files "$n_compiled"
fact deps_compiled_digest "$digest"
ok "recorded sha256 of $n_compiled compiled dependency files (digest $digest)"

fact deps_disk_usage "$(du -sh "$OAI_LEAN/.lake" | awk '{print $1}')"
mark_phase 5
log "dependencies ready. Next: $(phase_command 6)"
