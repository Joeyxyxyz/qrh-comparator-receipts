#!/usr/bin/env bash
# Re-derive every hash this record cites and re-read every verdict from the receipt bundles.
# Read-only apart from a temporary directory.  Needs: sha256sum, tar, python3; curl is optional.
#
#   ./verify_deposit.sh            (run inside the record folder)
#
#   1. every file listed in CHECKSUMS.sha256 hashes as listed;
#   2. qrh-receipt.tar.gz: receipt.json says verdict PASS, run_type cold, the pinned OpenAI commit;
#   3. qrh-mnf-receipt.tar.gz, qrh-mnf-v2-receipt.tar.gz, qrh-mnf-v3-receipt.tar.gz: check.out ends
#      in MNF_LIBRARY=ACCEPTED, and the library files they hash are the ones in the matching add-on
#      tarball (byte for byte, through library_sha256.txt);
#   4. qrh-zeta23-receipt.tar.gz: receipt.json says PASS, cold, the pinned formal-math commit, both
#      kernels; qrh-zeta23-mnf-receipt.tar.gz: check.out ends in MNF_ZETA23=ACCEPTED;
#   5. the add-on tarballs match their own MANIFEST.sha256 after extraction;
#   6. (if curl works) OpenAI's challenge file at the pinned commit hashes to the kit's pin, and
#      zeta23's Challenge.lean at the pinned commit hashes to the add-on's pin.
set -u
OAI_COMMIT="adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SHA_OAI_CHALLENGE="065f8c9a01d28db78c8b1bfc5083b535082a2d2aac2230d563f98b8caa812cc5"
FM_COMMIT="16a5ce41304fcdaea4e0be7c132e1c361dc26da5"
SHA_Z23_CHALLENGE="6f2a4ba95ab8c5319e541a1cc1b3699c0ae8cef23ea8e68f958e11b07281761e"
cd "$(dirname "${BASH_SOURCE[0]}")" || exit 2
fail=0
say() { printf '%s\n' "$*"; }
bad() { say "FAIL  $*"; fail=1; }
good() { say "ok    $*"; }
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

say "== 1. hashes"
if sha256sum --quiet -c CHECKSUMS.sha256 2>&1 | grep -v ': OK$' | grep -q .; then bad "CHECKSUMS.sha256 does not match"; sha256sum -c CHECKSUMS.sha256 | grep -v ': OK$'; else good "every listed file hashes as listed"; fi

say "== 2. the main receipt (OpenAI's 7/8 theorem)"
mkdir -p "$tmp/main" && tar -xzf qrh-receipt.tar.gz -C "$tmp/main" && rj="$(find "$tmp/main" -name receipt.json | head -1)"
if [ -n "$rj" ]; then
  python3 -I - "$rj" "$OAI_COMMIT" <<'PY' || fail=1
import json, sys
d = json.load(open(sys.argv[1])); ok = True
for k, want in (("verdict", "PASS"), ("run_type", "cold"), ("commit", sys.argv[2]), ("theorem", "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re")):
    got = d.get(k); print(("ok    " if got == want else "FAIL  ") + f"receipt.json {k} = {got!r}"); ok = ok and got == want
sys.exit(0 if ok else 1)
PY
else bad "no receipt.json in qrh-receipt.tar.gz"; fi

say "== 3. the MNF add-on receipts"
for pair in "qrh-mnf-receipt.tar.gz:qrh-mnf-addon.tar.gz:mnf" "qrh-mnf-v2-receipt.tar.gz:qrh-mnf-addon-v2.tar.gz:mnf-v2" "qrh-mnf-v3-receipt.tar.gz:qrh-mnf-addon-v3.tar.gz:mnf-v3"; do
  b="${pair%%:*}"; rest="${pair#*:}"; addon="${rest%%:*}"; sub="${rest#*:}"
  mkdir -p "$tmp/$b" "$tmp/$addon" && tar -xzf "$b" -C "$tmp/$b" && tar -xzf "$addon" -C "$tmp/$addon"
  co="$tmp/$b/$sub/check.out"
  if [ -f "$co" ] && [ "$(tail -1 "$co")" = "MNF_LIBRARY=ACCEPTED" ]; then good "$b: check.out ends in MNF_LIBRARY=ACCEPTED"; else bad "$b: check.out does not end in MNF_LIBRARY=ACCEPTED"; fi
  ls="$tmp/$b/$sub/library_sha256.txt"; adir="$(find "$tmp/$addon" -mindepth 1 -maxdepth 1 -type d | head -1)"
  if [ -f "$ls" ] && (cd "$adir" && sha256sum --quiet -c "$ls" >/dev/null 2>&1); then good "$b: the library files it hashed are byte-identical to those in $addon"; else bad "$b: library_sha256.txt does not match the files in $addon"; fi
done

say "== 4. the zeta23 receipts"
mkdir -p "$tmp/z23" && tar -xzf qrh-zeta23-receipt.tar.gz -C "$tmp/z23" && rj="$(find "$tmp/z23" -name receipt.json | head -1)"
if [ -n "$rj" ]; then
  python3 -I - "$rj" "$FM_COMMIT" <<'PY' || fail=1
import json, sys
d = json.load(open(sys.argv[1])); ok = True
for k, want in (("verdict", "PASS"), ("run_type", "cold"), ("commit", sys.argv[2]), ("kernels", "Lean's kernel and NanoDa")):
    got = d.get(k); print(("ok    " if got == want else "FAIL  ") + f"zeta23 receipt.json {k} = {got!r}"); ok = ok and got == want
print(("ok    " if len(d.get("theorem_names", [])) == 17 else "FAIL  ") + f"zeta23 theorem_names: {len(d.get('theorem_names', []))}")
sys.exit(0 if ok else 1)
PY
else bad "no receipt.json in qrh-zeta23-receipt.tar.gz"; fi
mkdir -p "$tmp/z23m" && tar -xzf qrh-zeta23-mnf-receipt.tar.gz -C "$tmp/z23m" && co="$(find "$tmp/z23m" -name check.out | head -1)"
if [ -n "$co" ] && [ "$(tail -1 "$co")" = "MNF_ZETA23=ACCEPTED" ]; then good "qrh-zeta23-mnf-receipt.tar.gz: check.out ends in MNF_ZETA23=ACCEPTED"; else bad "qrh-zeta23-mnf-receipt.tar.gz: not ACCEPTED"; fi

say "== 5. the add-on tarballs against their own manifests"
for addon in qrh-mnf-addon.tar.gz qrh-mnf-addon-v2.tar.gz qrh-mnf-addon-v3.tar.gz qrh-zeta23-addon.tar.gz; do
  mkdir -p "$tmp/m-$addon" && tar -xzf "$addon" -C "$tmp/m-$addon" && adir="$(find "$tmp/m-$addon" -mindepth 1 -maxdepth 1 -type d | head -1)"
  if (cd "$adir" && sha256sum --quiet -c MANIFEST.sha256 >/dev/null 2>&1); then good "$addon: matches its MANIFEST.sha256 ($(wc -l < "$adir/MANIFEST.sha256") files)"; else bad "$addon: differs from its MANIFEST.sha256"; fi
done

say "== 6. the trusted statement files upstream, at the pinned commits"
if command -v curl >/dev/null 2>&1 && curl -fsSL "https://raw.githubusercontent.com/openai/math/$OAI_COMMIT/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean" -o "$tmp/oai.lean" 2>/dev/null; then
  if [ "$(sha256sum "$tmp/oai.lean" | awk '{print $1}')" = "$SHA_OAI_CHALLENGE" ]; then good "openai/math QuasiRiemannHypothesis.lean matches the kit's pin"; else bad "openai/math challenge file differs from the pin"; fi
  if curl -fsSL "https://raw.githubusercontent.com/anthropics/formal-math/$FM_COMMIT/zeta23/Challenge.lean" -o "$tmp/z23.lean" 2>/dev/null && [ "$(sha256sum "$tmp/z23.lean" | awk '{print $1}')" = "$SHA_Z23_CHALLENGE" ]; then good "anthropics/formal-math zeta23/Challenge.lean matches the add-on's pin"; else bad "zeta23 Challenge.lean could not be fetched or differs from the pin"; fi
else
  say "skip  upstream files not fetched (offline?)"
fi

if [ "$fail" = 0 ]; then say "VERIFY=OK"; else say "VERIFY=FAIL"; fi
exit "$fail"
