#!/usr/bin/env bash
# Re-derive every hash the deposit cites and re-read the two verdicts from the receipt bundles.
# Read-only apart from a temporary directory.  Needs: sha256sum, tar, python3, curl (optional).
#
#   scripts/verify_receipts.sh [DIR]      DIR holds the bundles (default: $HOME)
#
# Checks, in order:
#   1. sha256 of the main-kit tarball, the main receipt bundle and the v1 add-on receipt bundle
#      against CHECKSUMS.sha256 (the v2 bundle is appended there once it exists);
#   2. in the main bundle: receipt.json says verdict PASS, run_type cold, the pinned commit;
#   3. in the add-on bundle(s): check.out ends in MNF_LIBRARY=ACCEPTED, and library_sha256.txt
#      matches the files of this add-on where the file is unchanged (Core.lean, Gap.lean);
#   4. (if curl works) the raw OpenAI challenge file at the pinned commit hashes to the value the
#      main kit pinned (SHA_CHALLENGE_LEAN in /opt/qrh-kit/PINS.env, copied below).
set -u
ADDON_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIR="${1:-$HOME}"
OAI_COMMIT="adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SHA_CHALLENGE_LEAN="065f8c9a01d28db78c8b1bfc5083b535082a2d2aac2230d563f98b8caa812cc5"
fail=0
say() { printf '%s\n' "$*"; }
bad() { say "FAIL  $*"; fail=1; }
good() { say "ok    $*"; }

say "== 1. bundle hashes (CHECKSUMS.sha256)"
while read -r sum name; do
  [ -n "${sum:-}" ] || continue
  case "$sum" in \#*) continue;; esac
  if [ -f "$DIR/$name" ]; then
    have="$(sha256sum "$DIR/$name" | awk '{print $1}')"
    if [ "$have" = "$sum" ]; then good "$name"; else bad "$name: sha256 $have, expected $sum"; fi
  else
    say "skip  $name: not present in $DIR"
  fi
done <"$ADDON_DIR/CHECKSUMS.sha256"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

say "== 2. main receipt"
if [ -f "$DIR/qrh-receipt.tar.gz" ]; then
  mkdir -p "$tmp/main" && tar -xzf "$DIR/qrh-receipt.tar.gz" -C "$tmp/main"
  rj="$(find "$tmp/main" -name receipt.json | head -1)"
  if [ -n "$rj" ]; then
    python3 -I - "$rj" "$OAI_COMMIT" <<'PY' || fail=1
import json, sys
d = json.load(open(sys.argv[1]))
ok = True
for k, want in (("verdict", "PASS"), ("run_type", "cold"), ("commit", sys.argv[2])):
    got = d.get(k)
    print(("ok    " if got == want else "FAIL  ") + f"receipt.json {k} = {got!r}")
    ok = ok and got == want
sys.exit(0 if ok else 1)
PY
  else
    bad "no receipt.json in qrh-receipt.tar.gz"
  fi
else
  say "skip  qrh-receipt.tar.gz not present"
fi

say "== 3. add-on receipts"
for b in qrh-mnf-receipt.tar.gz qrh-mnf-v2-receipt.tar.gz; do
  [ -f "$DIR/$b" ] || { say "skip  $b not present"; continue; }
  mkdir -p "$tmp/$b" && tar -xzf "$DIR/$b" -C "$tmp/$b"
  co="$(find "$tmp/$b" -name check.out | head -1)"
  if [ -n "$co" ] && [ "$(tail -1 "$co")" = "MNF_LIBRARY=ACCEPTED" ]; then good "$b: check.out ends in MNF_LIBRARY=ACCEPTED"; else bad "$b: check.out does not end in MNF_LIBRARY=ACCEPTED"; fi
  ls="$(find "$tmp/$b" -name library_sha256.txt | head -1)"
  if [ -n "$ls" ]; then
    # Only the files that are byte-identical across add-on versions can be checked against this
    # directory; the others belong to the add-on version that produced the bundle.
    (cd "$ADDON_DIR" && grep -E ' (MNF/RH/Core.lean|MNF/RH/Gap.lean)$' "$ls" | sha256sum --quiet -c - 2>&1) && good "$b: Core.lean and Gap.lean hashes match this add-on" || bad "$b: Core.lean/Gap.lean hashes differ from this add-on"
  fi
done

say "== 4. OpenAI challenge statement at the pinned commit"
if command -v curl >/dev/null 2>&1 && curl -fsSL "https://raw.githubusercontent.com/openai/math/$OAI_COMMIT/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean" -o "$tmp/ch.lean" 2>/dev/null; then
  have="$(sha256sum "$tmp/ch.lean" | awk '{print $1}')"
  if [ "$have" = "$SHA_CHALLENGE_LEAN" ]; then good "QuasiRiemannHypothesis.lean sha256 matches the kit's pin"; else bad "QuasiRiemannHypothesis.lean sha256 $have, pinned $SHA_CHALLENGE_LEAN"; fi
else
  say "skip  could not fetch the challenge file (offline?)"
fi

if [ "$fail" = 0 ]; then say "VERIFY=OK"; else say "VERIFY=FAIL"; fi
exit "$fail"
