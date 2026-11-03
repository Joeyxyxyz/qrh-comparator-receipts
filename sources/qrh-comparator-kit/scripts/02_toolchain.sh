#!/usr/bin/env bash
# Phase 2. Install the checker toolchain for the unprivileged user, at pinned revisions:
# elan and Lean (OpenAI's toolchain), landrun, Comparator and lean4export. Safe to run again.
#
# Takes a few minutes. Run it detached:   scripts/detach.sh toolchain 02_toolchain.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root
require_phase 1
need_cmd git
need_cmd curl
need_cmd go
need_cmd readelf
begin_phase 2

log "== toolchain =="
arch="$(uname -m)"

# --- elan, from a pinned release ---------------------------------------------------------------
if ! command -v elan >/dev/null 2>&1; then
  case "$arch" in
    x86_64) elan_sha="$ELAN_SHA256_X86_64" ;;
    aarch64) elan_sha="$ELAN_SHA256_AARCH64" ;;
    *) die "no elan release pinned for $arch" ;;
  esac
  url="https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-${arch}-unknown-linux-gnu.tar.gz"
  log "installing elan $ELAN_VERSION from $url"
  curl -sSfL "$url" -o "$TOOLS/elan.tar.gz"
  check_sha "$TOOLS/elan.tar.gz" "$elan_sha" "elan release archive"
  rm -rf "$TOOLS/elan-init.d"
  mkdir -p "$TOOLS/elan-init.d"
  tar -xzf "$TOOLS/elan.tar.gz" -C "$TOOLS/elan-init.d"
  "$TOOLS/elan-init.d/elan-init" -y --default-toolchain none --no-modify-path
  rm -rf "$TOOLS/elan-init.d" "$TOOLS/elan.tar.gz"
fi
need_cmd elan
fact elan_version "$(elan --version | head -n 1)"

# --- Lean: the toolchain OpenAI's project names ------------------------------------------------
tc="${OAI_TOOLCHAIN#leanprover/lean4:}"
if ! elan toolchain list | grep -F -- "$tc" >/dev/null; then
  log "installing Lean toolchain $OAI_TOOLCHAIN"
  elan toolchain install "$OAI_TOOLCHAIN"
fi
lean_version="$(elan run "$OAI_TOOLCHAIN" lean --version)"
ok "$lean_version"
fact lean_version "$lean_version"
lean_prefix="$(elan run "$OAI_TOOLCHAIN" lean --print-prefix)"
if [ "$arch" = "x86_64" ]; then
  # The kernel that will judge the proof lives in these files. They must be the released ones.
  check_sha "$lean_prefix/bin/lean" "$SHA_LEAN_BIN_LEAN" "Lean toolchain: bin/lean"
  check_sha "$lean_prefix/bin/lake" "$SHA_LEAN_BIN_LAKE" "Lean toolchain: bin/lake"
  check_sha "$lean_prefix/lib/lean/libleanshared.so" "$SHA_LEAN_LIBLEANSHARED" "Lean toolchain: libleanshared.so"
  check_sha "$lean_prefix/lib/lean/libleanshared_1.so" "$SHA_LEAN_LIBLEANSHARED_1" "Lean toolchain: libleanshared_1.so"
  check_sha "$lean_prefix/lib/lean/libleanshared_2.so" "$SHA_LEAN_LIBLEANSHARED_2" "Lean toolchain: libleanshared_2.so"
  check_sha "$lean_prefix/lib/lean/libInit_shared.so" "$SHA_LEAN_LIBINIT_SHARED" "Lean toolchain: libInit_shared.so"
  check_sha "$lean_prefix/lib/lean/libLake_shared.so" "$SHA_LEAN_LIBLAKE_SHARED" "Lean toolchain: libLake_shared.so"
  fact lean_toolchain_verified "yes (7 files match the pinned sha256 of the v4.34.1 release)"
else
  warn "no pinned checksums for the Lean toolchain on $arch; recording what was installed"
  deviation "Lean toolchain binaries not checked against pins on $arch"
  fact lean_toolchain_verified "no (no pins for $arch)"
  fact lean_bin_sha256 "$(sha256_of "$lean_prefix/bin/lean")"
fi

# --- landrun: a static binary, built with a pinned Go toolchain --------------------------------
# GOTOOLCHAIN makes the go command fetch exactly this Go release and verify it against Go's
# checksum database, as it does for the modules it downloads. CGO_ENABLED=0 gives a static
# binary: Comparator starts landrun with an environment in which a dynamic loader could be
# pointed at directories the sandboxed build can write to, so landrun must not need a loader.
if [ -x "$LANDRUN_BIN" ] && [ "$(cat "$LANDRUN_BIN.commit" 2>/dev/null)" = "$LANDRUN_COMMIT" ]; then
  ok "landrun already built at $LANDRUN_COMMIT"
else
  log "building landrun at $LANDRUN_COMMIT with Go $GO_VERSION (static)"
  GOTOOLCHAIN="go$GO_VERSION" CGO_ENABLED=0 GOFLAGS=-modcacherw GOBIN="$TOOLS/bin" GOPATH="$TOOLS/gopath" \
    go install "${LANDRUN_MODULE}@${LANDRUN_COMMIT}"
  echo "$LANDRUN_COMMIT" >"$LANDRUN_BIN.commit"
  fact go_version "$(GOTOOLCHAIN="go$GO_VERSION" go version)"
fi
[ -x "$LANDRUN_BIN" ] || die "landrun binary missing at $LANDRUN_BIN"
if readelf -l "$LANDRUN_BIN" 2>/dev/null | grep -q 'INTERP\|DYNAMIC'; then
  die "landrun is dynamically linked. It must be static (see the comment in this script); do not continue"
fi
ok "landrun is a static binary"
fact landrun_static "yes"
fact landrun_commit "$LANDRUN_COMMIT"
fact landrun_version "$("$LANDRUN_BIN" --version 2>&1 | head -n 1)"
fact landrun_sha256 "$(sha256_of "$LANDRUN_BIN")"

# --- Comparator and lean4export ---------------------------------------------------------------
if [ ! -d "$COMPARATOR_DIR/.git" ]; then
  git clone --quiet "$COMPARATOR_REPO" "$COMPARATOR_DIR"
fi
git -C "$COMPARATOR_DIR" fetch --quiet --tags origin
tag_commit="$(git -C "$COMPARATOR_DIR" rev-parse "${COMPARATOR_TAG}^{commit}")"
[ "$tag_commit" = "$COMPARATOR_COMMIT" ] || die "Comparator tag $COMPARATOR_TAG now points at $tag_commit, pinned $COMPARATOR_COMMIT"
git -C "$COMPARATOR_DIR" checkout --quiet --force --detach "$COMPARATOR_COMMIT"
[ "$(git -C "$COMPARATOR_DIR" rev-parse HEAD)" = "$COMPARATOR_COMMIT" ] || die "Comparator checkout is not at the pinned commit"

# The one deliberate change to Comparator: build it with OpenAI's Lean toolchain (see PINS.env).
upstream_toolchain="$(git -C "$COMPARATOR_DIR" show HEAD:lean-toolchain | tr -d '[:space:]')"
printf '%s\n' "$OAI_TOOLCHAIN" >"$COMPARATOR_DIR/lean-toolchain"
fact comparator_upstream_toolchain "$upstream_toolchain"
fact comparator_build_toolchain "$OAI_TOOLCHAIN"

log "building Comparator and lean4export with $OAI_TOOLCHAIN"
if ! (cd "$COMPARATOR_DIR" && lake build lean4export comparator) >"$LOGS/toolchain_build.log" 2>&1; then
  tail -n 30 "$LOGS/toolchain_build.log" | cut -c1-300 | sed 's/^/        /'
  die "building Comparator failed (full output in $LOGS/toolchain_build.log)"
fi
[ -x "$COMPARATOR_BIN" ] || die "Comparator binary was not built"
[ -x "$LEAN4EXPORT_BIN" ] || die "lean4export binary was not built"

l4e_commit="$(git -C "$COMPARATOR_DIR/.lake/packages/lean4export" rev-parse HEAD)"
[ "$l4e_commit" = "$LEAN4EXPORT_COMMIT" ] || die "lean4export is at $l4e_commit, pinned $LEAN4EXPORT_COMMIT"
changed="$(git -C "$COMPARATOR_DIR" status --porcelain | awk '{print $2}' | sort | tr '\n' ' ')"
[ "$changed" = "lean-toolchain " ] || die "unexpected changes in the Comparator checkout: $changed"
[ -z "$(git -C "$COMPARATOR_DIR/.lake/packages/lean4export" status --porcelain | head -n 1 || true)" ] || die "unexpected changes in the lean4export checkout"

fact comparator_commit "$COMPARATOR_COMMIT"
fact lean4export_commit "$l4e_commit"
fact comparator_sha256 "$(sha256_of "$COMPARATOR_BIN")"
fact lean4export_sha256 "$(sha256_of "$LEAN4EXPORT_BIN")"
ok "Comparator $COMPARATOR_TAG ($COMPARATOR_COMMIT) and lean4export ($l4e_commit) built"

mark_phase 2
log "toolchain ready"
