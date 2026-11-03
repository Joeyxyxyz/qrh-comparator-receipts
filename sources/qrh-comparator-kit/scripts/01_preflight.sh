#!/usr/bin/env bash
# Phase 1. Read-only checks of the machine. Changes nothing. Exit 0 = good to go.
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

failures=0
bad() { log "FAIL  $*"; failures=$((failures + 1)); }

begin_phase 1
log "== preflight =="

# --- identity ---------------------------------------------------------------------------------
if [ "$(id -u)" = "0" ]; then
  bad "running as root. Comparator must run as an unprivileged user (run 00_system_setup.sh as root, then log in as that user)"
else
  ok "unprivileged user: $(id -un)"
fi

# --- platform ---------------------------------------------------------------------------------
arch="$(uname -m)"
case "$arch" in
  x86_64 | aarch64) ok "architecture $arch" ;;
  *) bad "unsupported architecture $arch" ;;
esac
kernel="$(uname -r)"
kmaj="${kernel%%.*}"
krest="${kernel#*.}"
kmin="${krest%%.*}"
if [ "$kmaj" -gt 5 ] || { [ "$kmaj" -eq 5 ] && [ "$kmin" -ge 13 ]; }; then
  ok "kernel $kernel (Landlock needs >= 5.13)"
else
  bad "kernel $kernel is too old for Landlock (need >= 5.13)"
fi
# Ask the kernel directly: landlock_create_ruleset(NULL, 0, LANDLOCK_CREATE_RULESET_VERSION) returns
# the Landlock ABI version, or fails if Landlock is absent or disabled. (Syscall 444 on x86_64 and
# aarch64.) Reading /sys/kernel/security/lsm is not reliable: securityfs may not be mounted.
landlock_abi="$(python3 -c '
import ctypes
libc = ctypes.CDLL(None, use_errno=True)
r = libc.syscall(444, None, 0, 1)
print(r if r >= 0 else 0)
' 2>/dev/null || echo 0)"
if [ "$landlock_abi" -ge 4 ]; then
  ok "Landlock is available (ABI $landlock_abi; ABI 4 and later also block TCP inside the sandbox)"
elif [ "$landlock_abi" -ge 3 ]; then
  ok "Landlock is available (ABI $landlock_abi: file-system rules only, TCP is not blocked inside the sandbox)"
elif [ "$landlock_abi" -ge 1 ]; then
  bad "Landlock ABI $landlock_abi is too old (need 3 or later, kernel 6.2+): landrun would run with an incomplete rule set"
else
  bad "Landlock is not available in this kernel: the sandbox would not enforce anything"
fi
if [ -r /etc/os-release ]; then
  # shellcheck disable=SC1091
  ok "OS: $(. /etc/os-release && echo "$PRETTY_NAME")"
fi

# --- resources --------------------------------------------------------------------------------
cpus="$(nproc)"
mem_gb="$(awk '/MemTotal/ {printf "%d", $2/1048576}' /proc/meminfo)"
swap_gb="$(awk '/SwapTotal/ {printf "%d", $2/1048576}' /proc/meminfo)"
disk_gb="$(df -BG --output=avail "$QRH_WORK" | tail -1 | tr -dc '0-9')"
if [ "$cpus" -ge 8 ]; then ok "$cpus CPUs"; else warn "$cpus CPUs: the build of 2,924 files will be slow"; fi
if [ "$mem_gb" -lt 30 ]; then
  bad "${mem_gb} GB RAM: too little (the kernel replay holds the whole exported proof in one process)"
elif [ "$mem_gb" -lt 120 ]; then
  warn "${mem_gb} GB RAM: may not be enough for the export and kernel replay; 128 GB is the recommended size"
else
  ok "${mem_gb} GB RAM"
fi
if [ "$swap_gb" -ge 32 ]; then ok "${swap_gb} GB swap"; else warn "${swap_gb} GB swap: 00_system_setup.sh adds a swap file as a cushion against the OOM killer"; fi
if [ "$disk_gb" -lt 80 ]; then
  bad "${disk_gb} GB free under $QRH_WORK: need at least 80 GB"
elif [ "$disk_gb" -lt 200 ]; then
  warn "${disk_gb} GB free under $QRH_WORK: 200 GB or more is recommended"
else
  ok "${disk_gb} GB free under $QRH_WORK"
fi
map_count="$(cat /proc/sys/vm/max_map_count 2>/dev/null || echo 0)"
if [ "$map_count" -ge 1000000 ]; then ok "vm.max_map_count = $map_count"; else warn "vm.max_map_count = $map_count (OpenAI's README warns large builds can exhaust it; 00_system_setup.sh raises it)"; fi

# --- tools ------------------------------------------------------------------------------------
for c in git curl python3 tar sha256sum awk go readelf; do
  if command -v "$c" >/dev/null 2>&1; then ok "found $c"; else bad "missing command: $c"; fi
done
if [ "$QRH_NO_SYSTEMD" = "1" ]; then
  warn "QRH_NO_SYSTEMD=1: runs will NOT restrict AF_UNIX; this invalidates the run as a certification"
elif have_user_systemd && systemd-run --user --wait --collect --quiet -- /bin/true >/dev/null 2>&1; then
  ok "systemd user manager reachable and able to run a unit (needed for RestrictAddressFamilies=~AF_UNIX)"
else
  bad "no usable systemd user manager for $(id -un). Log in over SSH as this user (not via su). Phase 0 must have run as root: it enables lingering for this user and installs dbus-user-session and libpam-systemd"
fi

# --- network (needed only before the Comparator run; the run itself is offline) ---------------
# http_code 000 means no answer at all. This is a quick probe, not a guarantee: the real downloads
# in phases 2, 4 and 5 fail loudly if a host turns out to be blocked.
probe() {
  local code
  code="$(curl -s -m 15 -o /dev/null -w '%{http_code}' "$1" 2>/dev/null || true)"
  case "$code" in
    "" | 000) bad "cannot reach $1 ($2)" ;;
    403 | 407 | 5??) warn "$1 answered HTTP $code ($2). If a proxy or firewall sits in between, the downloads will fail" ;;
    *) ok "reachable: $1 (HTTP $code)" ;;
  esac
}
probe https://github.com "source repositories"
probe https://cache.mathlib.org "Mathlib build cache"
probe "https://proxy.golang.org/github.com/zouuup/landrun/@v/list" "Go modules for landrun"
probe "https://go.dev/dl/?mode=json" "Go toolchain download"

fact preflight_cpus "$cpus"
fact preflight_mem_gb "$mem_gb"
fact preflight_swap_gb "$swap_gb"
fact preflight_disk_free_gb "$disk_gb"
fact preflight_kernel "$kernel"
fact landlock_abi "$landlock_abi"
fact preflight_failures "$failures"

if [ "$failures" -gt 0 ]; then
  log "preflight: $failures blocking problem(s). Fix them before continuing."
  exit 1
fi
mark_phase 1
log "preflight passed"
