#!/usr/bin/env bash
# Drive the droplet from your own computer over SSH. For the case where Claude Code runs on
# Joey's machine instead of on the droplet. Needs bash, ssh, scp and tar here (macOS, Linux or
# WSL), and an SSH key the droplet accepts for root that works without typing a passphrase
# (DigitalOcean installs the key chosen when the droplet was created; if the key has a
# passphrase, load it into ssh-agent first). Test:  ssh root@ADDRESS true
#
#   scripts/remote.sh setup ADDRESS       remember the address, upload the kit, run phase 0 as root,
#                                         then check the unprivileged login. The only use of root
#                                         apart from oom-check. Takes a few minutes.
#   scripts/remote.sh run SCRIPT [ARGS]   run scripts/SCRIPT on the droplet as the unprivileged user,
#                                         e.g.  scripts/remote.sh run status.sh --wait 540
#   scripts/remote.sh fetch-receipt       copy the receipt bundle into ./results/ on this computer
#   scripts/remote.sh oom-check           as root, read-only: did the kernel kill something for
#                                         lack of memory? plus free memory and disk
#   scripts/remote.sh host                print the remembered address
set -euo pipefail

KIT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOSTFILE="$KIT_DIR/.qrh_host"
QRH_USER="${QRH_USER:-qrh}"
REMOTE_KIT="${QRH_REMOTE_KIT:-/opt/qrh-kit}"
SSH_OPTS=(-o ServerAliveInterval=30 -o ServerAliveCountMax=6 -o StrictHostKeyChecking=accept-new -o BatchMode=yes)
SCP_OPTS=("${SSH_OPTS[@]}")
if [ -n "${QRH_SSH_PORT:-}" ]; then
  SSH_OPTS+=(-p "$QRH_SSH_PORT")
  SCP_OPTS+=(-P "$QRH_SSH_PORT")
fi

fail() { echo "remote.sh: $*" >&2; exit 1; }
case "$QRH_USER" in "" | *[!a-z0-9_-]*) fail "QRH_USER must be a plain lower-case user name" ;; esac
case "${QRH_SWAP_GB:-64}" in "" | *[!0-9]*) fail "QRH_SWAP_GB must be a whole number" ;; esac
[ ! -f "$HOME/.qrh-droplet" ] || fail "this is the droplet itself; run the scripts directly (scripts/where.sh)"

cmd="${1:-}"
[ -n "$cmd" ] || fail "usage: remote.sh setup ADDRESS | run SCRIPT [ARGS] | fetch-receipt | oom-check | host"
shift

addr=""
if [ "$cmd" != "setup" ]; then
  [ -s "$HOSTFILE" ] || fail "no droplet address recorded yet; run: scripts/remote.sh setup ADDRESS"
  addr="$(cat "$HOSTFILE")"
fi

case "$cmd" in
  host)
    echo "$addr"
    ;;
  setup)
    addr="${1:-}"
    case "$addr" in "" | *[!A-Za-z0-9.:_-]*) fail "usage: remote.sh setup ADDRESS   (an IP address or host name)" ;; esac
    [ -f "$KIT_DIR/KIT_MANIFEST.sha256" ] || fail "KIT_MANIFEST.sha256 is missing from this kit"
    ssh "${SSH_OPTS[@]}" "root@$addr" true || fail "cannot log in as root@$addr with an SSH key (see the top of this script)"
    echo "$addr" >"$HOSTFILE"
    echo "[remote] uploading the kit to root@$addr:/root/qrh-comparator-kit"
    # Exactly the files the manifest names, and the manifest: whatever else has appeared in this
    # folder (Claude Code's own settings.local.json, results, editor files) stays here.
    list="$(mktemp)"
    trap 'rm -f "$list"' EXIT
    { echo "./KIT_MANIFEST.sha256"; sed 's/^[0-9a-f]\{64\}  //' "$KIT_DIR/KIT_MANIFEST.sha256"; } >"$list"
    while IFS= read -r f; do
      [ -f "$KIT_DIR/$f" ] || fail "the kit is incomplete: $f is missing. Unpack the kit again"
    done <"$list"
    COPYFILE_DISABLE=1 tar -czf - -C "$KIT_DIR" -T "$list" |
      ssh "${SSH_OPTS[@]}" "root@$addr" 'rm -rf /root/qrh-comparator-kit && mkdir -p /root/qrh-comparator-kit && tar -xzf - -C /root/qrh-comparator-kit'
    echo "[remote] phase 0 (system setup) on the droplet, as root"
    ssh "${SSH_OPTS[@]}" "root@$addr" "QRH_USER=$QRH_USER QRH_SWAP_GB=${QRH_SWAP_GB:-64} bash /root/qrh-comparator-kit/scripts/00_system_setup.sh"
    echo "[remote] checking the unprivileged login"
    ssh "${SSH_OPTS[@]}" "$QRH_USER@$addr" "cd $REMOTE_KIT && scripts/where.sh"
    ;;
  run)
    script="${1:-}"
    case "$script" in "" | *[!A-Za-z0-9_.]* | .*) fail "usage: remote.sh run SCRIPT [ARGS]   (a file name from scripts/)" ;; esac
    [ -f "$KIT_DIR/scripts/$script" ] || fail "no such script: scripts/$script"
    case "$script" in remote.sh | 00_system_setup.sh) fail "$script is not run this way" ;; esac
    shift
    remote="cd $REMOTE_KIT && scripts/$script"
    for a in "$@"; do remote="$remote $(printf '%q' "$a")"; done
    ssh "${SSH_OPTS[@]}" "$QRH_USER@$addr" "$remote"
    ;;
  fetch-receipt)
    mkdir -p "$KIT_DIR/results"
    scp "${SCP_OPTS[@]}" "$QRH_USER@$addr:qrh-work/qrh-receipt.tar.gz" "$KIT_DIR/results/qrh-receipt.tar.gz"
    tar -xzf "$KIT_DIR/results/qrh-receipt.tar.gz" -C "$KIT_DIR/results" receipt/RECEIPT.md
    tar -xzf "$KIT_DIR/results/qrh-receipt.tar.gz" -C "$KIT_DIR/results" receipt/BRIDGE.md 2>/dev/null || true
    echo "[remote] saved: $KIT_DIR/results/qrh-receipt.tar.gz"
    for f in "$KIT_DIR"/results/receipt/*; do echo "[remote]        results/receipt/$(basename "$f")"; done
    ;;
  oom-check)
    ssh "${SSH_OPTS[@]}" "root@$addr" "dmesg -T 2>/dev/null | grep -iE 'out of memory|oom-kill|killed process' | tail -n 20; echo ---; free -g; echo ---; df -h / | tail -n 1; echo ---; uptime -s"
    ;;
  *)
    fail "unknown command: $cmd"
    ;;
esac
