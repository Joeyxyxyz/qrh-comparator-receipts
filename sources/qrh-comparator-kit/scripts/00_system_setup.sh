#!/usr/bin/env bash
# Phase 0. Run ONCE, AS ROOT, on a fresh Ubuntu 24.04 droplet. Everything after this runs as
# the unprivileged user this script creates (Comparator's guarantees assume an unprivileged
# user). It installs OS packages, creates the user, enables its systemd user manager, adds swap,
# raises vm.max_map_count, and installs a read-only copy of the kit in the user's home.
# Safe to run again.
#
#   bash scripts/00_system_setup.sh                       # user "qrh", 64 GB swap file
#   QRH_USER=joey QRH_SWAP_GB=128 bash scripts/00_system_setup.sh
#   QRH_LOCAL=1 QRH_SWAP_GB=32 sudo -E bash scripts/00_system_setup.sh   # on your own Ubuntu machine
set -euo pipefail

[ "$(id -u)" = "0" ] || { echo "run this script as root" >&2; exit 1; }

KIT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QRH_USER="${QRH_USER:-qrh}"
QRH_SWAP_GB="${QRH_SWAP_GB:-64}"
say() { printf '[setup] %s\n' "$*"; }

# A fresh cloud machine is usually still installing updates in its first minutes. Wait for that
# to finish, and keep apt's background jobs out of the way: this machine is disposable and the
# run takes hours.
if command -v cloud-init >/dev/null 2>&1; then
  say "waiting for first-boot initialisation to finish"
  cloud-init status --wait >/dev/null 2>&1 || true
fi
systemctl disable --now apt-daily.timer apt-daily-upgrade.timer >/dev/null 2>&1 || true
systemctl disable --now unattended-upgrades.service >/dev/null 2>&1 || true
systemctl stop apt-daily.service apt-daily-upgrade.service >/dev/null 2>&1 || true

say "installing OS packages"
export DEBIAN_FRONTEND=noninteractive
apt_get() { apt-get -o DPkg::Lock::Timeout=600 "$@"; }
dpkg --configure -a >/dev/null 2>&1 || true
# A failing mirror must not stop the setup if the package lists are good enough: the install
# below is the real test.
apt_get update -y || say "apt-get update reported a problem; trying the install anyway"
apt_get install -y --no-install-recommends \
  git curl ca-certificates build-essential binutils python3 tmux jq zstd time unzip util-linux procps \
  golang-go dbus-user-session libpam-systemd systemd-container

if id "$QRH_USER" >/dev/null 2>&1; then
  say "user $QRH_USER already exists"
else
  say "creating unprivileged user $QRH_USER (no sudo rights, no password, SSH key login only)"
  useradd --create-home --shell /bin/bash "$QRH_USER"
  # No password login, but not "locked" either: some sshd configurations refuse key logins to
  # locked accounts.
  usermod -p '*' "$QRH_USER"
fi
user_home="$(getent passwd "$QRH_USER" | cut -d: -f6)"

if [ -f /root/.ssh/authorized_keys ] && [ ! -f "$user_home/.ssh/authorized_keys" ]; then
  say "copying root's SSH authorized_keys to $QRH_USER so you can 'ssh $QRH_USER@<droplet>'"
  install -d -m 700 -o "$QRH_USER" -g "$QRH_USER" "$user_home/.ssh"
  install -m 600 -o "$QRH_USER" -g "$QRH_USER" /root/.ssh/authorized_keys "$user_home/.ssh/authorized_keys"
fi

say "enabling a lingering systemd user manager for $QRH_USER (jobs survive logout and reboot)"
loginctl enable-linger "$QRH_USER"

if [ "$(sysctl -n vm.max_map_count)" -lt 2097152 ]; then
  say "raising vm.max_map_count to 2097152"
  sysctl -w vm.max_map_count=2097152 >/dev/null
  echo "vm.max_map_count=2097152" >/etc/sysctl.d/99-qrh.conf
fi

swap_now_gb="$(awk '/SwapTotal/ {printf "%d", $2/1048576}' /proc/meminfo)"
if [ "$swap_now_gb" -ge 32 ] || [ "$QRH_SWAP_GB" = "0" ]; then
  say "swap: ${swap_now_gb} GB present, leaving as is"
else
  free_gb="$(df -BG --output=avail / | tail -n 1 | tr -dc '0-9')"
  if [ "$free_gb" -lt $((QRH_SWAP_GB + 120)) ]; then
    say "swap: only ${free_gb} GB free on /, skipping the ${QRH_SWAP_GB} GB swap file (need that plus 120 GB for the run)"
  else
    say "swap: creating /swapfile-qrh (${QRH_SWAP_GB} GB), kept across reboots"
    fallocate -l "${QRH_SWAP_GB}G" /swapfile-qrh
    chmod 600 /swapfile-qrh
    mkswap /swapfile-qrh >/dev/null
    swapon /swapfile-qrh
    grep -q '^/swapfile-qrh ' /etc/fstab || echo '/swapfile-qrh none swap sw 0 0' >>/etc/fstab
  fi
fi

# The kit is installed under /opt, owned by root and read-only for everyone else: nothing that
# runs as the unprivileged user, the code under test included, can alter the scripts or the pins.
dest="/opt/qrh-kit"
if [ "$KIT_DIR" != "$dest" ]; then
  say "installing the kit, read-only, at $dest (with a link at $user_home/qrh-kit)"
  rm -rf "$dest"
  cp -a "$KIT_DIR" "$dest"
fi
rm -rf "$dest/results" "$dest/.qrh_host" "$dest/.claude/settings.local.json"
chown -R root:root "$dest"
chmod -R u=rwX,go=rX "$dest"
chmod 755 "$dest"/scripts/*.sh "$dest"/scripts/*.py
ln -sfn "$dest" "$user_home/qrh-kit"

# If a protocol is already under way in this account, say in its record that the kit was replaced.
if [ -d "$user_home/qrh-work/receipt" ]; then
  printf -- '- %s  the kit was (re)installed by 00_system_setup.sh; manifest digest %s\n' \
    "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$(sha256sum "$dest/KIT_MANIFEST.sha256" 2>/dev/null | cut -c1-16)" \
    >>"$user_home/qrh-work/receipt/DEVIATIONS.md"
  chown "$QRH_USER":"$QRH_USER" "$user_home/qrh-work/receipt/DEVIATIONS.md"
fi

# Marks this account as the account the kit's scripts are meant to run in.
date -u +%Y-%m-%dT%H:%M:%SZ >"$user_home/.qrh-droplet"
chown root:root "$user_home/.qrh-droplet"
chmod 444 "$user_home/.qrh-droplet"
if [ "${QRH_LOCAL:-0}" = "1" ]; then
  echo "local" >"$user_home/.qrh-local"
  chown root:root "$user_home/.qrh-local"
  cat <<EOF

[setup] done. This is your own machine, set up like the droplet. Everything from here on runs
        as $QRH_USER, never as root. Open a shell as that user (this starts its systemd session):
            sudo machinectl shell $QRH_USER@
        The kit is in /opt/qrh-kit (also reachable as ~/qrh-kit). First command there:
            cd ~/qrh-kit && scripts/where.sh
EOF
else
  cat <<EOF

[setup] done. Everything from here on runs as $QRH_USER, never as root.
        Log in as that user over SSH (not with 'su': su does not start its systemd session):
            ssh $QRH_USER@<this-droplet>
        The kit is in /opt/qrh-kit (also reachable as ~/qrh-kit). First command there:
            scripts/where.sh
EOF
fi
