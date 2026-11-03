#!/usr/bin/env bash
# Where is the library run? Read-only; the main kit's status.sh pointed at the add-on's own
# log directory.    scripts/mnf_status.sh [--wait SECONDS]
KIT="${QRH_KIT_DIR:-/opt/qrh-kit}"
[ -f "$KIT/scripts/lib.sh" ] || { echo "main kit not found at $KIT (set QRH_KIT_DIR)" >&2; exit 2; }
QRH_WORK="${QRH_WORK:-$HOME/qrh-work}"
exec env QRH_WORK="$QRH_WORK/mnf" "$KIT/scripts/status.sh" mnf-library "$@"
