#!/usr/bin/env bash
# Where is the density-layer run? Read-only.    scripts/z23_density_status.sh [--wait SECONDS]
KIT="${QRH_KIT_DIR:-/opt/qrh-kit}"
[ -f "$KIT/scripts/lib.sh" ] || { echo "main kit not found at $KIT (set QRH_KIT_DIR)" >&2; exit 2; }
exec env QRH_WORK="${QRH_Z23_WORK:-$HOME/qrh-zeta23-work}" "$KIT/scripts/status.sh" zeta23-density-v5 "$@"
