#!/usr/bin/env bash
set -euo pipefail

# Paths: adjust if your repo layout differs
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WHEELDIR="$REPO_ROOT/wheelhouse"
VENV="$REPO_ROOT/.venv"
LOG="$REPO_ROOT/install.log"

echo "Install started at $(date)" | tee "$LOG"

# Basic checks
if [ ! -d "$WHEELDIR" ]; then
  echo "ERROR: wheelhouse not found at $WHEELDIR" | tee -a "$LOG"
  exit 1
fi

# Ensure venv tool exists
if ! python3 -m venv --help > /dev/null 2>&1; then
  echo "python3-venv is missing. Install it with: sudo apt-get update && sudo apt-get install -y python3-venv python3-full" | tee -a "$LOG"
  exit 1
fi

# Create venv if needed
if [ ! -d "$VENV" ]; then
  python3 -m venv "$VENV"
fi

# Activate venv
# shellcheck source=/dev/null
source "$VENV/bin/activate"

pip3 install wheelhouse/networkx-3.5-py3-none-any.whl
pip3 install wheelhouse/PySMT-0.9.6-py2.py3-none-any.whl

cd tests/PACE2017-TrackA
make exact
chmod +x tw-exact
