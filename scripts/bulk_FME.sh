#!/usr/bin/env bash
set -euo pipefail

# Run scripts for each example (caller CWD must be repo root or path adjusted)
for i in {1..6}; do
  echo "=== Running Ex$i ==="
  bash "scripts/FME/Ex${i}.sh" || { echo "Ex${i} failed"; exit 1; }
done

echo "All FME scripts completed."
