#!/usr/bin/env bash
set -euo pipefail

# Directories / script locations
SRC_DIR="src/FME"
EXAMPLES_DIR="examples/LRA/Ex6"
ORDER_DIR="tests/order/LRA/Ex6"
OUT_DIR="tests/FME_results/Ex6"

# Common seed for all runs
SEED=2027

# Maximum capacity
CAP=10000000

# Ensure output directory exists
mkdir -p "$OUT_DIR"

# Per-run names and variable lists (index-aligned)
names=(
  "Ex6-1" "Ex6-2" "Ex6-3" "Ex6-4" "Ex6-5"
  "Ex6-6" "Ex6-7" "Ex6-8" "Ex6-9" "Ex6-10"
)

vars=(
  "6,10,21,24,25"
  "5,10,20,21,30"
  "10,13,15,29,30"
  "17,18,22,23,29"
  "7,11,14,19,28"
  "7,22,23,25,28"
  "6,12,19,27,30"
  "17,19,25,27,30"
  "2,6,15,22,30"
  "7,20,23,26,30"
)

# Run each job with the shared seed
for i in "${!names[@]}"; do
  name="${names[i]}"
  ine="$EXAMPLES_DIR/${name}.ine"
  ord="$ORDER_DIR/${name}.ord"
  out="$OUT_DIR/${name}.json"

  python3 "$SRC_DIR/compare_single_input.py" \
    --ine-input "$ine" \
    --ord-input "$ord" \
    --vars "${vars[i]}" \
    --seed "$SEED" \
    --cap "$CAP" \
    --output "$out"
done

# Build summarize input list and run summarizer
inputs=()
for name in "${names[@]}"; do
  inputs+=( "$OUT_DIR/$name.json" )
done

python3 "$SRC_DIR/summarize_fme_results.py" --input "${inputs[@]}" --out "$OUT_DIR/summary.json"
