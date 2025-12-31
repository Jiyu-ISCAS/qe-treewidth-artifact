#!/usr/bin/env bash
set -euo pipefail

# Directories / script locations
SRC_DIR="src/FME"
EXAMPLES_DIR="examples/LRA/Ex4"
ORDER_DIR="tests/order/LRA/Ex4"
OUT_DIR="tests/FME_results/Ex4"

# Common seed for all runs
SEED=2027

# Maximum capacity
CAP=10000000

# Ensure output directory exists
mkdir -p "$OUT_DIR"

# Per-run names and variable lists (index-aligned)
names=(
  "Ex4-1" "Ex4-2" "Ex4-3" "Ex4-4" "Ex4-5"
  "Ex4-6" "Ex4-7" "Ex4-8" "Ex4-9" "Ex4-10"
)

vars=(
  "2,8,15,16,18,20"
  "1,3,13,15,16,19"
  "4,7,13,14,17,20"
  "4,6,8,10,14,16"
  "1,2,3,6,18,19"
  "9,10,13,14,15"
  "4,6,9,14,15,17"
  "1,2,3,7,12,17"
  "2,5,11,12,17,20"
  "1,4,8,13,15,16"
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
