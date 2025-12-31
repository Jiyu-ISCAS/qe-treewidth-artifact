#!/usr/bin/env bash
set -euo pipefail

# Directories / script locations
SRC_DIR="src/FME"
EXAMPLES_DIR="examples/LRA/Ex3"
ORDER_DIR="tests/order/LRA/Ex3"
OUT_DIR="tests/FME_results/Ex3"

# Common seed for all runs
SEED=2027

# Maximum capacity
CAP=10000000

# Ensure output directory exists
mkdir -p "$OUT_DIR"

# Per-run names and variable lists (index-aligned)
names=(
  "Ex3-1" "Ex3-2" "Ex3-3" "Ex3-4" "Ex3-5"
  "Ex3-6" "Ex3-7" "Ex3-8" "Ex3-9" "Ex3-10"
)

vars=(
  "1,4,5,9,10,11,13,14,19,20"
  "4,8,9,10,11,12,15,16,17,20"
  "3,6,7,8,9,10,11,12,13,19"
  "1,3,5,8,9,13,14,15,18,19"
  "1,2,6,9,11,12,14,15,17,18"
  "3,5,6,8,10,12,14,15,18,19"
  "1,3,5,6,7,8,11,16,17,18"
  "2,4,7,8,10,11,13,16,17,18"
  "5,6,8,9,11,13,15,17,18,20"
  "1,2,4,5,6,7,12,13,14,17"
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
