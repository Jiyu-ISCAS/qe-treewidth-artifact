#!/usr/bin/env bash
set -euo pipefail

# Directories / script locations
SRC_DIR="src/FME"
EXAMPLES_DIR="examples/LRA/Ex5"
ORDER_DIR="tests/order/LRA/Ex5"
OUT_DIR="tests/FME_results/Ex5"

# Common seed for all runs
SEED=2027

# Maximum capacity
CAP=10000000

# Ensure output directory exists
mkdir -p "$OUT_DIR"

# Per-run names and variable lists (index-aligned)
names=(
  "Ex5-1" "Ex5-2" "Ex5-3" "Ex5-4" "Ex5-5"
  "Ex5-6" "Ex5-7" "Ex5-8" "Ex5-9" "Ex5-10"
)

vars=(
  "4,6,7,8,10,13,17,19,26,28,29,30"
  "3,5,6,7,10,11,14,19,21,26,27,29"
  "3,4,5,7,9,11,15,18,27,28,29,30"
  "1,2,4,5,8,11,12,14,15,19,21,30"
  "3,6,7,9,10,12,14,16,23,27,28,30"
  "4,6,7,9,10,13,18,21,23,25,26,27"
  "1,3,4,5,10,16,18,21,22,23,26,27"
  "4,10,14,15,18,22,23,24,25,26,28,30"
  "1,5,7,9,10,12,13,14,17,19,20,24"
  "2,6,7,8,14,16,18,22,23,24,28,30"
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
