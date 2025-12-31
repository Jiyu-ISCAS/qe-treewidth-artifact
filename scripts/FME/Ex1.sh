#!/usr/bin/env bash
set -euo pipefail

# Directories / script locations
SRC_DIR="src/FME"
EXAMPLES_DIR="examples/LRA/Ex1"
ORDER_DIR="tests/order/LRA/Ex1"
OUT_DIR="tests/FME_results/Ex1"

# Common seed for all runs
SEED=2027

# Maximum capacity
CAP=10000000

# Ensure output directory exists
mkdir -p "$OUT_DIR"

# Per-run names and variable lists (index-aligned)
names=(
  "Ex1-1" "Ex1-2" "Ex1-3" "Ex1-4" "Ex1-5"
  "Ex1-6" "Ex1-7" "Ex1-8" "Ex1-9" "Ex1-10"
)

vars=(
  "2,3,7,10,11"
  "1,3,6,10,11"
  "2,5,10,11,15"
  "1,3,5,13,15"
  "2,3,6,9,12"
  "1,6,9,10,11"
  "1,5,9,12,14"
  "1,4,6,11,13"
  "1,2,10,12,13"
  "3,6,8,11,15"
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
