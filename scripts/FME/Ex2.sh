#!/usr/bin/env bash
set -euo pipefail

# Directories / script locations
SRC_DIR="src/FME"
EXAMPLES_DIR="examples/LRA/Ex2"
ORDER_DIR="tests/order/LRA/Ex2"
OUT_DIR="tests/FME_results/Ex2"

# Common seed for all runs
SEED=2027

# Maximum capacity
CAP=10000000

# Ensure output directory exists
mkdir -p "$OUT_DIR"

# Per-run names and variable lists (index-aligned)
names=(
  "Ex2-1" "Ex2-2" "Ex2-3" "Ex2-4" "Ex2-5"
  "Ex2-6" "Ex2-7" "Ex2-8" "Ex2-9" "Ex2-10"
)

vars=(
  "3,5,8,9,10"
  "1,5,7,8,13"
  "3,9,11,13,15"
  "5,6,9,12,15"
  "3,8,9,10,15"
  "2,3,5,6,8"
  "2,3,9,12,14"
  "8,9,12,13,15"
  "3,7,11,13,15"
  "6,7,9,10,13"
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
