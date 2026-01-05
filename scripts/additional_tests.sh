#!/usr/bin/env bash
set -euo pipefail

# Directories / script locations
SRC_DIR="src/FME"
EXAMPLES_DIR="examples/LRA/Additional"
ORDER_DIR="tests/order/LRA/Additional"
OUT_DIR="tests/FME_results/Additional"

# Common seed for all runs
SEED=2027

# Maximum capacity
CAP=10000000

# Ensure output directory exists
mkdir -p "$OUT_DIR"

# Per-run names and variable lists (index-aligned)
names=(
  "AEx1-1" "AEx1-2" "AEx1-3" "AEx1-4" "AEx1-5"
  "AEx1-6" "AEx1-7" "AEx1-8" "AEx1-9" "AEx1-10"
)

vars=(
  "1,2,4,7,9"
  "1,3,5,6,10"
  "2,3,6,8,9"
  "1,4,6,9,10"
  "2,5,7,8,10"
  "1,3,4,8,9"
  "3,4,5,7,10"
  "1,2,6,8,10"
  "2,4,5,9,10"
  "1,3,6,7,8"
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
wolframscript src/CAD/AEx2.wls

echo "LRA results stored in tests/FME_results/Additional/, NRA results stored in tests/CAD_results/Additional/"