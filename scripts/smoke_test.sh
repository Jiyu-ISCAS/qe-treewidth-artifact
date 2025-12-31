source .venv/bin/activate

echo "Step 1: parse the .smt2 files and output associated primal graphs and intermediate results (variable renaming maps, Mathematica-styled formula strings)"
python3 src/heuristics/smt2graph.py --input tests/smoke_test/ --intermediate-output tests/smoke_test/ --gr-output tests/smoke_test/ --time 1 --log-path tests/smoke_test/smoke.log

echo "Step 2: conduct tree decompostion for primal graphs"
cd tests/PACE2017-TrackA
./tw-exact < ../smoke_test/smoke.gr > ../smoke_test/smoke.td
cd ..
cd ..

echo "Step 3: run heuristics"
python3 src/heuristics/heuristics.py --intermediate-input tests/smoke_test/ --gr-input tests/smoke_test/ --td-input tests/smoke_test/ --output tests/smoke_test/

echo "Running FME of 3 orders on the tiny example"
python3 src/FME/compare_single_input.py \
    --ine-input tests/smoke_test/smoke.ine \
    --ord-input tests/smoke_test/smoke.ord \
    --vars "1,2,3" \
    --seed 2027 \
    --cap 100000 \
    --output tests/smoke_test/result.json
cat tests/smoke_test/result.json

python3 src/FME/summarize_fme_results.py --input tests/smoke_test/result.json --out tests/smoke_test/summary.json
cat tests/smoke_test/summary.json
