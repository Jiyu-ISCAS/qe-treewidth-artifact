source .venv/bin/activate

echo "Step 1: parse the .smt2 files and output associated primal graphs and intermediate results (variable renaming maps, Mathematica-styled formula strings)"
python3 src/heuristics/smt2graph.py --input examples/ --intermediate-output tests/intermediate/ --gr-output tests/graph/ --time 1 --log-path tests/intermediate/smt2graph.log

echo "Step 2: conduct tree decompostion for primal graphs"
cd tests/PACE2017-TrackA
bash process_graphs.sh
cd ..
cd ..

echo "Step 3: run heuristics"
python3 src/heuristics/heuristics.py --intermediate-input tests/intermediate/ --gr-input tests/graph/ --td-input tests/TD_results --output tests/order/
