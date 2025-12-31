find . -type d -name "__pycache__" -exec rm -rf {} +
rm -r .venv
rm -r tests/graph
rm -r tests/intermediate
rm -r tests/order
rm -r tests/TD_results
rm -r tests/FME_results
rm -r tests/CAD_results
rm install.log
find . -name "*.gr" -type f -delete
find . -name "*.json" -type f -delete
find . -name "*.log" -type f -delete
find . -name "*.ord" -type f -delete
find . -name "*.td" -type f -delete
find . -name "*.txt" -type f -delete

cd tests/PACE2017-TrackA
make clean
