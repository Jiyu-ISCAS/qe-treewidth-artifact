find . -type d -name "__pycache__" -exec rm -rf {} +
rm -r .venv
rm -r tests/graph
rm -r tests/intermediate
rm -r tests/order
rm -r tests/TD_results
rm -r tests/FME_results
rm -r tests/CAD_results
rm install.log

cd tests/PACE2017-TrackA
make clean
