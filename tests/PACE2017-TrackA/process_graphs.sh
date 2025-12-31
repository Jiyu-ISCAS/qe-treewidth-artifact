#!/bin/bash

# Edit this line to point at LRA/NRA examples directory:
BASE=".."

# Ensure the test_results directory exists
if [ ! -d "$BASE/TD_results" ]; then
    mkdir -p "$BASE/TD_results"
fi

# Loop through all .gr files in the test_instance directory
for graph_file in "$BASE"/graph/*.gr; do
    # Extract the base name of the file (without directory and extension)
    base_name=$(basename "$graph_file" .gr)
    # Define the output file path in the test_results directory
    output_file="$BASE/TD_results/${base_name}.td"
    # Run the tw-exact program
    ./tw-exact < "$graph_file" > "$output_file"
    # Optional: Print a message indicating completion
    # echo "Processed $graph_file -> $output_file"
    # Optimal: Verify the result of the tree decomposition.
    # ./td-validate-master/td-validate $graph_file $output_file
done