# Quantifier Elimination Meets Treewidth

This repository (<https://github.com/Jiyu-ISCAS/qe-treewidth-artifact>) contains the research artifact for the publication:

Quantifier Elimination Meets Treewidth

Hao Wu, Jiyu Zhu, Amir Kafshdar Goharshady, Jie An, Bican Xia, and Naijun Zhan

TACAS 2026

This artifact is also available at Zenodo (<https://doi.org/10.5281/zenodo.18150640>).

## Directory Structure

```shell
qe-treewidth-artifact/
├── examples/
    ├── LRA/  # randomly generated examples written in pycddlib format and SMT-LIB format
    └── NRA/  # only SMT-LIB format
├── scripts/
├── src/
    ├── CAD/  # wolfram programs for NRA examples
    ├── FME/  # naive implementation of Fourier–Motzkin elimination
    └── heuristics/  # extract heuristic elimination order from .smt2 files
├── tests/  # auxiliary tools and working directory when running the artifact
├── wheelhouse/  # some python packages for offline environment setup
├── LICENSE
└── README.md
```

## System Requirements and Performance

### Operating System

The artifact targets `AMD64` systems, and has been tested on Windows 11 (`WSL 2, Ubuntu 24.04`) and on the TACAS 2026 virtual machine (`Ubuntu 25.04`) available at <https://zenodo.org/records/17171929>. We recommend running the artifact on a native Linux environment.

### Hardware Requirements

The heuristic algorithm itself has modest hardware requirements and takes only a few seconds. However, both `FME` and `CAD` algorithms are computationally expensive in both time and memory. On our test machine (`i7-13700` CPU with `32GB` RAM), running all LRA examples typically takes about 30 minutes, while running all NRA examples takes about 3 hours.

The minimum recommended RAM for running the full artifact is `16GB`. We recommend `24GB` or `32GB` of RAM to avoid premature termination on larger instances.

Accordingly, in addition to the `smoke test` described in `Setup`, we provide alternative ways to run smaller subsets of the experiments.

## Setup

- OpenJDK 21.0.9 (required for tree decomposition tool)
- Python 3.13
- networkx 3.5 (provided in this repository)
- PySMT 0.9.6 (provided in this repository)
- Wolfram engime 14.3 (required for NRA examples)

1. Clone this repository from GitHub

    ```shell
    git clone https://github.com/Jiyu-ISCAS/qe-treewidth-artifact
    cd qe-treewidth-artifact
    ```

2. Create the Python environment and build the tree decomposition tool (<https://github.com/TCS-Meiji/PACE2017-TrackA>) using provided script

    ```shell
    bash scripts/setup_venv.sh
    ```

    Activate the created virtual environment to verify setup

    ```shell
    source .venv/bin/activate
    ```

    When the activation succeeds your shell prompt will typically show `(.venv)` at the start and you can run `pip3 list` to check installed packages.
  
## Reproduce Results

1. (*Optional*) Run the smoke test early to test the algorithm pipeline

    ```shell
    bash scripts/smoke_test.sh
    ```

2. Run the main algorithm to extract heuristic elimination orders from `.smt2` files using the provided script

    ```shell
    bash scripts/heuristic.sh
    ```

    see [Heuristic Results](#heuristic-results) for more details.

3. Verify results on LRA examples (`Table 1` in the paper) by running the bulk test script

    ```shell
    bash scripts/bulk_FME.sh
    ```

    see [LRA/FME Results](#lrafme-results) for more details.

4. Verify results on NRA examples (`Table 2` in the paper)
   - Download `Wolfram Engine 14.3` from the official site (<https://www.wolfram.com/engine/>) since no direct download link is available. `Wolfram Engine` is free but requires a one-time activation. Click `Start Download`, follow the `Get your license` link, sign in with your Wolfram ID, and complete the activation.
   - Make the installer executable and install (example)

        ```shell
        sudo bash /path/to/<installer_name.sh>
        # press ENTER to accept the default installation path when prompted
        ```

   - Activate the Engine from the terminal

        ```shell
        wolframscript --activate
        # follow the prompts to enter your Wolfram ID credentials
        ```

   - Once activated, run the NRA bulk test script

        ```shell
        bash scripts/bulk_CAD.sh
        ```

        see [NRA/CAD Results](#nracad-results) for more details.

5. (*Optional*) Clean up the setup virtual environemt and running results using the script

    ```shell
    bash scripts/clean.sh
    ```

## Partial Tests

### Test on Single LRA Instance

If you are interested in a single LRA instance set `Ex<i>`, you can run only that set using

```shell
bash scripts/FME/Ex<i>.sh  # replace <i> with a number from 1..6
```

### Test on Single NRA Instance

If you are interested in a single NRA instance `Ex<i>`, you can run only that instance using

```shell
wolframscript src/CAD/Ex<i>.wls # replace <i> with a number from 7..12
```

You may also evaluate specific heuristic elimination orders for a single instance by passing additional options

```shell
wolframscript src/CAD/Ex<i>.wls [-SVO] [-Brown] [-PEO] [-TD]  # replace <i> with a number from 7..12
```

- `-SVO`: use the order suggested by Maple’s `SuggestVariableOrder`

- `-Brown`: use the Brown heuristic

- `-PEO`: use the PEO heuristic

- `-TD`: use the elimination order produced by our heuristic

You may select any subset of these four options. If no options are specified, all four orders are evaluated by default.

## Reuse

We provide additional tests for LRA and NRA inputs that are not included in the research paper. This section demonstrates that our software can process inputs provided the LRA/NRA system files use the `.ine` and `.smt2` format.

You can run the additional tests with

```shell
bash scripts/additional_tests.sh 
```

## Explanation of Important Files

### LRA Examples

```shell
LRA/
    ├── Ex1/  # 10 instances for experiment result (Table 1, ID 1)
    ├── Ex2/  # subsequent lines follow the same format
    ├── ...
    └── Ex6/
```

Note that each LRA instance is written in 2 equivalent formats: the SMT-LIB format (`.smt2` file) and `pycddlib` format (`.ine` file).

If a linear system has $n$ variables and $m$ inequalities:

$$
\begin{equation*}
\begin{split}
& b_1 - a_{11} x_1 - a_{12} x_2 - \cdots - a_{1n} x_n \ge 0 \\
& b_2 - a_{21} x_1 - a_{22} x_2 - \cdots - a_{2n} x_n \ge 0 \\
& \cdots\\
& b_m - a_{m1} x_1 - a_{m2} x_2 - \cdots - a_{mn} x_n \ge 0
\end{split}
\end{equation*}
$$

then the `pycddlib` format describes the above linear system in the following way:

$$
\begin{equation*}
\begin{split}
& \text{H-representation} \\
& \text{begin} \\
& m \quad n \\
& b_1 \quad a_{11} \quad a_{12} \quad \cdots \quad a_{1n} \\
& b_2 \quad a_{21} \quad a_{22} \quad \cdots \quad a_{2n} \\
& \cdots  \\
& b_m \quad a_{m1} \quad a_{m2} \quad \cdots \quad a_{mn} \\
& \text{end}
\end{split}
\end{equation*}
$$

### Heuristic Results

After running `bash scripts/heuristic.sh` new working directories are created under `tests/`

```shell
tests/
├── graph/          # associated primal graphs (formats: see https://pacechallenge.org/2017/treewidth/)
├── intermediate/   # intermediate results; for each LRA/NRA instance this contains two files:
                    #   1) a substitution map (original variable names → x1 ... xn)
                    #   2) a formula in standard Mathematica format
├── order/          # heuristic elimination orders produced by our algorithm and by other heuristics
├── TD_results/     # tree decomposition results (formats: see https://pacechallenge.org/2017/treewidth/)
└── ...
```

### LRA/FME Results

```shell
tests/
├── FME_results/
    ├── Ex1/
        ├── Ex1-1.json  # results of example instance set 1, intance 1
        ├── ...
        ├── Ex1-10.json
        └── summary.json  # results summary of 10 instances
    ├── Ex2/
    ├── ...
    └── Ex6/
└── ...
```

For each set of 10 instances we record three different elimination orders in separate `.json` files and include a `summary.json` file in the same directory.

#### Per-instance files (`Ex<i>-<j>.json`)

Each per-instance JSON records results for three elimination orders:

- `random`: best random order (index is 1-based)
- `greedy`: greedy heuristic
- `heuristic`: our heuristic

Each order contains these fields:

- `aborted`: true if FME terminated early due to the inequality-capacity limit.
- `final_count`: number of inequality constraints at termination (estimate if aborted).
- `time_s`: runtime in seconds at termination.

> Note that for larger instances (`ID 2–5`) random ordering performs poorly: FME may abort early after reaching the limit of $10^{7}$ inequality constraints. In such cases, the recorded `final_count` is the estimate at termination and `time_s` is the runtime measured at termination.

##### Example per-instance JSON (schema)

```json
{
  "file": "examples/LRA/Ex1/Ex1-1.ine",
  "n_vars": 15,
  "actual_best_random_order_used_1based": [3,7,11,10,2],
  "result_random": {
    "aborted": false,
    "final_count": 67642,
    "time_s": 0.5226932239999975
  },
  "actual_greedy_order_used_1based": [11,7,10,3,2],
  "result_greedy": {
    "aborted": false,
    "final_count": 12346,
    "time_s": 0.04764381599999723
  },
  "actual_heuristic_order_used_1based": [11,7,10,2,3],
  "result_heuristic": {
    "aborted": false,
    "final_count": 16712,
    "time_s": 0.06850071700000271
  }
}
```

#### Summary file (`summary.json`)**

`summary.json` contains aggregated statistics:

- counts of successful vs. aborted instances per order
- averages for `final_count` and `time_s`

Averaging rules:

- `random`: averages computed over all 10 instances.
- `greedy` and `heuristic`: averages computed only over successful instances (`aborted == false`).

##### Example summary JSON (schema)

```json
[
  {
    "order": "random",
    "success": 10,
    "abort": 0,
    "ave_cnt": 51608.4,
    "ave_runtime": 0.22128993920000006
  },
  {
    "order": "greedy",
    "success": 10,
    "abort": 0,
    "ave_cnt": 4404.7,
    "ave_runtime": 0.01671946560000137
  },
  {
    "order": "heuristic",
    "success": 10,
    "abort": 0,
    "ave_cnt": 4841.3,
    "ave_runtime": 0.018299490699999053
  }
]
```

### NRA/CAD Results

```shell
tests/
├── CAD_results/
    ├── Ex7.csv
    ├── ...
    └── Ex12.csv
└── ...
```

Each instance’s results are stored as a `.csv` file under the above directory, easy to read.

#### Example result CSV

```csv
"Method","Time (s)","Cell Count"
"(1) Maple SuggestVariableOrder",456.821663,1133532
"(2) Brown heuristics",144.838163,271120
"(3) PEO",95.546835,274724
"(4) Brown + Tree Decomp",31.534584,110828
```
