# Quantifier Elimination Meets Treewidth

This repository contains the research artifact for the publication:

Quantifier Elimination Meets Treewidth

Hao Wu, Jiyu Zhu, Amir Kafshdar Goharshady, Jie An, Bican Xia, and Naijun Zhan

TACAS 2026

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

This artifact has been tested on Windows 11 (`WSL 2, Ubuntu 24.04`) and on the TACAS 2026 virtual machine (`Ubuntu 25.04`) available at <https://zenodo.org/records/17171929>. We recommend running the artifact on a native Linux environment.

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

3. (*Optional*) Run the smoke test early to test the algorithm pipeline

    ```shell
    bash scripts/smoke_test.sh
    ```

4. Run the main algorithm to extract heuristic elimination orders from `.smt2` files using the provided script

    ```shell
    bash scripts/heuristic.sh
    ```

5. Verify results on LRA examples by running the bulk test script

    ```shell
    bash scripts/bulk_FME.sh
    ```

6. Verify results on NRA examples
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

## Explanation of Important Files

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
└── ...
```

For each set of 10 instances we record three different elimination orders in separate `.json` files and include a summary `.json` file in the same directory. Note that for larger instances (IDs 2–5) random ordering performs poorly: FME may terminate early after reaching the limit of $10^7$ inequality constraints. In those cases the recorded `final_count` is the estimate at termination and the `time_s` is the runtime at termination.

### NRA/CAD Results

```shell
tests/
├── CAD_results/
└── ...
```

Each instance’s results are stored as a `.csv` file under the above directory, easy to read.

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
