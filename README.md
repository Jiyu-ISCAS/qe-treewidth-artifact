# Quantifier Elimination Meets Treewidth

This repository contains the research artifact for the publication:

Quantifier Elimination Meets Treewidth

Hao Wu, Jiyu Zhu, Amir Kafshdar Goharshady, Jie An, Bican Xia, and Naijun Zhan

TACAS 2026

## Directory structure

```shell
./qe-treewidth-artifact
├── examples/
    ├── LRA/  # randomly generated examples written in pycddlib format and SMT-LIB format
    ├── NRA/  # only SMT-LIB format
├── scripts/
├── src/
    ├── CAD/  # wolfram programs for NRA examples
    ├── FME/  # naive implementation of Fourier–Motzkin elimination
    ├── heuristics/  # extract heuristic elimination order from .smt2 files
├── tests/  # auxiliary tools and working directory when running the artifact
├── wheelhouse/  # some python packages for offline environment setup
├── LICENSE
└── README.md
```

## Setup

- OpenJDK 21.0.9 (for tree decomposition tool)
- Python 3.13
- networkx 3.5 (provided in this repository)
- PySMT 0.9.6 (provided in this repository)
- Wolfram engime 14.3 (for NRA examples)

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

3. Run the main algorithm to extract heuristic elimination orders from `.smt2` files using the provided script

    ```shell
    bash scripts/heuristic.sh
    ```

4. Verify results on LRA examples by running the bulk test script

    ```shell
    bash scripts/bulk_FME.sh
    ```

5. Verify results on NRA examples
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

## Explanation on LRA examples

```shell
LRA/
    ├── Ex1/  # 10 instances for experiment result (Table 1, ID 1)
    ├── Ex2/  # subsequent lines follow the same format
    ├── ...
    └── Ex6/
```

Note that each LRA instance is written in 2 equivalent formats: the SMT-LIB format (`.smt2` file) and pycddlib format (`.ine` file).

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

then the pycddlib format describes the above linear system in the following way:

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
