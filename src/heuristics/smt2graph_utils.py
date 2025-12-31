import json
import networkx as nx
import re
from pathlib import Path
from pysmt.shortcuts import *
from pysmt.typing import *
from pysmt.smtlib.parser import SmtLibParser
from typing import Dict, Iterator, List, Tuple


def iter_files(base_dir: str | Path) -> Iterator[Tuple[Path, Path]]:
    """
    Yield tuples (relative_dir, filename_path) where:
      - relative_dir is a Path relative to base_dir (Path('.') for top level)
      - filename_path is Path(filename) (the name only)
    """
    base = Path(base_dir)
    if not base.is_dir():
        raise ValueError(f"base_dir must be an existing directory: {base!s}")
    for file_path in sorted(base.rglob("*")):
        if file_path.is_file():
            rel_dir = file_path.parent.relative_to(base)  # Path('.') if top-level
            yield (rel_dir, Path(file_path.name))


def _natural_key(name: str):
    """
    Produce a tuple key for natural sorting: split on digit groups.
    Example: "x10_a2" -> ["x", 10, "_a", 2, ""]
    """
    parts = re.split(r"(\d+)", name)
    return tuple(int(p) if p.isdigit() else p.lower() for p in parts)


def parse_smt2_file(smt2_file: str) -> Tuple[nx.Graph, Dict[Symbol, Symbol], str]:
    """
    Parse an SMT-LIB file, build its associated primal graph, and
    rename all real-valued variables deterministically using
    lexicographic order of original variable names.

    Args:
        smt2_file: path to the .smt2 file.

    Returns:
        G: networkx.Graph whose nodes are integer indices 1..n (1 corresponds to x1).
        subs_map: Dict mapping original pysmt.Symbol -> new pysmt.Symbol (x1, x2, ...).
        merged_asserts: single string joining all renamed assertions with " && ".
    """
    p = Path(smt2_file)
    if not p.exists():
        raise FileNotFoundError(f"{smt2_file} not found")
    parser = SmtLibParser()
    with open(p, "r") as f:
        script = parser.get_script(f)

    # 1) collect assertions
    raw_asserts = []
    for cmd in script.commands:
        if cmd.name == "declare-fun":
            var = cmd.args[0]
            # Only keep real-typed variables
            if not var.symbol_type().is_real_type():
                raise TypeError(f"Non-real declared symbol: {var}")
        elif cmd.name == "assert":
            raw_asserts.append(cmd.args[0])

    # 2) collect all real free variables across assertions (as pysmt.Symbol)
    all_symbols = set()
    for a in raw_asserts:
        free = a.get_free_variables()
        for v in free:
            all_symbols.add(v)

    # 3) deterministic ordering: sort by symbol_name()
    sorted_symbols = sorted(all_symbols, key=lambda s: _natural_key(s.symbol_name()))

    # 4) build substitution map: original Symbol -> new Symbol (x1, x2, ...)
    subs_map: Dict[Symbol, Symbol] = {}
    # index_map: original symbol name -> integer index (1-based)
    index_map: Dict[str, int] = {}
    for idx, orig_var in enumerate(sorted_symbols, start=1):
        new_name = f"x{idx}"
        subs_map[orig_var] = Symbol(new_name, REAL)
        index_map[orig_var.symbol_name()] = idx

    # 5) apply substitutions and serialize assertions
    renamed_asserts: List[str] = []
    for a in raw_asserts:
        new_a = substitute(a, subs_map)
        s = str(new_a.serialize())
        s = s.replace("&", "&&").replace(" = ", " == ")
        renamed_asserts.append(s)
    merged_asserts = " && ".join(renamed_asserts)

    # 6) build primal graph with integer nodes (1..n)
    G = nx.Graph()
    for a in raw_asserts:
        free = [v for v in a.get_free_variables() if v.symbol_type().is_real_type()]
        indices = [
            index_map[v.symbol_name()] for v in free if v.symbol_name() in index_map
        ]
        for i, idx1 in enumerate(indices):
            G.add_node(idx1)
            for idx2 in indices[i + 1 :]:
                if idx1 != idx2:
                    G.add_edge(idx1, idx2)

    return G, subs_map, merged_asserts


def print_results(
    filename: Path,
    G: nx.Graph,
    subs_map: Dict[Symbol, Symbol],
    merged_asserts: str,
    intermediate_dir: Path,
    gr_files_dir: Path,
) -> None:
    """
    Print the results given by parse_smt2_file() to files.

    Args:
        filename: the filename with/without extensions.
        G, subs_map, merged_asserts: see comments from parse_smt2_file().
        intermediate_dir: directory to store subs_map and merged_asserts.
        gr_files_dir: directory to store G in .gr format for tree decomposition.

    Returns: None.
    """
    intermediate_dir.mkdir(parents=True, exist_ok=True)
    gr_files_dir.mkdir(parents=True, exist_ok=True)
    # Print graph
    gr_file = gr_files_dir / filename.with_suffix(".gr")
    with open(gr_file, "w") as file:
        file.write(f"p tw {G.number_of_nodes()} {G.number_of_edges()}\n")
        for u, v in G.edges():
            file.write(f"{u} {v}\n")

    map_file = intermediate_dir / filename.with_suffix(".json")
    with open(map_file, "w") as map_file:
        map_dict = {
            orig.symbol_name(): new.symbol_name() for orig, new in subs_map.items()
        }
        json.dump(map_dict, map_file, indent=2, sort_keys=True)

    formula_file = intermediate_dir / filename.with_suffix(".txt")
    with open(formula_file, "w") as asserts_file:
        asserts_file.write(f"{merged_asserts}\n")
