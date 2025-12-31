import argparse
import json
import sys
from heuristics_utils import *
from smt2graph_utils import *


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Extract elimination order using Brown, PEO and our heuristic"
    )
    p.add_argument(
        "--intermediate-input", type=Path, help="Directory for formula inputs"
    )
    p.add_argument("--gr-input", type=Path, help="Directory for .gr graph inputs")
    p.add_argument(
        "--td-input",
        type=Path,
        help="Directory for tree decomposition results input",
    )
    p.add_argument(
        "--output", type=Path, help="Directory for elimination order results"
    )
    return p.parse_args(argv)


if __name__ == "__main__":
    ns = parse_args(sys.argv[1:])
    for rel_dir, name in iter_files(ns.intermediate_input):
        if not str(name).lower().endswith(".txt"):
            continue
        formula_input = ns.intermediate_input / rel_dir / name
        map_input = ns.intermediate_input / rel_dir / name.with_suffix(".json")
        gr_input = ns.gr_input / name.with_suffix(".gr")
        td_input = ns.td_input / name.with_suffix(".td")
        output_dir = ns.output / rel_dir
        output_dir.mkdir(parents=True, exist_ok=True)
        order_output = output_dir / name.with_suffix(".ord")
        with open(formula_input, "r") as formula_file, open(
            map_input, "r"
        ) as map_file, open(order_output, "w") as output_file:
            formula = formula_file.readline()
            degrees = degree_matrix(formula)
            var_num = len(degrees[0]) - 1

            # Deal with the renaming map to generate an order for Maple
            map_dict = json.load(map_file)
            alias_map_back = {val: key for key, val in map_dict.items()}

            # Only uses brown's heuristics
            ordering_brown = [
                [0, 0, 0, i] for i in range(1, var_num + 1)
            ]  # degree_of_variable, highest_total_degree, terms, var_id
            for item in degrees:
                for i in range(len(item) - 1):
                    if item[i]:
                        ordering_brown[i][0] = max(ordering_brown[i][0], item[i])
                        ordering_brown[i][1] = max(ordering_brown[i][1], item[-1])
                        ordering_brown[i][2] += 1
            ordering_td_brown_height, ordering_td_brown_pq = order_from_td_results(
                td_input, ordering_brown
            )
            ordering_brown.sort(key=lambda x: (-x[0], -x[1], -x[2]))
            output_file.write("Brown's heuristics (descending mapped, for Mathematica): {")
            for i in range(len(ordering_brown)):
                if i:
                    output_file.write(",")
                output_file.write(f"x{ordering_brown[i][3]}")
            output_file.write("}\n")
            output_file.write("Brown (original var name, ascending, for FME or Maple): [")
            for i in range(len(ordering_brown) - 1, -1, -1):
                if i < len(ordering_brown) - 1:
                    output_file.write(",")
                new_symbol = alias_map_back[f"x{ordering_brown[i][3]}"]
                output_file.write(new_symbol)
            output_file.write("]\n")

            # Li's PEO
            PEO = mcs_m_hb(gr_input, degrees)
            output_file.write("PEO (descending mapped, for Mathematica): {")
            for i in range(len(PEO)):
                if i:
                    output_file.write(",")
                output_file.write(f"x{PEO[i]}")
            output_file.write("}\n")
            output_file.write("PEO (original var name, ascending, for FME or Maple): [")
            for i in range(len(PEO) - 1, -1, -1):
                if i < len(PEO) - 1:
                    output_file.write(",")
                new_symbol = alias_map_back[f"x{PEO[i]}"]
                output_file.write(new_symbol)
            output_file.write("]\n")

            # Brown's heuristics plus tree decomposition (our heuristic)
            output_file.write(
                "Brown's heuristics plus tree decomposition (our heuristic) (descending mapped, for Mathematica): {"
            )
            for i in range(len(ordering_td_brown_pq) - 1, -1, -1):
                if i < len(ordering_td_brown_pq) - 1:
                    output_file.write(",")
                output_file.write(f"x{ordering_td_brown_pq[i]}")
            output_file.write("}\n")
            output_file.write("Our heuristic (original var name, ascending, for FME or Maple): [")
            for i in range(len(ordering_td_brown_pq)):
                if i:
                    output_file.write(",")
                new_symbol = alias_map_back[f"x{ordering_td_brown_pq[i]}"]
                output_file.write(new_symbol)
            output_file.write("]\n")
