import heapq
import queue
import re
from copy import deepcopy
from typing import Dict, List, Tuple, Set, TypeVar

Node = TypeVar("Node")


def degree_matrix(renamed_str):
    """
    Given a string of one or more formulas (with variables x1, x2, ...),
    joined by '&&', compute:
      1) The degree of each variable in each atomic formula (as before).
      2) The degree of the highest-degree monomial in each formula,
         appending that as the last entry of each row.

    Args:
        renamed_str (str): A single string containing one or more formulas separated by '&&'.

    Returns:
        List[List[int]]: A matrix (list of lists) where:
            - Each inner list corresponds to one atomic formula.
            - The first N entries are the max exponents of x1…xN in that formula.
            - The (N+1)-th entry is the overall highest total degree of any single term.
    """
    # 1. Find the largest variable index (to know how many columns we need)
    var_indices = [int(i) for i in re.findall(r"x(\d+)\b", renamed_str)]
    max_var = max(var_indices) if var_indices else 0

    # 2. Split on top‐level '&&' to get each atomic formula
    formulas = re.split(r"\s*&&\s*", renamed_str)

    matrix = []
    for formula in formulas:
        # 3. Strip negations and parentheses
        f = formula.replace("!", "")
        f = f.replace("(", "").replace(")", "")

        # 4. Split on relational operators to isolate polynomial pieces
        parts = re.split(r"==|<=|>=|<|>", f)
        expr = "+".join(parts)

        # 5. Normalize '-' into '+-' where it’s binary subtraction
        expr_norm = ""
        i = 0
        while i < len(expr):
            if expr[i] == "-":
                # If '-' is at start or follows another operator, keep it as a unary minus.
                if i == 0 or expr[i - 1] in "+-*/":
                    expr_norm += "-"
                else:
                    expr_norm += "+-"
                i += 1
            else:
                expr_norm += expr[i]
                i += 1

        # 6. Split on '+' to get individual terms (monomials)
        terms = expr_norm.split("+")

        # 7. For each variable x1…xN, compute its degree in this formula
        degrees = []
        for var_idx in range(1, max_var + 1):
            var_name = f"x{var_idx}"
            max_deg_in_formula = 0

            for term in terms:
                term = term.strip()
                if not term:
                    continue

                # a) Find all xi^k in this term (e.g., 'x3^2'), sum their exponents
                exponents = [
                    int(exp) for exp in re.findall(rf"\b{var_name}\^(\d+)\b", term)
                ]
                sum_exp = sum(exponents)

                # b) Remove all 'xi^k' substrings so we don’t double-count plain 'xi'
                term_without_powers = re.sub(rf"\b{var_name}\^\d+\b", "", term)

                # c) Count any remaining standalone 'xi' (not followed by '^')
                count_plain = len(re.findall(rf"\b{var_name}\b", term_without_powers))

                # d) Total degree for xi in this term = sum of explicit exponents + plain counts
                deg_in_term = sum_exp + count_plain

                if deg_in_term > max_deg_in_formula:
                    max_deg_in_formula = deg_in_term

            degrees.append(max_deg_in_formula)

        # 8. Compute the highest total degree among all monomials in this formula
        max_term_degree = 0
        for term in terms:
            term = term.strip()
            if not term:
                continue

            # For each term, sum the degrees of all variables in that term.
            total_degree = 0
            for var_idx in range(1, max_var + 1):
                var_name = f"x{var_idx}"
                # Count exponents of the form xi^k
                exponents = [
                    int(exp) for exp in re.findall(rf"\b{var_name}\^(\d+)\b", term)
                ]
                sum_exp = sum(exponents)

                # Remove xi^k so we don’t double-count plain xi
                term_wo_powers = re.sub(rf"\b{var_name}\^\d+\b", "", term)

                # Count standalone xi (not followed by ^)
                count_plain = len(re.findall(rf"\b{var_name}\b", term_wo_powers))

                total_degree += sum_exp + count_plain

            if total_degree > max_term_degree:
                max_term_degree = total_degree

        # 9. Append the highest-degree-term value as the last entry in this row
        degrees.append(max_term_degree)

        matrix.append(degrees)

    return matrix


def farthest_distance(adj, start):
    """
    Compute the maximum shortest-path distance from `start` to any reachable node in an unweighted graph, using queue.Queue for BFS.

    Parameters:
    - adj: dict[node, list[node]]
        Adjacency list mapping each node to its neighbors.
    - start: node
        The starting node.

    Returns:
    - int
        The greatest distance (in number of edges) from `start` to any reachable node.
    """
    visited = {start}
    dist = {start: 0}
    q = queue.Queue()
    q.put(start)

    while not q.empty():
        u = q.get()
        for v in adj.get(u, []):
            if v not in visited:
                visited.add(v)
                dist[v] = dist[u] + 1
                q.put(v)

    return max(dist.values(), default=0)


def mcs_m_hb(graphfile, degree_matrix):
    with open(graphfile, "r") as file:
        # 0-1. Reconstruct the graph using provided file
        first_line = file.readline().rstrip("\n").split(" ")
        num_v, num_e = int(first_line[2]), int(first_line[3])
        G = {key: [] for key in range(1, num_v + 1)}
        for _ in range(num_e):
            line = file.readline().rstrip("\n").split(" ")
            u, v = int(line[0]), int(line[1])
            G[u].append(v)
            G[v].append(u)

        # 0-2. Compute DFV for each node
        PD = {key: None for key in range(1, num_v + 1)}
        for key, _ in PD.items():
            PD[key] = farthest_distance(G, key)

        # 0-3. Compute S1, S2, S3 for each variable using Brown's rules
        S1 = {key: 0 for key in range(1, num_v + 1)}
        S2 = {key: 0 for key in range(1, num_v + 1)}
        S3 = {key: 0 for key in range(1, num_v + 1)}
        for item in degree_matrix:
            for i in range(len(item) - 1):
                if item[i]:
                    S1[i + 1] = max(S1[i + 1], item[i])
                    S2[i + 1] = max(S2[i + 1], item[-1])
                    S3[i + 1] += 1

        """
        MCS-M algorithm, returning:
        - alpha: List[Node], in the order vertices are eliminated
        - H: the triangulated graph as an adjacency list

        Args:
        G: adjacency list of an undirected graph

        Returns:
        alpha: first element is the first vertex eliminated
        H: adjacency list of G augmented with fill edges
        """
        n = len(G)
        weights: Dict[Node, int] = {v: 0 for v in G}
        depth: Dict[Node, int] = {v: 0 for v in G}
        unnumbered: Set[Node] = set(G)
        alpha: List[Node] = []
        fill_edges: Set[Tuple[Node, Node]] = set()

        # Number from n down to 1; we append v in each iteration,
        # so the first append is the first eliminated.
        for i in range(n, 0, -1):
            if i != n:
                for v in unnumbered:
                    PD[v] = max([depth[x] for x in G[v]]) + 1
            # 1) pick unnumbered vertex of maximum weight and update depth
            v = max(unnumbered, key=lambda x: (weights[x], -PD[x], S1[x], S2[x], S3[x]))
            depth[v] = PD[v]

            # 2) build S
            S: Set[Node] = set()
            for u in unnumbered:
                if u == v:
                    continue
                if v in G[u]:
                    S.add(u)
                    continue

                # BFS using queue.Queue
                q = queue.Queue()
                visited = {u}
                q.put(u)
                found = False
                while not q.empty() and not found:
                    x = q.get()
                    for nbr in G[x]:
                        if nbr not in unnumbered or nbr in visited:
                            continue
                        if nbr is v:
                            found = True
                            break
                        if weights[nbr] < weights[u]:
                            visited.add(nbr)
                            q.put(nbr)
                if found:
                    S.add(u)

            # 3) increment weights of S
            for u in S:
                weights[u] += 1

            # 4) record fill edges for non-adjacent S
            for u in S:
                if v not in G[u]:
                    edge = (u, v) if u <= v else (v, u)
                    fill_edges.add(edge)

            # 5) record elimination and remove v
            alpha.append(v)
            unnumbered.remove(v)

        # build H = G ∪ F
        H = deepcopy(G)
        for u, v in fill_edges:
            H[u].append(v)
            H[v].append(u)

    return alpha


class PriorityElement:
    def __init__(self, data):
        self.data = data

    def __lt__(self, other):
        return tuple(self.data[:3]) < tuple(other.data[:3])

    def __repr__(self):
        return repr(self.data)


class PriorityQueue:
    def __init__(self):
        self._heap = []

    def push(self, element):
        heapq.heappush(self._heap, PriorityElement(element))

    def pop(self):
        if self._heap:
            return heapq.heappop(self._heap).data
        raise IndexError("pop from empty priority queue")

    def is_empty(self):
        return not self._heap


def order_from_td_results(filename, brown):
    """
    Compute a suggested CAD projection order using tree decomposition results
    and Brown's heuristic statistics.

    This function:
      1. Assigns heights to each bag in the tree decomposition:
         - Leaves are at height 0.
         - Parent heights are set to one more than the maximum height of their children.
      2. Records, for each variable, the height of the first bag that contains it.
      3. Uses a priority queue—ordered by Brown's heuristic scores—to produce
         a final projection order of the variables.

    Args:
        filename (str): Path to a file containing the tree decomposition.
        brown (List[List[int]]): A var_num*3 matrix of Brown's heuristic scores
            for each variable.

    Returns:
        res_height (List[List[int]]): For each variable i, a list
            `[height, 0, 0, 0, i]`, where `height` is the computed bag height.
        res_pq (List[int]): The variables in the suggested projection order.
    """
    # 1. Read the file header: bag_num = number of bags, var_num = number of variables
    with open(filename, "r") as file:
        info = file.readline().rstrip("\n").split(" ")
        bag_num, var_num = int(info[2]), int(info[4])

        # 2. Parse each bag’s variable list into a dict: {bag_id: [var1, var2, ...]}
        bag = {}
        for _ in range(bag_num):
            line = file.readline().rstrip("\n").split(" ")
            bag_id = int(line[1])
            bag_vars = [int(x) for x in line[2:]]
            bag[bag_id] = bag_vars

        # Initialize heights for each bag (all start at 0)
        height = {key: 0 for key in bag}

        # Prepare the result structure: one entry per variable [height, 0, 0, 0, var_index]
        res_height = [[0, 0, 0, 0, i] for i in range(1, var_num + 1)]

        # 3. Build an adjacency list for the tree decomposition (bags as nodes)
        adjacency_list = [[] for _ in range(bag_num + 1)]
        for _ in range(bag_num - 1):
            line = file.readline().rstrip("\n").split(" ")
            u, v = int(line[0]), int(line[1])
            adjacency_list[u].append(v)
            adjacency_list[v].append(u)

        # Keep a backup of the original adjacency structure for the second phase
        adjacency_list_bak = deepcopy(adjacency_list)

        # 4. Compute bag heights by peeling off leaves iteratively (leaf-stripping)
        q = queue.Queue()
        for i, neighbors in enumerate(adjacency_list):
            if len(neighbors) == 1:
                q.put(i)
        while not q.empty():
            p = q.get()
            # If the leaf still has a neighbor, process it
            if len(adjacency_list[p]):
                neighbor = adjacency_list[p][0]
                # For each variable in this leaf, if it’s not in the parent, record its height
                temp = []
                for v in bag[p]:
                    if v not in bag[neighbor]:
                        res_height[v - 1][0] = height[p]
                        temp.append(v)
                # Update parent height
                height[neighbor] = max(height[neighbor], height[p] + 1)
                # Keep only the  variables to be eliminated at the leaf
                bag[p] = temp
                # Remove the leaf from its parent’s neighbor list
                adjacency_list[neighbor].remove(p)

                # If parent becomes a leaf, enqueue it
                if len(adjacency_list[neighbor]) == 1:
                    q.put(neighbor)
            else:
                # No neighbors (root): record height for all remaining vars
                for v in bag[p]:
                    res_height[v - 1][0] = height[p]

        # Restore adjacency list for the priority queue phase
        adjacency_list = deepcopy(adjacency_list_bak)

        # Build a reverse map: var → the bag that currently holds it
        bag_rev = {}
        for key, value in bag.items():
            for item in value:
                bag_rev[item] = key

        # 5. Use a priority queue (min-heap) with Brown’s heuristic to order variables
        pq = PriorityQueue()
        res_pq = []
        # Start by pushing all variables in the original leaves
        for bag_id, neighbors in enumerate(adjacency_list):
            if len(neighbors) == 1:
                for var in bag[bag_id]:
                    pq.push(brown[var - 1])
        # Repeatedly pop the 'best' variable and update neighbor
        while not pq.is_empty():
            p = pq.pop()
            var = p[3]  # the 4th element is the variable index
            res_pq.append(var)

            # Remove var from its bag; if bag empties, consider its neighbor
            bag_id = bag_rev[var]
            bag[bag_id].remove(var)

            # If the bag becomes empty and still has a neighbor, push that new leaf's vars
            if bag[bag_id] == [] and len(adjacency_list[bag_id]):
                neighbor = adjacency_list[bag_id][0]
                adjacency_list[neighbor].remove(bag_id)
                if len(adjacency_list[neighbor]) == 1:
                    for var in bag[neighbor]:
                        pq.push(brown[var - 1])

        return res_height, res_pq
