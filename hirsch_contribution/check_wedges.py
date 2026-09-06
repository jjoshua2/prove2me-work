"""Exact rational sanity checks for the generalized wedge reduction.

These finite tests are NOT a proof of the reduction or the Hirsch conjecture.
Requires Python 3.10+, sympy, and networkx. No network or credentials are used.
Run: python check_wedges.py
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import networkx as nx
import sympy as sp


@dataclass(frozen=True)
class HPoly:
    dimension: int
    rows: tuple[tuple[int, ...], ...]
    offsets: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.dimension < 0 or len(self.rows) != len(self.offsets):
            raise ValueError("Invalid dimensions or row count")
        if any(len(row) != self.dimension for row in self.rows):
            raise ValueError("Every row must have the ambient dimension")

    @property
    def n(self) -> int:
        return len(self.rows)


def wedge(p: HPoly, row: int = 0) -> HPoly:
    """Replace row j by a_j*x+t <= b_j and append -t <= 0."""
    if not 0 <= row < p.n:
        raise ValueError("Wedge requires a valid inequality index")
    return HPoly(
        p.dimension + 1,
        tuple(a + (int(i == row),) for i, a in enumerate(p.rows))
        + ((0,) * p.dimension + (-1,),),
        p.offsets + (0,),
    )


def balance(p: HPoly) -> HPoly:
    q = p
    while q.n > 2 * q.dimension:
        q = wedge(q)
    padding = 2 * q.dimension - q.n
    return HPoly(q.dimension, q.rows + ((0,) * q.dimension,) * padding,
                 q.offsets + (1,) * padding)


@lru_cache(maxsize=None)
def graph(p: HPoly) -> nx.Graph:
    """Enumerate vertices and edges exactly for these bounded test systems.

    Vertices solve a full-rank active subsystem. Two distinct vertices are
    adjacent iff their common active rows have rank d-1. This criterion also
    applies to bounded lower-dimensional H-polytopes in an ambient R^d.
    """
    d = p.dimension
    vertices = set()
    if d == 0:
        if all(b >= 0 for b in p.offsets):
            vertices.add(())
    else:
        for subset in combinations(range(p.n), d):
            a = sp.Matrix([p.rows[i] for i in subset])
            if a.det() == 0:
                continue
            x = tuple(a.inv() * sp.Matrix([p.offsets[i] for i in subset]))
            if all(sum(ai * xi for ai, xi in zip(row, x)) <= b
                   for row, b in zip(p.rows, p.offsets)):
                vertices.add(x)
    if not vertices:
        raise AssertionError("Test system has no enumerated vertices")
    g = nx.Graph()
    g.add_nodes_from(sorted(vertices))
    active = {
        x: {i for i, (row, b) in enumerate(zip(p.rows, p.offsets))
            if sum(ai * xi for ai, xi in zip(row, x)) == b}
        for x in vertices
    }
    for u, v in combinations(sorted(vertices), 2):
        common = active[u] & active[v]
        rank = sp.Matrix([p.rows[i] for i in common]).rank() if common else 0
        if rank == d - 1:
            g.add_edge(u, v)
    if not nx.is_connected(g):
        raise AssertionError("Enumerated test graph is disconnected")
    return g


def check_projection(p: HPoly, q: HPoly) -> dict[str, int]:
    gp, gq = graph(p), graph(q)
    project = lambda v: v[:p.dimension]
    if not all(project(v) in gp for v in gq):
        raise AssertionError("A lifted vertex projects to a nonvertex")
    if not all(u + (0,) * (q.dimension - p.dimension) in gq for u in gp):
        raise AssertionError("An original vertex has no bottom lift")
    for u, v in gq.edges:
        a, b = project(u), project(v)
        if a != b and not gp.has_edge(a, b):
            raise AssertionError("An edge projects to a nonedge")
    dp, dq = nx.diameter(gp), nx.diameter(gq)
    if dp > dq:
        raise AssertionError("Diameter decreased")
    return {"original_vertices": len(gp), "lifted_vertices": len(gq),
            "original_diameter": dp, "lifted_diameter": dq}


def main() -> None:
    square = HPoly(2, ((-1, 0), (1, 0), (0, -1), (0, 1)), (0, 1, 0, 1))
    cases = {
        "zero_dim_no_rows": HPoly(0, (), ()),
        "zero_dim_tight_and_slack": HPoly(0, ((), ()), (0, 1)),
        "interval": HPoly(1, ((-1,), (1,)), (0, 1)),
        "triangle": HPoly(2, ((-1, 0), (0, -1), (1, 1)), (0, 0, 1)),
        "square": square,
        "hexagon": HPoly(2, ((1, 0), (-1, 0), (0, 1), (0, -1),
                              (1, 1), (-1, -1)), (2, 0, 2, 0, 3, -1)),
        "singleton_ambient_two": HPoly(2, square.rows, (0, 0, 0, 0)),
        "segment_ambient_two": HPoly(2, square.rows, (0, 1, 0, 0)),
        "square_redundant_positive": HPoly(2, square.rows + ((0, 0),),
                                            square.offsets + (1,)),
        "square_redundant_tight": HPoly(2, square.rows + ((0, 0),),
                                         square.offsets + (0,)),
        "square_row_tight_at_vertex": HPoly(2, square.rows + ((-1, -1),),
                                              square.offsets + (0,)),
        "tetrahedron": HPoly(3, ((-1, 0, 0), (0, -1, 0), (0, 0, -1),
                                   (1, 1, 1)), (0, 0, 0, 1)),
        "octahedron": HPoly(3, tuple(product((-1, 1), repeat=3)), (1,) * 8),
    }
    report = {"status": "passed", "arithmetic": "exact rational",
              "limitation": "Finite sanity checks, not a general or formal proof.",
              "single_wedges": [], "balanced_systems": []}
    for name, p in cases.items():
        for i in range(p.n):
            item = {"case": name, "row": i, **check_projection(p, wedge(p, i))}
            report["single_wedges"].append(item)
        q = balance(p)
        assert q.n == 2 * q.dimension
        assert q.dimension == p.dimension + max(0, p.n - 2 * p.dimension)
        assert q.dimension <= p.n + p.dimension
        item = {"case": name, "original_dimension": p.dimension,
                "original_rows": p.n, "balanced_dimension": q.dimension,
                "balanced_rows": q.n, **check_projection(p, q)}
        report["balanced_systems"].append(item)
    report["single_wedge_count"] = len(report["single_wedges"])
    report["balanced_system_count"] = len(report["balanced_systems"])
    out = Path(__file__).with_name("sanity_checks.json")
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("single_wedges", "balanced_systems")}, indent=2))


if __name__ == "__main__":
    main()
