#!/usr/bin/env python3
"""Finite regression tests for exact selected-cut accounting, not a Lean proof.

Enumerates every selected subset of a path with up to --max-vertices vertices.
This verifies only graph counting and integer budget consequences. It neither
constructs polytopes nor certifies the Lean source or Polynomial Hirsch.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def check(max_vertices: int, max_gap: int) -> dict[str, object]:
    if not 0 <= max_vertices <= 20:
        raise ValueError("max_vertices must be between 0 and 20")
    if not 0 <= max_gap <= 100:
        raise ValueError("max_gap must be between 0 and 100")
    masks = vertex_cases = budgets = easy_cases = 0
    for size in range(max_vertices + 1):
        for mask in range(1 << size):
            selected = {i for i in range(size) if (mask >> i) & 1}
            r = len(selected)
            degrees = {i: int(i - 1 in selected) + int(i + 1 in selected)
                       for i in selected}
            components = sum(i - 1 not in selected for i in selected)
            singletons = sum(degrees[i] == 0 for i in selected)
            assert sum(degrees.values()) == 2 * (r - components)
            assert sum(deg == 2 for deg in degrees.values()) == r - 2 * components + singletons
            for i in selected:
                nonneighbors = {j for j in selected if j != i and abs(j - i) != 1}
                assert len(nonneighbors) + 1 + degrees[i] == r
                assert len(nonneighbors) >= max(r - 3, 0)
                vertex_cases += 1
            for gap in range(max_gap + 1):
                e = r + gap
                # Simultaneously attain the numerical caps, without asserting
                # these caps arise as actual carriers of any one polytope.
                caps = {i: gap + 1 + degrees[i] for i in selected}
                assert sum(caps.values()) == r * (e - r + 3) - 2 * components
                for i, cap in caps.items():
                    assert cap + r == e + 1 + degrees[i]
                    assert cap + (r - 1 - degrees[i]) == e
                    if gap + degrees[i] <= 2:
                        assert cap <= 3
                    if cap >= 4:
                        assert gap + degrees[i] >= 3
                    if gap == 1 and cap >= 4:
                        assert degrees[i] == 2
                    if gap == 2 and cap >= 4:
                        assert degrees[i] >= 1
                if all(gap + degrees[i] <= 2 for i in selected):
                    assert sum(caps.values()) <= 3 * r
                    easy_cases += 1
                if gap == 0 and r:
                    assert sum(caps.values()) <= 3 * r - 2
                budgets += 1
            masks += 1

    # The sharper degree budget still permits this independent-call majorant.
    # This is NOT an exponential lower bound on polytope diameter.
    majorant = [0, 1, 2, 3]
    for e in range(4, 41):
        majorant.append(1 + 2 * majorant[e - 2] + 2 * majorant[e - 1])
        assert majorant[e] >= 2 * majorant[e - 1]
    return {
        "status": "PASS",
        "max_path_vertices": max_vertices,
        "max_support_deficit": max_gap,
        "selected_subsets_checked": masks,
        "selected_vertex_counting_cases": vertex_cases,
        "support_budget_cases": budgets,
        "easy_support_cases_including_empty": easy_cases,
        "four_call_majorant": {str(e): majorant[e] for e in (4, 5, 10, 20, 40)},
        "scope": "Finite path counting and integer regression checks only; not Lean verification or geometric realizability.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-vertices", type=int, default=14)
    parser.add_argument("--max-gap", type=int, default=6)
    args = parser.parse_args()
    result = check(args.max_vertices, args.max_gap)
    source = Path(__file__).resolve().parents[1] / "Solutions/PolynomialExactSelectedSupport.lean"
    if source.is_file():
        result["candidate_lean_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
