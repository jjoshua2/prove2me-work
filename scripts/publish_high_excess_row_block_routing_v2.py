#!/usr/bin/env python3
"""Root-level `solution` wrapper for the audited row-block publisher.

Prove2Me proof files require the distinguished declaration to be named exactly
`solution` at the root. The first publication packet accidentally placed that
declaration inside namespace `Hirsch`; the checked proof body itself was
unchanged and the server therefore reported only `Unknown identifier solution`.
This wrapper reuses all reviewed/frozen publication logic and changes only the
scope of that distinguished declaration.
"""
from __future__ import annotations

import argparse
import hashlib

import publish_high_excess_row_block_routing as base


def expected_packets() -> tuple[bytes, bytes]:
    prefix = base.source_prefix()
    hsmall_type = """    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n - d))
"""
    apply_args = """      dims counts a b T e A hrows hbd hne hcount hsmallcount"""
    driver = prefix + "\n\nnamespace Hirsch\n\ntheorem checked_row_block_adapter\n" + hsmall_type + base.BINDERS + " := by\n  exact HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks hsmall\n" + apply_args + "\n\n#print axioms checked_row_block_adapter\n\nend Hirsch\n"

    dep_import = "import Theorems.Thm_" + base.DEPENDENCY_NAME.replace(".", "_") + "\n"
    solution = dep_import + prefix + "\n\ntheorem solution\n" + base.BINDERS + " := by\n  exact HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks\n    (fun {d n} a b hbd hrows =>\n      Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three d n a b hrows hbd)\n" + apply_args + "\n\n#print axioms solution\n"
    return driver.encode("utf-8"), solution.encode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["prepare", "publish"])
    args = parser.parse_args()
    base.expected_packets = expected_packets
    if args.mode == "prepare":
        base.prepare()
    else:
        base.publish()


if __name__ == "__main__":
    main()
