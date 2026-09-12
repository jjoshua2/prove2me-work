# Target-preserving blocker deletion: verified canonical interface

Date: 2026-09-12. PR #166.

## Executed verification

- Frozen source file: `Solutions/PolynomialTargetPreservingBlockerDeletion.lean`.
- Source commit: `aaa2324a9219a5e3501e30d60a43fab1e415dd97`.
- Source SHA-256: `5cea6e0d31c4bfa0c4ee8c7e836c42689c7a7488f613ca1e4c39f63ba9d851fd`.
- Gate checkout: `bd689b048844a957579703d6fa2b6f3f62cdfae8`.
- Actions run: `34673934390`; job: `103500280969`.
- Conclusion: SUCCESS on the first final-gate run, with no source repair or rerun.
- Lean: `4.30.0`; Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Artifact: `10291871105`, `target-preserving-blocker-deletion-verification`.
- ZIP SHA-256: `f43aeb63ae6b254f2cdef05cca744b853908fda50d6a5764d9a0ee679b71092e`.

The ZIP was downloaded and its hash checked independently. The exact report matched the locally reproduced report. All seven complete transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or extra assumptions.

## Verified declarations (namespace HirschDeletion)

1. `rowMap_rowsWithout_not_injective_of_unique_nonneutral`
2. `rowCircuit_pointed_deletion_iff_other_nonneutral`
3. `vertex_survives_rowsWithout_of_slack`
4. `rowMap_rowsWithout_injective_of_slack_vertex`
5. `rowsWithout_card_lt`
6. `rowCircuitStep_same_phase_has_target_preserving_pointed_deletion`
7. `slack_row_has_lower_excess_target_preserving_cubic_outer`

## Relationship to concurrent PR #165

PR #165 is the GENERAL batch-deletion interface: preserve all target-tight rows, delete any target-slack batch, and characterize the target-tight outer's singleton vertex set.

This module is the CANONICAL one-row/support and quantitative interface. In particular it supplies the exact other-nonneutral-row iff criterion, the concrete `rowsWithout`/`rhsWithout` representation, a retained trapped-reference certificate, and the combined strict row-excess/cubic-walk conclusion. Its small one-row vertex/injectivity lemmas support those canonical conclusions. Do not redo or copy #165's batch construction or target-cone proof here. The independent strict-cut-based vertex-survival proof gives a second verified derivation of the overlapping one-row fact.

## Quantitative conclusion

For any row j strictly slack at a vertex target v, any original feasible x has a `17*m^3` circuit walk to v in the canonical deletion outer. The same theorem proves `m<n` and `m-d<n-d`, because the retained map is injective and therefore `d<=m`.

The same-phase theorem supplies such a row without requiring x to be a vertex or the parent to be bounded. It retains the original trapped-reference inequality as well as pointedness and target extremality.

This is NOT a parent-edge routing or reinsertion theorem. The relaxed circuit walk may violate the removed row; the phase state need not be retained. The fixed-degree global polynomial cost remains unproved.

## Exact regression

Full report SHA-256: `f75e223f2c7fa436b78f1b438370025bf256c3f3bf4c71aa937a672e891587ad`.

24 presentations (8 base geometries at 3 row rescalings): 1,236 maximal circuit steps; 1,140 nonvertex-source steps; 1,308 blocker rank checks; 324 exceptional all-vertices-face cases; 147 arbitrary slack-row/vertex checks; 1,413 slack-target preservation checks; and 915 same-phase checks, 885 from nonvertex sources. Two local runs and the hosted run gave identical reports. These finite controls do not replace the dimension-general Lean proofs.

## Reproduction and publication

Run with the committed pins:

```bash
set -euo pipefail
python3 scripts/check_nonvertex_blocker_deletion.py
lake build Solutions.PolynomialTargetPreservingBlockerDeletion
lake env lean Solutions/PolynomialTargetPreservingBlockerDeletion.lean > /tmp/target-preserving-axioms.log
```

Audit each of the seven qualified names above with `scripts/check_lean_axiom_log.py`.

No Prove2Me API credentials were used, and no platform registration or proof submission occurred in this PR. Kernel verification is not a Prove2Me acceptance verdict. The one-shot verifier is removed before integration.
