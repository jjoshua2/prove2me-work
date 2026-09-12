# Verified #201/#202 integration

Frozen mathematical source: `117709458ec4b071dc846cd8443feea19ca2669b`.
PR #201 is the integration vehicle; #202's two Lean sources are preserved
byte-for-byte from `4797a18206c63e761628e556d5ca4bd1eef3c169`.

`local-build.log` is the complete successful output of:

```
lake build Solutions.PolynomialSelectedRunBudgets Solutions.PolynomialFixedExcessLarman
```

`local-verification.json` records SHA-256 hashes for all five source modules,
the 30 required declaration names, and the audit of all 406 transitive reports.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. No theorem stub is
imported by these local adapters: the public diameter inputs remain explicit.
To reproduce the audit:

```python
import json, sys
from pathlib import Path
sys.path.insert(0, "scripts")
from check_lean_axiom_log import audit
p = Path("research/verification/2026-09-12-exact-support")
r = json.loads((p / "local-verification.json").read_text())
audit((p / "local-build.log").read_text(), r["required_declarations"])
```

`finite-check.json` and `support-deficit-check.json` are fresh successful runs
of the two committed finite checkers. They cover only finite counting, integer
budgets, and explicit examples; they do not substitute for geometry proofs.
The original candidate receipts remain in the research directory as history.
The two #201 compiler fixes were a missing `classical` declaration and the
correct spelling `Finset.card_insert_of_notMem`.

The authenticated input snapshots verify Larman, facet reduction and small
excess are Proved at Mathlib c5ea003. `open-leaves.json` records the root's sole
Open leaf, and `discussion-before.json` preserves all 48 pre-continuation posts.
The empty fixed-excess search snapshots precede the new publication.

The existing final hosted run is
[34708143326](https://github.com/jjoshua2/prove2me-work/actions/runs/34708143326)
on the frozen source commit passed. `hosted-run.json`, `hosted-build.log`, and
`hosted-audit.json` retain its successful build and standard-axiom audit.
The separately submitted public theorem packet, driver audit, exact statement,
proof and authenticated verdict live in
[fixed_excess_larman](../../publication_packets/fixed_excess_larman/).
Only that packet's server verdict establishes its platform acceptance. The
larger selected-run and clipping assemblies retain local verification status.
