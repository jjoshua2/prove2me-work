# Fixed-excess Larman publication

Theorem: [Hirsch.hpoly_diameter_le_fixed_excess_larman](https://prove2.me/theorems/49576ed3-5185-4951-9215-43283ef6169e).
Publication job: `3bf16396-6d1d-4420-b7a2-34c87b8d39b1` (PUBLISHED).
Proof submission: `cd24addc-446f-4d16-b814-85315057c98f`.
**ACCEPTED**; authenticated theorem readback: **Proved**.
`verification.json` and `target-after.json` preserve the verdict and readback.
`decompositions.json` records the real Larman and facet-reduction inputs.

The statement is: a bounded n-row H-polyhedron in ambient dimension d, with
`n<=d+E`, has padded ordinary-edge diameter at most `2*E*2^(E-3)`. Natural
subtraction saturates below zero. Empty and degenerate sets and redundant/zero
rows are included. The classical descent and the conservative Larman constant
are described in `explanation.md` and attributed precisely in `problem.json`.
The dependence on E is exponential, so this does not prove Polynomial Hirsch.

The independent local driver keeps the exact Larman and facet-reduction
propositions as premises. Its axiom audit is `driver-audit.json`. The public
`solution.lean` composes their already-Proved platform declarations. Its local
typecheck uses interface placeholders, not claimed as local proof evidence.
The two authenticated dependency snapshots are included. No Open ancestor is
imported. The larger clipping assembly is a separate locally verified result.

Frozen mathematical input: `117709458ec4b071dc846cd8443feea19ca2669b`.
All source Git blobs and packet SHA-256 hashes are in `manifest.json`.
To reproduce the packet without modifying any receipt:

```
python3 scripts/prepare_fixed_excess_larman.py --source 117709458ec4b071dc846cd8443feea19ca2669b --out /tmp/reproduced-fixed-excess
lake env lean /tmp/reproduced-fixed-excess/driver.lean
lake build Theorems.Thm_Hirsch_larman_bound Theorems.Thm_Hirsch_facet_reduction
lake env lean /tmp/reproduced-fixed-excess/statement.lean
lake env lean /tmp/reproduced-fixed-excess/solution.lean
```

The builder reproduces all six original prepared files byte-for-byte. The
publisher checks their hashes and audit receipts before each bounded API stage.
It refuses to duplicate an existing publication/verification request.
Credentials are read only from the environment or gitignored local file and
are never stored in this packet. Do not rerun publication for this completed
statement: use its theorem and submission IDs.
