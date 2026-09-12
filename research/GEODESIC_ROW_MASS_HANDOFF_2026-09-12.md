# Verification-agent handoff: joint all-available-row carrier mass

**Integration update:** all four modules now compile locally at the committed
pin. Two natural-number normalization repairs preserve every theorem hypothesis.
All twenty required declarations pass the transitive standard-axiom audit.
See [current verification](verification/2026-09-12-geodesic-mass/local-audit.json).
The candidate-status language below describes the original submission; hosted
verification and public acceptance are recorded separately when completed.

This is independent of #205 and the rank-localized-cuts ZIP. Do not redo the
product/feedback work to use it. All imported repository modules were present
on main after #204. No dependency pin, workflow, or existing source is changed.

## New statements worth verifying

1. `geodesicContactSupport_card_le_three`: any graph vertex, including an
   unselected one, has at most three closed-neighborhood contacts on a shortest
   path. The two-edge shortcut proof uses `path.shortest`, not just chordlessness.
2. `DeferredClipCertificate.carrier_mass_subtraction_free`:
   `sum(delta)+r*s <= r*(n-d)+3*s`, on the same chosen portal pairs.
3. `basis_star_exists_linear_carrier_mass`: retain a supplied d-row tight basis,
   use a SEPARATE strictly interior radial center, and obtain D=1, s=n-d and
   `sum(delta)<=3*(n-d)` even when the target is nonsimple.
4. Intrinsic row/dimension mass and actual dimension-capped edge routing:
   `D+6e*2^(H-3)` at full availability, hence `D+24e` at H=5.

The run refinement `sum(delta)+2c<=r*(e-s)+3s` is fully argued and regression-
tested in the note. It is not yet a new Lean declaration. Reuse the existing
`sum_selected_degrees_add_twice_runStarts` if formalizing it. The new tight-basis
wrapper takes a basis explicitly; basis extraction from vertex spanning is a
separate finite-linear-algebra composition, not an assumed simple target.

## Run locally before any hosted gate

```sh
python3 scripts/test_geodesic_row_mass.py
python3 scripts/geodesic_row_mass.py fixtures/stacked_48_row_incidence.json
lake build Solutions.PolynomialGeodesicRowIncidence \
  Solutions.PolynomialAllCutCarrierMass \
  Solutions.PolynomialGeodesicMassRouting \
  Solutions.PolynomialBasisStarMass
```

No new Lean compilation was possible here: neither lean nor lake is installed.
The candidate proof bodies contain no holes or target theorem placeholders.
Check all 20 printed declarations with the repository's standard logical axiom
allowlist. Classical Larman remains an explicit input. Fix any elaboration or
namespace issues locally; do not use Actions as an interactive compiler.

Potential API-sensitive points are Finset min-image/cardinality simp rules,
coercions of the mixed-label graph and subtype complement, and the existing
Walk.take/drop length rewrites. Preserve the mathematical hypotheses if making
repairs: all available row labels must be injective, true metric shortestness
is essential, and the basis-star center must be strictly feasible independently
of the target.

## Evidence actually produced

The compact committed summary and full generated receipt come from a real local
run and hash all four Lean modules
and both Python files. It distinguishes numerical incidence audits from the
rational geometric fixtures. The 48-row fixture demonstrates a bound improvement
493 -> 133 while the true computed carrier mass is 59. The dimension-six
nonsimple fixture restores 26 additional target-tight rows without losing
strict radial-center feasibility. The graph-only CLI deliberately does not
claim to verify continuous geometry supplied by arbitrary users.

Publication requires its own exact self-contained interface, dependency audit,
and authenticated acceptance. No platform status is changed by this packet.
Do not claim Polynomial Hirsch follows merely from the factor-three mass sum:
the note includes an exponential independent-call majorant that satisfies it.

The repository commits the generator and compact summary. Running the test
creates all three numerical fixtures and the full detailed receipt; those
generated files are also already included in the conversation ZIP.

## Final integration verdict

Hosted run [34723720395](https://github.com/jjoshua2/prove2me-work/actions/runs/34723720395)
passed at `8e4a666f9bc54c64ff38f93223a965c6181751b6`; all twenty required
transitive reports contain only standard logical axioms. The exact graph-budget
packet is [Proved](https://prove2.me/theorems/b8f45079-9784-43a0-b659-0914a2038332),
submission `83ed9045-971b-4ad8-ae0d-3659c625e850` ACCEPTED. Authenticated
accepted-source readback matches its frozen hash. This platform theorem states
the graph incidence and integer-budget consequence; the separately checked
geometric adapters are not mislabeled as this theorem's platform verdict.
The regenerated full numerical receipt and fixtures can be reproduced by the
committed test script; the compact source-hashed summary is durable.
