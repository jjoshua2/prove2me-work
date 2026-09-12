# Target-preserving blocker deletion

Date: 2026-09-12.
Status at creation: ordinary proof and exact rational regressions complete; the new Lean module awaits its one-shot frozen-source compilation/axiom gate. Not submitted to Prove2Me.

## What was already done

PR #163 already formalizes the source-nonvertex split: a destination blocker either permits pointed row deletion, or all original vertices are on that row. This work preserves that module unchanged and adds `Solutions/PolynomialTargetPreservingBlockerDeletion.lean`.

## Stronger result

Let P be any finite H-polyhedron, v an actual vertex of P, and j an inequality strictly slack at v. Removing j:

1. preserves v as a vertex;
2. leaves an injective row map (hence a pointed outer);
3. strictly lowers the number of rows, and also the row excess in the same ambient dimension;
4. permits the existing injective cubic circuit construction to route from every original feasible point to the SAME target v in the relaxed outer.

No boundedness, source-vertex, ambient-injectivity, or circuit-direction hypothesis is needed for this slack-target statement. Preservation of the vertex follows from the verified strict-cut vertex lemma. The surviving vertex's tight rows span, which supplies injectivity after deletion.

For m retained rows, injectivity gives d <= m, while m < n. Consequently the natural-number subtraction is genuine and m-d < n-d. The fresh route has exactly the padded length 17*m^3.

## Same-phase consequence

For any maximal circuit step x -> y whose source and destination share the fixed-reference progress set relative to the actual vertex target v, a newly tight blocking row is target-positive and already trapped. Thus it is strictly slack at v. The stronger result applies even when x and y are nonvertices.

`rowCircuitStep_same_phase_has_target_preserving_pointed_deletion` returns the concrete destination blocker, its positive displacement, strict slack at v, trapped-reference inequality, injectivity of the deleted presentation, and preservation of v as an actual vertex.

This eliminates #163's all-vertices-on-the-blocker alternative for same-phase steps: v is a counterexample to that alternative. It also removes the need to replace the target after the deletion.

## Exact support criterion

For a nonneutral row j of an injective row circuit, deletion stays pointed if and only if there is a second nonneutral row. The backward direction reuses #158. For the forward direction, if all retained rows were neutral, the nonzero circuit direction would remain in their kernel.

## Exact regression evidence

`scripts/check_nonvertex_blocker_deletion.py` uses only Python's standard-library rational arithmetic. Two local executions produced byte-identical reports.

Coverage: eight two-dimensional base presentations, each at three positive row rescalings, for 24 presentations total. These include bounded polytopes, pointed unbounded strips/wedges, the nonnegative quadrant, a lower-dimensional ray, a singleton, and redundant/zero rows. One rescaling is 10^36+1. These are finite regression checks, not a proof in arbitrary dimension.

Totals:
- 1,236 maximal circuit steps, 1,140 with nonvertex sources;
- 1,308 blocker-deletion rank checks;
- 324 genuine unique-nonneutral/all-vertices-face exceptions;
- 147 arbitrary slack-row/vertex checks, independent of circuit choice;
- 1,413 slack-target preservation checks on selected blockers;
- 915 same-phase blocker/target checks, including 885 with nonvertex sources.

Full report SHA-256: `f75e223f2c7fa436b78f1b438370025bf256c3f3bf4c71aa937a672e891587ad`.
Script SHA-256: `7b602249161b8677fcc5bdca8086a7be4d4b99e4cd1d4898e899c03adfb9fd25`.
Frozen Lean source SHA-256: `5cea6e0d31c4bfa0c4ee8c7e836c42689c7a7488f613ca1e4c39f63ba9d851fd`.
Lean source commit: `aaa2324a9219a5e3501e30d60a43fab1e415dd97`.

## Remaining boundary

The new route is a CIRCUIT walk in the relaxed outer. It may violate the removed inequality. It is not an ordinary-edge route in P, and it need not retain the original phase state. A same target is not a proof of cost-controlled reinsertion.

PR #164 already supplies bounded-parent reinsertion from explicit old-outer edge budget D and parent-face route budget B, with D+1+B total. Those budgets remain assumptions. Combining independent lower-excess and lower-dimensional recursions without amortization can have Pascal/binomial growth, not a uniform fixed-degree polynomial.

The useful next target is a target-aware reinsertion/amortization bound that pays repeated target-positive blocker faces globally rather than independently at every recursive node. Do not replace that obligation with another cubic circuit count.

## Verification procedure

The current chat runtime has no Lean/Lake and cannot resolve GitHub directly. Local proof compilation is therefore not claimed. The explicit ready-for-review gate checks frozen hashes and pins, runs the exact regression before Lean setup, restores the existing shared cache, compiles only the new module/dependencies, and audits all seven declarations. It has no secrets and no push/synchronize trigger. Retain its receipt and remove it before integration after a successful result. If it fails, record the concrete failure rather than start a speculative hosted compiler loop.
