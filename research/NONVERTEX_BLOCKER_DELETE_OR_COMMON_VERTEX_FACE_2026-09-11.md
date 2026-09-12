# Nonvertex circuit blocker: pointed deletion or a universal vertex face

Research date: 2026-09-11 (America/New_York).
Status: complete ordinary deduction from existing kernel-checked primitives; NOT a separately compiled Lean theorem and NOT submitted to Prove2Me.

## Motivation

PR #158 gives two pointed row deletions for a maximal circuit step starting at a vertex. The actual cubic circuit route can have nonvertex checkpoints. The vertex-start premise can be removed if one retains the following explicit exceptional case, rather than assuming that every blocker deletion stays pointed.

## Statement

Let P = {z : <a_i,z> <= b_i for all i} be a finite H-presentation with injective row map. Let x -> y be any maximal nonstationary row-circuit step; x need only be feasible. Put g=y-x. Choose the destination-tight increasing blocker j supplied by `rowCircuitStep_exists_target_blocking_row`:

- a_j is nonzero;
- <a_j,y> = b_j;
- <a_j,g> > 0.

Then at least one of these two conclusions holds:

1. deleting j preserves row-map injectivity (hence pointedness); or
2. every original vertex z of P satisfies <a_j,z> = b_j.

The second conclusion concerns a row-tight supporting face. Do not call it a genuine facet without the needed full-dimensional/irredundancy assumptions.

## Proof

If some row i != j has <a_i,g> != 0, the already-verified theorem

`HirschDeletion.rowMap_rowsWithout_injective_of_two_nonneutral_rowCircuit`

applies directly to g, i, j. It does NOT require the source x to be a vertex. Its proof retains all neutral rows and the second nonneutral row i; these have full rank because the neutral kernel is precisely the circuit line and i does not annihilate that line. This proves conclusion 1.

Otherwise every row except j annihilates g. Let z be any original vertex. Suppose j were slack at z. Every tight row at z would then be different from j and would annihilate g. The existing theorem

`HirschPolynomialAccess.vertex_tight_rows_span_checked`

forces g=0, contradicting nontriviality of the row circuit. Thus j is tight at z, proving conclusion 2.

In this exceptional case deleting j really is noninjective: the nonzero g lies in the kernel of every remaining row. The exception is not just an artifact of the proof.

## Graph-cost consequence of the exception

Let F=P intersect {z : <a_j,z>=b_j}. If every parent vertex lies in F, an intrinsic edge budget B for F immediately gives the same budget B for P: regard each parent endpoint as an extreme point of the extreme face F, use its route, and lift each face edge to a parent edge. No deletion-outer cost D and no cap correction are needed for this case.

This is only a conditional cost consequence. A quantitative lower-dimensional pointed-face routing theorem must still supply B. The two-or-more-nonneutral-row branch still requires cost-controlled reinsertion after pointed row deletion.

## Exact elementary controls

- Exceptional case: P is the nonnegative quadrant, x=(1,1), y=(0,1), g=(-1,0). This is a maximal circuit step from a nonvertex. Only the x>=0 row changes. Deleting that row creates horizontal lineality; the sole original vertex (0,0) lies on x=0.
- Pointed-deletion case: P=[0,1]^2, x=(0,1/2), y=(1,1/2), g=(1,0). Both endpoints are nonvertices. The two x-bound rows are nonneutral. Deleting the destination blocker x<=1 leaves the pointed half-strip x>=0, 0<=y<=1.

## Focused formalization target

First prove `vertices_on_unique_nonneutral_row` for any nonzero direction g, with no circuit or boundedness premise. Then combine it with #158's two-nonneutral-row theorem and the existing target-blocker characterization. This is a genuinely smaller structural statement than the global edge-refinement theorem: it handles the source-nonvertex issue while exposing the exact alternative rather than hiding it behind another conjectural child.

Do not infer a polynomial global recurrence, arbitrary pointed edge diameter, or Prove2Me acceptance from this note.
