# Cross-presentation minimality for common-face row counts

Date: 2026-09-10 (America/New_York).
Mission: The Polynomial Hirsch Conjecture.

## Status and scope

**Ordinary proof complete; exact rational regressions PASS; Lean source and
common-face adapters kernel-checked; standalone theorem ACCEPTED / Proved on
Prove2Me 0.10.0.**

Public theorem:
`Hirsch.irredundant_rows_card_le_any_equivalent_presentation`
(theorem `8538150b-8afe-47ad-94b0-d72189b80264`, submission
`9194432c-54e2-4e6a-9aaf-d7c27fb9934e`). Full verification/publication
provenance is in
`research/IRREDUNDANT_ROW_COUNT_PUBLICATION_RECEIPT_2026-09-10.md`.

This is a separate row-semantics contribution. It does not create a new Open
mission child. The edge-refinement theorem
`73beca40-31bc-42d5-8350-5ec9ac28bd3e` remained exactly Open before and after
the publication transaction, with no frontier graph modification.

The repository previously proved a least equivalent *original-row
subpresentation* count for common faces. The new result is stronger: under
strict feasibility and irredundancy, that count agrees with the number of rows
in **any** equivalent irredundant coordinate presentation, even when its
normals were not selected from the original rows. This makes the row count
representation-independent without introducing an abstract geometric facet
type.

This is a formalization of standard finite polyhedral geometry, not a new
diameter theorem. Abstract geometric facet-count equality remains a separate
semantic bridge; it must not be marked formalized by this packet.

## Main theorem

Let

    P = {x in R^d : a_i . x <= b_i, i = 1,...,n}.

Assume the presentation is strictly feasible and irredundant in the repository's
exact sense: deleting row i admits a point that violates i and satisfies every
other row. If

    P = {x in R^d : c_j . x <= beta_j, j = 1,...,m},

then **n <= m**.

The comparison rows are arbitrary real rows. They may be redundant, repeated,
or zero-normal tautologies. They do not have to be a subset of the original
presentation. Boundedness is not required.

Consequently, equivalent irredundant presentations have the same number of
rows when one is strictly feasible. Strict feasibility transfers to the other
irredundant presentation, so it need not be separately assumed twice.

## Complete ordinary proof

### 1. Finite perturbation

For finitely many real slopes q_i and positive margins r_i, there is epsilon>0
such that epsilon*|q_i|<r_i for every i. For example, take half the minimum of
1 and all r_i/(|q_i|+1). The Lean proof establishes this by finite induction,
including the empty set.

Suppose x is feasible for a finite row system and strict on every nonzero row.
If c.x<=beta is valid on its feasible set and c is nonzero, then c.x<beta.
Otherwise, move a sufficiently small positive distance in direction c. Finite
perturbation preserves all nonzero rows; zero rows do not change. But the valid
inequality increases by epsilon*||c||^2>0, a contradiction.

Taking the contrapositive, if a nonzero valid inequality is tight at a feasible
point, at least one **nonzero** describing row is tight there. Excluding zero
rows is necessary: a comparison presentation may contain 0.x<=0.

### 2. A singleton-tight witness for each indispensable row

Choose a strict feasible centre z. For original row i, take its deletion
witness w_i, so

    a_i.z < b_i < a_i.w_i,
    a_k.w_i <= b_k for k != i.

Set

    t_i = (b_i - a_i.z)/(a_i.w_i - a_i.z),
    p_i = (1-t_i)z + t_i w_i.

Then 0<t_i<1, row i is tight at p_i, and every other original row is strict.
The latter follows because the strict centre still has positive coefficient:

    b_k - a_k.p_i
      = (1-t_i)(b_k-a_k.z) + t_i(b_k-a_k.w_i) > 0.

Thus p_i is feasible, with exactly the original row i tight. Irredundancy and
nonemptiness also ensure a_i is nonzero.

### 3. Match witnesses to comparison rows

At p_i, the original nonzero inequality i is valid and tight. Since the
comparison presentation defines exactly P, step 1 supplies a nonzero comparison
row f(i) tight at p_i. Choose any such row for each i.

This choice is injective. Suppose i!=k but f(i)=f(k). At the midpoint
q=(p_i+p_k)/2, every original row is strict: each row is strict at at least one
of the two endpoints and is satisfied at both. By step 1, every nonzero valid
comparison inequality is therefore strict at q. However, the common row f(i)
is tight at both endpoints and hence tight at q. Contradiction.

There is an injection from n original rows to m comparison rows, so n<=m.
Importantly, no facet-dimension theorem, supporting-hyperplane proportionality,
Farkas lemma, compactness theorem, or graph-diameter bound is needed.

### 4. Equality for two irredundant systems

A strict original centre is feasible in the comparison system. Its rows are
nonzero because that system is irredundant and nonempty. Step 1 shows that the
same centre is strict in the comparison system. Apply n<=m in both directions.

## Connection to the existing common-face minimum

Let M_min be `commonFaceMinSubpresentationCount a b u v`.

First, any strictly feasible irredundant original-row subpresentation with r
rows satisfies M_min=r. The inequality M_min<=r is immediate from the
definition. For the reverse inequality, compare the r-row irredundant system
with a witness at the minimum original-row budget and apply the new cardinality
theorem.

Now take ANY equivalent strictly feasible irredundant coordinate model with m
rows. Its strict centre is strict on every nonzero row of the original
coordinate presentation, by the perturbation lemma. Feed that centre twice to
the existing `HirschCircuit.exists_irredundant_strict_model` theorem: its
separation hypothesis only concerns nonzero rows. This extracts an original-row
irredundant strict subpresentation with r rows. The previous paragraph gives
M_min=r, and cross-presentation equality gives r=m.

The kernel-checked adapter proves

    commonFaceMinSubpresentationCount a b u v = m

for arbitrary equivalent strictly feasible irredundant coordinate normals.
This equality can rewrite the existing excess/defect inequality's row-count
term. The selected-row neutral-rank defect is still the existing selected-row
quantity: this theorem does not make circuit status or neutral rank invariant
under deletion of redundant ambient rows.

## Why strict feasibility cannot be removed

In R^2 the same singleton {0} has these two irredundant presentations:

    x<=0, -x<=0, y<=0, -y<=0                (4 rows)
    x<=0, y<=0, -x-y<=0                    (3 rows).

Each row has an explicit deletion witness; both feasible sets are exactly the
origin. The regression checks both inclusions by exact nonnegative row
combinations. In either system, summing the inequalities gives 0<=0, so having
all inequalities strict would imply 0<0. This example is bounded, so adding
boundedness does not repair the missing strict-feasibility hypothesis.

## Files and evidence

- `Solutions/PolynomialIrredundantRowCount.lean`: finite perturbation, valid-row
  strictness, nonzero blocker extraction, singleton-tight witnesses, global
  minimality, strict-feasibility transfer, count equality, and extraction of a
  globally minimal irredundant subpresentation.
- `Solutions/PolynomialCommonFaceIntrinsicRowCount.lean`: kernel-checked
  original-subset and arbitrary-presentation adapters for the existing
  common-face minimum.
- `Solutions/Sol_Hirsch_irredundant_rows_card_le_any_equivalent_presentation.lean`:
  independently audited standalone Prove2Me packet.
- `scripts/check_irredundant_row_count.py`: dependency-free Fraction arithmetic.
- `research/IRREDUNDANT_ROW_COUNT_EXACT_CHECKS_2026-09-10.json`: exact-regression
  output.
- `research/IRREDUNDANT_ROW_COUNT_PUBLICATION_RECEIPT_2026-09-10.md`: durable
  kernel/server/publication receipt.

The exact run passes 42 source models, 252 equivalent comparison presentations,
278 singleton-tight witnesses, 1,724 strict pair midpoints, and 2,582 nonzero
tight blocker incidences. Families include boxes, simplices, cross-polytopes,
deformed cubes, a carrier hexagon, unbounded orthants/halfspaces, empty row
systems, and sheared/translated versions. Comparison systems include positive
scalings, permutations, duplicates, nonnegative row combinations, loose rows,
and zero-normal tautologies. Exact coefficient identities certify equality of
the compared feasible sets for all real points, not just sampled points.

The regression also passes under `python3 -O`: its checks do not rely on Python
assert statements. It is still finite evidence, not a general kernel proof.

## Verification and publication record

Frozen verified source commit:
`1ff86eb9c69679c6355c6fa968b6601482b046a1`.

The source/common-face/standalone gate was GitHub Actions run `34559027640`
(artifact `10183697315`). It compiled the core reusable source, both common-face
adapters, and the standalone public packet under Lean 4.30.0 / pinned Mathlib.
Every audited new declaration used only `propext`, `Classical.choice`, and
`Quot.sound`. The standalone solution SHA-256 is
`33be3fdd17714bc1439b0bef73489c571ae41b14f5b06443c4ab6f85e905af55`.

The authenticated Prove2Me publication gate was run `34559453698` (artifact
`10183894675`, artifact digest
`sha256:e2d5f54b586b267bb625f1d394f7028bb22debc68e8b34063008ab6830581f95`).
It registered theorem `8538150b-8afe-47ad-94b0-d72189b80264`, submitted exact
standalone solution `9194432c-54e2-4e6a-9aaf-d7c27fb9934e`, and received
**ACCEPTED** / live **Proved**. Mission discussion comment
`33f2c225-aae0-458b-8c98-8575c4e453c5` links the result to the Polynomial
Hirsch mission.

The same authenticated transaction read
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`) as **Open** both before and after,
created no conjectural children, and did not modify the frontier graph.
