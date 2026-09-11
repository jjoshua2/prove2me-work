# Exact circuit-carrier deletion savings and the limits of amortization

Date: 2026-09-11. Repository: `jjoshua2/prove2me-work`.

## Result and evidence boundary

`Solutions/PolynomialCircuitDeletionSavings.lean` proves a sharper version of
the nonvertex circuit-carrier resource inequality. Its four declarations were
verified locally by Lean 4.30.0 against Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, using the source-faithful standalone
builder described below. Each transitive axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`.

This is a universal **one-carrier accounting theorem**, not a polynomial
ordinary-edge routing theorem. No Prove2Me registration, proof submission, or
ACCEPTED/live-Proved claim is made for this package. The geometric control
families below have explicit ordinary proofs and exact-rational finite checks;
they have not been formalized in Lean.

The earlier exact nonvertex resource theorem was completed independently in
PR #111. This package does not re-prove that milestone or the existing
small-excess routing wrappers.

## 1. Exact identity

Let `P = Hpoly a b` be bounded, `x` feasible, and `g = y-x` an ambient row
circuit. Neither endpoint must be a vertex; the target need not be feasible.

Write:

- `W = commonDirection a b x y`, `h = dim W`;
- `E` for all ambient rows whose restriction to `W` is nonzero;
- `Z` for the nonzero ambient rows neutral on `g`;
- `F` for any selected subset of `E` with `h <= |F|`.

`F` need not be an equivalent presentation. For the intended minimum equivalent
presentation, existing bounded/feasible minimum-witness results supply
`|F| = M_min` and `h <= |F|`.

Let `r_F` be the rank on `W` of the rows in `F intersect Z`, and define

```text
e     = |F| - h
delta = h - 1 - r_F
kappa = n + h - (|E| + d)
s     = |(E \ F) \ Z|
q     = |(E \ F) intersect Z|
tau   = q - delta.
```

All these quantities are nonnegative under the stated hypotheses. The new
identity is

```text
e + delta + kappa + s + tau = n-d.
```

In particular,

```text
e + delta + s <= n-d.
```

The previous inequality discarded the explicit savings. Here `kappa` counts
rows disappearing on the carrier beyond the required codimension, `s` counts
discarded nonneutral effective rows, and `tau` is the number of discarded
neutral rows beyond the actual neutral-rank loss. Each omitted nonneutral row
therefore saves one full unit without reducing neutral rank.

The old bound is an equality exactly when

```text
|E| + d = n + h,
s = 0,
q = delta.
```

Thus saturation has a concrete structural meaning: no surplus disappearing
rows, no discarded nonneutral effective rows, and every discarded neutral row
accounts for one independent unit of lost rank.

## 2. Proof

The bounded nonvertex neutral-rank theorem gives rank `h-1` for all neutral
rows restricted to `W`. Removing ineffective rows does not change that rank.
Deleting down to the selected neutral rows loses at most

```text
q = |(Z intersect E) \ (F intersect Z)|
  = |(E \ F) intersect Z|
```

units. Hence `delta <= q`; crucially, there is no need to replace `q` by the
larger count `|E \ F|`.

The existing effective-row count gives `|E| + d <= n + h`. The exact partition

```text
|E| = |F| + s + q
```

then yields the identity by substitution. The Lean proof justifies the
natural-number subtractions using `h <= |F|`, `d <= n`, `delta <= q`, and the
effective-row count before invoking arithmetic automation.

Checked declarations, all in namespace `HirschCircuitLocalization`:

```text
rowCircuit_selected_defect_le_discarded_neutral_of_bounded
rowCircuit_selected_excess_defect_savings_identity_of_bounded
rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded
rowCircuit_selected_budget_saturated_iff_of_bounded
```

## 3. High intrinsic excess can have zero savings, even in balanced genuine-facet parents

For any integer `k >= 4`, use coordinates
`(x_0,...,x_(k-1),t,s_1,...,s_(k-2))` and inequalities

```text
x_0 >= 0
0 <= x_i <= 1                          (1 <= i < k)
t >= 0,  s_j >= 0
x_0 + t + sum_j s_j <= 1
x_i - x_0 + 2*t <= 5/2                 (1 <= i < k).
```

There are `D = 2k-1` dimensions and `N = 4k-2 = 2D` inequalities. The parent is
bounded and full-dimensional. Every inequality is a genuine facet, not a
redundant row: the regression constructs a strict interior point and, for each
row, a feasible point tight on that row and strictly satisfying every other
row. These witness conditions imply facetness in a full-dimensional
H-polyhedron.

The face `t=s_1=...=s_(k-2)=0` is an unchanged `k`-cube. Its opposite vertices
are joined by a maximal ambient row-circuit step. Indeed the containing-face
normals contribute `k-1` independent neutral equations and the cap normals
contribute another `k-1`, for neutral rank `D-1`. The step stops at the opposite
cube vertex because all changing cube coordinates have reached their upper
bounds.

On this carrier the `2k` cube inequalities are a minimum equivalent
presentation. The cap restrictions are strictly redundant; all of them are
neutral on the diagonal. Consequently,

```text
h = k,  M = 2k,  e = k,  delta = k-1,
kappa = s = tau = 0,
N-D = 2k-1 = e+delta.
```

This rules out a claim that high carrier excess must force a positive savings
term, even with exact balance and genuine ambient facets. It does not rule out
efficient graph routing for the family; the cube itself is easy to route.

Exact checks cover `k=4,...,12`. This family specializes the project's
existing circuit-completion obstruction theme; no literature novelty claim is
made.

## 4. Savings do not telescope, even along short simple walks with distinct carriers

For `k >= 3`, take the `(k+1)`-cube with a genuine corner cut

```text
P = [0,1]^(k+1) intersect {sum_i x_i + t <= k+1/2}.
```

Here `D=k+1`, `N=2k+3`, and `N-D=k+2`. All rows are genuine facets. On the
floor `t=0` the new inequality is strict everywhere, so that floor remains a
`k`-cube.

Choose the first `L=2k+1` edges of a binary reflected Gray-code walk on the
floor. All its vertices and edge carriers are distinct. These are actual
parent edges and maximal row-circuit steps.

For each edge carrier, its minimum interval presentation has `h=1`, `M=2`,
`e=1`, and `delta=0`. The corner-cut row restricts nontrivially to that edge
direction, but is redundant there. It is the one discarded nonneutral row, so
`s_i=1` at every step. Therefore

```text
sum_i s_i = 2k+1 > k+2 = N-D.
```

The walk has only linear length, so the obstruction is not caused by a long
cyclic walk. Distinct-carrier deduplication does not fix it: the same genuine
parent facet supplies the saving on different carriers.

Exact checks cover `k=3,...,8`. This refutes automatic global consumption of a
static per-carrier saving. It does not refute a specially chosen path,
a persistent-row invariant with additional hypotheses, or the existence of
shorter routes between these endpoints.

## 5. Regression results

The standard-library-only exact-rational test was executed twice with seed
`20260911` and produced the same JSON data:

- 768 selected-row identity checks, including 192 minimum cube-carrier cases;
- 144 nonvertex sources and 149 nonvertex targets within those 192 cases;
- examples with each of `delta`, `kappa`, `s`, and `tau` positive;
- four negative controls detecting omitted savings terms or a negated defect;
- nine exactly balanced high-excess zero-savings models;
- six short simple-walk non-telescoping controls;
- 354 strict single-tight-row witnesses certifying genuine facets across the
  two geometric control families.

These are finite regression counts, not proof of a universal geometric family.
The algebraic savings identity itself is separately kernel-checked.

Run:

```bash
python3 scripts/test_circuit_deletion_savings.py \
  --output /tmp/circuit-deletion-savings-checks.json
```

The committed report is
`research/CIRCUIT_DELETION_SAVINGS_EXACT_CHECKS_2026-09-11.json`.

## 6. Verification method and reproducibility

This workspace could not reach GitHub or Prove2Me by DNS. A pre-existing public
Lean/Mathlib cache export was restored through the GitHub connector; no hosted
Actions proof run was launched for this work. All seven transfer-part hashes,
the combined payload, and the compiler/dependency/source archive hashes were
checked. The source baseline was
`533ec66e7809b420749467c73e2a7d0e39828a0c`; the bounded neutral-rank module was
updated to exact Git blob `469c4c31eafcfd34192cfda61bcec78a76bfa1c8`.
The imported pre-existing modules were also checked against integration base
`e755788e72e700e22f9b74b67a1fb5927f6cf90e` using GitHub's commit comparison.

The exported dependency cache lacks Git metadata. A normal Lake invocation
attempted dependency retrieval, and loading the full `import Mathlib` umbrella
exceeded the practical memory budget. **No successful full `lake build` or
separate original-module gate is claimed.**

Instead, `scripts/build_circuit_deletion_savings_standalone.py` retains the
definition and proof bodies of all 17 local modules in dependency order,
replaces their imports with explicit focused Mathlib imports, closes file-local
sections, and removes only dependency axiom-print commands. Global
`autoImplicit false` matches the package setting. It rejects theorem-stub
imports and checks both dependency pins. The final source was compiled directly
by pinned Lean, with exit code zero.

All four requested declarations then passed the existing transitive axiom
checker; only `propext`, `Classical.choice`, and `Quot.sound` occurred. The log
has a few linter warnings from unchanged dependency bodies, but no proof errors.
The builder was rerun against the frozen source manifest and reproduced the
standalone byte-for-byte.

In a normal pinned checkout:

```bash
python3 scripts/build_circuit_deletion_savings_standalone.py \
  --output /tmp/DeletionSavingsFinal.lean \
  --manifest /tmp/deletion-savings-manifest.json \
  --expected-manifest research/CIRCUIT_DELETION_SAVINGS_SOURCE_MANIFEST_2026-09-11.json
set -o pipefail
lake env lean /tmp/DeletionSavingsFinal.lean 2>&1 | tee /tmp/deletion-savings.log
python3 scripts/check_lean_axiom_log.py /tmp/deletion-savings.log \
  HirschCircuitLocalization.rowCircuit_selected_defect_le_discarded_neutral_of_bounded \
  HirschCircuitLocalization.rowCircuit_selected_excess_defect_savings_identity_of_bounded \
  HirschCircuitLocalization.rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded \
  HirschCircuitLocalization.rowCircuit_selected_budget_saturated_iff_of_bounded
```

For an offline exported cache, invoke the pinned `lean` binary directly with
`LEAN_PATH` containing each exported package's `.lake/build/lib/lean` directory,
rather than allowing Lake to fetch missing Git metadata.

SHA-256 receipts:

```text
Lean module:
19c5164f3294edcbceb5717c545e09293afe3bb0582a997d2a9fdeb448c31598
Generated standalone:
6c097dd636c44f1baccd4d8fad87015f1dfef127e5946202125a50b1c4483cbf
Committed compiler/axiom log:
147041067491b3edc54211137672561f1c6cc4bdd9166f183ec1312c2fed95f7
Exact regression JSON:
2009b887878b68a0080712105e91482d0ae3c6ec7a86169f62527033ea5551a5
```

## 7. Corrected next research target

A polynomially long circuit walk already exists (`17*n^3`). Merely proving that
the number of expensive carriers is polynomial therefore does not solve the
remaining problem: even a single carrier still needs a justified graph-cost
bound. The target is a polynomial bound on total **ordinary-edge cost**, or a
cost-controlled replacement of hard blocks, not another polynomial count.

The savings identity identifies exactly when the old resource bound is loose.
The two controls show why neither positive savings nor globally consumable
credits follow automatically. Useful next work must add route-dependent
structure: a provably persistent set of consumed rows, an actual inexpensive
bypass, or a recursive routing construction whose branching costs and decrease
are both quantified. For near-saturated carriers, the new equality criterion
gives explicit structural hypotheses to investigate rather than a vague scalar
potential.

Do not infer a graph-distance decrease merely from positive accounting slack.
Do not treat a repeatedly discarded row as a newly consumed resource.
Do not add another small-excess routing wrapper; that interface already exists.
