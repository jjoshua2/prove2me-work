# Actual high-excess edge cost from certified independent row blocks

Date: 2026-09-11. Repository: `jjoshua2/prove2me-work`.
Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Result, not another scalar accounting bound

`Solutions/PolynomialRowBlockRouting.lean` supplies a sufficient algebraic
criterion for a genuinely short ordinary-edge route even when total carrier
presentation excess is arbitrarily large. It derives the product geometry
from row identities rather than assuming a product-set equality or a graph
route. It reuses, rather than reproves, the existing product-walk and affine
transport machinery.

Suppose a nonempty bounded n-row H-polyhedron in dimension d has an invertible
linear coordinate change and a partition of its rows into independent blocks.
Write d_i for the number of coordinates of block i and m_i for its rows. Every
row in block i must depend only on that block's coordinates. If

```text
d_i <= m_i <= d_i + 3  for every i,
```

then

```text
sum_i (m_i-d_i) = n-d,
DiamLE P (n-d).
```

This is an upper bound, not a claim that the actual diameter always equals n-d. There is no bound on the total excess
or the number of blocks. This applies to any equivalent intrinsic carrier
presentation, not just a minimum one, and it has no circuit or checkpoint-vertex
hypothesis. A useful carrier can be high-excess but factorwise inexpensive.

**Formal dependency boundary:** the final Lean theorem explicitly takes the
universal bounded-H-polyhedron excess-at-most-three diameter theorem as a
premise `hsmall`. That premise is exactly the existing public mathematical input
`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`, theorem
`12426807-9602-4014-bd5e-c69fb43f4cb6`, accepted proof
`59736803-0e9d-40bb-875d-7ca66b9ccd45`, recorded in the prior authenticated project
receipts. The new file does not import a theorem placeholder or conceal this
premise in an axiom. Its first three declarations have no diameter premise.
This work did not independently refresh that Prove2Me record or publish a new
platform theorem.

## Checked Lean declarations

All four declarations are in `HirschRowBlocks`:

- `image_hpoly_eq_pi_of_row_blocks`: the linear coordinate and row-enumeration
  equivalences plus blockwise linear evaluation identities imply equality
  between the image of the complete parent feasible set and a Cartesian product.
- `factors_bounded_of_row_blocks`: nonemptiness and boundedness of the parent
  imply boundedness of every factor; no factor boundedness is assumed.
- `row_block_excess_sum`: row/cardinality and dimension equivalences imply
  `sum_i (m_i-d_i) = n-d`, with the lower count checks justifying natural subtraction.
- `hpoly_diamLE_excess_of_small_row_blocks`: combines the three algebraic/
  geometric facts with the existing small-excess input and the already checked
  product and affine graph transport theorems.

The final theorem does not assume factor diameter bounds individually. They
are discharged from the numerical row counts and `hsmall`. Intermediate
moves are genuine factor edges, embedded as genuine product edges; an
invertible affine map transfers them to parent edges. This is an actual
ordinary-edge cost bound, not a count of circuit steps or expensive carriers.

## Finite exact certificate construction

The companion standard-library Python tool is
`scripts/row_block_certificate.py`.

For retained nonzero normals spanning R^d, select d independent original rows
as the rows of an invertible matrix B. Set z=Bx and C=A B^{-1}. Join two basis
coordinates whenever some row of C has nonzero coefficients at both. Connected
components partition the coordinates. Each transformed row has its support
entirely inside one component, and is assigned to that component's row block.

Thus the transformed inequalities involve disjoint coordinate sets. Every
combination of factor-feasible points is feasible in the transformed parent;
there is no unproved compatibility/portal condition. The components are the
fundamental-support representation of the direct-sum components of the selected
normal vector configuration. No literature novelty is claimed for this
standard linear-algebra/product construction.

A separate verifier checks both inverse identities, every transformed-row
identity, the complete coordinate and row partitions, each support containment,
each factor rank, the count budget, and the small-excess condition. It does not
trust the component-discovery routine's answer.

Input feasibility is certified by an exact feasible point. Boundedness is
certified by full normal rank and strictly positive weights lambda with
`sum_j lambda_j A_j = 0`. This certificate has an elementary boundedness proof:
each row value has its usual upper bound b_j and the lower bound

```text
b_j - (sum_l lambda_l b_l)/lambda_j.
```

In particular the independent basis-row values lie in finite intervals, and
B^{-1} maps their box to a bounded set. No numerical LP solver or floating-point
tolerance is used.

Optional row deletion requires exact nonnegative-combination certificates:
for every discarded inequality, its normal must be a nonnegative combination
of retained normals and the same combination of retained right-hand sides must
not exceed the discarded right-hand side. These checks prove feasible-set
equivalence. Zero-normal tautologies can be deleted with zero multipliers.
Arbitrary row deletion, wrong multipliers, and an insufficient right-hand-side
bound are rejected.

**Numerical evidence boundary:** the Python checker uses exact rational
arithmetic and emits algebraic witnesses; it does not emit Lean proof terms
for individual numerical instances. The universal certificate-to-product/
route implication is separately Lean-checked as described above.

## Resolving the zero-savings control family

PR #122's balanced genuine-facet family has a k-cube carrier with

```text
ambient D=2k-1, N=4k-2,
h=k, minimum M=2k, e=k, delta=k-1,
kappa=s=tau=0.
```

Its intrinsic effective system includes the cube bounds and the redundant
neutral restrictions `x_j-x_0 <= 5/2` for j=1,...,k-1. Before removing those
restrictions, the normal support graph is connected: these rows obscure the
product structure. This is why testing the ambient/full effective normal
system alone is insufficient.

Each such cap row is implied by `x_j<=1` plus `-x_0<=0`; their summed bound is
1<=5/2. After these certified deletions, the retained system has k independent
interval blocks, each with dimension 1, two rows, and excess 1. The new criterion
therefore certifies actual carrier graph diameter at most k.

This is constructive progress on the existing adversarial control family:
zero scalar savings need not be an obstacle to cheap graph routing. It is NOT
a proof that every saturated carrier has a product decomposition, and it does
not bypass the general completion/universality obstructions.

## Executed regressions

The deterministic test command was executed repeatedly and produced byte-identical
JSON output with SHA-256

`8e3c6fe5732386d7756c7775e97a1dc1a06ff6e60a15fb89e5c525d7d6214bc1`.

The full report is reproduced by the command below; the committed summary records
its digest and totals. The downloadable continuation packet also contains the
full JSON report.

Scope:

- 14 complete exact vertex-edge graph enumerations: 256 vertex occurrences and
  558 edge occurrences; all applicable certified diameter bounds hold.
- Nine zero-savings cube carriers, k=4,...,12: all cap deletions are certified,
  all unreduced systems are one connected high-excess block, and all reduced
  systems split into k interval blocks with cost k.
- Four larger products, dimensions 8,12,16,20 and total excesses 10,14,18,22:
  certificate verification includes dense invertible shears, translations,
  positive row scalings, and row permutations; their full graphs were not enumerated.
- Twelve negative controls: wrong inverse, wrong transformed row, duplicate
  coordinate/row, hidden coupling, invalid positive balance, infeasible witness,
  negative/incorrect/missing deletion certificate, and floating-point input.
- A hexagon, and a hexagon times two intervals, are deliberately left unresolved
  by this sufficient small-block-excess criterion despite being easy examples
  by other methods. Connected excess>3 means "not covered", not "provably hard".

The fully enumerated cases include two squares (actual/certified diameter 4/4),
a pentagon times an interval (3/4), two pentagons (4/6), a 3-simplex times a
pentagon (3/4), and two squares times an interval (5/5), with scrambled copies.
The test independently enumerates all vertices from active d-row systems and
uses rank d-1 of common tight normals for adjacency, then computes graph
diameter by breadth-first search. All tested models are bounded and full-dimensional.
The individual large-family evidence remains finite; the theorem itself is universal.

## Verification and reproducibility

The existing offline environment export from Actions run `34563882704` was
restored locally. All seven transfer ZIP digests and the source, toolchain, and
cache archive SHA-256 checks passed. No new hosted proof/publication workflow
was launched for this work; no credential was read or exported.

The exact current imported source blobs were checked against GitHub:

```text
Definitions.Def_Hirsch_model             53acfb1a0eb3af6719173c233788199dcb987eca
Solutions.PolynomialProductWalk         64e5977f9cd5fd9617b67e82f504550236d49b83
Solutions.PolynomialAffineDiameterTransport
                                        ada90a58fe876f5e0b31ec20a0f8c22b1c408dd1
```

Because the export lacks package Git metadata and the Mathlib umbrella is
large for this 4-GiB workspace, verification used a source-faithful focused-import
standalone retaining all definition/proof bodies from those modules and the
new module. No full normal `lake build` is claimed. The final direct pinned
Lean invocation exited zero; all four required transitive axiom reports passed
the repository checker with only `propext`, `Classical.choice`, and `Quot.sound`.
The sole warning in the final log is from unchanged affine-transport source.

Hashes:

```text
New Lean source:
b027747a18327b343778a7ae2e49be2654b1a5db57094a116b7eacaf034e5712
Generated standalone:
3bcf1c7b2568239c6036b665f37b93789e8f76c5f9a9b183e2707ee3a63ffd4a
Compiler/axiom-report log:
cc2779faa7301349445f45ba369ec26c83cc8f7de5685bc80144ddf2accc9576
```

In a normal pinned checkout:

```bash
python3 scripts/build_row_block_standalone.py \
  --output /tmp/RowBlocksVerified.lean \
  --manifest /tmp/row-block-manifest.json \
  --expected-manifest research/ROW_BLOCK_SOURCE_MANIFEST_2026-09-11.json
set -o pipefail
lake env lean /tmp/RowBlocksVerified.lean 2>&1 | tee /tmp/row-block-lean.log
python3 scripts/check_lean_axiom_log.py /tmp/row-block-lean.log \
  HirschRowBlocks.image_hpoly_eq_pi_of_row_blocks \
  HirschRowBlocks.factors_bounded_of_row_blocks \
  HirschRowBlocks.row_block_excess_sum \
  HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks
python3 scripts/test_row_block_certificate.py --output /tmp/row-block-checks.json
sha256sum /tmp/row-block-checks.json
```

For an exported offline cache invoke pinned Lean directly with LEAN_PATH
containing the package `.lake/build/lib/lean` directories. The builder was
rerun and reproduced the compiled standalone byte-for-byte.

## Narrowed next target

Do not spend another iteration proving this product composition or counting
expensive carriers. Apply the exact detector to equivalent intrinsic
presentations of actual selected checkpoint carriers, recording factor ranks
and excesses after certified deletions. Factors already certified here can be
paid at their explicit ordinary-edge cost via the existing carrier-routing API.

What remains is a cost bound or cost-controlled bypass for the genuinely
coupled factors not covered by this criterion. A useful extension must either
prove more such factors inexpensive or quantify a valid coupling-removal/
replacement operation. Simply dropping a coupling row is not allowed. Nor does
a polynomial number of unresolved factors imply polynomial total graph cost.

The Polynomial Hirsch root and global edge-refinement statements have not
been proved by this work. No Prove2Me theorem, submission, Open child, or
frontier mutation was created. Concurrent PR #126 owns the separate publication
of the existing deletion-savings identity and was left untouched.
