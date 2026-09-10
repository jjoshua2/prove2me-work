# Reconciled circuit-checkpoint continuation — 2026-09-10

## Status and provenance

This is a DRAFT integration. No new Lean compilation or Prove2Me verdict is claimed.

PR #63 separately integrated the exact previously compiled `PolynomialCircuitCarrierEdge` module and its durable audit. Its three declarations passed run `34533747844` at `71efbbcb66528871c0ff0508fe6b31b6c1b7b646`, using only standard logical axioms. The draft is based on that clean integration.

The rank, active-defect, and step-commutation files, and the two existing exact regression scripts, are copied by Git blob identity from research snapshot `f8b8f66634cf57fd379f595eaa6058e08cdff57d`. These newer candidate sources have NOT been compiled. In particular the last failed run `34534351717` used an older rank source and is not evidence about the corrected snapshot.

The chat attachment `circuit_checkpoint_continuation.zip` was based on older commit `8d0433e`. Its blind application would overwrite the newer rank source and redeclare `activeNeutralDefect_displacement_eq_commonFaceDim_sub_one`, already present in `PolynomialCircuitCarrierDefect`. This integration keeps the newer rank proof and reuses the existing defect module. The routing module adds only two declarations: carrier closedness and the conditional routing specialization. Checkpoint localization adds six declarations.

The old branch's manual workflow referenced a nonexistent `research/circuit_carrier_defect_regression.json`. This integration uses the already committed SHA-256 expectations for BOTH existing suites, plus the unchanged checkpoint-regression digest. It does not import the obsolete one-shot workflow.

## Ordinary mathematical argument

Let P be a finite H-presentation `a_i dot z <= b_i` in ambient dimension d with n rows. For distinct feasible points x,y, put g=y-x. Let X,Y be the sets of nonzero rows tight at the respective endpoints, C=X intersect Y, S=X minus Y, T=Y minus X, and Z the nonzero rows neutral on g. Define

```
h = d-rank(A_C)
p = d-rank(A_X)
q = d-rank(A_Y)
delta = (d-1)-rank(A_Z).
```

The first three numbers are the common-carrier and endpoint minimal-face dimensions. The last is the ALL-neutral direction defect, not the source-active defect. Since g is nonzero and lies in the neutral kernel, rank(A_Z)<=d-1.

Adding S to the common rows decreases nullity from h to p, hence `h-p<=|S|`; similarly `h-q<=|T|`. The sets S,T,Z are pairwise disjoint: neutrality of a row tight at one endpoint would make it tight at the other. Consequently

```
n >= |S|+|T|+|Z| >= (h-p)+(h-q)+rank(A_Z),
2*h+d <= n+p+q+delta+1.
```

The slack has the exact nonnegative decomposition

```
n+p+q+delta+1-d-2*h
 = (|S|-h+p) + (|T|-h+q)
 + (|Z|-rank(A_Z)) + (n-|S|-|T|-|Z|).
```

If g is a row circuit and the total row map is injective, its neutral kernel is exactly span(g). Thus delta=0. Bounded nonempty presentations have injective total row map. The Lean candidate instead uses any reference extreme vertex of the same presentation to invoke the already checked neutral-rank theorem; it need not be x or y. The candidate's circuit statement is

```
2*commonFaceDim(x,y)+d
 <= n+commonFaceDim(x,x)+commonFaceDim(y,y)+1.
```

Its more general defect-corrected rank inequality does not assume feasibility or a circuit. Natural subtraction handles its coincident-point and deficient-row-map edge cases. The geometric interpretation as minimal-face dimension is used only for feasible points.

## Why nonvertex endpoint terms cannot be discarded

For d>=2, use coordinates `(z_1,...,z_(d-1),t)` and the balanced irredundant bounded polytope

```
0<=t<=1,   0<=z_i<=1+t.
```

All coordinates 1/2 are strictly feasible. Starting at the zero vertex, the displacement to the all-ones point is a row circuit: the d-1 independent upper-row normals annihilate it. The step is maximal at t=1, but its endpoint is in the relative interior of the top facet. Thus

```
h=d, p=0, q=d-1, delta=0, source-active defect=d-1.
```

The generalized inequality is sharp and the first common carrier is the whole parent. Raising the z_i one at a time from 1 to 2 completes a d-step circuit walk to a vertex, with carrier dimensions d,d-1,...,1.

There is nevertheless an explicit d-edge route: raise t first while keeping the z_i zero, then raise each z_i from zero to two. At each circuit checkpoint choose a vertex preserving all tight rows by placing the remaining free coordinates at zero. This supplies compatible cheap portals in this family. The example refutes automatic small/proper first carriers, NOT polynomial edge refinement.

## Conditional routing, not an assumed global cost bound

For any feasible checkpoint sequence in one compact parent, with vertex endpoints, the common carriers are closed extreme faces. Face-preserving selection rounds intermediate checkpoints compatibly. If the carrier diameter budgets B_i are supplied, the checked feasible-face-cover theorem gives a route with total budget sum B_i. The new routing module only specializes that theorem and keeps every B_i as a hypothesis. It charges occurrences; repeated carriers can instead use the existing distinct-face theorem.

Source-active neutral rows on y-x are exactly C, so source-active defect is h-1. The already present defect identity is a local recognition test, not a new independently decreasing potential. If the first carrier is the entire parent, assuming a polynomial budget for it would be circular.

## Executed checks and boundaries

The unchanged exact checkpoint script was rerun twice in this integration session. Both outputs matched SHA-256 `ac80905f0ae4669f3ee86a51abd8b85773287e98186a16a20284caa87b3c3126`:

- 6,519 point pairs on 25 models;
- 943 circuit pairs, including 198 vertex-circuit pairs;
- 5,834 pairs with a nonvertex endpoint;
- 5,576 positive all-neutral-defect pairs;
- 691 tight generalized inequalities;
- sharp balanced examples through dimension 8.

Pair selection is capped at 350 per model; this is not an all-pairs claim for every model. The sharp family uses its complete binary vertex formula, with exhaustive row-basis vertex reconstruction only through dimension 4. The Python certificates are finite checks, NOT Lean proofs.

Seven independent gate control-flow tests passed using explicitly SYNTHETIC regression fixtures. They check unknown arguments, wrong Lean/Mathlib pins, disabled Python assertions, corrupt hashes, checks-only status, and failing-compiler behavior. No synthetic test produces a kernel-success receipt. These are software tests, not additional geometric instances.

Python AST parsing, shell syntax, changed-workflow trigger/setup checks, and lexical admission checks passed. The two imported older regression suites were preserved byte-for-byte but were NOT rerun in this session. The full combined mathematical/Lean gate has NOT been executed.

## Local verification and publication gate

```
bash scripts/verify_circuit_checkpoint_continuation.sh --checks-only
bash scripts/verify_circuit_checkpoint_continuation.sh
```

The gate checks exact pins, all three regression outputs, targeted source compilation, and 28 FRESH axiom reports from a separate audit file. It does not rely on cached build output containing all #print lines. Its receipt explicitly says no standalone server proof or Prove2Me verdict is implied.

`.github/workflows/circuit-checkpoint-final.yml` is manual-only and uses the shared pinned setup action. Use hosted verification only after local compilation, not as an edit/compile loop. This session had no Lean installation, container network access failed, and the available GitHub connector has no workflow-dispatch operation. No new hosted job was started.

After the source gate is actually green, prepare a public-vocabulary solution adapter and flattened proof, compile and audit those independently, refresh the upstream platform skill/version, perform collision-safe authenticated publication, and re-read the verdict. Do not publish these candidates before those gates. No API key or credential belongs in source, logs, or artifacts.

Polynomial Hirsch is not solved. Keep `Hirsch.polynomial_edge_refinement_of_circuit_walks` (`099c6686-560c-48fc-b2c2-18b6a620a06e`) as the sole Open frontier; no new equivalent or cyclic child is proposed. No literature-priority claim is made.
