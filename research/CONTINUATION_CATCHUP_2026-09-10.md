# Polynomial Hirsch continuation catch-up — 2026-09-10

This note records work produced after the earlier September 10 research-status sweep and corrects one stale verification boundary on `main`.

## Formal state

Polynomial Hirsch is **not solved**. The unique formal Open frontier remains
`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`). Do not create an equivalent one-step or balanced reformulation as a supposedly smaller child.

### Compact simultaneous clipping is now kernel verified end-to-end

PR #53 (`chatgpt/verify-simultaneous-clipping`) repaired and completed the bounded all-final-vertex clipping chain. At commit
`446304d56513437aad9c0a02fc1d202e41783259`, Actions run `34485975796`:

- compiled the complete source chain plus public `theorem solution` adapter;
- generated the standalone proof deterministically from the exact source;
- independently compiled the flattened standalone proof;
- audited all required declarations and `solution` with only `propext`, `Classical.choice`, and `Quot.sound`;
- reproduced the exact carrier regressions.

Verified standalone SHA-256:
`fe83809fcda2cc6b2714193964e8f8be6ad2a1705ac4e3383b8dc6621736564f`.
Artifact `10155724751`, digest
`sha256:ff0ff54c263efd482cded2e7edba27324276094a143264adae49731ed6bbdcfe`.

The theorem is `HirschRadial.simultaneous_clipping_diameter_bound`. For compact convex outer `Q`, finite simultaneous halfspace cuts, outer padded diameter `D`, and intrinsic padded budgets `B_i` on the **final** exposed cut faces, it proves final padded diameter `D + sum_i B_i`. It covers final vertices created by the cuts and removes a separate strict-centre hypothesis via the strict-centre/universal-cut dichotomy. The `B_i` remain genuine assumptions; this is not Polynomial Hirsch.

The public Prove2Me adapter is `Solutions/Sol_Hirsch_simultaneous_clipping_diameter_of_compact_outer.lean`. Publication status is recorded separately in `research/PUBLICATION_UPDATE_2026-09-10.md`; do not infer platform acceptance merely from this local verification receipt.

### Exterior-cap theorem

`Hirsch.simultaneous_clip_diameter_of_exterior_cap`
(`2e20b0a7-503c-4be4-bd9c-446b88f77c8e`) is already Prove2Me **Proved**. Its formal scope assumes an explicit compact cap witness and classification of new cap vertices. The universal pointed-H-polyhedron cap-existence theorem remains ordinary mathematics unless separately formalized.

## Later ordinary-mathematics research — NOT Lean / NOT Proved

The following continuations have complete ordinary arguments and exact finite certificates, but no Lean verification yet. Keep that evidence boundary explicit.

### Balanced isometric circuit localization

`BalancedIsometricCircuitLocalization.md` proves the proposed localization bound for a vertex-to-vertex row-circuit displacement in an `N`-row `D`-polytope:

`h <= floor((N-D+1)/2)`

for the dimension `h` of the minimal common face. It also introduces an intrinsic circuit-rank defect `delta` after passing to a genuine facet presentation and derives the accounting inequality

`(f-h) + delta <= N-D`.

Exact examples show circuit status can disappear after redundant restricted inequalities are removed, even when the ambient circuit direction occurs as an actual edge elsewhere. A separate construction embeds the original polytope isometrically as a face of an exactly balanced ambient polytope while making the chosen pair a maximal circuit step. This is a hardness/localization diagnostic, not a solution.

### Optimal circuit-defect completion

`OptimalCircuitDefectCompletion.md` sharpens that bookkeeping. If the original facet excess is `e=n-d` and the neutral-rank defect of a selected displacement is `delta=d-1-r`, then among proper face-containing bounded extensions that restore the displacement to a circuit, the ordinary proof gives exact minimum ambient facet excess `e+delta` and minimum facet count `n+delta+1`, attained in dimension `d+1` while preserving every original vertex-pair distance. The claimed minimum exactly balanced ambient dimension is `max(d+1, n-d+delta)`. Requiring an external parallel realizing edge can cost one additional excess unit in the maximum-defect case.

These optimality statements have not been formalized in Lean and no literature-priority claim has been established.

## Literature triage

Current primary literature confirms several important boundaries:

- Borgwardt, Stephen, Yusun, *On the Circuit Diameter Conjecture* (arXiv:1611.08039): classical wedge equivalences do not transfer automatically to circuit diameter; realizations with the same combinatorics can have different circuit behavior.
- Borgwardt, Brugger, *Circuits in Extended Formulations* (Discrete Optimization 52 (2024), arXiv:2208.05467): circuits are not generally inherited under projection and the noninheritance gap can be exponential. Do not present representation sensitivity as new.
- Michael Todd, *An improved Kalai–Kleitman bound for the diameter of a polyhedron* (arXiv:1402.3579): supplies the established quasipolynomial diameter input used by the low-rank box continuation.
- Blanchard, De Loera, Louveaux, *On the Length of Monotone Paths in Polyhedra* (arXiv:2001.09575): supplies the established edge-direction/monotone-path input used by the linked-direction continuation.
- Bento Natura, *Circuit Diameter of Polyhedra is Strongly Polynomial* (arXiv:2602.06958, 2026): proves a strongly polynomial circuit-diameter bound, reinforcing that the remaining project frontier is the conversion to ordinary edges rather than availability of short circuit walks.
- Dadush, Kober, Koh, *On Circuit Diameter and Straight Line Complexity* (arXiv:2602.05699, 2026): gives additional strongly polynomial circuit-diameter results in structured systems and relates circuit diameter to straight-line complexity.
- Borgwardt, Grewe, Lee, *On the Combinatorial Diameters of Parallel and Series Connections* (arXiv:2203.09587): relevant to structured cross-block repair models; the hypotheses must be compared carefully before importing any connection bound.

No exact prior statement matching the later sharp defect-completion minima was located in this initial search. That is **not** evidence of novelty; a deeper literature review is required before any novelty claim.

## Platform/tooling note

During the bounded-theorem publication gate on 2026-09-10, authenticated `/agent/refresh` reported Prove2Me **0.9.9**. The first publisher attempt intentionally stopped because the repo-local skill still expected 0.9.8. The official `prove2me/prove2me_workspace` `SKILL.md` now reports version 0.9.9. Future authenticated agents must refresh the upstream skill/reference material rather than weakening the version check.

## Next useful formalization

After the bounded clipping theorem is published, the best small non-cyclic Lean target from the ordinary research is the circuit-localization / defect accounting layer, not single-step universality as a new Open child. In particular, formalize the active-row/common-face rank facts needed for

`2*h <= N-D+1`

and then the genuine-face defect accounting. Only promote those statements if their Lean versions preserve the geometric hypotheses used in the ordinary proofs. The larger optimal-completion construction should wait for that foundation.
