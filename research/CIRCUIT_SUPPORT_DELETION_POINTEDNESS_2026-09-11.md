# Circuit-support row deletion preserves pointedness

Date: 2026-09-11 (America/New_York)

Status while written: candidate formalization; focused hosted Lean verification pending. This note does not claim kernel verification or Prove2Me publication.

## Structural observation

For an injective row presentation and a row-circuit direction `g`, the neutral rows have kernel exactly `span {g}`. Therefore adding any single nonneutral row kills that last one-dimensional kernel: the neutral rows plus any one row `i` with `<a i,g> != 0` already have injective row evaluation.

Consequently, if the circuit has two distinct nonneutral rows `i` and `j`, deleting `j` preserves injectivity as long as `i` is retained. This is stronger than the earlier bounded-parent one-row-deletion lemma because it is local to a circuit support and requires no boundedness.

## Vertex-starting maximal steps

For a maximal row-circuit step `x -> y` whose source `x` is a parent vertex:

- feasibility plus vertex tight-row spanning forces some source-tight row `i` to decrease strictly along `y-x`;
- maximality supplies a destination-tight blocker `j` that increases strictly;
- the two rows are distinct and both are nonneutral.

Hence either the source row or the target blocker can be deleted while preserving injectivity of the remaining finite row presentation.

## Intended frontier use

This creates a genuine row-count descent interface for vertex-starting circuit steps in pointed presentations. In particular, once a noncompact carrier portal is rounded to a parent vertex, the next maximal circuit step has two certified one-row deletions that remain pointed.

The theorem does not by itself show that an edge route in the relaxed deletion outer can be repaired back to the original polyhedron. That clipping/repair cost remains the dynamic part of the ordinary-edge refinement problem.
