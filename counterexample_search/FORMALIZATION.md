# Scalar-fiber obstruction formalization status

The two general mathematical obstruction arguments from `RESEARCH.md` are now
represented on Prove2Me as Open Lean formalization targets in the original
Polynomial Hirsch environment (Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`).

The shared formal model compiled locally before publication and was published as:

- `Hirsch_scalar_fiber_model` — Definition
  - Prove2Me ID: `59af3151-06aa-45f7-a758-293ca1fc5a83`
  - Defines `ScalarHeightFiber`, `EndpointWalkLE`, `StrictHeightEdgeWalk`,
    `VertexCover`, and `EdgeCover`.

Published theorem targets:

1. `Hirsch.scalar_height_fiber_monotone_path_bound` — Open
   - Prove2Me ID: `fcbddd0a-3ee0-42e9-8def-df3d4292ec73`
   - Formalizes the additive synchronization bound
     `1 + sum_i (L_i - 1)` for strictly height-decreasing factor edge paths.
   - The Q28 six-edge path gives the research consequence `5*k + 1` for
     independently scalar-glued/projectively skewed copies.

2. `Hirsch.scalar_height_fiber_diameter_linear` — Open
   - Prove2Me ID: `b372d4fc-5bbd-4d32-96fc-d6d560d70422`
   - Formalizes the bound `sum_i (3*v_i + e_i - 1)` using explicit finite
     vertex and undirected-edge covers for nonempty compact convex seed sets.
   - For Q28 (`v=274`, `e=720`) this yields `1541*k`.

These are not attached as children of the main Polynomial Hirsch leaf: proving
either obstruction does not prove that leaf. They record class-wide limitations
on scalar-height amplification and are useful standalone progress/results.

The exact definition and both `by sorry` theorem declarations compiled in the
pinned environment before the API publication calls were allowed to run.
The initial publication workflow's publication step succeeded; its final GitHub
artifact-finalization step received a separate 403 after publication and did not
affect Prove2Me state.
