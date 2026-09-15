# Handoff: compulsory uphill defect repair, not another neutral plateau

Base main: 2c517a877e8aab885ae1583d97fc2e2ae6d9b017.
Coordination #263 comment5689268988; distinct from #264 plateau and the
cactus-incidence/graphical-refinement work also claimed there.

## Exact new result

For ANY proper finite complex K on n actual vertices, take the classical
building set consisting of singletons and ALL nonfaces. Its nestohedron is a
simple(n-1)-polytope. The higher minimal nonfaces of its dual are exactly K's
higher minimal nonfaces on the designated singleton labels. Original facets
are all proper building-set members, not merely those n singleton labels.
The explicit integer H-system and complete nested faces are derived in the note.
The realization can have exponentially many facets; caps fail rather than
produce incomplete incidence or geometry claims.

For a Steiner triple system, every first subdivision of a pair of GROUND
singleton labels removes one old triple but forces n-3 distinct newborn
triples. This remains true after ANY preceding subdivisions involving outside-
ground labels. The old induced complex is unchanged until that first pair.
Therefore EVERY flagification, or even net-W-decreasing sequence, reaches
W>=W0+n-4. Auxiliary preparation can be arbitrarily long; this is not a
bounded-search claim. Binary systems n=2^r-1 give required debt d-3, unbounded.

The actual Fano nestohedron has d6,m70,1050 vertices/3150 edges, W7.
An explicit11-step word attains weights7,10,8,6,9,7,5,4,3,2,1,0. Minimum peak10
is proved by lower+upper arguments; minimum LENGTH11 is not claimed. Its final
flag refinement has81 vertices and bound75. Original exact diameter is12;
classical permutation sorting provides all-pairs bound21 independently. These
are not long-diameter examples or a failure of Polynomial Hirsch.

## Preserve these distinctions

- The ground labels are a subset of the ORIGINAL facets. Outside-ground
  labels include other original facets as well as newly inserted vertices.
- Input-realizing face subdivisions (63 for Fano) are NOT counted as the
  eleven later edge-repair operations.
- Arbitrary K need not be pure/polytopal; the explicit nestohedron is.
- The universal lower barrier follows from induced-face preservation and
  minimality of the forced triples, not from trying all first moves at the
  initial state or a finite number of auxiliary prefixes.
- Required weight peak is not a lower bound on operation count or diameter.
- No constant debt allowance can work universally. Polynomial debt/length
  bounds and higher-dimensional subdivisions are not excluded by this result.
- The general direct sorting bound is classical for generalized permutohedra,
  not a new polynomial-diameter theorem for arbitrary polytopes.
- The complete Fano original and refined graphs ARE enumerated. Only the
  sorting producer avoids a supplied graph; choosing endpoint orders generally
  is not advertised as an efficient unknown-H recognizer.
- Larger binary r4/r5 cases check designs only; no nestohedron graph is built.

## Sources and reproducibility

New files: nestohedral_defect_barrier.py and test_nestohedral_defect_barrier.py.
They import two EXACT unchanged dependencies:

- stellar_defect_budget.py, Git blob b51e2c3edec2c85026344566978561eb430050ec;
- simple_tangent_policy_audit.py, blob73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976.

    python3 -m py_compile scripts/nestohedral_defect_barrier.py scripts/test_nestohedral_defect_barrier.py
    python3 scripts/test_nestohedral_defect_barrier.py

Individual stages: algebra, family, geometry, negative, assemble. Run geometry
before negative because its saved-packet controls require the generated fixture.
The saved auditor N.audit_saved(fixture) checks the model, barrier, full weight
history, witnesses, carriers and sorting edges with discovery disabled. It does
not recompute the stored exact graph diameter; that field comes from the full
geometry stage. Original H-data and proofs are hash-bound in the reports.

The final full suite has48 abstract realizations,96 arbitrary auxiliary-prefix
checks,591 first-pair design cases,one complete6D nestohedron,66924 intermediate
carrier checks,32 paired route comparisons and22 rejected controls. Refined
routes237 edges versus230 shortest, sorting263;7/17 nonshortest respectively.
Do not quote superiority or shortestness for those sampled constructed routes.

This is research-only. No Lean file, Actions gate, axiom audit, Prove2Me packet,
submission, credential change or accepted-source edit is included. The next
agent should pursue a genuinely global variable-debt ledger or a bypass route,
not republish the already refuted zero/fixed-debt assumption.
