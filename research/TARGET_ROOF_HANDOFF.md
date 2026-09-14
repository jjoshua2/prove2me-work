# Target-roof continuation handoff

Base main: `8a124f0e9db9d330cc3733b7ca39cf37ec0219ae`.
New branch: `research/target-roof-constant-face-phase`.
Coordination on #250: comments5672070606 and5672145693. The other agent owns
its accepted adaptive-face-locking theorem and integration; do not republish it.

## Exact distinction

#249 defeats only initial common-face restriction. #250's adaptive locking
improves that example. This NEW roof has exactly3d original facets and a target
strictly interior to all the OLD cube inequalities. Every other old vertex is
strict inside every NEW target inequality. Their midpoint is strictly interior,
so the common face remains the whole polytope for2^d-2 genuine edges. Canonical
active-row normalized gain then finishes in d-1 more locked edges after the
first roof hit, total2^d+d-2. A different, explicit c-monotone original route has
d edges. This is not a graph-diameter lower bound.

The general target-hiding lemma and explicit tail/comparison proofs are in
TARGET_ROOF_CONSTANT_FACE_BARRIER.md. Do not turn the observed full-gain d-step
trajectories into a universal polynomial guarantee, or identify the canonical
height with #248's actual default LP height without replaying it.

## Local checks

    python3 -m py_compile scripts/target_roof_phase_barrier.py scripts/test_target_roof_phase_barrier.py
    python3 scripts/test_target_roof_phase_barrier.py --dimension 4
    python3 scripts/test_target_roof_phase_barrier.py --dimension 12
    python3 scripts/test_target_roof_phase_barrier.py --aux
    python3 scripts/test_target_roof_phase_barrier.py --assemble

Run all dimensions2..12 before assembly. A no-argument call runs everything.
The completed12D regression is a local Python computation, not an Actions job.
The exact first-acquisition CLI writes a PHASE certificate, not a claimed full
route. Complete locked-route checks are in execute_locked/audit_locked_route.
The full-gain comparator is the unchanged #249 implementation.

Frozen dependency: scripts/simple_tangent_policy_audit.py, Git blob
73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976. It is bundled for standalone testing,
but is NOT a modification or addition in the incremental patch.

The small complete H-graphs use SymPy only as an independent test oracle.
Production rays and verifiers receive no neighbor lists. The verifier uses
T*D=-I and actual original-row ratios; it succeeds with inversion disabled.
For locked faces, signed dual coefficients are allowed ONLY on locked equality
rows. All other coefficients stay nonnegative. Initial full-face checks use
strict midpoint feasibility against every original row, not an assumed facet
intersection catalogue.

## Evidence and limits

Full d2..12:8243 locked edges,8166 constant-full-face edges,8177 first-acquisition
prefix edges,77 constructed comparison edges,77 completed-gain edges,231 facet
anchors. Three independent graphs:50 vertices/87 edges, distances2/3/4.
Seventeen rejected controls. Large d16/32/64: four selected phase steps each;
full exponential trajectories and large comparison paths are formula-only.

This packet is deliberately RESEARCH/CODE. Local Lean is unavailable; there is
no new Lean file, compile/axiom claim, publication gate or Prove2Me acceptance.
The existing accepted edge-validity and face-locking statements are unchanged.
The mathematical claims are written proofs, with exact finite regression checks
as separate supporting evidence. No global polynomial bound is established.

Next useful work is a positive phase-exit guarantee or selector analysis beyond
canonical normalized derivative, or a careful replay of the default LP-selected
height on this new input. Do not attempt to prove the already-refuted bound
from valid edges + canonical normalized progress + adaptive face locking alone.
