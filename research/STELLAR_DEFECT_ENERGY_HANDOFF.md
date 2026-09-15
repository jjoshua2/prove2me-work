# Stellar energy continuation: mixed absorption, branching, and plateau escape

## Read current live state before continuing

Prepared on main `13fd398df7dc224deccef4cd2c1506069ed042a3`, after #260/#261.
The research branch is `research/stellar-defect-energy`. Inspect its live PR
and main before reusing this snapshot. This is RESEARCH/CODE, not a Lean
packet, compile, axiom audit, or platform acceptance. No Actions/publication
run was requested. Keep the existing Lean/Mathlib pin and publisher isolation.

The initial coordination comment on #261 was blocked before creation and was
not retried by another route. Normal creation of this independent source branch
succeeded. Existing #244/#238/#250/#255/#208 and retired/reserved #210 were not
changed or triggered. No accepted or pending theorem was resubmitted.

## Exact new mathematics

Reuse #261's stellar membership formula and original carrier proof. For a face
edge E and fresh z, persistent minimal nonfaces are E, all old nonfaces not
containing E, descendants of old nonfaces containing E, and descendants of old
missing pairs touching E. Only mixed HIGHER descendants can add new generators.

The EXACT no-branch condition is: for every higher N meeting E in one endpoint,
there is old M with either E subset M or M a missing pair touching E, such that
M minus E is a subset of N minus E. This is necessary and sufficient, not just
an extra sufficient heuristic. Equal nonempty higher incidence is the special
case with no mixed N. Both old pairs AND higher both-endpoint descendants can
be absorbers. The full proof is STELLAR_DEFECT_ENERGY.md sections 1--2.

Let Phi=sum_high(|N|-2), c_E=#higher N containing E, and B_E be the total
(|D|-2) of ACTUAL surviving extra higher descendants after minimization. Then

    Phi(K_E)=Phi(K)-c_E+B_E.

Counting raw generated sets is not enough. No-branch productive moves strictly
decrease Phi. Branching may also help: the exact simple polytopal seed has
q12->13 while Phi19->16 (c4,B1). Higher support need not shrink, so #261's
support-descent estimate is not reused for arbitrary mixed steps.

## Genuine polytopal obstruction and positive repair

The ten integer paraboloid seed points and eight exact shallow ridge cuts are
in the note and test script. Exact all-active-basis seed enumeration followed
by proved cut completeness gives a simple6D original-H polytope with18 genuine
facets and164 vertices. Its complete higher list is

    {0,5,16}, {0,6,7}, {1,2,16}, {1,4,6}.

All115 possible dual face-edge subdivisions have nonnegative Delta Phi; twelve
productive edges each have c=B=1. Thus EVERY strict one-step Phi strategy stalls
at Phi4 on an ACTUAL polytopal sphere. This is not a diameter lower bound: the
complete original graph has diameter8.

The explicit four-step word (0,6),(0,5),(1,4),(2,16) has energies4,4,3,2,0.
The first two are a descending macro; the third branches but pays for itself.
It yields flag M22 and the classical/carrier ALL-PAIRS original bound16. The
older twin-only residual block has135 nonempty faces on8 labels and bound139.
These are certificate bounds, not actual shortest-distance comparisons.
The new generic two-step heuristic independently escapes in FIVE steps, not
four; its bound is17. Preserve this adverse distinction.

A product-with-interval followed by a shallow ridge cut along old label3 and
one new interval facet extends the obstruction to ALL d>=6, with m=3d,
Phi4, no strictly decreasing single move, and the same four-step repair. The
minimal-nonface incidence graph stays connected, excluding a nontrivial
combinatorial Cartesian product. This is not Minkowski indecomposability.
The final flag count3d+4 gives diameter<=2d+4. This is a special-family result,
not a new best general diameter bound. The all-d proof is in section6.

## Executed scope and independent checks

Two standalone standard-library scripts; no old source was patched. Core
stellar/carrier arguments are explicitly credited to #261. The all-4-label
antichain sweep plus random small complexes gives218 complexes and1910 literal
stellar comparisons. Counts:285 non-twin no-branch productive moves,19 energy-
decreasing branching moves,13 of which increase higher-defect count.

Six exact cyclic polars all stall under twins and all resolve under absorption;
their new t values are4,6,9,8,13,12. Original graphs have14,20,27,30,50,55 vertices.
They supply72 endpoint pairs/159 original edges versus156 BFS, with3 nonshortest.
The barrier gives40 pairs/159 original edges versus159 BFS. All318 edges are
checked against original inequalities, active-basis rank and maximal feasible
step. The finite reference router DOES enumerate the refined graph. Original
minimal-nonface classification is also potentially exponential. Neither is a
polynomial-H-size algorithm.

The family recurrence is checked for every r=0..64 (d6..70) without claiming
large original graph enumeration. Explicit full rational H lifts are only
r0/1/2:164/394/920 vertices. The four-step all-d argument, not a numerical
extrapolation, gives the larger-dimensional bound.

Fourteen invalid complex/ledger/schedule controls and five forged carrier
routes are rejected. The saved fixture audit reconstructs the exact seed and
cuts, recomputes complete nonfaces and all115 move balances, and checks40 saved
routes/159 original edges with no routing BFS. It does not recompute the
historical graph-diameter field. Its geometry table is not accepted on faith.

The complete `STELLAR_DEFECT_ENERGY_CHECK.json` is raw program output. The
replay/source manifests are explicitly derived local records. A clean directory
with ONLY the two source files reproduced every test field and both serialized
fixtures byte-for-byte; independent serialized checking passed. Python compiler
success is not Lean verification. Full fixtures and logs are in the download
and regenerate from the committed source.

    python3 scripts/test_stellar_defect_energy.py --stage all --out /tmp/energy.json --fixtures /tmp/energy-fixtures
    python3 scripts/test_stellar_defect_energy.py --verify-fixture /tmp/energy-fixtures/stellar-energy-barrier.json

## Highest-value next step

The general obstruction is now concrete: useful schedules may need actual
branching and a first move with no energy decrease. Search for a bounded escape
or amortized ledger that controls these plateaus ON POLYTOPAL spheres, while
also avoiding dependence on exponentially many initial higher nonfaces. The
current two-step search only tries productive edges; its universal completion
is NOT proved. A proof under an assumed cheap schedule or small residual core
would merely restate the missing ingredient. No new open child was published.

Root/leaf status is inherited from the last preserved authenticated audit in
STATUS, not a fresh direct platform poll. This turn creates no new verification
or publication state to resume. The research/code result should not be uploaded
as though it were a complete Lean proof packet.
