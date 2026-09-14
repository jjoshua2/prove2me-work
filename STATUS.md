# Current Polynomial Hirsch frontier

Repository `jjoshua2/prove2me-work`; refreshed September 14, 2026 UTC.
Keep Lean `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Read this file, AGENTS.md, CLOUD_AGENT.md, SKILL.md and CONTINUE_HIRSCH.md,
then inspect LIVE PR heads, comments and receipts before choosing work.

The preceding complete overview through accepted #240 is retained VERBATIM in
[the previous frontier](research/FRONTIER_BEFORE_GENERIC_FIBRE_2026-09-14.md),
Git blob `4ed959bb035a2a76dda1bb9e8dc6fd841afdca28`. Its publication IDs,
source hashes, limitations, older archives and geometric estimates remain
available. This shorter current index does not discard their evidence.

## Objective and root status

The last preserved authenticated mission audit reports the Polynomial Hirsch
root `58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` Open, all six curated milestones
Proved, and open leaf `Hirsch.common_face_diameter_of_dim_ge_six`,
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`. This GitHub refresh is NOT a new
authenticated root/leaf poll. The uniform arbitrary-carrier ordinary-edge
diameter bound is not established by the results below.

The clipping framework already selects actual portal pairs and controls
certain sums of their intrinsic sizes. Fixed support deficit, small excess,
low dimension and verified geometric models have their own bounds. Auxiliary
circuits and normalized multiplier vertices are not original polytope edges.
A factor-three sibling mass estimate alone does not close a polynomial
recurrence; an exact decomposition test alone does not find useful summands.

## Accepted ingredients: do not reprove or resubmit

Read the exact packet and its own authenticated receipt before composing it.

| PR | Exact role | Packet under research/publication_packets/ |
|---|---|---|
| #216 | Compact weighted tests imply simultaneous whole-set feasibility | compact_dual_minkowski |
| #218 | Fixed positive-circuit family tests the nonnegative kernel | finite_positive_circuit_tests |
| #219 | Bounded-simplex alternative and finite Minkowski criterion | finite_allocation_minkowski |
| #221 | Original-H primal/dual support interface | See the merged #221 packet |
| #222 | Signed-kernel characterization and rank-plus-one support cutoff | positive_circuit_rank |
| #224 | Normalized circuits equal auxiliary-section extreme points | normalized_circuit_vertices |
| #227 | Pointwise criterion plus sharp support witnesses gives scalar budgets | finite_allocation_support_budgets |
| #229 | Actual finite rational checker/output is the complete REAL circuit catalogue | checked_circuit_catalogue |
| #230 | Finite column identities certify a one-ray restricted kernel | rref_restricted_kernel_certificate |
| #233 | Actual checked output tests every real nonnegative null vector | checked_catalogue_dual_tests |
| #234 | Covering resource budgets have a full allocation alternative | covering_allocation_alternative |
| #235 | External minimal circuits: exact support, nonnegative deficits, zero pattern | joint_circuit_support_deficits |
| #236 | Actual catalogue, matrix binding, allocation, geometry and sharp budgets compose | checked_covering_support_budgets |
| #237 | Coverage iff normalized nonnegative resource recession is absent | coverage_recession_alternative |
| #239 | Additive count for finite affine-envelope exposed-edge certificates | simultaneous_envelope_edges |
| #240 | Construct whole exposed Minkowski bridges over exposed core edges | generic_minkowski_edge_lift |
| #242 | Construct generic endpoint-preserving objectives with no independent ties | generic_fibre_objectives |

#236 is the completed checked-output-to-geometric-budget adapter, not an open
composition task. #237 concerns bounded COEFFICIENT sets, not automatically
bounded images: B=0,G=0 has unbounded coefficients and image {0}. #235 needs
full circuit support minimality, not merely externality and nullness. Python
producers and JSON readers are not Lean-extracted; passing their tests does
not individually kernel-certify arbitrary finite input data.

## New accepted genericity theorem: PR #242

`Hirsch.generic_fibre_objectives_without_independent_ties` is ACCEPTED;
theorem `d323320e-6843-4743-a2ea-e46b770cb3c8`, submission
`4ac637cb-f9c4-47fe-9bc2-8d435e539177`. The authenticated publisher receipt
records live Proved. Frozen proof `0e9c7ad7ea0e46623df0718564f0917ac50f027a`,
run `34798475975`. See [accepted evidence](research/publication_packets/generic_fibre_objectives/accepted-evidence.md)
and [the handoff](research/GENERIC_FIBRE_HANDOFF.md). Do not resubmit.

The theorem constructs objectives f,g inside two supplied nonempty finite
strict endpoint cones. On a finite list of nonzero differences it excludes
independent simultaneous ties along the ENTIRE affine objective line, by
proving the corresponding two-by-two determinants nonzero. A helper preserves
shared strict core comparisons on the closed interval. Empty index types and
arbitrary real vector spaces are retained; genericity is not an input oracle.

The 165-line proof commands and target are unchanged from the old local
candidate. The first workflow stopped before Lean because the raw admission
scanner matched an English word in a comment. Changing that prose word only
allowed the first actual compilation and first actual platform submission to
pass. All three compile exits are zero; all five audited declarations use
only propext, Classical.choice and Quot.sound. Raw logs, audit, manifest and
publication receipt are preserved; both ZIPs and all five hashes were checked.
No verifier, pin, workflow, allowlist or secret-separation change occurred.

## New compiled crossing geometry: same PR, separate evidence

`Solutions.PolynomialEnvelopeCrossingEdges` passed module-only run
`34799074798` at `ad42bf00ef2d5b79ae6211529cba4efedbc97066`.
Source blob `3c3695a01b2e7b0474c86111184c01c2dea53649`.
The exact two-site repair from the failed first module gate is preserved;
no theorem statement or mathematical hypothesis changed.

`crossing_support_segments` derives every ENTIRE component supporting slice
from actual finite left/wall/right maximizing comparisons and parallel ties.
`affine_crossing_exposed_edge` derives the global supporting-slice equality
and actual Hirsch.Adj, including summed endpoint nondegeneracy. It reuses the
integrated Minkowski support assembler rather than assuming an exposed edge.

IMPORTANT: the module-only artifact records successful Lake compilation, but
the trusted builder discards successful stdout. No independent printed-axiom
list for this module is retained, and no separate platform submission exists.
Do not transfer #242's public packet audit or ACCEPTED status to this module.
Its exact artifact and labeled inspection are in
[the current verification folder](research/verification/generic-fibre-current/).

## Next exact formal task and mathematical applicability

The next task is the FINITE CROSSING-SEQUENCE ASSEMBLY, not another genericity
or bridge-existence theorem. Instantiate #242 on actual nonzero within-factor
differences and endpoint comparisons. Form and sort the finite interior roots,
choose interval samples, prove unique winners persist and neighboring winners
are wall maxima, discard stationary repetitions, and apply the new crossing
module. Feed the retained strictly increasing samples into #239's count and
concatenate with #240's actual bridges. Endpoint membership and stationary
zero-step cases must remain explicit. See
[the detailed proof/interface note](research/GENERIC_FIBRE_CROSSING_PROGRESS.md).

For a given decomposition R=P+sum Q_i, the written geometric lifting bound is
L+(L+1)K, where L is the core walk and K=sum_i(f0(Q_i)-1). For ACTUAL selected
carriers with bounded core cost and K controlled by intrinsic dimension, the
existing mass accounting gives useful polynomial costs. Such controlled
decompositions are NOT established for arbitrary high-dimensional carriers.
A different method is needed where those models do not apply. Do not turn
this applicability condition into a supposedly solved premise or publish an
open child merely restating it.

The deterministic exact scripts are now committed. Their rerun covers 85
paths/103 edges, 82 whole-sum audits, 3465 edge/tuple checks and 17 rejected
controls. A clean replay reproduces the receipt and fixtures exactly. The
32D example has 24 fibre edges and budget 48 without enumerating 9.32 trillion
raw point tuples; this is not a distinct-vertex count. Supplied finite factor
presentations and exposed endpoints are inputs, not discovered H-decompositions.

## Live work queue and execution discipline

#238 owns strict original-H support-witness existence. #241 owns bounded-image
compact representatives. Inspect their current states rather than duplicating
them. #208 retains its distinct additive-spill/portal-selection line; its last
persisted submission `2a2dd9bd-9ee5-43fa-bc04-def26a5a2a98` is PENDING, not a
freshly polled verdict in this turn. Do not resubmit it. #210 is retired/reserved
historical ancestry; do not modify, trigger or merge it without reassignment.
#239/#240 are accepted and merged. #242 is accepted with its companion build;
check live integration state before changing that branch or rerunning anything.

Use local pinned Lean where available. This runtime lacked Lean/Lake; exact
Python/source checks were not represented as compilation. Hosted gates are
prepared final checks, not speculative edit/compile loops. Post real new
top-level comments on open same-repository PRs, read them back, and follow the
resolved PROOF SHA through jobs, logs, artifacts and authenticated verdict.
Preserve raw records separately from derived summaries. Compilation, axiom
audit, ACCEPTED and live Proved are distinct claims. No accepted/pending packet
is resubmitted and no secrets leave the trusted main publisher.
