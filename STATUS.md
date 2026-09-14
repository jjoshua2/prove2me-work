# Current Polynomial Hirsch frontier

Repository: `jjoshua2/prove2me-work`. GitHub state refreshed 2026-09-13.
Keep Lean `v4.30.0` and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Read this file, AGENTS.md, CLOUD_AGENT.md, SKILL.md and CONTINUE_HIRSCH.md,
then the LIVE PR heads/comments before choosing work. Historical next-step
paragraphs are not evidence that a later accepted result remains unproved.

The previous status overview is preserved verbatim in
[the frontier archive](research/FRONTIER_ARCHIVE_BEFORE_CHECKED_DUAL_TESTS_2026-09-13.md),
Git blob `256e16e82e9b7679fe08d38f410be1c14e5881e4`. Its older proof history,
mission discussion IDs, cost bounds and receipts have not been discarded.

## The mathematical objective

The last authenticated mission audit preserved in the archive reports the
Polynomial Hirsch root `58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` Open and the six
curated milestones Proved. Its remaining open leaf is
`Hirsch.common_face_diameter_of_dim_ge_six`,
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`.
This GitHub refresh is NOT a new authenticated poll of that root or leaf.

The objective remains a uniform ordinary-edge diameter bound for arbitrary
high-dimensional common faces, with constants independent of dimension.
Auxiliary nonnegative-kernel circuits and their normalized-section vertices
are not ordinary edges or vertices of the original polytope. Finite exact
allocation tests alone do not prove a polynomial graph-diameter bound.

The integrated clipping framework selects actual portal pairs before charging
their local route costs. Fixed support deficit, small intrinsic excess, low
dimension, and the verified sufficient geometric models already have their
own estimates. Arbitrary high-dimensional carriers and cross-level control
of repeated charges are not discharged by a factor-three mass bound alone.
Reuse the archive and the public-results inventory rather than reproving
Santos, circuit walks, fixed-dimensional bounds or accepted repair lemmas.

## Accepted algebraic and allocation results: do not resubmit

Every row below has its own accepted-evidence/receipt under its packet.
Read the exact statement before composing it; an informal description is not
an extra hypothesis or a stronger conclusion.

| PR | Accepted result | Packet under research/publication_packets/ |
|---|---|---|
| #216 | Compact-convex whole-set sufficiency from weighted tests | [compact_dual_minkowski](research/publication_packets/compact_dual_minkowski/) |
| #218 | One support-indexed positive-circuit family tests the whole nonnegative kernel | [finite_positive_circuit_tests](research/publication_packets/finite_positive_circuit_tests/) |
| #219 | Bounded-simplex allocation alternative and finite whole-set Minkowski criterion | [finite_allocation_minkowski](research/publication_packets/finite_allocation_minkowski/) |
| #221 | Exact original-H primal/dual support witnesses | Inspect #221's merged packet and receipt |
| #222 | Signed-kernel characterization and rank-plus-one circuit support cutoff | [positive_circuit_rank](research/publication_packets/positive_circuit_rank/) |
| #224 | Normalized positive circuits are exactly auxiliary kernel-section extreme points | [normalized_circuit_vertices](research/publication_packets/normalized_circuit_vertices/) |
| #227 | Pointwise allocation tests collapse to scalar budgets given exact support witnesses | [finite_allocation_support_budgets](research/publication_packets/finite_allocation_support_budgets/) |
| #229 | Actual rational Boolean checker/output filter gives exactly all normalized REAL circuits | [checked_circuit_catalogue](research/publication_packets/checked_circuit_catalogue/) |
| #230 | Supplied finite row identities imply a one-ray restricted kernel | [rref_restricted_kernel_certificate](research/publication_packets/rref_restricted_kernel_certificate/) |
| #233 | The ACTUAL checked catalogue tests every real linear functional on the entire nonnegative kernel | [checked_catalogue_dual_tests](research/publication_packets/checked_catalogue_dual_tests/) |
| #234 | Full allocation alternative for separate, overlapping and signed budgets with finite coverage | [covering_allocation_alternative](research/publication_packets/covering_allocation_alternative/) |
| #235 | External minimal joint circuits have exact support multipliers, nonnegative deficits and a common-maximizer zero pattern | [joint_circuit_support_deficits](research/publication_packets/joint_circuit_support_deficits/) |

#229 theorem: `49468d71-eb2e-4908-a15e-a89d1d23622a`;
submission: `0dcf5eea-df74-4295-9a5e-c71edb96589d`, ACCEPTED.
Its checker certifies omitted supports as well as emitted rays; catalogue
completeness is no longer an open obligation. Python producer/auditor code is
committed, but arbitrary JSON does not become kernel-certified without
instantiating and evaluating the Lean checker.

#230 theorem: `4a5d83c2-d0fa-4e24-93b2-29bb39eb55e8`;
submission: `de82dc98-0819-4305-968d-cff93ef9ada6`, ACCEPTED.
Use its actual column-identity assumptions; it is not an unconditional
correctness theorem for an imperative row-reduction implementation.

## Accepted concrete catalogue bridge: PR #233

Public name: `Hirsch.checked_rational_catalogue_dual_tests`.
Theorem: `3999b5a0-22c8-44a5-9886-6838b03fd07f`.
Submission: `c31a55eb-d210-4678-8401-fed4f4d005bd`, **ACCEPTED**;
authenticated publisher readback: **Proved**.
See [accepted evidence](research/publication_packets/checked_catalogue_dual_tests/accepted-evidence.md)
and the unchanged downloaded publication-receipt.json beside it.

For the ACTUAL catalogue C returned by #229's passing finite arithmetic check,
this proves, for EVERY real linear functional B,

```text
B(w) >= 0 for every real w >= 0 with A*w=0
  iff
B(cast(q)) >= 0 for every q in C.
```

The proof normalizes the accepted negative support-minimal witness, transports
its support predicate, and invokes the checked catalogue's real completeness.
It does not assume completeness as an oracle. The helper `checked_rhs_tests`
specializes B to arbitrary real RHS pairings. Of 711 standalone source lines,
571 reuse accepted proof blocks unchanged; 140 contain the new bridge,
specialization, statement adapter and axiom printouts.

The FIRST prepared gate and first authenticated submission succeeded in run
`34790147221`, frozen head `8da78fd4f3d880fa053446d8170e11aa501cb43e`.
Driver, solution and statement all compiled with exit code zero; all three
printed declarations use only `propext`, `Classical.choice`, `Quot.sound`
transitively. No proof edit, retry or duplicate registration was needed.
Solution SHA-256: `5f661c7b4bff18859b12611e4f2b3b8f72be0100bd99a75a3fcd09a6609d1897`.
Both verification and publication archives were downloaded, hash-checked,
and preserved as raw records plus explicitly derived inspection summaries.
The prior verification-evidence.md is a historical intermediate record,
not a reason to resume this now-ACCEPTED submission. Do not resubmit #233.

## Accepted covering-budget alternative: PR #234

Public name: `Hirsch.covering_budget_allocation_alternative`.
Theorem: `124be5aa-74ac-45b3-be3b-f02f8f9d4242`.
Submission: `81b93d5c-1b53-4c6c-9074-7d5c8eb9d736`, **ACCEPTED**;
authenticated publisher readback: **Proved**.
Proof head `fb182322048816ba626cb6f1c821d4cb332224d3`, run `34790733652`.
Merged in `6a2eabd05dc79ced01c5ce74d194dece1014a368`.
See [accepted evidence](research/publication_packets/covering_allocation_alternative/accepted-evidence.md)
and the raw packet audit, verified manifest and publication receipt beside it.

For actual constraint rows a and resource rows B, supplied rho>=0 with
B^T*rho>=1 gives the full nonnegative allocation alternative for a*x<=b,
B*x<=t. Right sides and individual B coefficients may be signed. All original
budgets are retained; the extra redundant total-mass multiplier is absorbed
into budget and nonnegativity multipliers. No Farkas, strict-feasibility,
full-rank or already-feasible-allocation premise is assumed. Coverage remains
an explicit finite condition.

The original 427-line candidate passed its first prepared compile/axiom gate
and first submission unchanged. All three compile exit codes are zero; all
four audited declarations use only standard logical axioms. Source SHA-256:
`0f3b70e88d6b989ccf2d3cc16676258ae714b6c05eefb49a9ba109a8729f7b3e`.
The old blocked-commit/uncompiled notes are superseded for this exact packet.
They are not evidence that another covering alternative needs to be written.
Do not resubmit #234. This acceptance does not verify the older 1170-line
one-block composition or the entire multi-block Minkowski adapter.

## Accepted joint-circuit sign and zero-pattern theorem: PR #235

Public name: `Hirsch.joint_external_circuit_support_and_zero_deficit`.
Theorem: `215a5bbf-fda4-467b-9e99-8714e6ec007b`.
Submission: `108c2171-0be9-48bd-a1f2-191f35f8b6fc`, **ACCEPTED**;
authenticated publisher live readback: **Proved**.
Frozen head `e78b966247f66bbe3906851395a1fd63bfb243b0`, run `34791096717`.
Read [accepted evidence](research/publication_packets/joint_circuit_support_deficits/accepted-evidence.md)
and [the handoff](research/JOINT_CIRCUIT_HANDOFF_2026-09-13.md).
The old local-only candidate passed its FIRST prepared compile/axiom gate and
first platform submission unchanged. All three compile exits are zero and all
four audited declarations use only standard logical axioms. Post-gate work
preserves raw receipts, full compile logs and the exact tested Python source;
it does not alter the proof, problem or frozen explanation. No retry occurred.

For external support-minimal nonnegative null multipliers of the actual
independent simplex-block allocation rows, each total multiplier is the
attained support of the combined original rows. Thus valid nonnegative
candidate support bounds give nonnegative packing deficits Gamma. Gamma=0
iff one listed point (including the anchor) attains every positively weighted
row bound. This supplies exact coefficient signs and their zero pattern,
not an original-H support optimizer or an ordinary-edge bound. Empty,
repeated and dependent generator lists are included.

Internal-only multipliers instead give automatic budgets at nonnegative scales.
External nonminimal multipliers can have negative deficits: keep full support
minimality from #218/#229, rather than inferring it from #219's weaker public
nonnegative-null invariant. The named Solutions mirror in the earlier local
bundle has no separate module-build claim; the verified source here is the
standalone publication packet. The committed regression script checks 59
systems and 267 circuits; this software evidence is distinct from Lean proof.
Do not resubmit #235 or label its universal tightening routine Lean-extracted.

## Next exact proof obligation

Compose #233's ACTUAL catalogue tests with the accepted allocation alternatives,
not with a newly assumed Farkas or catalogue-completeness statement.
For one simplex, explicitly reindex J=Fin m+Option(Fin k) and the transpose of
`(-aG,-I,ones)` into the rational checker's coordinate type. Prove row-sum and
RHS pairing transport for arbitrary real weights, then apply #219.

For multiple candidate blocks or covering resource budgets, use #234 and
C=(-aG,-I,B). Independent simplex blocks have automatic coverage rho=1.
The actual point-dependent RHS is

```text
d(x,t)=(b-a(x)-H*t,0,t).
```

After coefficient/index binding, #233 supplies every real null test from the
actual emitted catalogue, and #234 produces one simultaneous feasible allocation.
This yields x=(x-G*theta)+G*theta in the claimed erosion-plus-allocation image.
Finally #227's exact original-H sharp support witnesses replace the universal
original-point tests by explicit scalar budgets. Retain valid candidate support
bounds, the shared scale vector, all original rows and every rational-to-real
coefficient correspondence. Overlapping resource budgets do not automatically
represent independent Minkowski summands; use their actual allocation image.
For independent simplex blocks, transport true circuit minimality to #235 to
derive nonnegative coefficients and discard automatic internal/zero rows.

See [the precise next interface](research/COVERING_CHECKED_COMPOSITION_NEXT.md).
The old local composition may provide proof ideas, but its catalogue-to-dual
subproof is now superseded by #233. Do not copy or republish completed ingredients.
This is one concrete adapter chain; do not publish new open children that
merely restate it. Useful shape selection and arbitrary residual ordinary-edge
routing remain separate mathematical problems even after this composition.

## PR lifecycle and retired ancestry

#233 and #234 are accepted and merged with exact evidence. Neither requires
another proof or publication run. #235 is also accepted with its receipts;
check GitHub for its final integration state before changing its branch.
Check live ownership before choosing the remaining adapter or a genuinely new
geometric routing obligation.

#208 remains the distinct additive-spill/portal-selection draft. Existing
submission `2a2dd9bd-9ee5-43fa-bc04-def26a5a2a98` is PENDING in its latest
persisted receipt. Poll that submission through the approved existing path;
do NOT resubmit. Its geometric selection/existence premise remains explicit.

#210 is CLOSED as a superseded historical research stack. Its branch
`formal/dual-wall-carrier-routing` at `11172b1165b31a81e8755bd9f88651a2a9ed4b8c`
and all research/fixtures remain retained. Do not merge its obsolete ancestry.
Clean integration successors are merged #225, #226, #228, #231 and #232.
#231's three residual modules passed `34785937763`; #232's two repaired
geometric cores passed clean-main run `34789669353` and merged as
`f452b23a06f0122c9b9dda774fadad1ed99813b7`. These are module builds, not new
Prove2Me acceptances. Historical UNCOMPILED source headers do not override
later successful receipts. #234 is the separate accepted covering-budget
packet; it was not silently included in those earlier integration merges.

## Execution discipline

Use the committed pin and local Lean when available. Source-text and exact
Python checks are not Lean verification. Hosted Actions are prepared final
gates, not a speculative edit/compile loop. Publish only a complete packet on
an open same-repository PR with a NEW top-level conversation comment:

    /prove2me publish research/publication_packets/PACKET

Read back the bot's exact SHA/run, audit logs/artifacts, and authenticated
verdict. Keep secrets only in the trusted main publisher. Preserve source
hashes and raw receipts before artifact expiry; distinguish derived summaries.
Keep completed/superseded PRs out of the active queue and update this handoff
when the recorded publication state changes.
