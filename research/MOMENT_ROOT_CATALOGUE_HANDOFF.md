# PR #299: exact original moment-vertex catalogue — ACCEPTED

Read live STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and actual open PR
heads/comments before continuing. No accepted or pending theorem needs a duplicate
submission. Initial inspection main9d1994b8a27b505455179777c5e99d08ec49bc05;
branch base ad7284ebacca004ab48987796c0d1b34e85822e6 preserves newer #297.
Coordination #295 comment5720578881 was posted/read back. #296 sliding-block
routes, #297 cut-coordinate catalogue, concurrent #298 local pivot, all older
owned work and reserved #210 were left untouched.

## Accepted result and immutable receipt

Hirsch.moment_root_polynomial_vertex_catalogue is ACCEPTED/live Proved.
Theorem42f4500a-b696-4451-9d49-a13c7a2f98e5, submission40c8e1bb-8669-473c-8262-9c6523b8f24e.
Proof f5f8093b1be2815dba7329b08cbd04493ff09140, run35270250702.
NEW conversation trigger5720698587; exact-SHA acknowledgement5720700975;
authenticated verdict5720740558. Trusted workflow main d17513f45e297c1c3aa08d266d65c9a109c67673.
The first compiler/axiom gate and first actual submission both passed unchanged.
All three compile exit codes zero; five transitive proof reports contain only
propext, Classical.choice and Quot.sound. No repair or second command.

Read publication_packets/moment_root_vertex_catalogue/accepted-evidence.md,
publication-receipt.json and packet-audit.json. Live Proved is the publisher's
authenticated readback, not a fresh direct chat platform poll. No root/leaf poll
is claimed. Local Lean/Lake was absent; successful compilation is the pinned
hosted evidence. Do not reclassify exact Python tests as formal verification.

## The complete, explicit interface

Fix any d<m and injective a:Fin m->R. Use the original rows
A_i(x)=sum_(j=1..d)(a_i^j-average_z a_z^j)x_j<=1. For EVERY d-label subset S put

    q_S(t)=product_(i in S)(t-a_i),
    mu_S=average_(all m labels) q_S(a_i),
    v_S(j)=-coeff_(j+1)(q_S)/mu_S.

The filter on all d-subsets uses ONLY mu_S!=0 and all q_S(a_i)/mu_S>=0.
Its image is exactly ALL actual Mathlib extreme points, without duplicates.
Each candidate has exactly S tight. Image cardinality equals the number of
passing subsets and is at most choose(m,d). Neither catalogue membership,
vertex status, a feasible support, rank/inverse nor factorization is an oracle.

New reverse argument: at an actual vertex take its exact d-row tight set S.
If mu_S=0, the nonconstant coefficient vector of q_S is annihilated by every
active row. Accepted extreme_kernel forces it to vanish. The centered identity
then makes q_S zero at every original node, contradicting any label outside S,
which exists since d<m. Thus mean nonzero is a conclusion, not an extra premise.
Active-evaluation injectivity identifies the candidate with the actual vertex.
Forward correctness follows from the exact slack formula and accepted #293
vertex criterion; injectivity of the catalogue follows from recovering S as
the exact active set.

The entire349-line accepted #293 namespace prefix is unchanged. The old public
root/print suffix is omitted, not resubmitted. The standalone proof is583 lines,
solution blobe0886b346742e7860463425a69e2a0ec5f90eff1, SHA256
d85770ad23c903d7c436519ebf0c902316d035d9c419250d9c165085cf364655.
Exact public lets use only Mathlib symbols and an imports/open/options preamble.

## Important sign and complexity boundaries

Mean positivity is FALSE as a universal restriction. On parameters0,...,4,
S={0,4} has q=t(t-4), mean-2 and candidate(-2,1/2), a valid vertex. The test
suite contains77 negative-mean vertices and high-dimensional wrap-around-root
examples. Do not replace mean!=0 by mean>0 when reusing this interface.

All original rows and the FULL-label average are preserved. d0, odd dimensions,
unsorted labels and arbitrary real spacings work. The theorem does not claim
every original row is an irredundant facet in every boundary case. It is a
noncomputable finite catalogue on real data, not an extracted efficient solver.
choose(m,d) can be exponential and is not a uniform polynomial inventory.
No ordinary-edge path, arbitrary-endpoint short route, or Polynomial Hirsch
bound follows just from this complete list. Classical algebra is not claimed
historically new.

## Next useful mathematical step and coordination

The actual all-vertex reconstruction gap is closed; do not create another child
assuming this same catalogue or republish it. #295 supplies an accepted original
edge criterion for vertices sharing d-1 rows. #296 handles consecutive blocks,
while #298 separately develops release pivots at arbitrary moment vertices.
Respect those owners and inspect their current receipts before composition.

A future global route proof must derive a bounded sequence of ADMISSIBLE root
sets between arbitrary catalogue members, not assume all vertices have the
consecutive-block form or count only formal exchanges that lose feasibility.
The new filter includes both normalization signs and all nonconsecutive cases.
Even a complete result for this moment family would remain a class result,
not the unrestricted arbitrary-carrier conjecture. Global coordinate-inventory
and total-refinement obstructions from previous research remain in force.

## Reproducible evidence

The original request, verification and publication archives were downloaded;
all three ZIP hashes and all five frozen packet hashes match. Raw logs, audit,
manifest, resolved request and receipt are separate from derived readbacks.
No individual raw API bodies absent from the publisher export are fabricated.
Warnings in the raw compile logs are retained; no cleanup changed the proof.

The Fraction-only supporting script exhausts695 square systems on16 small
models, independently recovering209 vertices,684 coefficient solutions and5846
original-row identities. It excludes475 infeasible candidates and11 zero-mean
inconsistent systems. Eight selected d8/16/32/64 cases evaluate every original
row, without full graph enumeration. Eighteen saved records/530 rows replay
with product and square-solver discovery disabled. Six forgeries are rejected.

The entire7319-byte report and78114-byte fixture reproduce BYTE-FOR-BYTE in a
fresh single-script workspace. Script SHA2561ced63aee976a036e6036b74d71cf3524a9232ec002fac77eef31b17ae66ebda;
report5a676525151c755894cfcfa3c355712fd9fe6d7eba7c86597f385ce0601ee460;
fixture1d9c39127405ffb46115c7a8356c2d21464b0c445d65c6252d512c77d1aca9cc.
The full fixture and original ZIPs accompany the export and regenerate:

    python3 scripts/test_moment_root_catalogue.py \
      --out /tmp/moment-root-tests.json --fixtures /tmp/moment-root-fixtures.json

Existing main sources, root STATUS, Lean4.30.0/Mathlib pin, protocol0.10.4,
workflows, allowlist, duplicate guards and trusted secret separation are unchanged.
This handoff and the completion cross-reference record the new accepted theorem.
