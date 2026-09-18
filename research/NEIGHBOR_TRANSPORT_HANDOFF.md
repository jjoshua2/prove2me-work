# PR #303: quantitative actual-neighbor transport — ACCEPTED

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and the LIVE queue
before continuing. #300 owns separated-pair routes and #302 owns even-gap
classification. They were not edited or retriggered. Reserved #210 is untouched.

## Accepted exact target

`Hirsch.moment_quantitative_neighbor_transport` is ACCEPTED, theorem
b949797e-9406-4235-9a41-19bce04cf5f9, submission41e163ac-e425-45d4-a471-c22b77345379.
The publisher receipt records authenticated live Proved. Frozen proof
7c75245fcbcca2127fdc3bff635f0ec38c8e4b9f, run35375655311. Actual new top-level
trigger5733856223, resolved acknowledgement5733858775, verdict5733918919.
The unchanged939-line source passed FIRST compilation and FIRST platform
submission: all three exits zero, five transitive audits standard axioms only.
Do not resubmit. No source, metadata, assumption, pin or workflow was repaired.

All three original ZIPs and five frozen file hashes were checked. Complete raw
compiler logs, audit, manifest, request and publication receipt are retained.
Derived readback data are explicitly labelled. Live Proved is the publisher's
readback, not an independent chat-side platform poll; no root/leaf status poll
was performed. Local Lean/Lake is absent; hosted compilation is the evidence.

## The actual quantitative interface

For distinct actual original moment vertices u,v with d<m and injective real
parameters, construct normalized release directions w_p and positive times t_p
for every source-tight row. Their endpoints z_p=u+t_p*w_p are actual neighboring
extreme points on exposed original edges. The proof uses accepted first-blocking
construction internally; the public type states normalized endpoints, not an
additional separate minimum-ratio formula.

Define b_p=(1-A_p(v))/t_p and Lambda=sum_p b_p. Prove b_p>=0, Lambda>=1 and

    v-u=sum_p b_p*(z_p-u).

For target score f=sum_(target-tight rows) A_i, there is a positive-weight
neighbor with gain h=f(z_p)-f(u)>0 and gap<=Lambda*h. It preserves all shared
target-tight rows. No supplied neighbor, rank, step, small-mass bound or path
oracle. This is a nonnegative LINEAR displacement combination, not generally
a convex combination of neighbors. The finite weighted maximum supplies the
quantitative index. The source-to-target weights are explicit and depend on
the actual first-blocking times.

The accepted source prefix through MomentRelease is byte-identical to #301,
722 lines up to that namespace end; row_finite_sum and target_score_strict are
also unchanged. The old public roots and unused catalogue/ascent sections are
not submitted again. Source blob6d3b107ba24b08e9562ab8c132a093274f823a9d,
SHA25654b31726d9fab594b2438499e245debc36f42748b5c4637c435d8970e74308cb.

## Important mathematical boundary: small total mass is false

Read NEIGHBOR_TRANSPORT.md for the complete WRITTEN proof and exact slack table.
At parameters(0,e,1,2,3),0<e<1, source active labels{0,1}, target{3,4}, the
actual two edge coefficients have total

    Lambda=(4-e)(14+e-e^2)/(e*(e^2-5e+14)) > 1/e.

So this mass is unbounded already at fixed d2/m5; do not make another child
assuming a universal dimension-only small-mass estimate. This section is not
part of the accepted Lean target: its geometry uses the prior accepted vertex
and common-edge interfaces, with all displayed rational identities and signs
proved in the note and checked symbolically. It has no additional platform
verdict. The first neighbor's relative score gain tends to-1/13 and the second
to6/13, while1/Lambda tends tozero. Thus the weak lower guarantee does not mean
actual gains are small or paths long. Cancellation in the weighted score sum
is a real issue, not a diameter obstruction.

A useful next direction must retain more of the signed gain distribution or
use another route-local invariant; merely bounding this entire weight sum
cannot work uniformly. Even a uniform fractional score reduction would need
care with arbitrarily small terminal gaps. No polynomial route count or
unrestricted Polynomial Hirsch result is claimed. Classical cone/weighted-
average mathematics is credited, not claimed historically novel.

## Tests and reproduction

Six complete small original-H models:153 square systems,51 vertices,578 ordered
distinct endpoint pairs,2060 original-edge checks and coordinate identities.
170 equality cases and158 unit-mass cases retained. Selected d8/d16 examples
check all outgoing edges but have unit mass and are not hard long routes.
Twelve saved records/47 edges replay with production disabled; six forgeries
fail. The full2676-byte report and282982-byte fixture repeat byte-for-byte in a
clean workspace with the new script plus two UNCHANGED existing test helpers.

The symbolic five-row script checks the four full slack tables, normalization,
weights, displacement, mass factorization and limiting gains. Its report also
repeats exactly. These are not Lean-extracted Python or kernel-checked JSON.

    python3 scripts/test_moment_neighbor_transport.py --out /tmp/transport
    python3 scripts/check_neighbor_mass_family.py --out /tmp/transport/symbolic.json

New test SHA256b447168d508e92cbb4d1a2a1e2701ec8496ac39c4863ba499f82a6df9f7cf788;
report48eb2c1ecfc9065dff2d9f87aa8a51b9ed3b3b8a91bf7909c82ccc3b3b54d9fd;
fixture41dcc5bff59ff114a39782459829c03dd1c3de5b0a6ef45aa6902d93628a3cfa.
The full fixture and original archives accompany the export and regenerate.

## Completed #301 integration

Before this proof, the continuation integrated already-ACCEPTED #301's receipts,
archived the stale failed handoff and merged it asbe7b4e8972a698526670f8de181fe8e7df3a684a.
No #301 proof/metadata change or repeated submission occurred. Its all-endpoint
L<choose(m,d) route bound remains potentially exponential. This #303 branch
starts at that merge. Root STATUS was not replaced underneath concurrent work;
use the current receipts/handoffs rather than its old snapshot. Lean4.30.0,
Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, protocol0.10.4, duplicate guards,
allowlist, workflows and trusted verify/publish secret separation are unchanged.
