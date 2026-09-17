# Ordered moment labels: full minimal incompatibility

## Exact public target

`Hirsch.moment_curve_ordered_minimal_nonfaces` concerns the ORIGINAL mean-centered
moment inequalities in dimension 2k on m labels. Let a be any injective real
parameter map, and let b select 2k+3 labels in strictly increasing parameter
order. Let N contain the k+1 labels at positions 1,3,...,2k+1 in that selection.
The theorem proves all three of the following, with no supplied sign or support
certificate:

1. N has exactly k+1 labels.
2. No feasible point makes every N row tight.
3. Every proper subset T of N has a feasible point making exactly T tight among
   ALL m original rows; every unselected row is strictly slack.

This is an actual minimal-incompatible-row theorem, not just a sign-side
exclusion assuming the side has a suitable size. The selection b need not be
increasing in the original LABEL order; only its real parameters must increase.
The original centering mean is always over all m labels, never just the selected
chain. k=0 and empty proper subsets are included. The theorem does not assert a
new diameter bound or a solution of Polynomial Hirsch.

## Dependencies reused, not resubmitted

The self-contained packet includes the namespace proof bodies from two ACCEPTED
packets, byte-for-byte between their namespace delimiters:

- #285 `Hirsch.moment_curve_exact_small_face_witnesses`, accepted proof
  c8589a1fee999c8497ebd2d1e6e9601ce739ec8b, source blob
  3506c3b28278e52412e7867b08f81c096b836334.
- #286 `Hirsch.moment_curve_barycentric_nonfaces`, accepted proof
  5b44ad2795b85acb693e6e9f44039e9d9c425e85, source blob
  6050e16e234b64011ea8bb8b643cc9461c327ce3.

Their old top-level solution declarations and print suffixes are omitted, not
redeclared as separate target assumptions. All substantive dependency definitions
and proofs are unchanged. The final audit therefore verifies the actual transitive
proofs under the same Mathlib pin, not unproved restatements of those theorems.
Neither accepted theorem is registered or submitted again by this packet.

## New ordered-sign argument

For strictly increasing nodes c_0,...,c_(2k+2), use the explicit barycentric weight

    w_i = 1 / product_(j != i) (c_i-c_j).

Split its denominator into factors below and above i. Every lower factor is
positive. For the upper factors, pull out one minus sign each; their reversed
factors are positive. The number of upper factors is exactly 2k+2-i. Its parity
is the parity of i. Thus w_i is positive at every even i and negative at every
odd i. The proof derives the signs from strict order and finite interval counts;
no hypothesis tells Lean the signs in advance.

For an original-H feasible x, the accepted slack-polynomial argument constructs

    p(T) = 1 - sum_j (T^(j+1)-average_l a_l^(j+1))*x_j.

It has degree at most 2k and is nonnegative at every original parameter. Its
average over all labels is 1, so it is not the zero polynomial. Apply the
accepted barycentric polynomial lemma on the selected 2k+3 nodes. There must
be a negative-weight node where p is strictly positive. The new sign theorem
locates it at an odd rank, hence in N. Its original row is strictly below 1.
This proves incompatibility without changing the original inequality system.

The odd-rank embedding from Fin(k+1) is injective, and b is injective because
its selected parameters are strictly increasing. Therefore the image N has
k+1 elements. Any proper subset T has at most k elements. The accepted squared-
root-polynomial witness then gives a feasible point with exact active set T.
Combining these arguments proves minimality, including all proper subsets.

## What is not yet formalized by this packet

For the numerical moment family on 0,...,4k, a (k+1)-subset of odd labels can
be interleaved by adding an even label before the first and after every odd
label. This instantiates the current ordered-chain statement in the written
argument and in the finite tests. The Lean packet does NOT yet construct that
embedding for every such subset, prove the cardinality of the whole catalogue,
assemble its finite family with #281, or formalize the full geometric realization
and exponential asymptotics. Those are distinct next interfaces, not conclusions
silently inferred from numerical examples.

Nor does minimal incompatibility provide an original-edge upper bound. #267's
obstruction concerns the total size of complete forward flag refinements, not
the length of a path through the original polytope or a huge implicit refinement.
The unrestricted Polynomial Hirsch conjecture remains a separate target.

## Verification boundary

The originating runtime has no Lean/Lake executable and cannot resolve the
public toolchain host. Exact rational tests and source/signature checks therefore
are NOT local Lean compilation. A prepared publication comment on an open
same-repository PR requests the normal pinned compile/axiom gate and trusted
publisher. No workflow, pin, permissions, token or secret split is changed.
The actual run and publisher receipt must establish compilation and acceptance;
this explanation alone claims neither.

The rational regression checks arbitrary scrambled real-label orders represented
by fractions, nonuniform parameters, selected subchains, positive/negative
weights, original full-label means and exact proper-subset witnesses. Larger
samples through dimension64 do not enumerate a full vertex graph or the whole
exponential nonface family. Producer-disabled audits and malformed-input controls
remain software checks, not Lean-extracted code.

Primary mathematical infrastructure: Mathlib's Lagrange interpolation,
https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Lagrange.html.
All new sign/cardinality/minimality steps are in the submitted source. Classical
moment-curve/interpolation mathematics is not claimed as a new historical theorem.
