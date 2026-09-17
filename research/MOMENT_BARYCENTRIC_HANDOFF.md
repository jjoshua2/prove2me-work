# Continue the moment barycentric incompatibility proof

Read live STATUS, actual main, PR heads/comments and the packet's latest evidence.
This packet is on PR #286, branch proof/moment-barycentric-nonfaces. The first
actual command is comment5707380638; run35173425528 resolved proof head
29b326b349a71c81990032a43e061a295b084deb. This handoff is written while that
verification is in progress and is not a verdict. Do not duplicate a pending run.

Target: Hirsch.moment_curve_barycentric_nonfaces.
Packet: research/publication_packets/moment_barycentric_nonfaces/.
Initial224-line source SHA256:
3ff079a40a2ca53d9ba6c7f47f0c18d5c7f085a5d638cf64340e7200439b99e3.
Lean4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f are unchanged.
The original runtime has no local Lean/Lake and toolchain DNS fails. Source and
arithmetic checks are NOT compilation; only actual job logs/receipts decide.

The live check found that #285's small-face witness packet is already ACCEPTED
(theorem d8214487-c5aa-446b-8e75-f485979b94f3, submission
bd1595ff-d987-4a5b-8f0c-017dec561971). It is not edited or retriggered. Coordination
for the distinct next step is #285 comment5707304949. #281 and #284 are accepted
separate counting results and are not resubmitted. Other owned branches remain
untouched, including deliberately blocked #270 and reserved #210.

## Exact new result

For injective real nodes a on m original labels and a selected set s with
|s|>=d+2, define w_i=1/product_{j in s minus {i}}(a_i-a_j). The source derives
w_i!=0 and sum_{i in s}w_i*a_i^r=0 for every0<=r<=d. Every feasible x for the
ORIGINAL mean-centered moment inequalities has both a negative-weight and a
positive-weight selected row that is strictly slack. Thus neither weight-sign
class can all be tight. No affine-dependence certificate, rank, interior point,
optimizer, sign-ordering or incompatibility oracle is assumed.

The coefficient of degree |s|-1 in Lagrange interpolation supplies the exact
annihilation. A nonzero low-degree polynomial nonnegative at all selected nodes
has positive values on both signs. The actual slack polynomial has degree<=d
and evaluations1-row_i(x); its sum over all ORIGINAL labels equals m>0, so it
is nonzero. This gives the public result, including the valid d0 case.

## Scope and next interface

This complements #285's proper-small-face feasibility construction. For odd
(k+1)-sets in nodes0,...,4k, explicit even separators give2k+3 alternating nodes;
the intended odd set is the negative sign class. The numerical tests check that
identification and all its small proper faces. The GENERAL ordered-sign/parity
lemma, minimum-nonface catalogue/cardinality, original polytopality and assembly
with #281 are NOT part of this Lean packet. Do not label the whole exponential
family or Polynomial Hirsch proved from this result.

The classical interpolation tools are credited, not republished as new theory.
The formal target uses only Mathlib types and explicit let expressions. Helpers
are confined to the solution; the preamble contains only import/open directives.

## Executed supporting tests

1125 exact rational cases,6577 moment equations,11261 original-row checks and
8647 selected inverse weights. There are76 complete small odd-set applications
with354 proper-face checks. Three selected large examples have dimensions16,
32,64 and33,65,129 original rows; their full odd-set catalogues are not enumerated.
Nine invalid controls fail;15 stored audits pass with witness generators disabled.
The final public signature equals problem.json and no proof admissions occur.

    python3 scripts/test_moment_barycentric_packet.py

A clean directory with just that script and the source/target inputs reproduces
the report and full35838-byte fixture byte-for-byte. These checks do not verify
Python/JSON in Lean and are not evidence of a platform acceptance. The new files
are all additions; no pin, workflow, permission, credential or trusted publisher
isolation is changed. Preserve failed diagnostics if any and do not weaken the
mathematical statement to pass a gate.
