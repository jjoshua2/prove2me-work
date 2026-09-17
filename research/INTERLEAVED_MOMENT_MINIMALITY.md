# Interleaved moment sets: explicit signs and minimal original-H nonfaces

## Precise mathematical claim

Take distinct real parameters a_i on m original labels. In dimension 2k define
row_i(x)=sum_{j=1}^{2k}(a_i^j-average_z a_z^j)x_j, with the average over ALL m
labels. Choose k+1 ordered pairs of labels satisfying

    a(l_0)<a(r_0)<a(l_1)<a(r_1)<...<a(l_k)<a(r_k).

The new packet proves that L={l_0,...,l_k} and R={r_0,...,r_k} each contain k+1
distinct labels, are disjoint, and are both minimal nonfaces of the original
inequality system row_i(x)<=1. Neither side can be entirely tight at a feasible
point. Every proper subset S of either side has an actual feasible x making
EXACTLY the original S rows tight and all other original rows strict.

The real order conditions and injectivity are assumptions. A sign pattern,
minimality, a feasible proper-face witness or a nonface catalogue are not.
k=0 is included as a degenerate row statement; genuine facets and full-dimensional
bounded polytopal realization are not asserted in every degenerate case.

## Pair grouping, instead of an assumed parity rule

For the selected 2k+2 nodes put w_i=1/product_{j!=i}(a_i-a_j). At a node x of
pair i, each OTHER pair contributes (x-a(r_j))(x-a(l_j))>0, because its two
factors have the same nonzero sign. The only unpaired factor is the partner:
negative at a(l_i), positive at a(r_i). Therefore ALL left weights are negative
and ALL right weights positive. This argument permits arbitrary spacings and
arbitrary permutations of the original labels.

The accepted barycentric polynomial theorem (#286) gives sum_i w_i*p(a_i)=0
for degree at most 2k, and forces positivity of a nonzero nonnegative p on a
node of each sign side. The ORIGINAL slack polynomial

    p_x(t)=1-sum_{j=1}^{2k}(t^j-average_z a_z^j)x_j

has degree at most 2k, is nonnegative at every original parameter for feasible
x, and is not zero: its full-label average is one. Consequently one left
and one right original row is strictly slack at every feasible point.

## Proper subsets are feasible with no hidden extra tight rows

Every proper S of L or R has size at most k. The accepted #285 construction uses

    p_S(t)=product_{i in S}(t-a_i)^2,
    h=average_z p_S(a_z)>0,
    x_j=-coeff_j(p_S)/h.

It proves row_i(x)=1-p_S(a_i)/h for every ORIGINAL label i. The polynomial
is nonnegative and vanishes precisely at labels in S, establishing all-row
feasibility and the exact tight set. This is stronger than merely proving
that some unspecified point meets S. Combining the explicit sign partition,
incompatibility and these witnesses establishes minimality.

The standalone packet includes the full accepted helper namespaces from #285
and #286 byte-for-byte, omitting only their old standalone root aliases. It
does not import the new target or re-register the accepted dependencies.

## Application to the earlier odd-label family, and the exact remaining gap

For the integer parameter family 0,...,4k, take any k+1 odd labels
s_0<...<s_k from {1,3,...,4k-1}. Set l_i=s_i-1 and r_i=s_i. They interleave:
s_i<s_j-1 for i<j, since two distinct odd integers differ by at least two.
Thus this new theorem is the missing per-subset minimality interface for the
written moment-family obstruction in #267. The even companion set is minimal
as well.

This paragraph explains an instantiation; the submitted public target does not
yet construct and count the complete Finset of every odd-label subset or connect
that finite registry to the accepted stellar persistence theorem #281. Neither
an exponential original-edge distance nor a Polynomial Hirsch proof follows.
The known strategy-size obstruction is about completing an entire forward
stellar flagification, not about the number of edges actually used by a route.

A next formal assembly should explicitly enumerate the odd-subset registry,
prove distinctness and its binomial cardinality, instantiate the interleaving
maps for each member, then use #281. Any additional full-dimensionality or
genuine-facet conditions must have their own geometric proof. For the conjecture
itself the remaining task is a polynomial ORIGINAL-edge upper bound, not
another assumption that a complete global refinement is cheap.

## Exact tests and their boundary

The script uses exact Fraction arithmetic and constructs 150 configurations:
72 randomly spaced/label-permuted cases with k=0..3, every k+1 odd subset for
k=1..4 (76 cases), and selected examples at dimensions16 and32. It checks1120
inverse weights,970 moment equations,4782 proper-subset witnesses,72414
original-row identities and9564 sign/slack conclusions. Large full subset
families are not enumerated. All original-label averages include unused nodes.

Removing interleaving is false: in dimension2 at parameters0,1,2,3, the
nonnegative polynomial t(t-1) yields x=(1/2,-1/2), feasible with BOTH adjacent
labels0,1 tight. Three malformed order/injectivity configurations are rejected.
A clean script-only replay reproduces the whole report byte-for-byte. These
are supporting computational checks, not an all-real proof by sampling or a
formal verification of Python/JSON.

## Verification and ownership

Read the packet's current evidence record for actual compilation and publication
status. An issued PR comment, passed rational test or successful statement-only
compile is not an authenticated Prove2Me acceptance. Preserve the frozen proof
SHA, original logs, audit, receipt and separate failed-gate history if any.
No older accepted theorem or other agent's branch is changed. In particular
#285/#286 are reused, #282 remains separate, and #270's blocked integration and
reserved #210 are untouched. Lean/Mathlib pin, protocol, workflows, allowlist
and trusted secret separation remain unchanged.

Classical moment-curve interpolation and its geometric uses are credited; no
historical-priority claim is made. This contribution formalizes the concrete
missing interleaving/minimality interface recorded in STATUS at
9a1b6768d27d38b719bf4c0c795f8f7257415626.

## Concurrent accepted interface

The final live main refresh found #288 concurrently accepted and merged at
dfa4c0b4834fd302818646f56a0801fbbf54be75. It proves minimality of the odd side
of an ordered2k+3-node chain. The present theorem proves both sides of an
interleaved2k+2-node chain. These are distinct but substantially overlapping
results. Their files are disjoint, and neither accepted proof is altered or
resubmitted. The parity/minimality obligation is now closed in both interfaces;
future work should move to actual catalogue/count assembly or a genuinely new
original-edge route argument rather than another version of this theorem.
