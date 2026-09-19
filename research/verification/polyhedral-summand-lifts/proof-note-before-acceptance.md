# Lifting arbitrary original-H endpoints into a Minkowski sum

## Written argument and precise scope

Let P={x in R^d: A_i(x)<=b_i for i=1,...,m}, where the rows are arbitrary real
linear functionals. Let Q be nonempty compact convex. At ANY actual extreme
point u of P, let I be the original rows tight there and put f=sum_(i in I) A_i.
The construction derives a compatible extreme q of Q with u+q extreme in P+Q.
No objective, compatible endpoint, rank certificate or finite Q catalogue is
an assumption.

First, any w annihilated by the active rows must be zero. If not, the finitely
many inactive rows have positive slack at u. Choose e>0 small enough that both
u+e*w and u-e*w satisfy them all. The active rows remain equalities, contradicting
extremality. This argument works for unbounded and lower-dimensional P as well.

For x in P, every active-row slack b_i-A_i(x) is nonnegative, so f(x)<=f(u).
Equality makes every active slack zero. Thus x-u lies in the active kernel and
x=u. The active-row sum uniquely maximizes at u; it is not merely a supporting
functional with an unspecified large face.

## Compact maximizing faces and a compatible sum vertex

Compactness makes F={q in Q: f(q)=max_Q f} nonempty and compact. The pinned
Mathlib extreme-point existence theorem provides an extreme point q of F.
Since F is an exposed face, q is extreme in Q. It is important to choose an
extreme point of this entire maximizing face, not an arbitrary maximizer.

Suppose u+q lies in an open segment between x+y and x'+y', with x,x' in P and
y,y' in Q. Applying f shows that both endpoint sums attain the maximum f(u)+f(q).
The separate inequalities f(x)<=f(u) and f(y)<=f(q) force x=x'=u. Cancelling u
leaves an open-segment decomposition of q in Q, so y=y'=q. Hence u+q is extreme
in P+Q. Different requested P endpoints may use different maximizing faces and
different q; they need not share one objective.

The lift lemma produced a standard-only axiom report in the actual compiler
run. The complete packet nevertheless FAILED because of a later arithmetic
tactic in the elementary proof that P is convex. No platform acceptance is
claimed for any new public packet. Read the handoff and raw diagnostics for the
actual status rather than inferring acceptance from this written argument.

## Endpoint-preserving route transfer

Assume every pair of actual extreme points in P+Q has an exposed-edge vertex
walk of length at most B. Lift independently chosen u,v in P using the argument
above. The accepted #309 theorem contracts the resulting sum walk into P after
deleting stationary component steps. Uniqueness of each sum vertex's decomposition
identifies the two contracted endpoints as exactly the requested u and v.
Therefore the same bound B applies to independently chosen vertices of P.

This final assembly is still awaiting complete pinned Lean verification. Its
statement assumes the actual uniform sum bound; it does not prove that a good
summand/completion exists or bound its complexity. Consequently it does not
settle Polynomial Hirsch, and does not permit arbitrary linear projections as
an edge-preserving substitute. The classical Minkowski diameter relationship
is credited to Deza--Pournin, arXiv1806.07643 (2019), with no historical-priority
claim for this formalization.

Compactness and nonemptiness are real restrictions: P=[0,1], Q=(0,1) yields
P+Q=(0,2), with no extreme points; Q=R or Q=empty also destroys the desired
lifts. These are written counterexamples, not extra Lean theorems in this packet.
For a square summed with itself, opposite corners sum to an interior point,
so simply pairing arbitrary factor vertices is not enough. The test suite
retains this distinction and tied maximizing faces.

## Finite checks and formal evidence are separate

The exact-rational implementation checks114 selected lifts and566 endpoint
pairs over25 independently reconstructed finite H models, with scaled and
redundant rows. It additionally checks unbounded/lower-dimensional finite
vertex-and-ray examples and selected high-dimensional boxes. A finite strict
perturbation certificate is used in these tests to verify the chosen lifts;
it is not assumed in the Lean theorem. No arbitrary real-number runtime,
extracted code, or formally verified JSON parser is claimed.

The current source, both request histories, full compiler diagnostic/axiom block,
and a separate uncompiled convexity repair are preserved. Source equality and
byte-identical regression replay do not replace compilation or platform verdicts.
