# Actual planar vertices, derived radial convexity, and original-edge walks

## What is new in this packet

Accepted #338 computes the exact source rank of a STRICT CONVEX CHAIN. Its
polygon-to-chart and original-edge interpretation was explicitly left written
and tested. This packet formalizes that geometric bridge and constructs the
original walks. It does not republish #338 or assume its favorable chain as a
new geometric hypothesis.

The input consists of a planar set P, a target v, a list p indexed by Fin(n+1),
and two linear forms h,e. The following remain EXPLICIT:

- P is exactly the hull of v and the listed p_i;
- v and every p_i are actual Mathlib extreme points of P;
- h(p_i-v)>0;
- z -> (h(z),e(z)) is injective;
- p is ordered by strictly increasing e(p_i-v)/h(p_i-v).

These specify the complete original-vertex chart, not a sample. Strict ordering
and positivity imply that the list has no repeats and excludes v. Exact hull
identity plus extremality is the supplied complete finite-hull representation.
The packet does not derive H-to-V enumeration, choose h,e, or sort an unordered
input. Accepted #336 derives a strict exposure from an actual target vertex;
a formal choice-and-sorting adapter remains a separate obligation here.

The outputs include strict chart convexity, EVERY consecutive original exposed
segment, both original target edges, and a finite walk from each p_k to v with

    L = min(k,n-k)+1,             2L <= n+2.

Every visited point is an actual original extreme point. Every consecutive
segment is nondegenerate and IsExposed in P itself. The same L equals the exact
optimized reciprocal-height rank and is bounded by one plus the distinct upper
height count for EVERY real tilt. The count n+2 is the complete original-vertex
inventory, not a formal count of original inequalities or irredundant facets.
No uniform arbitrary-dimensional Polynomial Hirsch conclusion is claimed.

## 1. Extremality supplies strict radial convexity

A generic lemma first works in any ambient finite real coordinate space. Suppose
x is an actual extreme point of a convex P, v,u,y belong to P and differ from x,
and r,s are nonnegative with

    x-v = r(u-v)+s(y-v).

Then r+s>1. Otherwise x is the convex combination of v,u,y with weights
1-r-s,r,s. Mathlib's characterization says P without the extreme point x is
convex. Those three other feasible points and the nonnegative weights therefore
put x in P without x, a contradiction. This proves the strict inequality without
an oracle about facets, edges or a catalogue of supporting planes.

For the planar chart write

    w_i = e(p_i-v)/h(p_i-v),      a_i = 1/h(p_i-v)>0.

If i<j<k, let

    r=(w_k-w_j)/(w_k-w_i),        s=(w_j-w_i)/(w_k-w_i).

Then r,s>0, r+s=1 and r*w_i+s*w_k=w_j. Injectivity of the two linear coordinates
proves the normalized vector equality

    a_j(p_j-v) = r*a_i(p_i-v)+s*a_k(p_k-v).

Consequently p_j-v is a positive radial combination of p_i-v and p_k-v with
coefficient sum h(p_j-v)*(r*a_i+s*a_k). The generic extremality lemma forces
that sum above one, proving

    a_j < r*a_i+s*a_k.

Multiplication by the positive horizontal gap gives the strict triple-secant
inequality used by #338. Thus strict convexity is a CONCLUSION of original
extremality, not an input rank/chain promise.

## 2. Consecutive secants expose original segments

For consecutive chart points let s,t solve

    a_j=s*w_j+t,     a_(j+1)=s*w_(j+1)+t.

Strict triple-secant inequalities on both sides prove s*w_i+t<a_i for every
other index. Define the original linear functional f=s*e+t*h. The identity

    f(v)+1-f(p_i) = h(p_i-v)*(a_i-(s*w_i+t))

shows that f is maximized exactly at p_j,p_(j+1) among all original generators.
The target is strictly below the maximum by one. The accepted finite-hull
support argument extends the inequality and its equality set to the WHOLE
hull: the maximizing face is precisely the segment between those two points.
The proof constructs IsExposed with f.toContinuousLinearMap.

The smallest and largest normalized horizontal coordinates similarly yield the
two extreme-ray supports. For an extreme index j and sign s in {-1,1}, use

    f=s*e-s*w_j*h.

Its difference from f(v) at p_i is h(p_i-v)*s*(w_i-w_j). This is nonpositive,
and zero only at p_j. The original maximizing face is exactly [v,p_j].

No adjacency graph, supplied edge witness, arbitrary chord, refinement edge or
auxiliary-graph edge is used as a public premise. Nondegeneracy follows from
strict chart ordering and target positivity.

## 3. Build and count the original walks

The constructed left walk is

    p_k, p_(k-1), ..., p_0, v,

and has k+1 original edges. The right walk has n-k+1 edges. Natural-number
induction constructs both with all vertex and whole exposed-segment properties;
the public theorem chooses the shorter and exports a Fin(L+1)-indexed sequence.
There is no short-walk existence hypothesis in the public statement.

The exact accepted ConvexChainRank namespace from #338 now applies to the
DERIVED chart. It proves the all-real minimum upper-height count min(k,n-k)
and gives one M>0 independent of k whose two tilts attain the endpoint counts.
The original walk length is therefore exactly one plus the optimized upper
count. A positive translation and reciprocal target-zero counting supply the
same length as the finite lower-ratio count in the public conclusion.

This is not a formal shortest-path lower bound against every arbitrary original
walk, nor a proof that the displayed cycle exhausts every possible exposed edge.
The constructed walks happen to be the usual shorter polygon arcs. Their
classical interpretation is not a claim of historical mathematical novelty.
The public walk does not separately export injectivity or target-facet locking.
The singleton chart n=0 is included and gives one original segment; a point-only
polytope is outside this distinct-target/listed-source chart input.

## 4. Reuse and remaining mission gap

The first 297 lines (12486 bytes) of accepted #338's proof are reused exactly,
through end Hirsch.ConvexChainRank and before its old public root. SHA256:
93b00f51c9f6d3c02a56e4996a4ac205e3ba988245d8bb4c30ffccbba54441d9.
The hull_support declaration is reused exactly from accepted #336, within its
original namespace and a small namespace wrapper. No accepted target is imported
as its own proof or resubmitted. Everything after these dependencies is a new
geometric/walk proof and a new public assembly.

The proof works with original P and actual extreme points. Nevertheless its
finite complete vertex chart, strict exposure, independent coordinates and order
are supplied. The two-dimensional bound n+2 is not a polynomial bound in original
facets for arbitrary dimension. Removing chart selection hypotheses, attaching
an original-H inequality count, and generalizing the useful invariant beyond an
ordered one-dimensional chart remain distinct tasks. A favorable low-dimensional
result is not an answer to the high-dimensional common-carrier mission.

## 5. Executed exact supporting tests

A new standard-library Fraction test constructs charts from complete planar
original-H references, using multiple weighted target exposures. It checks every
triple's normalized interpolation, strict radial-mass margin and secant defect,
then checks every candidate support against ALL original vertices. Whole support-
line intervals are independently checked against every original inequality.
An independent JSON consumer rechecks the chart, triple witnesses, supporting
functionals, edge cycle and counted routes without calling the chart constructor.

The small suite has eleven polygons: three named models plus eight invertible
integer shears and translations. Across two exposure variants and all targets it
checks 114 charts, 1032 triples, 622 exposed-segment occurrences, 508 routes and
872 original-edge occurrences. The larger 32-vertex rational polygon checks four
targets: 4 charts, 17980 triples, 128 exposed segments, 124 routes and 1024 original-
edge occurrences. Combined: 118 charts, 19012 triples, 750 exposed segments,
632 routes and 1896 original-edge occurrences. This is planar, not dimension32.

Ten controls reject missing vertices, changed heights, dependent coordinates,
reversed order, omitted edges, false support maxima, false convexity margins,
wrong endpoints, incorrect lengths and a nonextreme boundary point. A clean
three-script workspace reproduced all FOUR complete report/fixture files byte
for byte. The two dependencies are unchanged #337 rational utilities, not the
previously blocked order-cell solver. Python and JSON are not kernel-verified.
The executable tests do not cover the singleton-chart case, which the formal
statement includes; no numeric fixture is presented as an all-real proof.

## Verification boundary

The full 940-line candidate imports Mathlib only and has no written admission or
new axiom. The top-level solution type matches problem.json exactly. Seven
transitive axiom reports cover inherited rank, radial mass, derived chain,
original secant/ray edges, route assembly and the public root.

No local Lean/Lake executable or standard cached installation was found, and
release/raw toolchain DNS failed. Source hashes, type-text matching and exact
rational execution are not Lean compilation. Use one prepared complete pinned
hosted gate. Preserve any failure separately; do not weaken the hypotheses or
turn a clean helper in a failed file into a complete acceptance claim.
Keep Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
existing duplicate guards and verifier/publisher credential separation unchanged.
