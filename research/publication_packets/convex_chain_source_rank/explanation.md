# Exact source rank on strictly convex inverse-height chains

## Formal result: a derived sharp bound, not another search theorem

Let w_0 < ... < w_n be real abscissas. The ordinates a_i are arbitrary real
numbers subject to the strict secant inequalities, for every i<j<k,

    (a_j-a_i)(w_k-w_j) < (a_k-a_j)(w_j-w_i).

These are geometric strict-convexity hypotheses, not a bound on a rank, a supplied
small spectrum, or a short path. For source index k and real tilt t, let

    U(t,k) = {a_i+t*w_i : a_k+t*w_k < a_i+t*w_i}.

This is a set of DISTINCT values. The complete candidate proves

    min_(all real t) |U(t,k)| = min(k,n-k).

More strongly, it derives a single M>0, independent of k, for which

    |U(-M,k)|=k,             |U(M,k)|=n-k

for every source. One of these TWO tilts attains every source's optimum. There
is no need to enumerate a slope arrangement or optimize separately at each
source. The public conclusion explicitly retains the lower bound for EVERY
real tilt, not just the two exhibited choices.

For each source it then derives a common shift c making all
f_i=a_i+t*w_i+c positive. Adjoin target zero to the reciprocals 1/f_i. The number
of distinct values below 1/f_k is exactly min(k,n-k)+1, and

    2 * (that reciprocal source rank) <= n+2.

The formal theorem is Hirsch.strict_convex_chain_exact_source_rank. It contains
only real sequences, strict order/secant hypotheses, finite sets, the derived
tilts/shifts and exact cardinalities. It does NOT formalize the polygon-to-chart
construction or a new original-edge route theorem. Those geometric applications
are proved in writing below and exercised by exact tests. Neither this class
result nor a planar bound solves the arbitrary-carrier Polynomial Hirsch mission.

## 1. Why every tilt has a complete side of distinct upper levels

Adding t*w leaves every strict secant inequality unchanged by cancellation.
Fix a tilted chain f_i=a_i+t*w_i and source k. If k=0, the required lower bound
is zero. Otherwise inspect the preceding index p=k-1.

If f_p>f_k, strict convexity forces f_i>f_p for every i<p: the secant from i to p
is smaller than the negative secant from p to k. Hence all k left-hand values
are above f_k. They are pairwise distinct and strictly decrease toward k. For
any i<j<k, the negative secant from j to k forces the secant from i to j to be
negative too. Thus U contains at least k distinct values.

If f_p<=f_k, the secant from p to k is nonnegative. Every subsequent secant is
strictly larger, so the complete right side is strictly increasing away from k.
It contributes n-k distinct values above f_k. Equal adjacent source/predecessor
heights belong in THIS case; no generic-position or no-ties premise is added.

Consequently |U(t,k)|>=min(k,n-k) in either case. Coincidences BETWEEN the two
sides do not defeat this argument: one complete side is already injective.
The Lean candidate proves side injectivity and the finite-set cardinal bound
explicitly, rather than counting indices as though their values were distinct.

## 2. Two extreme tilts attain the matching bound

There are finitely many secants. Choose M greater than the absolute value of
all their slopes. The formal proof uses a finite maximum over all index pairs;
zero/reversed pairs are harmless under Lean's total division, and only strictly
ordered pairs are used to infer inequalities. The denominator for each used
secant is strictly positive.

Then a_i+M*w_i is strictly increasing, and a_i-M*w_i is strictly decreasing.
Their upper sets at source k have exactly n-k and k values respectively. Choose
the direction with the smaller count. Strict convexity was needed for the
universal LOWER bound, not for the existence of extreme monotone tilts.

The executable uses M=1+max absolute adjacent secant slope. Strictly increasing
adjacent slopes imply that every longer secant is their positive weighted mean,
so this also dominates all pair secants. The independent checker reconstructs
that weighted telescoping sum for EVERY pair, rather than sampling secants.
The Lean statement asks for all strict triple inequalities; their implication
from adjacent slope ordering is written arithmetic, not a separately submitted
formal theorem. Small tests also check every triple directly.

A common shift c=1-min_i(a_i+t*w_i) makes every f_i>=1. Translation preserves
all upper comparisons and coincidences. Reciprocation strictly reverses order
on positive reals and is injective. Its upper-level image never contains zero.
Adjoining target zero therefore adds EXACTLY one, proving the reciprocal count.
The final half-size bound follows from 2*min(k,n-k)<=n.

## 3. Complete written reduction for original convex polygons

This subsection is a written geometric argument, NOT additional Lean output.
It explains why this is a structural bound for #336/#337's planar invariant,
rather than an arbitrary sequence exercise or a claim from numerical samples.

Translate an actual polygon vertex v to zero. Choose a linear h strictly
positive at all other actual vertices, as supplied by accepted #336. Choose a
linear e independent of h. In the plane, every linear slope can be written
D=t*e+c*h. For each non-target vertex z define

    w_z=e(z)/h(z),      a_z=1/h(z)>0.

Two non-target vertices cannot have the same w: their (e,h) coordinates would
be positive multiples, making the nearer point lie in the segment from v to the
farther, contrary to extremality. Thus these points can be ordered by w.

The ordered points (w_i,a_i) form a STRICT convex chain. To see this, take i<j<k
and positive interpolation weights lambda+mu=1 with
w_j=lambda*w_i+mu*w_k. If a_j>=lambda*a_i+mu*a_k, then in (e,h) coordinates

    z_j = (lambda*a_i/a_j) z_i + (mu*a_k/a_j) z_k
          + (1-(lambda*a_i+mu*a_k)/a_j) v.

All coefficients are nonnegative, the first two are positive, and their sum is
one. This contradicts z_j being an actual extreme point. Hence a_j lies strictly
below the chord, which is exactly the formal strict-secant hypothesis.

The inverse height from #337 becomes a_i+t*w_i+c. Its unconstrained optimum is
therefore min(k,n-k), so the corresponding positive-denominator source rank is
min(k,n-k)+1. This holds for ANY fixed strict target numerator h; choosing a
particularly favorable unit-weight h was not part of the argument.

For completeness, the original edge interpretation can be read off from the
chart without a graph assumption. Write the original vertices in (e,h)
coordinates as z_i=(w_i/a_i,1/a_i). Each consecutive chain secant has equation
 a=beta_i*w+alpha_i. Strict convexity makes

    beta_i*X+alpha_i*Y <= 1

valid on the whole original hull, with equality at exactly z_i,z_(i+1) among
its vertices. Hence its maximizing face is the whole segment between them.
The two extreme-ray inequalities X>=w_0*Y and X<=w_n*Y similarly expose the
segments [v,z_0] and [v,z_n]. These are actual original exposed edges, not edges
of a refinement or a newly added auxiliary graph.

These edges exhaust the polygon boundary. The two routes from z_k to v have
k+1 and n-k+1 edges, so their shorter length equals the derived source rank.
For a full-dimensional polygon with n+2 actual vertices, there are n+2 genuine
edge facets. Any exact original halfspace representation uses at least that
many inequalities, even if it also contains redundant rows. Thus this written
argument gives L<=floor(m/2) for m original inequalities. This is a familiar
planar diameter bound, NOT a claim of a new general polygon theorem or historical
priority. The contribution here is the exact characterization of the proposed
inverse-height invariant and the resulting two-witness replacement for search.

Current common-target faces cause no discrepancy: an adjacent source/target
pair lies on its original edge and has rank one; a nonadjacent pair in a
full-dimensional polygon shares no proper supporting face, so the current
face is the whole polygon. Segment/point degeneracies are handled separately;
the finite-chain theorem itself includes n=0 and n=1.

## 4. Scope and essential restrictions

The source is a chain index k, and all real tilts are compared for the SAME
ordinates and abscissas. The formal theorem does not derive a chain from an
arbitrary higher-dimensional polytope and does not reselect the numerator.
In higher dimension the normalized points live in a space of dimension up to
d-1, not on one ordered line, so the two-side argument does not carry over.

Strictness matters. With five ordered w_i and constant a_i, the zero tilt gives
upper count zero at the middle source, below the proposed value two. Weak
convexity cannot silently replace the strict hypothesis. Concave or unsorted
data are also rejected by the tests. Arbitrary signed ordinates are allowed,
since positivity is a DERIVED property after shifting, not an input restriction.

No original-vertex catalogue, H/hull identity, endpoint extremality or facet
count is formalized by this finite-chain packet. Original-route use must retain
and prove those geometric facts. The complete polygon argument above is not
represented as a separate authenticated route theorem. The high-dimensional
mission remains open; a closed-form planar rank is not a uniform polynomial
bound for arbitrary carriers.

## 5. Executed tests, reproducibility and formal-verification boundary

The exact regression has24 completed polygon configurations: three named small
polygons,20 seeded irregular integer hulls, and the64-vertex rational polygon
with EIGHT targets. It checks2030 delivered routes and11464 original-edge
occurrences through1840 individually verified state transitions. There are1084
nonacquiring unique steps. All original row-pair systems are checked for vertex
completeness, and every state transition has an exact whole supporting-line
interval certificate. Route production uses linear objectives and original
support lines, not the reference cycle graph. Polygon distances are used only
after construction for comparison.

The small/random runs compare the closed-form answer with all9194 cells from
#337's independently implemented exhaustive breakpoint method, using unequal
positive original-row weights for h. They check9188 strict triple inequalities
directly. The large run validates all15624 source-independent pair secants and
their weighted identities; it does NOT enumerate all triple inequalities or an
arrangement. It completes512 routes/8192 edge occurrences, the exact old eight-
target64-vertex SCOPE, with a NEW method. This does not retroactively turn the
previously timed-out algorithm run into a success.

Five separate finite chains of sizes1,2,3,7,20 exercise singleton/endpoints,
nonuniform abscissas and signed ordinates. Ten malformed/premise controls fail.
An initial test-harness tuple-mutation error was corrected before producing
complete reports; no failed mathematical assertion was erased. The initial
50-polygon exploratory sweep (3934 states) is recorded separately, not added to
regression totals. All six complete outputs reproduce byte-for-byte in a clean
four-script workspace. Two dependencies are unchanged #337 scripts; no previously
blocked script is used, copied or reuploaded.

The scripts and certificate decoder are NOT kernel-verified or Lean-extracted.
This packet requests six transitive axiom reports, but requests and static
checks do not establish compilation. No local Lean/Lake/Elan or cache was found
on PATH or within the checked /opt,/home/oai,/mnt/data locations; release/raw
hosts failed DNS. A complete prepared pinned final gate is required. Keep
Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
duplicate guards and verifier/publisher secret isolation unchanged. Respect
changing-numerator claim5786607495 and other-owned #326/#282/reserved #210.
