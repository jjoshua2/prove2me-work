# Acquiring target facets can justify objective-decreasing edges

## Status, scope and distinction from the concurrent work

This is a written mathematical argument plus executed exact rational research,
not a Lean-compiled theorem or a Prove2Me verdict. No new proof skeleton or
publication workflow is added. PR #250 already formalizes adaptive common
IMAGE-face locking and its original-edge transfer; its accepted proof and its
owner's projected-image implementation are not modified or duplicated here.

The present selector works directly in the original H-coordinates of SIMPLE,
bounded, full-dimensional polytopes. It takes A,b and two vertex coordinates.
It discovers every incident edge from exact active-row inverse identities;
no neighboring vertex, route, source/image graph, or external objective is
supplied. It can accept an edge that DECREASES the current target objective
when that edge permanently acquires a new target facet. Its radius-two variant
can commit a whole two-edge first-acquisition block even if its first edge
decreases the old objective. This is deliberately not a globally monotone
simplex trajectory. There is no universal polynomial count or novelty claim
for classical simplex primitives.

The unchanged prior target_slack_pivot.py is included so the previous
bundle-only comparator is now reproducible from the same branch. That code is
not newly authored by this continuation. The prior unchanged full-default
replay through dimension12 is not rerun or silently reclassified here; the
current comparison freshly reruns its target-slack comparator with the
unchanged #248-discovered target objective.

## 1. A phase objective with an intrinsic normalization

Let P={x:a_i(x)<=b_i} be simple and bounded in R^d; v is the prescribed target.
Let T be its d independent active facet rows. At the start p of a phase, let
J=T intersect active(p), and retain every row in J as an equality. Put
s_j=b_j-a_j(p)>0 for j in T\J, and define

    f_p(x)=sum_{j in T\J} a_j(x)/s_j.

The objective is fixed until a new target facet is acquired. On the current
face, v is its UNIQUE maximizer: equality in all positive target-row upper
bounds, together with the retained equalities, forces all d independent target
rows tight. Also

    f_p(v)-f_p(p)=|T\J|.

This is normalization, not a lower bound on any completed edge gain. At a later
point in the same phase the gap may be much smaller or much larger after a
terminal acquisition block; no uniform contraction is assumed.

At a simple current vertex x let D_i be inverse tangent columns satisfying

    a_j(D_i)=-delta_ij for all current active rows j.

Exactly the columns releasing rows outside J stay in the retained face.
The finite identity

    v-x = sum_{i active at x, i not in T} (b_i-a_i(v))*D_i

has strictly positive coefficients on every eligible column. Applying f_p
shows that at least one eligible edge improves f_p whenever x!=v. Following
it to the maximal original feasible endpoint therefore cannot get stranded
before a target acquisition. This conclusion is derived from the original
row identities, not a assumed path-existence oracle.

## 2. The acquisition-first rule

At each current vertex, certify all its eligible incident edges and their
maximal endpoints. Prefer a one-edge acquisition of a previously missing
target facet, regardless of whether its f_p gain is positive. Break ties by
new-facet count, completed f_p gain, then the target-slack signature below.

With lookahead=2, if no immediate acquisition exists, construct the active-row
inverse certificate at EVERY eligible neighbor and inspect its eligible edges.
If a two-edge first acquisition exists, commit one complete two-edge block.
Only when neither one nor two edges can acquire a target facet does the rule
fall back to the largest completed positive f_p gain. The objective resets
only after the first new target facet; acquired facets are never released.

The auditor checks every certified branch, including negative local coverage:
missing a neighbor or an alternative acquisition fails verification. No
inverse, rank calculation, LP, discovery function or global graph search runs
inside the auditor. It recomputes the finite arithmetic comparisons and
maximal-step ratios. At most d root directions and d^2 second-level directions
are examined per decision, but the number of decisions is NOT proved polynomial.
Rational bit growth and the producer's total time are not bounded here.

### Finite termination, without global objective monotonicity

There are at most d-|J_initial| phase endings. Between endings, every fallback
step strictly improves the fixed f_p, so it cannot revisit a vertex. A terminal
two-edge block also cannot revisit an earlier vertex of that same phase: its
intermediate vertex already has an immediate acquisition edge, and an earlier
visit there would have ended the phase immediately. The final vertex has a new
target equality, and hence was not visited earlier. Repetition across phases
is impossible because each phase permanently increases the actual target
active set. Bounded polytopes have finitely many vertices, so the uncapped
mathematical procedure terminates. Software caps explicitly report incomplete
work, not a negative geometric result.

This is a finite-termination argument. Counting phase endings does not bound
fallback steps inside a phase. The family in section5 shows why that distinction
must remain in the next theorem.

## 3. The complete selector is affine-equivariant, including tie breaking

For two endpoints y compared from anchor x, use the ordered signature

    (-(b_j-a_j(y))/(b_j-a_j(x)))_{j in T, b_j-a_j(x)>0}.

It contains only target-slack ratios. With the locked target rows it determines
y uniquely, since all target rows are independent. Radius-two ties use the final
signature and then the intermediate signature, both measured at the same root.
The order is the fixed order of original row labels.

Multiplying any original inequality and its RHS by a positive number leaves
these signatures, the phase objective gains and every maximal edge endpoint
unchanged. Under any invertible affine coordinate change x'=M*x+c, transform
A'=A*M^-1 and b'=b+A'*c. All slacks, gains and signatures are unchanged, and
all chosen vertices become M*x+c. Thus both invariance properties hold for the
ENTIRE trajectory, including ties. An arbitrary permutation of the fixed row
labels can change a tied lexicographic choice; no label-invariance is asserted.
Twenty-four whole-route affine and24 positive row-scaling checks are executed.

## 4. A family where decreasing the old objective is the correct progress

For N>=2 take the polygon whose vertices are (t,t^2) at the ordered parameters

    0, 1, 1+3/(2N), 1+6/(2N), ..., 5/2, 3.

There are N+3 genuine facets. The lower edge between parameters a<b has row
(a+b)*x-y<=a*b; the upper closing edge is y<=3*x. Consecutive slopes strictly
increase, so every listed row is a genuine facet. The tests additionally
check a strict relative-interior anchor for EACH row against all original rows.
Start at u=(1,1), target v=(3,9). Their common face is the entire polygon.

The target rows are (11/2)*x-y<=15/2 and -3*x+y<=0. Their slacks at u are3 and2.
Therefore the automatically constructed phase objective is EXACTLY

    f(x,y)=x/3+y/6.

It increases strictly along the entire parabolic chain. Any route required
to increase this fixed phase objective takes N+1 edges to v; the first phase
alone has N edges, with N-1 steps acquiring no target facet. Resetting the
objective at phase endings does not help, since the first ending has not occurred.

In contrast u -> (0,0) -> v is an ordinary two-edge route. The first step
DECREASES f by1/2 (one quarter of the original gap2), but permanently acquires
the upper target facet. Acquisition-first must choose it because it is the
only immediate new-target-facet edge. The remaining retained face is the
upper edge, so the next step reaches v. The two-edge result is shortest because
u and v are not adjacent. The experiment checks N=2,4,8,16,32,64; the count is
proved above for arbitrary N, not extrapolated from those samples.

Products of p such polygons have the same two-move mechanism in each factor.
Every acquisition changes one coordinate factor, and there is always an
immediate acquisition until that factor reaches v. The algorithm thus takes
2p=d steps, independent of N, with a matching source-facet-drop lower bound.
The tests reach dimension16 without enumerating the product graph. Product
diameter behavior is classical; this is a trajectory/phase comparison, not a
new general Hirsch theorem.

## 5. A fixed lookahead radius does NOT bound the phase

Insert h additional parameters strictly between0 and1, namely j/(h+1) for
j=1,...,h, into the same polygon. Start and target stay u=(1,1),v=(3,9).
The initial objective is still x/3+y/6. The short backward path now reaches the
upper target facet after h+1 edges and v after h+2. With N>=h+2 this is the
shortest route around the polygon.

A radius-h acquisition-first rule cannot see that exit at the initial vertex.
Its only improving fallback is forward along the parabolic chain. The backward
exit becomes farther away at every such step. Eventually the forward target
facet comes within the horizon; committing that block still follows the same
forward chain. Total route length is therefore N+1, while the true distance
is h+2. The common face stays full until the forward target facet is reached.
This argument covers arbitrary fixed positive h; the IMPLEMENTED/tested depths
are only1 and2. For depth2,N=64 the actual certified route has65 edges versus
four shortest, on a69-facet polygon.

This disproves a constant phase bound or constant-factor approximation from
fixed local lookahead. It does NOT disprove a polynomial facet-count bound:
the displayed bad route is linear in its number of ORIGINAL facets. A future
proof needs an n-dependent global bound inside the phase, not just bounded
lookahead or the number of target acquisitions.

## 6. Reproduced numerical comparisons and their limits

On the original six non-product models, all614 ordered endpoint pairs are
retested against independent exact graphs. The prior target-slack baseline
uses1258 edges in total and has28 nonshortest routes. Facet-first at depth1
uses1243 edges and has13 nonshortest routes. Depth2 uses1230 edges and has2
nonshortest routes, versus1228 total shortest-path edges. Relative to the prior
baseline:28 pairs improve,584 tie, and TWO become longer. Those regressions
are retained in the saved pair table, not silently dropped.

On six additional models (100 deterministic sampled pairs each), depth2 uses
1529 edges and has27 nonshortest routes, versus the prior baseline's1564 edges
and53 nonshortest routes; the exact shortest total is1499. Thirty-four pairs
improve,559 tie and SEVEN become longer. One further generated model is
nonsimple, is rejected as outside this simple-original-H implementation, and
is explicitly reported rather than counted as a geometric failure.

The original and additional groups therefore comprise1214 pairs over twelve
independent reference graphs. Four new-policy ablations are executed per pair.
The tests verify2506 radius-two first-hit decisions against an independent
restricted-graph breadth-first search. The produced depth-two routes contain63
steps decreasing the previous fixed objective. Every actual original edge is
checked against the reference graph; the reference is never passed to the
selector. Candidate exploration is counted separately from committed edges.
Twenty-four audits pass with all inverse/LP/discovery routines disabled, and
fourteen malformed/capped inputs fail. See the raw graph and family receipts.

Larger capped Klee--Minty instances2..12 are also tested; all four new policies
return d-step routes meeting the existing facet-drop lower bound. This remains
an observed all-tested-dimensions trajectory, not a new all-dimensional proof.

## Reproduction and relation to classical lower bounds

    python3 scripts/test_target_phase_pivot.py --part graphs
    python3 scripts/test_target_phase_pivot.py --part families
    python3 scripts/target_phase_pivot.py input.json --lookahead 2 --output route.json

Input JSON uses A,b,start,target (target is a coordinate list). --certificate
re-audits a saved result without discovery. CLI supplies explicit route caps.
Raw receipts and regenerated fixture files are exact rational data, not Lean
proof terms. No new Actions or Prove2Me publication was requested.

Known lower bounds already apply to several classical pivot rules and even
portfolios of Dantzig/Bland/Largest Increase (Disser--Mosis, arXiv:2309.14034).
That literature does not automatically classify this nonmonotone, target-given
phase rule, but it prevents inferring a universal guarantee from a favorable
Klee--Minty comparison. We make no historical novelty claim for largest gain,
vertex-figure directions, finite face locking or the parabolic-polygon device.

The concrete remaining research task is quantitative: bound genuine original
edges before the next target-face acquisition, or select a globally controlled
route family. The present code supplies exact phase traces, candidate counts,
positive examples and counterexamples for testing such a bound. It does not
solve Polynomial Hirsch or weaken the root's original-facet requirement.
