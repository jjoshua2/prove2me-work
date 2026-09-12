# All-available-row incidence gives a joint carrier resource bound

**Integration update:** all four modules now compile locally at the committed
pin. Two natural-number normalization repairs preserve every theorem hypothesis.
All twenty required declarations pass the transitive standard-axiom audit.
See [current verification](verification/2026-09-12-geodesic-mass/local-audit.json).
The candidate-status language below describes the original submission; hosted
verification and public acceptance are recorded separately when completed.

## Status, dependencies, and contribution

This is an independent mathematical continuation of the Polynomial Hirsch
work, after the selected-run and intrinsic-carrier integration (#201/#202).
It uses the existing deferred certificate from #200 and does not depend on the
unverified feedback-box work in #205 or the separate rank-localized-cuts packet.
The repository was read at the #204 integration baseline
`321f473d871aad2d692595acd97a667d6a648d06`; the final PR records its actual parent.

The four new Lean modules are proof candidates: no local Lean compilation,
transitive-axiom acceptance, hosted verification, or Prove2Me submission is
claimed for them. The mathematical arguments below are complete under their
stated hypotheses. The finite/rational checks have actually been executed.
The run-component correction is proved here and checked computationally, but
only the unrefined aggregate is a new Lean declaration in this packet.

The key improvement is **joint accounting over all available rows**, not a
new special class of polytopes. The existing certificate already stores metric
shortestness, but the preceding estimates used only chordlessness and only
selected rows. Metric shortestness also constrains every unused graph vertex.
The resulting estimate is

    sum_i delta_i + r*s <= r*e + 3*s,

where e=n-d, s is the number of available cuts, r is the number selected, and
delta_i is the minimum intrinsic presentation excess of the SAME actual portal
pair charged on selected cut i. If s=e, their total excess is at most 3e,
regardless of the used-support deficit e-r, cut rank, or factorization.

A second construction retains only an independent target-tight basis rather
than every tight row. It makes exactly e cuts available even at a nonsimple
target. Its radial center is a separate strictly interior point. A third
consequence turns aggregate size into ordinary-edge bounds for dimension-capped
actual carriers, without paying the ambient row count for every call.

## 1. Three-position contact windows, including unused labels

Let p_0,...,p_L be a metric-shortest path in an undirected simple graph G.
For any graph vertex z, say z contacts p_j when z=p_j or z is adjacent to p_j.
Suppose z contacts positions r<=t. There is a walk of length at most two from
p_r through z to p_t, omitting a stationary leg when z equals an endpoint.
Replacing the subpath between these positions produces a walk of length at
most r+2+L-t. Since L realizes the endpoint distance, t-r<=2.

Therefore all positions contacted by z lie in a window of three consecutive
indices. There are at most three, whether or not z belongs to the chosen path.
This is stronger than saying a selected label has at most two selected
neighbors. It controls labels that were available but never selected.

Metric shortestness is essential. A long induced path plus a new off-path
vertex adjacent to every path vertex remains chordless as a sequence. That
vertex contacts arbitrarily many positions; the sequence is no longer a
geodesic. The checker rejects this exact negative control. Three contacts are
possible: add a vertex adjacent to all three vertices of a two-edge geodesic.
This creates another length-two route, not a shorter one.

`PolynomialGeodesicRowIncidence.lean` builds the shortcut using the existing
Walk.take/append/drop API. It then chooses the first contacted support index,
places every contacted label in its three-element window, and double-counts
finite incidences. No geometric or routing-cost premise occurs in this module.

## 2. Put all available cut faces in the incidence count

Let P=Hpoly(a,b) be bounded. Its mixed graph has one label for each available
cut face, plus the clipped old-edge regions and the two endpoint singletons.
Adjacency means a shared parent extreme vertex. Every region is a closed
extreme face of P, and the deferred certificate fixes its shortest mixed path
and actual portal pairs before any local costs are supplied.

Let A be the set of all available cut labels, |A|=s, and S the selected cut
labels on the path, |S|=r. Their row map into the n original inequalities must
be injective. For selected i, set

    t_i = #{ j in A : j=i or j is adjacent to i }.

For each of the s-t_i noncontact labels j, the row face F_j is disjoint from
F_i. Indeed, a nonempty intersection of two closed extreme faces of a compact
parent contains a parent extreme vertex, which would give graph adjacency.
The actual entry and exit vertices p_i,q_i both lie on the nonzero row i.
Consequently their smallest common face C_i lies in F_i, and every noncontact
row is strictly slack throughout C_i, not merely at its endpoints.

The already-established strict-row savings theorem gives

    delta_i + (s-t_i) <= e,              e=n-d,

or equivalently, without truncated subtraction,

    delta_i + s <= e + t_i.                         (1)

There is no premise placing the unselected available labels on the path.
Their absence from the path does not stop their inequalities from excluding
rows from the current carrier's irredundant presentation. This is precisely
what the earlier selected-only estimate left unused.

The Lean geometric adapter invokes the existing
`commonFace_minExcess_add_disjoint_rowFaces_le` and then threads (1) through
`DeferredClipCertificate` without replacing the path or changing a portal.
A strict feasible point for the cut rows proves that a selected tight cut has
a nonzero normal; an empty available row face simply makes no contacts.

## 3. Joint excess mass and the sharper run correction

Count ordered incidences (i,j) with selected i and available j contacting i.
Each available j contacts at most three selected path labels, so

    sum_i t_i <= 3s.                                (2)

Sum (1) and use (2):

    sum_i delta_i + r*s <= r*e + 3*s.                (3)

Formula (3) is subtraction-free and remains meaningful when s>e. When s+a=e
with a>=0 it becomes

    sum_i delta_i <= r*a + 3*s.                     (4)

Here a=e-s is the **availability defect**, not the old used-support deficit
g=e-r. The latter can be arbitrarily large even when a=0. For s=e, (4) is

    sum_i delta_i <= 3e.                            (5)

### Runs and comparison with the preceding estimate

Let c count nonempty runs of selected cut labels on the mixed path. The graph
induced by these labels is a disjoint union of paths. A selected available
label contacts itself and its selected neighbors; their total contribution
is r+2(r-c)=3r-2c. The other s-r available labels contribute at most 3(s-r).
Thus

    sum_i t_i + 2c <= 3s,
    sum_i delta_i + r*s + 2c <= r*e + 3s,            (6)
    sum_i delta_i <= r*(e-s)+3s-2c,  when s<=e.      (7)

Empty support has r=c=0. There is no spurious negative correction.
For s=e and nonempty support, the mass is at most 3e-2c.

The old selected-only run estimate was r*(e-r+3)-2c. Subtracting (7) from it
gives exactly

    (r-3)*(s-r).

The new bound improves it whenever r>3 and unused rows exist, agrees at r=3,
and can be weaker at r<3. Retain the minimum of the two bounds; do not discard
an earlier stronger estimate. The new unrefined bound is formalized as a
candidate in `PolynomialAllCutCarrierMass.lean`. The existing verified
`sum_selected_degrees_add_twice_runStarts` supplies the finite identity needed
to add (6) to Lean; that additional composition is not claimed checked here.

## 4. Nonsimple targets: retain a basis, not every active row

The old target-slack construction deletes just rows strictly slack at target v.
At a nonsimple vertex more than d rows can be tight, so it can leave s<e and
incur the r*(e-s) term. This is avoidable in a full-dimensional strictly
feasible presentation.

The tight normals at a vertex span the ambient dual space. Choose d independent
tight original rows, indexed injectively by e0:Fin d -> Fin n. Retaining these
alone gives an outer cone with injective row map and unique vertex v. To prove
uniqueness, any extreme point z of this cone has active rows spanning the
ambient dual space. All retained right-hand sides equal their evaluations at
v, so z-v annihilates every active row at z and must be zero. Conversely,
injectivity and the tight equalities show v is extreme.

Cap this cone at a level strictly beyond the bounded original parent. The
existing compact-cap classification shows that all other capped vertices are
adjacent to v. The old target-rooted graph budget is therefore still D=1.
Its definition does not require retaining every row active at v; injectivity
of the chosen rows is enough.

Now restore ALL rows outside the chosen basis, exactly n-d=e rows. This list
includes nonbasis rows tight at v, which is why one cannot use v as the radial
center anymore. Choose an independent point o strictly satisfying the parent
inequalities and use o in the existing deferred radial clipping construction.
The endpoint remains v and its old star route still costs one; the center need
not coincide with a route endpoint. Endpoint lifts and all closed/extreme-face
proofs are unchanged. No local route premise enters this construction.

It follows that every target and endpoint in such a presentation, with a
supplied tight basis and strict point, admits a certificate satisfying (5).
`PolynomialBasisStarMass.lean` includes the generalized unique-cone-vertex,
compact star, exactly-e complement, cost-independent certificate, and excess
mass assembly. It does not merely assume that an exactly-e certificate exists.

**Formalization boundary:** the Lean wrapper takes the tight basis and the
strict point as explicit geometric data. Selecting a basis from the existing
vertex-spanning theorem is standard finite linear algebra but not automated
by the new Lean wrapper. Degenerate/redundant zero-equality presentations may
lack a strict point. First pass to an equivalent intrinsic irredundant strict
model, as provided by the existing common-face normalization, rather than
pretending this hypothesis holds for every ambient H-description.

## 5. Intrinsic-size and ordinary-edge consequences

For actual parent-vertex portal pairs, the previously integrated theorem gives
h_i<=delta_i and M_i<=2delta_i. Thus, writing R=r*a+3s,

    sum_i h_i <= R,       sum_i M_i <= 2R.           (8)

At full availability R=3e, this is a joint bound of 3e on dimensions and 6e
on minimum row counts. No rank, support-size, product, or feedback condition
is assumed.

This is not yet a distance bound. However, with actual dimensions h_i<=H,
apply the explicit public Larman input in each minimum intrinsic presentation:

    local_cost_i <= M_i*2^max(h_i-3,0).

The SAME certificate assembles the corresponding ordinary parent edges, giving

    route_cost <= D + 2R*2^max(H-3,0).              (9)

At s=e this is D+6e*2^max(H-3,0). In particular, actual dimensions at most five
give **D+24e**, compared with the earlier D+(4n+3)e adapter that repeatedly
paid the ambient row count. For a target-rooted basis-star certificate D=1.
The dimension condition concerns just selected pairs, not every pair on every
unused facet. It is not established for arbitrary high-dimensional inputs.

A count of exceptional calls also follows directly: for T>0,

    T * #{i:delta_i>=T} <= sum_i delta_i <= R.        (10)

The threshold inequality has a separate Lean candidate. It bounds the number
of exceptional calls, not their individual costs. Combining it with explicit
local routes is valid; replacing those routes by delta_i without justification
is not.

## 6. Exact tests and substantive examples

The self-contained checker validates the graph, every label list, the whole
walk, and its BFS distance. It does not trust a supplied assertion of
shortestness. Its core audit certifies finite incidences and numerical budgets,
not that an arbitrary supplied graph or excess list came from a polytope.
The regression suite independently constructs rational polytopes and computes
the geometric quantities before calling that audit.

### Growing unused-row savings

Start from a 3-simplex and repeatedly truncate one simple vertex by a plane
separating only that vertex. Each step preserves all other vertices and
replaces the chosen vertex by exactly three edge intersections. Strict signs,
rank and active sets are checked at each step; at small sizes a separate full
active-basis enumeration agrees. This gives exact complete vertex lists for
all 96 construction steps exercised across the five fixtures.

The 48-row example has 92 vertices, d=3 and e=s=45. Its actual shortest mixed
repair path selects 15 cuts in one run. The numerical comparison is

    previous selected-only upper bound: 493,
    new all-available, run-refined bound: 133,
    exact available-contact load sum:   101,
    actual carrier excess sum:           59.

The improvement 360 equals (15-3)*(45-15), as predicted. The selected carriers
have dimension two; their independently computed local edge distances assemble
at cost 33. This last number is an assembled cost from finite carrier graph
calculations, not a claim that the full parent distance is 33 or that the new
uniform estimate is optimal. The complete conversation ZIP contains the rational row/vertex fixture and
mixed incidence fixtures. The committed self-contained regression reproduces
all of them; the repository preserves the compact receipt rather than every
large generated incidence table.

### Nonsimple target and full-rank controls

The basis-star suite includes a square pyramid with its nonsimple apex as
target and crosspolytopes through dimension six. In the six-dimensional
crosspolytope, 32 of 64 rows are tight at the target. Retaining a six-row basis
leaves 58 available rows, including **26 rows still tight at the target**.
A separate strict interior point and an explicit containing simplex cap are
verified. This directly exercises the distinction between radial center and
route endpoint; merely reusing the old target-as-center construction fails its
strictness hypotheses here. The available normals have full rank six.

Additional rational positive-packing examples use full cut rank in dimensions
three through five. The theorem is not being tested only in low cut rank.
For r=1 or 2 the preceding bound can be smaller, as the receipt openly records.

### Regression coverage and limitations

The run on this source covers all 1,099 undirected labeled graphs through five
vertices, 23,493 connected ordered endpoint geodesics and 116,503 individual
vertex contact windows. It performs 148,126 all-available incidence audits,
26 geometric certificate instances and 61 actual selected-carrier calculations.
It also checks 48 availability-defect cases and the subtraction-free s>e boundary.
Eight deliberately invalid inputs are rejected. The exact receipt records the
current source hashes, counts and per-example data. Runtime is an observation
of this execution, not a performance guarantee or asymptotic complexity claim.

No test result is a substitute for Lean's kernel. The compact committed receipt is `GEODESIC_ROW_MASS_SUMMARY_2026-09-12.json`;
the full generated receipt is `GEODESIC_ROW_MASS_CHECK_2026-09-12.json`.
The four Lean sources contain
20 axiom printouts for the verification agent; none was compiled in this session.

## 7. What still prevents a uniform polynomial conclusion

The important step is now genuinely joint: a single original available row
can affect only three consecutive selected regions at one recursion level.
But rows can be charged again inside descendant carriers. This theorem does
not yet control that cross-level reuse or provide a uniform edge cost for
one large carrier.

A concrete numerical warning: two subcalls each with excess e-1 satisfy both
the earlier selected-degree caps and the new refined mass bound,

    2(e-1) <= 3e-2.

The independent-call majorant T(e)=1+2T(e-1), with T(0..3)=0,1,2,3, is 511 at
e=10, 524,287 at e=20, and 549,755,813,887 at e=40. These are values of an
allowed *numerical majorant*, not a construction of polytopes realizing the
recursion and not an exponential diameter lower bound. They show exactly why
one must not announce that a factor-three resource sum closes a scalar
polynomial induction.

The next substantive target is to make the three-position incidence windows
persist across nested repairs, or charge/reuse routes for common rows rather
than solving overlapping high-excess subcalls independently. Equal-length
geodesic replacements through unused labels are permitted when they contact
positions two apart, but no theorem here claims such replacements improve
portal costs. That is an actual geometric optimization question, not an
additional assumed diameter oracle.

This packet adds no new open platform child and no cosmetic root dependency.
It supplies a stronger resource theorem, an actual exactly-e basis-star
construction, and concrete edge-cost consequences where the local dimension
factor is controlled. The uniform Polynomial Hirsch obligation is not solved
by these statements.
