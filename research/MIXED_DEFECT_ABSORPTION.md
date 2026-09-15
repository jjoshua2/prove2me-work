# Counted macros beyond single-step defect descent

## Status and pre-merge reconciliation

This is written mathematical research and exact Python, NOT a Lean compilation,
axiom audit or Prove2Me acceptance. It does not solve Polynomial Hirsch.
Input polytopes are simple, bounded and full-dimensional, with genuine ORIGINAL
facet inequalities. All route bounds count genuine original edges.

The other agent's #262 merged at932a9fad51b50f7482ad4809d897c3f5fcc2c8df just
before #263 opened. The two preparations overlapped on the shielding/absorption
criterion and cyclic distance-two stage. That overlap was reconciled BEFORE
merge: the final source IMPORTS scripts/stellar_defect_budget.py unchanged,
Git blob b51e2c3edec2c85026344566978561eb430050ec. The shared criterion, full
birth/death accounting and first cyclic stage are credited to #262, not claimed
as another new repository theorem. #261's carriers and #258's segment/edge
auditors are also unchanged. All tests were rerun with these FIVE dependencies.

The distinct contributions are a POLYTOPAL stall for the broader #262 budget
rule, a verified bounded-macro crossing of that stall, a sharper two-half finish
to the cyclic schedule, and an original-H-to-macro-to-original-edge adapter.
The earlier independently prepared version is retained in Git history, not
silently described as the final reconciled implementation.

## 1. Reused exact accounting and the new macro theorem

For a finite complex K let H(K) be its minimal nonfaces of size at least three,
and put W(K)=sum_{N in H(K)}(|N|-2). In the dual of a polytope these are minimal
incompatible original facet families. W=0 is exactly the flag condition.

For a FACE edge E={u,v}, a stellar subdivision inserts z. Its minimal nonfaces
are the inclusion-minimal members of

    {E}, old N not containing E, and {z} union(N minus E) for old N meeting E.

This is #261's exact membership formula. #262 refines it by minimizing the
residues N-E. If c higher nonfaces contain E and the genuinely new higher
descendants have total weight D, its exact identity is

    W_after = W_before-c+D.

Shielding means D=0. An explicit equivalent certificate is: every mixed high
N with |N intersect E|=1 has an old minimal-nonface blocker B such that
(i) E is contained in B or B is a missing pair meeting E, and (ii) B-E is
contained in N-E. A shared high descendant or pair then makes that mixed
child nonminimal. Equal higher incidence from #261 is only a special case.
The final program delegates the exact update to #262 and independently checks
the supplied blocker table. It does not retain a duplicate accounting engine.

An arbitrary edge subdivision can have D>=c. The new planner therefore uses
CHECKPOINTS. Prefer a shielded decreasing step; if none exists, try one arbitrary
productive edge followed by shielded steps. Accept the resulting macro only
if it has at most ell subdivisions and W at its endpoint is strictly smaller.
Every intermediate complex and exact weight is verified; individual moves may
be neutral or increasing. A macro's claimed endpoint improvement is not trusted.

If accepted macros have total t subdivisions, integer descent gives

    t <= ell*(W_initial-W_residual).                           (1)

Indeed each macro costs at most ell, decreases the nonnegative integer W by
at least one, and the decreases telescope. This elementary accounting also
holds for other explicitly checked bounded macros; the supplied producer
searches only the narrower one-bridge-then-shielded class.

If the final complex is flag, it has M=m+t vertices and the original sphere
dimension. The classical Adiprasito--Benedetti normal-flag theorem supplies a
path of at most M-d refined edges. By the existing carriers,

    diameter(original P) <= m-d+t <= m-d+ell*W_initial.          (2)

This is CONDITIONAL ON COMPLETION. If higher defects remain, use the established
residual-block refinement with M=m+t-|B|+f_B and claim only the actual M-d. The
macro prefix does not make that residual cost small. Initial W can itself be
exponential in original input size. A trial cap is incomplete search, not proof
of no better macro; ell=3 is not asserted universally sufficient. Neither (1)
nor (2) is an unrestricted Polynomial Hirsch proof or a polynomial runtime.

## 2. A genuine polytopal plateau, including #262's actual default replay

The fixture gives ten integer points in dimension five. Subtract their mean
and polarize with inequalities (point_i-mean).x<=1. The original polytope has
36 simple vertices and ten genuine facets. The reference reconstructs all
252 square active systems using exact rational arithmetic and checks original
facet relative-interior witnesses. The exploratory floating hull that helped
FIND the fixture is not used as final verification data.

Three valid stellar subdivisions produce W9->7->5->3. The remaining higher
nonfaces are precisely

    {2,3,4}, {2,7,8}, {4,5,7}.

All other minimal nonfaces are pairs, preserved in the detailed fixture. At
this state every productive edge gives the following next weights:

    23:3, 24:4, 27:4, 28:3, 34:3,
    45:3, 47:4, 57:3, 78:3.

An edge contained in no higher minimal nonface cannot remove any old higher
nonface, so it cannot decrease W either. Hence NO single stellar edge move
lowers this actual potential. This is not merely the failure of one tie-break.
The state is polytopal: it is obtained from an exactly realized dual polytopal
boundary by valid edge subdivisions, realizable by shallow primal ridge cuts.

The final regression executes #262's unchanged 'budget' policy on the ORIGINAL
input. It chooses edges01,56,08 and returns status stalled, W3, n13 after three
moves. Its terminal complex exactly matches the one above. Running that same
policy again on the terminal complex returns stalled with zero moves. This
policy already permits new defects when D<c, so the example goes beyond a
failure of shielding alone. Both the original baseline packet and the complete
independent neighbor-weight scan are saved. The assertion concerns this actual
greedy run and its reachable state; it does not assert every strictly descending
choice from the original input must reach the same plateau.

The macro chooses edge34 with W3->3, then two shielded moves give3->2->0.
The complete path of weights is

    9 -> 7 -> 5 -> 3 -> 3 -> 2 -> 0.

Six subdivisions give a flag refinement on16 vertices, so the original5D
polytope has the certified all-pairs bound11 from this construction. The old
#261 twin-plus-block completion used266 refined vertices. #262's budget run
itself returns a truthful partial/stalled result, not that block completion.
One of our sampled endpoint routes is still nonshortest. We do not equate a
small refinement certificate with optimal route selection.

## 3. Original-edge transport is not an arbitrary projection

A maximal simplex containing the fresh stellar vertex z contains exactly one
of u,v. Replacing z by {u,v} therefore gives an old maximal simplex of the same
size d. Adjacent new maximal simplices share a ridge; its old carrier has at
least d-1 labels. Their carriers are equal or adjacent old maximal simplices.
This holds whether a move increases, preserves or decreases W.

Compose this map through every intermediate subdivision, then the already
proved residual-block carrier if needed. Remove stationary consecutive
carriers. Every remaining step is an original adjacency and length cannot
increase. Compatible endpoint lifts preserve original common facets. The
program checks the carrier relation at EVERY stage and independently checks
the final coordinate edges using original inverse identities and the maximal
feasible ratio. No extension edge is projected and assumed to remain an edge.

The path comes from the flag subdivision, not necessarily from the restricted
original combinatorial-segment family. It may reenter an original facet; the
regression deliberately preserves such a case. The existing exponential lower
bound for raw original combinatorial segments is not contradicted.

## 4. A sharper finish to the shared cyclic schedule

For C(n,4), n>=6, label moment-curve vertices cyclically0,...,n-1. Higher minimal
nonfaces are exactly stable triples of this cycle, numbering n(n-4)(n-5)/6.
The supporting quartic through four moment parameters has a constant sign on
all other parameters precisely for the usual two-adjacent-pair facets,
including a wrap pair. A four-set without a stable triple is a four-path or
two disjoint cycle edges, hence such a facet. Every larger set contains a
stable triple when n>=6. Thus this is the COMPLETE higher-nonface family,
not an incomplete sample of triples.

### Common first stage, credited to #262

Process cyclic distance-two pairs E={i-1,i+1}, omitting any with no surviving
higher triple. A mixed stable triple {u,a,b}, u in E, cannot have both a,b
adjacent to the other endpoint v: one of v's neighbors is adjacent to u.
Choose w in {a,b} nonadjacent to v. If vw was previously subdivided, its missing
pair blocks the mixed child. Otherwise {u,v,w} is a surviving shared high
triple and blocks it. Its other pairs survive because the mixed triple and
current E survive. This is a valid shielding certificate. At the end no high
triple contains a distance-two pair; only original triples have survived.

### New two-half completion

After that first stage, EVERY productive pair of original labels is shielded.
The only possible failure of the preceding argument would have a,b as the two
neighbors of v, a distance-two pair which no surviving triple can contain.

Divide the cyclic order into two contiguous parts of sizes a=floor(n/2) and
b=ceil(n/2). Process only pairs internal to these parts when still productive.
Every triple has a same-part pair, so this finishes. Each original pair is
used at most once. The first stage has at most n distance-two pairs. Within
parts there are binom(a,2)+binom(b,2)-(n-2) noncycle pairs, of which n-4 are
already distance-two pairs. Therefore

    T_n <= binom(a,2)+binom(b,2)-n+6.                           (3)

This improves the previous #262 bound n(n-3)/2, roughly halving its leading
coefficient. The new contribution is this stronger finish/count, not another
claim to discover quadratic cyclic flagification. The all-size proof covers
all n>=6; numerical schedule instances n6..16 are additional checks.
Greedy shielding at n7/n8 uses4/6 moves, whereas this explicit uniform schedule
uses5/8. The report keeps those procedures separate.

## 5. Geometric multiwedges and exact scope of the class extension

A wedge along a facet a.x<=b replaces that row by a.x+s<=b and a.x-s<=b,
retaining the other rows. It adds one dimension and one genuine facet. Its
vertices over an old off-facet vertex are the two slack endpoints; an old
on-facet vertex has just the one lift. Convex combinations of old vertices
and their available slack intervals prove these exhaust the wedge. Simplicity
and boundedness persist.

A minimal nonface containing the old row replaces it by BOTH new row labels;
others are unchanged. A set with only one copy can meet its equality by choosing
the sign of the extra coordinate, so it gives no new minimal obstruction.
Repeated wedges replace original cyclic label i by a group of a_i labels.
With m=sum a_i the new dimension is d=4+m-n, and its high nonfaces are exactly
the unions of clone groups belonging to stable triples.

Compress each clone group to one representative in a_i-1 of the old safe
moves, then apply the common cyclic first stage and our two-half completion.
The exact count is

    t <= m-n+T_n,    M<=2m-n+T_n,
    diameter(original)<=M-d<=m-4+T_n=O(m^2).                    (4)

For n>=7 the higher-nonface incidence is connected, excluding a nontrivial
combinatorial Cartesian product. Distance-two connections connect each parity
class and a stable triple joins them when necessary. Replacing a label by a
group preserves that connectivity. n6 is deliberately excluded from the
nonproduct claim; its two stable triples are disjoint. No Minkowski
indecomposability claim is made.

This is a cheap FLAG REFINEMENT class, not a newly discovered polynomial-
diameter class. The ordinary wedge graph consists of two copies of the base
graph identified along its facet, with vertical edges elsewhere. Diameter
rises by at most one per wedge; a fixed-four-dimensional base already has
polynomial bounds. That easier fact is retained rather than inflating (4).
The value is an explicit counted refinement compatible with the general
carrier framework, where the preceding residual refinement was much larger.

## 6. Actual tests, independent references and limitations

After reconciliation all sources use the exact unchanged #262 account. The
abstract stage checks114 labelled four-vertex complexes plus210 seeded random
antichains on5--7 labels. It compares the full update against literal maximal-
simplex subdivision and independent nonface reconstruction:3189 updates,
1013 shielded updates (546 unequal-incidence),891 blocker records and10550
pure-carrier adjacencies. It retains931 W-increasing arbitrary moves. Abstract
inputs are not all polytopal; no normal-flag diameter theorem is applied to them.

Six independently reconstructed original-H models give58 endpoint pairs:
123 delivered edges versus129 for #261 and122 BFS. One route is nonshortest
and one reenters an original facet. There are125 refined steps,two stationary
carriers,2222 LP calls and10500 internal pivots. The reference evaluates502
exact square systems and genuine-facet witnesses. The models are a targeted
stress suite, not a statistical universal-superiority claim.

#262's budget baseline is executed separately for all six inputs. It completes
five (with the same cyclic4/7 and4/8 refined counts11 and14), but stalls on the
five-dimensional plateau. The new macro completes that one. Earlier twin-only
refinements had M70/96/126 on cyclic7/8/9, now11/14/18 using the shared shielded
rule. Those cyclic improvements belong to the shared/#262 result; the plateau
crossing to M16 is the distinct macro example.

The family stage checks11 cycle sizes and9 original wedge instances. For n8
and three clones per label: dimension20,24 original facets,M48 versus previous
M128,bound28,selected route4. For n12 and two clones: dimension16,24 facets,
M60 versus264,bound44,selected route12. These are selected routes, not tests of
all endpoint pairs. Base4D graphs only choose test endpoints and confirm their
moment-curve structure. One10D/12-facet wedge additionally gets full exact
final-H graph/nonface reconstruction (66 square systems,36 vertices,distance2).
Other larger instances use the proved wedge history plus actual original-edge
audits, not full final graph enumeration or generic LP classification.

Thirteen malformed/capped types are rejected. Six complete stored audits run
with LP,inverse,basis/intersection production and planner selection disabled.
Finite classification, BFS and recursion ARE still replayed. Complete original
minimal-nonface discovery and trial exploration can be exponential. Caps are
explicit; no efficient recognition or universal macro completion is claimed.
Global simplicity/genuine-facet assumptions are independently established for
the test models, not inferred from a few visited bases. Python/JSON is not
Lean-extracted or otherwise formally verified.

All three stages reproduce in a clean workspace with two new scripts, one
integer fixture and FIVE byte-identical existing dependencies. All nontiming
report/source fields and both full generated fixture files match exactly.
Detailed reports/certificates regenerate and are bundled. Repository summaries
are explicitly derived local records, not platform receipts. No Actions or
Prove2Me workflow is triggered for this research-only contribution.

    python3 scripts/test_mixed_defect_absorption.py --stage abstract
    python3 scripts/test_mixed_defect_absorption.py --stage geometry
    python3 scripts/test_mixed_defect_absorption.py --stage family

## 7. Literature guard and the remaining general obstacle

The classical short refined path is Adiprasito--Benedetti arXiv1303.3598.
Stellar theory is classical; this contribution claims no historical priority
for all equivalent formulations. #262 supplies the reused local accounting,
not a claim that every edge reduces defects.

A relevant search trap is arXiv1303.5885, whose abstract advertises a strong
missing-face-size bound but whose record explicitly says WITHDRAWN and that
the main proof has a mistake. That bound is NOT an input. A surviving abstract
must not be used to convert these scoped results into a general theorem.
Primary records: https://arxiv.org/abs/1303.3598 and
https://arxiv.org/abs/1303.5885 (withdrawn, not a valid imported bound).

The remaining problem is an original-size bound for a successful refinement
schedule on arbitrary dual polytopal spheres, or a different genuine-edge
argument. The new example shows that single-step strict descent is insufficient,
and that bounded checkpoints can sometimes repair it. It does not prove a
fixed macro horizon sufficient everywhere. Neither polynomial initial W,
cheap universal bridges nor a cheap residual block is inserted as an assumed
lemma. The conjecture remains open; the result is the exact plateau certificate,
a successful crossing, and stronger counted schedules on stated classes.
