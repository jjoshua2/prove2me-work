# Circuit localization, rank loss on faces, and balanced isometric installation

Project: `jjoshua2/prove2me-work`. Continuation of `SingleStepUniversality.md`.
Working date: September 9, 2026, America/New_York; executions cross midnight UTC.

## Evidence and scope

This packet supplies ordinary mathematical proofs of three related statements:

1. A circuit displacement between two vertices lies in a common face of
   dimension at most half the ambient facet excess, with the precise bound below.
2. Restriction to the genuine facets of that face need not preserve the circuit.
   However, the lost neutral rank can be charged against a genuine reduction in
   facet excess. The new rank-defect inequality quantifies the tradeoff.
3. Every bounded polytope can be left completely unchanged as an isometric face
   of an exactly balanced larger polytope, while a chosen pair of its vertices
   becomes one maximal circuit step apart. The direction is realized by an
   actual edge outside the protected face.

The general theorems are NOT Lean-verified. No Lean source or extra uncompiled
candidate chain is added. The finite exact tests are described separately; they
are not a substitute for the proofs. No repository write, Library mutation,
Prove2Me submission, registration, or publication is performed by the original packet.

The standard wedge operation and its graph projection are established tools.
The project's public `Hirsch.spindle_wedge_vertex_graph_projection` already
records a corresponding Proved result in symmetric coordinates. We reuse that
geometry and prove the circuit-preservation calculation in one-sided coordinates;
we do not present the wedge graph lemma itself as new work. Literature priority
for the combined statements in this packet has not been determined.

This is a structural strengthening and a corrected face-reduction diagnostic,
not a new universal polynomial diameter bound. In particular the balanced
single-step equivalence below is NOT a smaller Open child to register.

## 1. Notation and assumptions

Let P={x in R^D : a_i x <= b_i, i=1,...,N} be a bounded full-dimensional
polytope. Unless specified otherwise the N rows are its genuine facets. The
rank/count statements themselves also hold for redundant descriptions, with N
then counting written rows; the intrinsic face count always counts true facets.

For x in P, let I(x) be its tight-row set and f_x the dimension of its minimal
face. For x != y let F be their minimal common face and h=dim F. Then

    lin F = ker A_(I(x) intersect I(y)),
    h = D - rank A_(I(x) intersect I(y)),
    f_x = D - rank A_(I(x)).

The midpoint of x,y is strict in every inequality not tight at both, which
justifies the common-face identity without a simplicity assumption.

A nonzero g is a row circuit when supp(A g) is inclusion-minimal among nonzero
row images. Since A has full column rank, this is equivalent to

    rank {a_i : a_i g=0} = D-1.

Indeed a smaller kernel than the annihilator of g is impossible. If that kernel
had dimension at least two, an additional nonzero row could be made zero without
making the vector zero, contradicting support-minimality. Conversely a
one-dimensional kernel makes any proposed smaller-support vector parallel to g.

## 2. A sharp dimension bound, with nonvertex defects explicit

### Theorem A

If g=y-x is a row circuit, then

    2h <= N-D+1+f_x+f_y.                                      (A1)

In particular, for distinct VERTICES u,v,

    dim F(u,v) <= floor((N-D+1)/2).                            (A2)

No maximal-step hypothesis is needed for (A1). When both endpoints are vertices,
a feasible straight step between them is automatically maximal in both directions.

### Proof

Put C=I(x) intersect I(y), Z={i:a_i g=0}, and partition the remaining rows
according to the positive or negative sign of a_i g. Feasibility implies

    I(x) intersect Z = I(y) intersect Z = C,
    I(x) minus C consists of strictly negative rows,
    I(y) minus C consists of strictly positive rows.

The rank increment from C to I(x) is h-f_x, so I(x) minus C has at least h-f_x
rows. Similarly I(y) minus C has at least h-f_y. The neutral rows Z contain at
least D-1 rows because g is a circuit. These three sets are disjoint. Therefore

    N >= (D-1)+(h-f_x)+(h-f_y),

which proves (A1), and (A2) follows by f_u=f_v=0. QED.

### Consequences that must not be confused

* A full-common-face circuit pair (h=D) requires N>=3D-1.
* In particular, a polytope with N=2D and D>=2 has NO circuit displacement
  between vertices sharing no facet. Balanced and estranged are different
  restrictions; an exactly balanced one-step pair must share a proper face.
* If N-D<=2, every vertex-to-vertex circuit step is already an edge, since h<=1.
* Nonvertex intermediate points require the f_x+f_y terms. They cannot be
  silently discarded when applying this result to a complete circuit walk.

The bound is sharp in every dimension D>=2. Start with the D-dimensional
triangular deformed cube in the preceding packet and its two opposite bit
vertices. Their difference vanishes on no original row and their minimal common
face is the whole cube. The preceding remote-edge installation adds D-1 genuine
facets, strictly retaining both endpoints. The resulting polytope has
N=3D-1, the chosen displacement is a circuit, and the common face still has
h=D. Thus equality holds in (A1). No simplicity assertion about that modified
polytope is needed. Direct saved examples in dimensions 2--5 are audited here.

## 3. What happens to a circuit when passing to the common face

Keep the assumptions of Theorem A. View F in its h-dimensional affine hull,
and retain an irredundant list of its f genuine facet inequalities. Each comes
from an original row, restricted to aff F. Let

    r_F = rank of its genuine facet normals which annihilate g,
    delta = h-1-r_F >= 0.

The direction g is an intrinsic row circuit of the genuine presentation of F
exactly when delta=0. Translations or invertible affine coordinates within F
cannot change r_F, f, or delta.

### Theorem B: the rank-loss / facet-excess budget

    (f-h) + delta <= N-D.                                    (B)

Thus if the circuit property is lost on irredundant restriction (delta>=1),
there is a genuine decrease of at least delta in facet excess. If delta=0,
there need not be any such decrease.

### Proof

Choose D-h independent common tight rows as affine-hull equations for F and
delete those D-h rows. This leaves N-D+h candidate inequalities. The common
rows restrict to zero on lin F.

The restrictions of ALL ambient neutral rows to lin F have kernel exactly
span(g): their common ambient kernel is span(g), which is contained in lin F.
Their restricted rank is therefore h-1.

Select one original row representing each of the f true facets of F. Every
face facet is induced by an original inequality, so this selection is possible.
It uses no common affine-hull row. At most

    N-D+h-f

other rows have been discarded. Deleting this many row vectors can lower rank
by no more than that number. The neutral rank after the deletion is r_F, hence

    delta=(h-1)-r_F <= N-D+h-f.

Rearrange to obtain (B). QED.

This proof handles duplicate facet restrictions by keeping one representative;
proportional copies cannot lower rank when removed. It does not assume that a
nonzero restricted inequality is nonredundant. That distinction is essential.

This is a correct local resource inequality, NOT an induction closing the global
problem. A surviving circuit can leave unchanged excess in an unbalanced full
common face. A lost circuit changes the type of subproblem. Neither case licenses
a cyclic call to a balanced ancestor or an unproved polynomial face-diameter
hypothesis.

## 4. Two complete small examples of nonheredity

### 4.1 Six genuine facets: balanced, simple, and sharp in both inequalities

In coordinates (x,y,z), use

    z >= 0,
    z/2 <= x <= 1-z/2,
    z/2 <= y <= 1-z/2,
    x-y+2z <= 3/2.                                           (C)

Before the last cut the first five inequalities describe a square pyramid
with apex (1/2,1/2,1). The last cut truncates that apex. All six inequalities
are genuine facets; the result is simple, bounded, and full-dimensional.

Take u=(0,0,0), v=(1,1,0), g=(1,1,0). The two neutral rows are

    (0,0,-1), (1,-1,2).

They have rank two, so g is an ambient circuit and u to v is a maximal step.
Their common face is the untouched bottom square z=0, of dimension h=2.
Equation (A1) is exact: 2h=4=N-D+1.

Intrinsically that face is [0,1]^2. The extra row restricts to x-y<=3/2, which
is STRICT on the entire square and redundant. Its removal leaves no neutral
facet normal on (1,1), so r_F=0, delta=1, f=4. Equation (B) is exact too:

    (f-h)+delta = (4-2)+1 = 3 = N-D.

The pair has graph distance two, not one. No ambient edge is parallel to g in
this six-facet example: such an edge would have both neutral rows tight, but
z=0 and x-y=3/2 do not meet this square.

### 4.2 Seven genuine facets: the circuit direction is realized elsewhere

Instead use

    [0,1]^3 intersect {x-y+2z <= 5/2}.

The same bottom square, endpoints, and intrinsic failure remain. This time an
actual upper edge joins (1/2,0,1) to (1,1/2,1), parallel to g. Thus requiring
that the ambient circuit be realized by an actual edge does not repair
nonheredity. The full polytope has ten vertices; the independent auditor
reconstructs them all and checks every edge and facet witness.

Both examples have vertex checkpoints already. Face-preserving rounding cannot
fix a loss caused by removing intrinsically redundant rows.

## 5. Preserve an ENTIRE polytope as an isometric face

### Theorem C: isometric face-preserving installation

Let P be any bounded full-dimensional d-polytope with n genuine facets, and let
u,v be distinct vertices. There is a bounded full-dimensional (d+1)-polytope R
with exactly n+d+1 genuine facets such that:

1. P_0={(x,0):x in P} is an unchanged facet of R.
2. R's vertex graph has an edge/stay map pi to P's vertex graph fixing P_0.
3. Every original graph edge remains in P_0. Consequently ALL original vertex
   pair distances are exactly preserved: dist_R((a,0),(b,0))=dist_P(a,b).
4. (v-u,0) is a row circuit, and (u,0) to (v,0) is maximal in both orientations.
5. An actual edge in the top plane t=1 has that direction, outside P_0.
6. For rational input all choices can be rational.

No simplicity assertion about R is needed. This theorem strengthens the previous
same-dimensional installation, which removed one old vertex and supplied only
a non-shortening inequality on the retained set.

### Construction

Start with the prism P times [0,1]. If d=1, use the prism itself; it already has
n+d+1=4 facets and the needed top edge. Suppose d>=2.

If g=v-u is not parallel to any old edge, put r=g. Otherwise choose ANY rational
nonzero direction r not parallel to an old edge; there are only finitely many
excluded lines. The desired g already has the old circuit rank in the second case.

Use the remote-cap normal construction from the preceding packet, with r:
choose d-1 independent h_j perpendicular to r, all uniquely maximized at one
old vertex q, and shallow thresholds beta_j=h_j(z), with z interior to P near q,
such that

    h_j(p)<beta_j<h_j(q) for all old vertices p!=q.

Here uniqueness follows by choosing an r-perpendicular normal not annihilating
any old edge; small independent perturbations preserve its maximizing vertex.
Set M_j=h_j(q)-beta_j+1>0 and impose the sheared cuts

    h_j(x)+M_j t <= beta_j+M_j = h_j(q)+1.                    (D)

On the entire bottom copy every cut is strict, with gap at least one. On the
top plane these are exactly the preceding shallow cuts h_j(x)<=beta_j. Among
all old prism vertices, ONLY (q,1) is removed, and every cut strictly retains
all the other old prism vertices.

### Genuine facets and feasibility

A point (o,t) with o interior to P and sufficiently small t>0 is strict in all
rows, so R is full-dimensional. It is bounded as a subset of the prism.

Every old side facet retains a relatively open patch near its bottom copy.
The bottom is unchanged. The top has a full-dimensional clipped copy of P,
so it also remains a facet. Each new cut has a point on its top facet patch
where all other new cuts and old P rows are strict. Move slightly below t=1,
adjusting x to keep that one new cut at equality. This gives a point where
only that new row is tight, proving it is a genuine facet in R. Thus the count
is n+2+(d-1)=n+d+1, not merely a redundant presentation count.

### Edge/stay projection and exact metric preservation

Apply the preceding single-removed-vertex graph-map argument to the PRISM:
retain each old prism vertex and map all newly created vertices to (q,1).
An edge incident to a retained prism vertex has no new inequality tight near
that vertex. It is a clipped part of an old prism edge. Its other old endpoint
is either retained, in which case the whole old edge survived, or is (q,1).
An edge with two new endpoints maps to a stay.

Compose this map with the prism projection to P. Prism edges project to old
P edges or stays, so the composite pi has the stated property and fixes every
bottom vertex. The bottom copy contains every old edge; mapping paths down
and lifting old paths along the bottom prove both distance inequalities.

In particular the cap cannot use an upper-layer shortcut to shorten distances
inside the protected face. All original faces, coordinates, and intrinsic edge
metrics in P_0 are retained, not approximated.

### Circuit and actual parallel edge

If r=g, the top plane t=1 and all d-1 new planes meet in the segment

    {(z+lambda g,1):z+lambda g in P}.

It is nondegenerate because z is interior, and is an exposed edge of R. Their
normals give d independent neutral rows in ambient dimension d+1, proving
that (g,0) is a circuit.

If g was already an old edge direction, its neutral rows already have rank
 d-1. The prism's height row raises this to d, and adding further inequalities
cannot destroy the circuit: all old neutral rows remain, and no neutral rank
can exceed d. An upper copy of any old g-edge retains a nontrivial upper edge
segment after removal of just (q,1), so an actual g-edge still lies at t=1.

In both cases the bottom section is exactly P. Extremeness of u,v means the
line through them meets P in [u,v], proving maximality in both orientations.
QED.

### Optional objective-preserving strengthening

For any linear objective c on P, pull it back by ignoring the added coordinates.
If an R edge maps to a nontrivial P edge, its objective difference has exactly
the same sign as on that old edge: it is a positive-length subsegment of an
old horizontal prism edge. Edges mapping to stays can be deleted. Thus minimum
weakly monotone path lengths between bottom vertices are preserved too, including
unreachable pairs. The same sign argument also applies to strictly monotone
paths after stays are removed. The finite tests check the weak version for two
specified objectives, not all possible objectives by sampling.

## 6. Wedges preserve the chosen circuit and the protected metric

For a genuine facet a_f x<=b_f of a bounded polytope S, take the one-sided wedge

    W={(x,t): a_i x<=b_i (i!=f), 0<=t, a_f x+t<=b_f}.           (E)

Its floor t=0 and roof t=b_f-a_f x are affine copies of S. Its vertices are
exactly the two lifts of every old vertex, coincident over the chosen facet.
Any edge either lies in a floor/roof or is vertical over an old vertex. Hence
projection sends each edge to an old edge or a stay; the floor is isometric.
It has one extra dimension and one extra genuine facet, and remains bounded
and full-dimensional. These are standard wedge facts already used in the project.

The additional calculation is circuit preservation on the floor. For a circuit g
of S, the new floor row vanishes on (g,0). All old neutral rows survive with last
coordinate zero, except possibly row f, which becomes (a_f,1). When f was neutral,
subtract the height row to recover (a_f,0). Therefore

    neutral_rank_W((g,0)) = neutral_rank_S(g)+1.

The circuit remains a circuit. The endpoint line is the old line in the floor,
so maximality remains true. An existing edge realizing g lifts as a floor edge.
These claims do not require a generic position or a simple polytope.

## 7. Exact balance without changing the original graph metric

The prism-cap R in Theorem C has

    dimension D_0=d+1, facets N_0=n+d+1, excess N_0-D_0=n.

A bounded full-dimensional d-polytope has n>=d+1. Consequently

    k=N_0-2D_0=n-d-1>=0.

Apply k wedges. Each adds one dimension and one facet and retains the whole
previous polytope as its floor. The final polytope Q has

    dimension n, facets 2n.                                  (F)

The copy of P remains an actual face, all distances between its vertices are
exactly unchanged, and the chosen pair is one maximal circuit step with an
actual realizing edge outside that face. The composite edge/stay projection
is explicit. All extra coordinates of the protected P are zero; the realizing
edge retains original prism coordinate t=1, so it is genuinely outside P.

The test implementation wedges first over the protected bottom facet, then over
the most recently added floor. If R has V_0 vertices and P has V vertices,
this gives V_0+k(V_0-V) vertices, equivalently

    final vertices = V + (k+1)(V_0-V).

This is linear in the number of wedges for a fixed R, not a claim that V_0,
input bit lengths, or the full construction running time are polynomial.

### Corollary: balanced one-step refinement still contains the whole problem

A polynomial edge-distance bound C(N+D)^p for single maximal circuit steps
ONLY in exactly balanced polytopes would imply, by (F),

    dist_P(u,v) = dist_Q(u',v') <= C(3n)^p <= 3^p C(n+d)^p.

The exponent p is unchanged. The implication holds with the further requirement
that the circuit direction is realized by an edge outside the protected face.
The reverse implication from a general polynomial diameter bound is immediate.
No cubic circuit theorem is used.

The pair's minimum common face is the old common face, not necessarily all of P.
Its dimension h is unchanged. The usual endpoint tight-row count gives
h<=min(d,n-d)<=floor(n/2), so the protected pair can even be required to have
common-face dimension at most half the balanced ambient dimension.

This does not give an estranged balanced one-step pair: Theorem A proves that
would be impossible in dimension >=2. When the original input has n=2d and the
chosen endpoints are estranged, the final Q has dimension 2d and the unchanged
common face has dimension d, saturating the integer half-dimensional bound.

Thus "first restrict balanced one-step pairs to their small common face" is a
valid localization, but NOT automatically a circuit-preserving reduction on
irredundant presentations. The original arbitrary polytope can be present there
literally unchanged, with its entire metric protected from outside shortcuts.

## 8. Executed finite evidence

| Executed quantity | Count |
|---|---:|
| Original models / chosen-pair constructions | 10 / 12 |
| Fully checked construction stages / wedges | 37 / 25 |
| Original protected unordered-pair distance comparisons | 5,228 |
| Weakly monotone ordered-pair comparisons, two objectives | 21,862 |
| Edge occurrences checked under the retraction | 10,629 |
| Explicit genuine-facet witnesses | 461 |
| Independent input / prism-cap square systems | 551 / 12,029 |
| Vertex occurrences independently checked at all stages | 2,845 |
| Maximal circuit-step defect certificates | 336 |
| Such steps involving a nonvertex endpoint | 264 |
| Additional sharpness models / independent square systems | 4 / 2,398 |
| Deliberately corrupted certificate types rejected | 5 |

The largest final model has dimension 10, twenty genuine facets, 445 vertices,
and 2,225 edges. All of its 40 original face vertices retain their pairwise
metrics. Counts above are occurrences across models and stages, not an assertion
that those are all distinct geometric objects. The original-model diagnostic
also checks all 1,102 unordered distinct vertex pairs, including 216 circuit
pairs and 24 estranged balanced pairs which correctly are NOT circuits.

The saved constructor and independent-audit JSON give all actual counts and
inputs. Ten original models yield twelve chosen-pair constructions, thirty-seven
stages, and twenty-five wedges. Examples include the earlier 4D/5D Dantzig
witnesses, a nonsimple octahedron, the moving-cut cube, and the deformed-cube
direction control.

At every stage the tests check ALL pairs of original protected vertices, not
only the selected circuit pair. They do NOT claim all-pairs circuit conversion
or a diameter bound for arbitrary newly created vertex pairs.

The final models include an 8-dimensional, 16-facet polytope retaining the 4D
Dantzig polytope as an isometric 14-vertex face, and a 10-dimensional, 20-facet
polytope retaining the 5D Dantzig polytope as an isometric 40-vertex face. The
selected distances remain four and five, respectively, while both ambient
circuit distances are one.

The independent auditor imports neither the constructor nor its rational
polytope utility. It uses integer-preserving elimination and exhausts every
square row system of every input and prism-cap stage. Subsequent wedge vertices
are independently reconstructed as two explicit affine copies, justified by the
proved wedge vertex description; all their edges are recomputed from exact
common-tight-row ranks. Those later stages are NOT claimed to have undergone
exhaustive row-base enumeration.

The circuit-rank defect checks independently enumerate each common face from
its affine-hull equations and the remaining rows, identify genuine restricted
facets by affine dimension, and compute the surviving neutral rank. A separate
suite checks maximal circuit steps from all vertices, all edge midpoints, and
the centre in four small models, including nonvertex endpoints.

Strict feasibility and genuine facets have explicit rational witnesses.
Boundedness is certified by a nonnegative row dependence whose positively
weighted normals span the ambient space. All edge/stay maps, floor embeddings,
parallel-edge witnesses, and forward/reverse blocking rows are checked exactly.
The auditor rejects five kinds of corrupted certificate. Timing failures or
serialization attempts are not counted as successful evidence.

No floating-point LP, heuristic rank, or original shortest-path oracle is used
to choose cuts. Breadth-first search is used after construction to audit metrics.

## 9. Reproduction and next task

From the original packet root run

    bash scripts/verify_balanced_isometric_circuit.sh

Only the Python standard library is required; assertions must be enabled. The
script reruns the constructor and independent auditor and compares their outputs
with the saved JSON. Source hashes, complete-run records, patch checks, and the
absence of a Lean check appear in `balanced_isometric_circuit_receipt.json`.

The next reduction should retain the actual intrinsic row model and the lost
neutral-rank variable delta, rather than assuming ambient circuit status survives
row deletion. Equations (A) and (B) are valid local constraints. They do not
establish the missing polynomial cost of a connected repair network. The balanced
isometric construction explains why replacing the open problem by a universal
balanced single-step statement would not produce a genuinely smaller child.

No publication or additional generic graph-routing child is proposed here.

## 10. Provenance and attribution

* Supplied current-state handoff: separate representation from polynomial cost;
  do not register equivalent or cyclic smaller children; check actual geometry.
* Prior `SingleStepUniversality.md` and exact packet: the unique-vertex cap,
  its edge/stay map, the local enumeration argument, and deformed-cube sharpness.
  The new prism shear leaves the complete original polytope untouched.
* The standard wedge graph projection is recorded as Proved on Prove2Me under
  `Hirsch.spindle_wedge_vertex_graph_projection`, theorem
  `44a39279-7644-45f2-95c1-845c1b59c053`.
* Primary background on circuits and edge walks: Borgwardt, De Loera, Finhold,
  *Edges versus circuits: a hierarchy of diameters in polyhedra*, arXiv:1409.7638.
  It is not cited as establishing the new combined statements.

The standard wedge facts are reused, not credited as new. The combined
localization/rank-defect/isometric circuit installation has not received a
literature-priority determination. It has ordinary proofs and exact finite
certificates, not a Lean kernel verdict or Prove2Me ACCEPTED submission.
