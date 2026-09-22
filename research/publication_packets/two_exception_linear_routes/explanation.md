# Linear original-row routing with two exceptions

## Exact statement

Let P be both the convex hull of a finite real family C in ambient dimension d
and the set defined by its m original linear inequalities. Let u,v be ACTUAL
extreme points of P. Let B contain at most two original row labels. Every row
tight at target v outside B is required to take its boundary value and at most
one other value on all actual vertices. Exceptional rows and rows not tight at
v can have arbitrarily many levels. The theorem constructs an original-edge
route from u to v of length at most (m-d)+m, preserving every acquired target
row, including exceptional ones.

The natural-number expression is exactly (m-d)+m. Actual vertex extremality
already implies d<=m, so this is 2m-d, not a truncated negative bound. Each edge
is a WHOLE nondegenerate Mathlib IsExtreme segment in the ORIGINAL P. The public
type does not separately assert original-ambient exposure, shortestness, simple
paths, global monotonicity or all-facet nonrevisiting.

Exact H/hull equality, endpoint extremality and the outside-B two-level condition
remain explicit. The at-most-two hypothesis is not replaced by an assumed plane,
rank, basis, vertex count, graph or cheap finishing route. C can have redundant
or interior generators; rows may be redundant; nonsimple and lower-dimensional
bodies, zero dimensions, empty B, nontarget exceptions and equal endpoints remain.

## 1. Reuse the proved good-row entry and residual dimension

Accepted #325 constructs a prefix acquiring all good target rows by genuine
original improving edges inside the retained target-lock face. Each prefix edge
acquires a new good original label, while every existing target lock remains.
Its cost is at most the number initially missing, which is at most m-d.

Let N be the common kernel of the fixed good target rows. Evaluation on B is
injective on N: a motion vanishing also on the exceptional evaluations vanishes
on every row tight at v, hence is zero by the accepted active-kernel theorem.
Consequently dim(N)<=|B|<=2. Every difference of two actual residual vertices
lies in N. This is derived geometry, not a residual-dimension premise.

## 2. At most two extreme points in an affine line

For any finite family V of extreme points of an ambient set, suppose every
pairwise difference lies in an affine image of a space of dimension at most one.
Derive a single spanning vector and real parameters for V. Take attained minimum
and maximum parameters. Any third point would lie strictly between them; the
explicit positive convex coefficients contradict its ambient extremality.
Thus |V|<=2. No convexity or ordered vertex enumeration oracle is needed for this
helper; the endpoints themselves belong to the ambient set.

## 3. Count genuine original-row incidences in the plane

Suppose dim(N)=2. Exclude every original row whose RESTRICTION to N is zero.
Such rows may be tight at all residual vertices and must not be counted as
one-dimensional slices. Both sides of the incidence argument use the same
nonzero-restriction filter.

At each actual residual vertex x, evaluation on all active NONZERO restricted
rows is injective on N. Indeed zero restrictions add nothing, and the full active
kernel at x is trivial. Finite-dimensional rank therefore implies at least two
such incident original rows. This does not assume simplicity or a selected basis.

For each original row with nonzero restriction to N, its kernel is a proper
subspace of N and has dimension at most one. Differences of residual vertices
on its equality slice lie in that kernel. Step 2 proves that at most TWO actual
residual vertices can lie on this slice. This remains true with redundant rows,
a lower-dimensional actual residual body, or a row tight everywhere on that body.

Double-count actual pairs (vertex, incident nonzero original row):

    2 |V| <= incidence count <= 2 |nonzero original rows| <= 2m.

Hence |V|<=m when dim(N)=2. When dim(N)<=1, Step 2 gives |V|<=2. With m=0,
active-kernel triviality implies that every two actual extreme points coincide.
These boundary cases yield the uniform, slightly slack bound |V|<=m+1.
This avoids all optional-slot encodings and all enumeration of possible bases.

## 4. Construct the route, rather than assuming it

Reuse the accepted strict separator of v and the genuine improving-edge
construction inside each current target-lock face. Strict objective increase
orders the finitely many actual residual vertices. Strong induction on the
number of vertices above the current objective constructs the entire suffix,
with length+1<=|V|. The new incidence estimate makes its cost at most m.
Append it to the actual good-row prefix to obtain (m-d)+m.

Residual steps need not acquire a new row. The two-exception hexagon from
(0,0) to (2,2) has distance three, two initially missing target labels, and no
acquiring source neighbor. The public statement preserves locks but does not
repeat the stronger every-step-acquisition conclusion of #323/#324.

## Relation to prior work and limits

For two exceptions #325 gives (m-d)+((m+1)^2-1), quadratic in original m. This
packet gives (m-d)+m, linear in the SAME original row count, independently of
how many values the two exceptional rows take. #324 remains sharper with at most
one exception. #326 independently studies arbitrary positive affine roofs over
0/1 bases; this packet neither uses its unaccepted source nor modifies that work.

This is classical line/plane convex geometry in substance, not a historical-first
or best-known-diameter claim. A full polygon boundary argument can sharpen some
constants, but is not silently asserted here. When three independent exceptional
motions remain, a nonzero row slice may be two-dimensional and contain many
vertices; the incidence bound above does not extend automatically. Uniform-degree
Polynomial Hirsch for arbitrary carriers is not established.

## Formal source and execution boundary

The source copies accepted #325 helper blocks byte-for-byte, omitting only its
old public root/prints and unused target-two-level route, optional-code and old
residual-bound blocks. The accepted retained theorem bodies are unchanged. New
code proves affine-line cardinality, nonzero incidence rank, row-slice cardinality,
double-counting and the linear route assembly. Eight final transitive axiom reports
are requested, including the complete public solution. The target preamble uses
only imports/open/options and its public type matches solution exactly.

Local Lean/Lake and checked caches are absent, and release/raw-host DNS probes
failed. Source matching, exact tests, and JSON/certificate replays are NOT Lean
compilation. This complete candidate is prepared for one normal pinned hosted
compiler/axiom/publication gate. Any failure must remain visible; no repeated
speculative hosted editing or weaker replacement statement is authorized.

The exact test suite includes arbitrary small H hulls, explicit affine equations,
redundant rows, nonsimple vertices, nontarget exception labels, empty/point/line
residuals, nonregular polygons and polygon prisms. It reconstructs the full kernel
basis and both incidence tables independently and checks the entire support slice
for each delivered edge. The producer does not read the independent edge graph.
Saved JSON certificates replay with incidence and edge/route construction disabled.
Nonshortest and nonacquiring steps are retained; the executable and parser are not
Lean-extracted or kernel-verified. Counts in the evidence report describe actual
executed finite tests, not an all-real proof by sampling or a runtime guarantee.
