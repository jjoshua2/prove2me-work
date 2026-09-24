# Forced-run interiors survive original-row deletion

## Precise result and relation to the mission

Let P be a finite original real halfspace system in arbitrary dimension. Fix an
actual extreme target v and a set J of original row labels. Retain all rows tight
at v together with J, giving the relaxation Q. Suppose p_0,...,p_(n+2) is a SIMPLE
run of n+2 genuine exposed original edges, all its points are actual original
vertices different from v, and every edge's entire target-slack common-tight row
set lies in J. This is exactly the forced-label condition from accepted PR343.

The new candidate derives:

- Every shared internal point p_1,...,p_(n+1) is an exposed and extreme point of Q.
- The explicit trimmed sequence r_i=p_(i+1), 0<=i<=n, remains injective, and its n
  connecting segments are WHOLE nondegenerate exposed edges of Q.
- For each of these middle edges, its full relaxed affine-line section equals
  the SAME original segment, with no subdivision or replacement edges.
- Any edge of the original run whose relaxed carrier grows must be the first
  or the last edge. There are at most two such edge positions, independent of
  the run length and ambient dimension.

Thus an n+2-edge original run provides an unchanged n-edge relaxed subpath after
trimming just the two boundary edges. For n=0 the input has two edges and the
output is its one shared exposed vertex and a zero-edge path. Single-edge and
empty runs are not disguised as instances of this particular public statement.

This is a quantitative LOCAL boundary-loss theorem. The original simple forced
run is INPUT, not a constructed globally short route. The theorem does not bound
its length, the number of forced runs in a route, the total number of relaxed
carriers, geodesicity in either graph, or optimal row congestion. It does not
solve Polynomial Hirsch. Its contribution is to turn PR344's separate surviving
line carriers into an actual unchanged ordinary-edge path on their interior,
without assuming that its internal vertices survive.

No boundedness, finite-hull representation, full-dimensionality, simplicity of
the polyhedron, active-rank oracle or supplied relaxed-vertex catalogue is needed.
The run's injectivity, actual original vertices, genuine exposed edges and forced
label condition remain explicit. Target extremality and target avoidance specify
the intended routing application; the internal generic lemma actually uses only
target feasibility. Repeated rows retain their original labels.

## 1. Reuse exact original carrier geometry

Accepted PR344 proves that, when all common-active original rows of an edge are
retained, Q intersect affline(edge) is exposed in Q and contains the old edge.
Intersecting that carrier back with P recovers the whole original edge. Its
common-active affine-line equality is derived by two-sided finite perturbations,
not assumed as a rank property.

The new standalone source copies the accepted PR344 namespace prefix through
end Hirsch.RowDeletionEdges byte-for-byte (323 lines / 13000 UTF-8 bytes), omitting
only its old public solution and audit commands. The source identity is checked
against accepted blob387280cd1b07c65480a4fefa34148c24a15c5aed. Its public target is
not imported or resubmitted. Retaining target-tight rows plus J retains every
common-active row of an edge forced into J, by a direct tight/slack case split.

## 2. Adjacent distinct edge carriers meet only at their old junction

Consider successive original vertices a,x,c, all distinct, with original edges
[a,x] and [x,c]. Suppose a point z other than x belongs to both affine lines.
Rebase both lines at x and write

    z=x+s(a-x)=x+t(c-x).

Since z is not x, s is nonzero. Dividing the equality by s puts a on affline(x,c).
Because a is feasible, original-line recovery for [x,c] then puts a on [x,c].
But a is an actual original extreme point distinct from x and c, which is
impossible. Therefore the two affine lines meet in exactly {x}.

Their relaxed carriers are exposed sets and both contain x. The intersection of
two exposed sets is exposed: sum their maximizing functionals. Mathlib's pinned
IsExposed.inter and IsExposed.isExtreme implement these classical facts. Their
intersection here is exactly the singleton {x}; hence x is exposed and extreme
in Q. This derives vertex survival at every genuine junction, even though an
isolated edge's endpoints need not survive.

## 3. Two surviving extreme endpoints prevent extension

Take a point z=u+t(w-u) in Q, where u and w are distinct extreme points of Q.
If t<0, then u lies in the open segment between w and z, with positive weights
(-t)/(1-t) and 1/(1-t). That contradicts extremality of u. If t>1, w lies in the
open segment between u and z, with weights (t-1)/t and 1/t, contradicting
extremality of w. Thus 0<=t<=1 and z belongs to [u,w].

The reverse containment is already provided by the retained original carrier.
Consequently Q intersect affline(u,w)=[u,w]. Its exposure is inherited from the
canonical relaxed carrier, not inferred just from feasible endpoints.

Every middle edge of a forced run joins two internal junctions. Both endpoints
therefore survive by the preceding step, and the whole edge is unchanged by
this step. Only the first and last edges lack two internal-junction guarantees.
The formal conclusion explicitly locates every possible extension at index 0
or n+1; no guessed cardinality or hidden route budget is used.

## 4. Why simple runs matter

It is false that every shared point in an arbitrary repeated walk survives.
For the clipped square 0<=x,y<=2, x+y<=3, use target(0,0) and retain its tight rows
plus x+y<=3. The old diagonal edge joins u=(1,2) to w=(2,1); its relaxed carrier
is [(0,3),(3,0)]. Both old endpoints cease to be relaxed vertices.

The backtracking sequence u,w,u consists of two traversals of that same forced
edge, but its internal point w is lost. It violates the public injectivity
hypothesis and is an executed adverse control, not a counterexample to the
stated theorem. Classical simple-path extraction does not by itself construct
a polynomial route, and no such global claim is smuggled into this packet.

Even a simple forced run can remain arbitrarily long relative to a proposed
cheap bound unless further geometry controls it. The trimming theorem preserves
edges; it does not prove that the trimmed path is shortest or that a shortcut
in the relaxed body can be pulled back cheaply through deleted inequalities.
Those are subsequent original-route obligations.

## Executed exact supporting tests

The new script imports unchanged committed PR343/PR344 rational utilities. It
constructs original vertices and edges from exact H data, examines every target
and target-slack row subset in ten small models, and audits all distinct forced
two-edge junctions and every edge having two such internal endpoints. The suite
checks 1372 row subsets, 13078 junctions and 3355 middle edges, after 961 original
square-system checks. Examples include nonsimple bodies, an embedded square and
a nonvacuous unbounded five-vertex chain. The three-vertex unbounded example and
segment example are correctly vacuous for these non-target two-edge runs.

Finite-run assembly is checked on at most four deterministically selected longest
BFS paths per target/row subset, not on every possible path. These are BFS paths
in the forced-edge subgraph, not claimed geodesics in the full original or relaxed
graphs. There are 3319 tested runs containing 11365 original-edge occurrences;
8046 internal-vertex occurrences and 4727 middle-edge occurrences survive. The
4552 observed carrier extensions occur only at boundary positions. Seven altered-
certificate or invalid-hypothesis controls are rejected.

Selected cube runs in dimensions 8,16,32,64 add four runs with 116 original edges,
112 retained internal vertices and 108 unchanged middle edges. Each has just one
extending boundary edge. The 64-dimensional run has 63 edges and retains its
61 middle edges. No full high-dimensional vertex or graph enumeration is done.

An initial version attempting every BFS endpoint pair hit a 45-second local tool
limit after the first two models. The final script retains exhaustive LOCAL
junction/middle-edge checks and explicitly limits path assembly sampling, with
memoization of exact arithmetic keyed by immutable full inputs. Two complete
executions in clean three-script workspaces reproduce all four final report and
fixture files byte-for-byte. The earlier timeout is not counted as a passed run.

The consumer reconstructs original eligibility, retained rows, extreme-point
ranks and full one-dimensional intervals, without calling the producer or path
search. Arithmetic functions and immutable-input caches are shared; these are
supporting checks, not an independently verified implementation. Python, JSON,
Gaussian elimination and caching are not kernel-verified or Lean-extracted.

## Formal verification boundary

The new source imports Mathlib only and has a top-level theorem solution with
exactly the type in problem.json. The target preamble contains only imports,
opens and options. There is no written admission, new axiom or own-target import.
Five transitive reports are requested for line intersection, junction exposure,
extreme endpoint containment, finite-run assembly and the public root.

No local lean/lake/elan executable or checked conventional installation/cache
was available; raw.githubusercontent.com and releases.lean-lang.org failed DNS.
Text/hash/type checks and rational execution are NOT Lean compilation. A single
carefully prepared complete pinned hosted gate is requested, with failures to
be preserved rather than an iterative speculative Actions edit/compile loop.
Preserve Lean4.30.0, Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, current
reviewed strict protocol0.11.0, all other ownership and verifier/publisher isolation.
No earlier-contribution licensing request is made or authorized by this packet.
