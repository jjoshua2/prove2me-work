# Original-row routes with finitely many exceptional target inequalities

## Statement and parameter

Let P be exactly both conv(C), for a finite set C of real points in ambient
R^d, and the intersection of the m displayed original halfspaces A_i x <= b_i.
Let u,v be actual extreme points. Let B be ANY finite set of original labels.
For each row tight at target v and outside B, assume that its values on actual
vertices are its boundary b_i and at most one other real value. Rows in B and
all nontarget rows are unrestricted. Write k=|B|.

The public theorem constructs an indexed walk through actual extreme points,
with each consecutive segment a nondegenerate whole IsExtreme subset of the
ORIGINAL P. Every acquired target row stays tight. Its bound is

    L <= m-d + ((m+1)^k - 1).

All subtraction in the Lean type is natural truncated subtraction. Existence
of an actual vertex already implies d<=m, which is derived from original active
rows, not separately assumed. Empty B, B containing nontarget labels, redundant
rows, redundant/interior generators, nonsimple or lower-dimensional bodies,
dimension zero and equal endpoints are included.

For EACH FIXED k this is polynomial in original m, independent of the number
of real values attained by the exceptional rows. The degree depends on k. It
is NOT a uniform-degree polynomial for arbitrary carriers, nor a polynomial-time
recognition, H-to-V enumeration or route algorithm. In particular B=all rows
makes the structure premise vacuous but yields a generally exponential bound.
Accepted #324 is sharper when k<=1; this packet does not replace its m-d result.

The proof uses classical finite-dimensional basis selection and polyhedral
edge ascent, not a claim of historical priority or a new best-known diameter
estimate. The contribution is the explicit geometric/formal connection to the
project's target-row hypotheses and actual original-edge interfaces.

## 1. Acquire the good rows using original edges

Let G be the target-active labels outside B. At the current vertex x, retain
ALL target rows already tight, including exceptional rows acquired early.
The hull of the generators satisfying these equations is an extreme subset
of P; the entire retained face is proved by the accepted support-filter result.
The actual x remains extreme in it, and v belongs to it.

If j in G is still missing, A_j(v)>A_j(x). The accepted improving-edge geometry
constructs a better actual vertex y along a whole exposed edge of the retained
face. Extremality transfers to ORIGINAL P. Since A_j has only two possible
vertex values, strict improvement must attain b_j. All previous target locks
are retained. Thus the number of missing good labels strictly decreases.

Induction constructs a prefix ending at a vertex w with every row of G tight.
Its length is at most the number of initially missing good labels, hence at
most m-d: the initially missing target labels are disjoint from all source-active
labels, and active-kernel triviality proves at least d such source labels.
Neither this prefix nor an improving neighbor is input to the theorem.

## 2. Derive the dimension bound for the remaining affine space

Define N={z : A_i z=0 for every i in G}. This is the direction space of the
affine equations which remain fixed, not a supplied geometric rank.
The map

    E : N -> R^B,  E(z)_i=A_i z

is injective. If its values vanish, all target-active rows annihilate z: each
is either in B or in G. The accepted original-H active-kernel theorem at v then
forces z=0. Therefore dim(N)<=k. N can be larger than the affine direction
space of the actual residual face; this only makes the estimate weaker.

This is the point where the NUMBER of independent exceptional directions
replaces the possibly enormous inventory of exceptional scalar levels.

## 3. Select a short original-row certificate for each remaining vertex

Let V_G consist of all actual vertices satisfying every equation in G.
It is derived by filtering C. Every actual extreme point of a finite hull is
among its generators, so this filter does not assume a complete vertex oracle.

For each x in V_G, restrict all original rows active at x to N. Extend the
empty independent family to an independent spanning subfamily of these
restricted dual vectors. Its index set T_x consists of original active labels
and has |T_x|<=dim(N)<=k. No selected basis, inverse or rank oracle is assumed.

If z in N is annihilated by all rows in T_x, evaluation at z annihilates their
span and hence all original rows active at x. Active-kernel triviality at x
forces z=0. Consequently T_x determines x among points of the residual affine
space: if two residual vertices x,y have the same selected original label set,
then x-y lies in N and is annihilated by those rows, so x=y.

Thus x -> T_x is injective. Encode each T_x into k optional original-label
slots, using a finite enumeration and padding with None. Membership can be
recovered from the slots, so equality of codes forces equality of label sets
and vertices. There are (m+1)^k possible codes, and therefore

    |V_G| <= (m+1)^k.

A sharper binomial subset count is possible in the written counting idea, but
is NOT asserted by the public theorem or separately formalized here. The actual
Lean proof uses the displayed k-slot bound. No assumed small vertex catalogue
or expanded coordinate-value inventory is substituted for this derivation.

## 4. Construct the remaining route and append

Derive a strictly target-maximizing linear functional from strict separation
of v from the hull of all other original generators. At any residual vertex
x different from v, apply the original improving-edge construction in the
current face of ALL acquired target rows. It remains inside V_G and preserves
every existing target lock. The chosen objective strictly increases.

Induct on the finite number of residual vertices with strictly greater objective
value. An improving step makes that set a strict subset. This constructs a
complete route to v with at most |V_G|-1 edges. There is no assumed connectivity,
termination, improving-neighbor or short-path hypothesis in the public type.

Append the prefix from Step 1. The two actual walks concatenate inside the
original vertex set, retain whole original edges and preserve target rows.
The length is at most m-d+((m+1)^k-1).

The terminal route need not acquire a new target label at every step. Requiring
that would be false already for two exceptional rows. The explicit hexagon
(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1), from source (0,0) to target (2,2), has
only two initially missing target rows but distance three, and neither source
neighbor acquires a target row. Both target rows have three levels. This is an
ordinary small polygon, not a diameter counterexample. It separates the new
multi-step conclusion from #324's one-edge terminal argument.

## 5. Several independent high-level rows: a written application

For n>=1 and k>=2, put d=n+k and impose

    0<=x_i<=1                 (i=0,...,n-1),
    0<=t_a<=h_a(x),           (a=0,...,k-1),
    h_a(x)=1+sum_i (a+1)*2^(-(i+1))*x_i.

There are 2d displayed inequalities. The vertices are exactly all Boolean base
points x and independently chosen lower/upper lifts t_a=0 or h_a(x).
For a fixed upper/lower pattern the lift is affine in x, so every feasible point
is a convex combination of those finite lifts: first combine the lower/upper
height choices over its base x, then expand x as a convex combination of Boolean
bases. Each listed lift has d independent active rows in a block-triangular
matrix with diagonal entries +/-1, so it is an actual vertex. This derives the
full hull identity and vertex classification in this WRITTEN application.

Each base row is two-level. At any target exactly one row per height pair is
tight. That row takes 2^n+1 vertex values: one boundary value and 2^n distinct
dyadic subset-sum values at the opposite height choice. Thus exactly k target
rows can be exceptional. On the residual space obtained by fixing all base
coordinates, their height-coordinate evaluations are independent. These are
several independent exceptions, not duplicate labels for one direction.

All displayed rows are genuine facets: fix a selected base boundary and choose
all other base coordinates interior and all heights interior, or fix a selected
height boundary with interior base coordinates and all other heights interior.
There is a relative-interior point with exactly that row tight. The proof of
this family classification/facet/level count is written, NOT a second Lean
instance theorem, and no general affine indecomposability is claimed.

The explicit test route changes Boolean base coordinates one at a time while
retaining the upper-height pattern, then lowers each height. It has d original
edges. A full active right inverse certifies each vertex; a common (d-1)-row
right inverse and the two private endpoint inequalities certify the whole edge.
At d=64,k=4, each exceptional row has 2^60+1 values, yet the explicit path has
64 edges. These counts are formula evaluations, not a complete large graph or
level enumeration. The general theorem's bound is much larger on these easy
instances; short example routes are not evidence of sharpness of that bound.

## 6. Formal provenance and verification boundary

The accepted #323 namespace prefix (844 lines / 35088 bytes) is included
byte-for-byte, with its old public root and prints omitted. It contains accepted
original-H active-kernel, rank, retained-face and improving-edge proofs. No
accepted target is registered again. The new namespace supplies arbitrary-
objective locked improvement, derived residual dimension, selected original-row
codes, the finite vertex bound, good-row prefix, strict terminal ascent and the
full public assembly. Seven final transitive axiom reports cover the chain.

The target preamble has only Mathlib import/open/options, and its exact type is
copied from the public top-level solution. No admission, new axiom, target import,
pin, workflow, publisher, allowlist or credential-isolation change is included.
Local Lean/Lake and cached dependencies were not found and toolchain-host DNS
failed. Source identities and exact tests are NOT compilation. This candidate
is prepared for one full pinned verification/publication gate; preserve any
actual failure without speculative hosted iteration or a weakened target.

## 7. Executed supporting arithmetic (not verified Python/JSON)

Small tests independently enumerate finite-hull supporting facets, original
vertices and the reference graph, including both signs of affine equations
for lower-dimensional inputs. The route producer uses the unchanged geometric
edge constructor and its supporting rows, never its reference edge table.
The consumer checks the full support maximizer set and original edges. Exact
linear algebra derives and checks the residual dimension and selected active
labels for every residual vertex. The tests implement the sum of target rows
as a concrete strict terminal objective; the Lean proof derives a strict
functional by separation. They do not claim identical noncomputable choices.

The suite covers 23 hulls, 160 actual vertices and 165 displayed rows. All 160
targets are handled, including 80 excluded by the one-exception premise. It
checks 434 residual vertex codes, 1402 ordered endpoint routes and 2137 original
edge occurrences versus 2130 shortest edges. Seven nonshortest outputs and
12 steps without a newly acquired target row are retained. All-row-exception
boundary certificates additionally exercise the vacuous structure hypothesis.

Four large multi-roof cases at d/k=8/2,16/2,32/3,64/4 check 120 original edges
without graph discovery. Twelve malformed controls are rejected. One initial
negative-test edit was a no-op (the first hexagon edge really acquired no label);
the control was corrected to an actually false label list before the final run.
That test-harness mistake is not described as a successful rejection or a Lean
failure. Full exact reports/fixtures and producer-disabled replay are preserved.

A clean workspace containing only the new script and its two unchanged
dependencies reproduces the reports and fixtures; the resulting hashes and
actual execution outcome belong in the final handoff. The scripts are reference
research software, not a formally verified general JSON parser or efficient LP
implementation. Do not infer large-graph enumeration or a universal original-
facet polynomial theorem from these computations.
