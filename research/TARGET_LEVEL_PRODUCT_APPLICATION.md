# An unbounded number of three-level target rows

This is a written application of the target-row level-budget construction,
with exact executable checks. It is NOT a separate Lean instance theorem.
The public packet must be judged by its actual compiler and publisher evidence.

## The exact original hexagon

In R^2 use the six original rows

    -x-y <= 0,   -x+y <= 2,   -y <= 0,
           y <= 2,    x-y <= 2,    x+y <= 4.

The six listed points in boundary order are

    a=(0,0), b=(2,0), c=(3,1), d=(2,2), e=(0,2), f=(-1,1).

For 0<=y<=1, these inequalities reduce to -y<=x<=y+2. For 1<=y<=2,
they reduce to y-2<=x<=4-y. Each of these two trapezoids is the convex hull
of its four corner points. Their shared y=1 endpoints are f,c, and their
remaining corners are a,b,e,d. Thus every feasible point is a convex
combination of the six listed points, and the reverse inclusion follows
from their feasibility and convexity of the original inequalities.

Each listed point is the intersection of two independent tight rows and
is therefore extreme: if it were an interior convex combination of two
feasible points, both corresponding rows would be tight at those points,
and independence would make both equal the listed point. Conversely, an
extreme point of this finite hull must be one of its generators. This
establishes the whole H/hull equality and actual vertex classification.

Choose source a and target d. The two target-tight rows are y<=2 and
x+y<=4. On actual vertices, the former takes {0,1,2} and the latter takes
{0,2,4}. Both are genuinely three-level, and both are initially missing.
The weighted budget is (3-1)+(3-1)=4. With K=2, m=6 and d=2, the general
input-size bound is K*(m-d)=8.

The exact tested route is

    (0,0) -> (-1,1) -> (0,2) -> (2,2).

Each whole segment is the maximizing slice of one original row: respectively
-x-y=0, -x+y=2, and y=2. Direct substitution of the original inequalities
shows that each slice is precisely the stated segment. The first two edges
strictly increase y from0 to1 to2, a genuine two-edge acquisition phase.
The first edge acquires no target row. The final edge increases x+y from2
to4 and preserves y=2. The actual selected row labels are charged only once.

## Products and original edges

For r>=1 take the Cartesian product H^r, with these six inequalities on each
coordinate pair. Its ambient dimension is2r and its displayed original row
count is6r. The product equals the convex hull of the product of the six
vertex lists: distribute the product of the individual convex-combination
weights, which are nonnegative and sum to one. An extreme product point has
every coordinate pair extreme (otherwise vary one pair in a decomposition).
Conversely a product of extreme points is extreme by applying extremality
to each factor of any strict convex decomposition. This proves the complete
product vertex description without enumerating the6^r vertices.

Use source a in every factor and target d in every factor. Exactly2r target
rows are tight, and each has three values. Thus the number of multilevel
target rows is unbounded as r grows, while K=2 stays fixed. The initially
missing rows are precisely these2r labels, giving weighted bound4r and
input-size bound2*(6r-2r)=8r.

Execute the three-edge local route in one factor at a time, holding all
other factors at their current vertices. An edge face of one factor times
singleton extreme faces of the other factors is a whole extreme face of
the product. It is one nondegenerate segment, hence a genuine original
ordinary edge, not a projected chord or an assumed product graph. The
explicit original supporting-row certificate is the sum of the local
edge's tight supporting row and a strictly exposing sum of the two active
rows at each stationary vertex. Equality forces exactly that product face.
The independent block ranks sum to1+2(r-1)=2r-1. This also gives the rank
certificate checked by the executable consumer.

The resulting route has3r original edges and preserves every acquired
target row. The length3r is a construction bound here, not a shortestness
claim. For r=4,8,16,32 the executed routes have12,24,48,96 edges. The last
case has64 dimensions,192 original rows and64 three-level target labels.
No full product graph or high-dimensional vertex list was enumerated.

This family demonstrates scope beyond a bounded NUMBER of exceptional rows,
not a universal small-level theorem. Other carriers may have very large row
level sets. The general Polynomial Hirsch objective remains distinct.
