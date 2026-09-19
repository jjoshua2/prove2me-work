# Exact original exposed-edge criterion

Let Z be the actual segment sum sum_i [0,w_i]. No independence or full dimension is assumed. For a linear objective f its support value is H=sum_i max(0,f(w_i)). For every bounded coefficient vector t, each difference max(0,f(w_i))-t_i*f(w_i) is nonnegative. Their sum vanishes exactly when every non-tied coefficient is fixed: t_i=1 at positive objective values and t_i=0 at negative values. Tied coefficients may take any value in [0,1]. This describes ALL representations of ALL points of the whole maximizing face, not only a list of corner samples.

## Sufficiency, including opposite and repeated directions

Suppose one nonzero tied generator w_j spans all tied generators: w_i=c_i*w_j whenever f(w_i)=0. Fix non-tied coefficients by their objective signs. At the lower endpoint choose coefficient1 on negative c_i and0 on nonnegative c_i. At the upper endpoint choose1 on positive c_i and0 otherwise. Their displacement is M*w_j, where M=sum_(tied i)|c_i|>0. Positivity follows from the nonzero chosen generator itself, so opposite directions cannot cancel away the edge.

For any maximizing coefficient vector, its displacement from the lower endpoint is a*w_j with0<=a<=M. The ratio a/M puts the point on the closed endpoint segment. Conversely each segment point is represented by the convex combination of the two endpoint coefficient vectors, which stays in the cube and fixes every non-tied coordinate. Thus the ENTIRE face is exactly the nondegenerate segment. The original linear objective exposes it in Z, and its endpoints are extreme points of this extreme face and hence of Z. No projected auxiliary edge is substituted.

## Necessity without a supplied face dimension

Take the maximizing corner b that chooses positive generators and zero on every tied one. For EACH tied i, both b and b+w_i lie in the actual maximizing face. If that whole face is a nondegenerate segment [u,v], subtracting the corresponding segment parameters proves every tied w_i parallel to v-u. There must be a nonzero tied generator: otherwise all maximizing representations equal b, contradicting nondegeneracy. Choose that w_j and divide its nonzero scalar coefficient to express every tied generator as a multiple of w_j. This proves the reverse implication, including rejection of empty/zero tied families and higher-dimensional tied spans.

## Scope and the next routing obligation

The theorem characterizes when an arbitrary objective exposes a genuine original edge. It neither assumes the criterion holds for every objective nor constructs a generic objective path. A completed short-sweep argument must still produce appropriate objectives for actual endpoints, handle tied parallel groups, and bound the transitions. In particular cube edges may project into the interior or to diagonals. The test suite retains such a countercontrol.

The result is useful for the explicit completion proved in #311, but no composition with its translated pair representation is silently claimed here. Generator counts and original facet counts remain distinct. This packet proves no all-pairs diameter bound or unrestricted Polynomial Hirsch result. Classical zonotope face geometry is credited, with no historical-priority claim. The elementary segment-parameter and line-injectivity proof bodies follow accepted #309; no previous target is submitted again.

## Verification and computational evidence

The public statement expands both the original segment sum and its whole objective-maximizing face using Mathlib-only notation. The top-level solution has that exact intended type, with no target import or admission. Five transitive reports cover coefficient saturation, constructed segment, necessity, endpoint extremality and the public theorem. Only actual pinned compilation can verify this source: no local Lean/Lake was available, and source-text or exact-rational tests are not Lean verification. The complete prepared packet receives one real top-level PR comment gate; preserve any failure without a speculative hosted repair loop.

The standalone Fraction suite independently enumerates all Boolean representations of66 small generator systems, computes face ranks and tests987 objectives. It checks37894 saturation identities and2961 fractional representations, distinguishes236 edge faces from751 nonedges, and independently reconstructs every original edge of the planar models (75 total). Higher-rank and singleton faces are retained rather than discarded. Five selected models through dimension64 cover parallel positive/negative/zero ties without full graph enumeration. Twenty-seven saved certificates replay with construction and rank/hull routines disabled; five forged records fail. These are supporting tests, not Lean-extracted code or a universally verified JSON consumer.
