# Applications of the protected-facet count

These are algebraic applications of the packet statement, not additional
Lean declarations or independently published theorems. The proof packet
remains unchanged at bf3db81677d9ec5e0e668bb39d558c789ec5e704.

For a nonempty loop-free simple-polytope edge path, n=L+1. With m original
facets, dimension d, excess e=m-d and k exceptions, the universal count gives
L <= (e+1)*2^k-1. A certified registry C instead gives L <= (e+1)*|C|-1.
Original adjacency, distinct states and protected intervals must be supplied;
the counting theorem does not construct the route or a small C.

When B is contained in the original ground set and k<=min(d,e), summing the
weighted theorem over every subset of B gives

    n <= 2^(k-1)*(2e-k+2), for k>=1; n<=e+1 for k=0.

This follows from the standard binomial identities sum C(k,s)=2^k and
sum s*C(k,s)=k*2^(k-1). The statement uses natural truncated subtraction, but
in this parameter range every capacity e-k+s+1 is positive. For a three-label
exception set whose whole triple is impossible at every visited vertex, remove
that signature of capacity e+1. The resulting edge bound is L<=7e-6.
That recovers the numeric count in research #259 WITHOUT formalizing that
research's separate geometric example or protected-interval existence argument.

A large exception set need not imply many states: when certified geometry
restricts C to polynomially many subsets, the registry theorem can still give
a polynomial bound. No such global registry construction is asserted for
arbitrary carriers. Conversely, the theorem is not a lower-bound measure: a
large powerset estimate can be very loose on a route that visits few signatures.

The explicit retirement encoding makes a proof interface available: one can
check membership and the integer counter instead of enumerating every original
vertex. That is a counting interface, not a proved polynomial-time algorithm
for finding the route.
