# A local obstruction to an unchanged edge version of the circuit proof

Status: ordinary mathematical argument with exact rational enumeration of a
specific two-dimensional example. This note is NOT a Lean theorem, NOT a
counterexample to Child B, and NOT a claim that all edge-routing approaches
fail. It records why one tempting direct extension of the completed circuit
proof cannot work as stated.

## Example

Consider

    P = {(p,q) : 0 <= p <= 2, 0 <= q <= 2, |p-q| <= 1}.

Use the six row normals

    (-1,0), (0,-1), (1,0), (0,1), (1,-1), (-1,1)

and right-hand sides `(0,0,2,2,1,1)`. This is a bounded, full-dimensional,
irredundantly presented hexagon. The point `(1,1)` satisfies every inequality
strictly. Its vertices, in boundary order, are

    (0,0), (1,0), (2,1), (2,2), (1,2), (0,1).

Take the start x=(0,0) and target v=(2,2). They have no common active row: the
start activates the two lower coordinate bounds, and the target activates the
two upper coordinate bounds. Thus this obstruction is not caused by violating
the separated-endpoints hypothesis used in the existing Child A.

## The diagonal is a genuine maximal circuit step

For g=(1,1), the row evaluations are

    A g = (-1,-1,1,1,0,0).

Any nonzero h whose row-evaluation support is contained in this support must
satisfy h_1-h_2=0. Therefore h is a nonzero scalar multiple of g and has exactly
the same support. Hence g is a support-minimal circuit direction for the
original row system, not merely a direction in a restricted auxiliary cone.

The step from x to x+2g=v is feasible and maximal: extending it by any positive
amount violates the upper coordinate bounds. It is not an edge, since x and v
are not neighboring vertices and their segment contains the interior point
(1,1).

## No outgoing edge is conformal to the target slack displacement

Slack is s(p)=b-Ap. The desired slack displacement is

    s(v)-s(x) = (2,2,-2,-2,0,0).

The only two outgoing edge directions at x are positive multiples of (1,0)
and (0,1). Their slack directions respectively are

    (1,0,-1,0,-1,1)
    (0,1,0,-1,1,-1).

Both change the last two coordinates, where the desired displacement is zero.
Every nonzero positive scaling therefore fails the coordinatewise absolute
bound required by `ConformalTo`. In particular, the assertion that every
nonzero feasible displacement admits a nonzero *edge* direction conformal to
it is false, even for this small separated, strictly feasible, irredundant
example.

## Consequence for further work

The circuit proof's conformal-piece existence theorem cannot simply be
strengthened by replacing "elementary/circuit" with "outgoing edge". A genuine
edge strategy must permit controlled deviations in some slack coordinates,
use a different invariant, or exploit a global route transformation.

This does not refute the actual Child B. There is a three-edge path from x to v
in this hexagon, and Child B permits a replacement graph route that ignores
the circuit intermediate points entirely.
