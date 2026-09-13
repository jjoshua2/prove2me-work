# Proof idea

Multiply each factor's demand inequality by its nonnegative weight and sum over all factors. Expanding the resulting double sum and exchanging the finite summations rewrites it as a sum over the `L` route transitions. By hypothesis, every one of those transition sums is at most one. Therefore the total weighted demand is at most `L`.

The theorem is deliberately combinatorial: it does not assume a particular polytope or route constructor. In PR #210 the `change` values come from candidate-factor allocation changes along ordinary edges, so any feasible fractional packing of factor weights yields a certified graph-distance lower bound without double-charging one edge for several simultaneous factor changes.
