# Proof idea

Assume the whole halfspace set decomposes as `P + [0,s g]`. Write the sharp feasible point as `x = p + t g` with `p ∈ P` and `0 ≤ t ≤ s`.

Because `p` and `p + s g` are both feasible, the negative row `j` bounds how far `x` can lie forward from `p`, while the positive row `i` bounds how much segment remains after `x` before `p+s g`. Multiplying those two bounds by the positive directional coefficients and adding them gives

`s * (a_i g) * (-a_j g)`

at most the opposing-row fiber-width expression at `x`. By the sharpness hypothesis that expression is exactly

`τ * (a_i g) * (-a_j g)`.

The product `(a_i g)(-a_j g)` is strictly positive, so `s ≤ τ`. The argument applies to any residual `P`; it therefore certifies maximality of the direction itself, not merely maximality of a particular erosion construction.
