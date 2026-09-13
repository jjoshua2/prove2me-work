# Proof idea

Write the sharp feasible point as `x = p + t g` using the assumed decomposition by `[0,s g]`. Since `p` and `p+s g` both belong to the original halfspace set, the negative row `j` bounds the backward part `t`, while the positive row `i` bounds the remaining forward part `s-t`.

After multiplying by the positive directional coefficients and adding, these two feasibility inequalities imply

`s * (a_i g) * (-a_j g)`

is at most the opposing-row width expression at `x`. The sharpness hypothesis identifies that expression with

`τ * (a_i g) * (-a_j g)`.

Because `(a_i g)(-a_j g)` is strictly positive, `s≤τ`. The theorem is independent of the residual `P`, so it certifies maximality of the direction itself rather than maximality of a particular erosion algorithm.

The target is deliberately written only with Mathlib symbols and set comprehensions so the submitted `theorem solution` has exactly the registered platform type.
