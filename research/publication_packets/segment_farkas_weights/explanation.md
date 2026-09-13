# Proof idea

For every positive/negative pair of original rows, the supplied nonnegative weights give a valid global linear consequence of the H-description. Evaluating its normal identity at an arbitrary feasible point turns the constant inequality into a lower bound on that point's complete fiber width parallel to `g`.

For a feasible point `x`, choose a positive row minimizing the forward endpoint ratio `U = (b_i-a_i x)/(a_i g)` and set `t=max(0,τ-U)`. The positive rows remain feasible after moving backward by `t g`; zero rows do not change. The certified opposing-row width inequalities provide exactly the backward slack required for every negative row. Hence `p=x-tg` lies in the endpoint erosion and `x=p+t g` with `0≤t≤τ`.

Conversely, every point in the endpoint erosion plus `[0,τg]` satisfies each original row because `t*(a_i g)≤τ*max(a_i g,0)`. The two inclusions prove the exact Minkowski equality.

This corrected platform target intentionally inlines the halfspace, erosion, segment, and certificate conditions so the submitted `theorem solution` has exactly the registered target type using only Mathlib symbols.
