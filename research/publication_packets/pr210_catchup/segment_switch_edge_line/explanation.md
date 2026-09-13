# Proof idea

Fix one common tight row `a_i`. Since `x` and `y` both satisfy it with equality, feasibility of `x+τg` implies `a_i g≤0`, while feasibility of `y-τg` implies `a_i g≥0`. Because `τ>0`, the two inequalities force `a_i g=0`.

Thus every common tight row annihilates `g`. The final hypothesis says that the simultaneous kernel of those rows is exactly the one-dimensional line spanned by `y-x`. Applying that kernel characterization to `g` gives a scalar `r` with `g=r(y-x)`.

In the intended polyhedral application, the common tight rows are those defining an ordinary edge. Therefore a segment factor whose endpoint allocation changes across that edge must be parallel to the edge itself.
