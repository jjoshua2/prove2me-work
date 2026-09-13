# Proof idea

Let `P = {x | a_i x ≤ b_i}` and fix a direction `g` and nonnegative length `τ`. The endpoint erosion is the set of points `p` for which both endpoints of `p + [0,τg]` satisfy the original inequalities. The easy inclusion `erosion + [0,τg] ⊆ P` follows row-by-row.

For the reverse inclusion, take an arbitrary `x ∈ P`. Among rows with positive directional coefficient `a_i g`, choose one minimizing the forward fiber endpoint ratio

`U = (b_i - a_i x)/(a_i g)`.

Set `t = max(0, τ-U)` and `p = x - t g`. Positive rows remain feasible because `τ-t ≤ U`. Zero-direction rows are unchanged. For a negative row `j`, the supplied certificate for the positive/negative pair `(i,j)` implies that the full `g`-fiber through `x` has width at least `τ`; after substituting the defining equality for `U`, this gives exactly the backward room needed to keep `p` feasible. Hence `p` lies in the erosion and `x = p + t g` with `0 ≤ t ≤ τ`.

The `PairCertificate` hypotheses are finite Farkas-style nonnegative combinations of the original inequalities. Their pointwise lemma converts each stored row-combination identity and constant bound into the required pairwise fiber-width inequality. Therefore the finite certificates prove the whole Minkowski equality, not merely nonempty erosion or feasibility at selected points.
