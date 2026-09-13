# Proof idea

Every component satisfies `a_i(x)≤b_i`. Multiplying by the strictly positive weight `w_i` preserves the inequality and summing gives the weighted support bound.

If some particular row is strict at a point `x∈P`, its positive weight makes that one summand strictly smaller while every other weighted summand remains no larger than its bound. The total weighted sum is therefore strictly below the sum of weighted upper bounds. Consequently equality of the weighted totals forces equality in every component.

The converse is immediate by summing the individual equalities. Thus the exposed slice of the positive combined objective is exactly the common tight face, which is the support identity used in PR #210's Minkowski/normal-fan route lifts.
