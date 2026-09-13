# Exact remaining allocation adapter after finite-circuit tests

This is a mathematical interface/next proof target, not an additional Lean-verified declaration or an assumed axiom. Reuse the finite-circuit theorem from PR #218 and the accepted compact-dual theorem from #216; do not resubmit either.

Let a:R^d->R^m be the original row map and R={x:a(x)<=b}. Let G:R^k->R^d send allocation coordinates to listed shape vectors, Q=conv{0,g_1,...,g_k}, and let h_i be valid support bounds for Q. For t>=0 set P_t={p:a(p)<=b-t*h}. No boundedness or full dimensionality of R is needed for the following pointwise identities.

Use the fixed (m+k+1)-row allocation system

    C theta = (-a(G theta), -theta, sum_j theta_j),
    d(x,t) = (b-a(x)-t*h, 0, t).

Then x is in P_t+tQ exactly when C theta <= d(x,t) for some theta. The bottom blocks enforce theta>=0 and sum(theta)<=t. This remains valid at t=0; nonnegative theta with zero sum is zero. The forward inclusion P_t+tQ subset R follows from the original support bounds and t>=0.

The missing alternative theorem is the FULL sufficiency statement

    (exists theta, C theta <= d)
      iff (forall w>=0, C^T w=0 -> dot(w,d)>=0).

Necessity follows by summing inequalities. Sufficiency must be proved from available separation/finite-dimensional closed-cone facts; it must NOT be added as a new axiom or merely restated as a hypothesis in a claimed completion. The cone range(C)+R_+^M is finitely generated and hence closed; supplying that closedness is one direct route to the geometric alternative already present in pinned Mathlib. In the present bounded-simplex allocation setting, a compact-feasibility route can avoid proving the fully general alternative.

Apply PR #218 with A=C^T and the linear functional b_d(w)=dot(w,d). Its support-indexed family c_s depends only on C, not x or t. The exact finite geometric target is consequently

    R = P_t+tQ
      iff (forall x in R, forall s, dot(c_s,d(x,t))>=0).

This is not yet a claim that the remaining universal quantifier over original x has been finitely or efficiently eliminated. For a circuit c_s=(lambda,mu,nu), the tested inequality is

    (t*(dot(lambda,h)-nu)) <= dot(lambda,b)-dot(lambda,a(x)).

Thus the existing original-H primal/dual support witnesses can eliminate x into budgets, once their support-optimality bridge is formalized. No original row may be dropped; no merely sufficient dual witness may be labeled an exact optimum. Multiple supplied shapes use one allocation block each and the SAME shared scale vector. Correctness of the executable enumerator, the support bound rank(C)+1, and polynomial complexity remain separate from finite dual completeness.
