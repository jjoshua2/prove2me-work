# Exact next interface after accepted #233 and #234

Read the live PR queue before choosing this work. The following two previously
separate interfaces are now ACCEPTED: #233 checked_rational_catalogue_dual_tests
and #234 covering_budget_allocation_alternative. Do not resubmit either. The
old one-block composition bundle remains uncompiled and need not be copied in
full: its catalogue-to-dual part is superseded by #233.

Let a be the ORIGINAL H-row map, G the generator map, and B the actual resource
budget map. A finite nonnegative rho with B^T*rho>=1 is supplied. For independent
simplex blocks B is the block-incidence map and rho=1. Retain all block rows.

Use the actual stacked allocation rows C=(-aG,-I,B). Bind the rational matrix
consumed by #233 to C^T through explicit coefficient identities and an index
bijection. For any original x and scale vector t, the right side is

    d(x,t)=(b-a(x)-H*t,0,t).

#233 turns nonnegativity of this pairing on the ACTUAL checker output into
nonnegativity on every real nonnegative null vector. #234 then produces a
single theta>=0 with -aG theta<=b-a(x)-H*t and B theta<=t. This yields the
actual geometric decomposition x=(x-G theta)+G theta. No Farkas or semantic
catalogue-completeness hypothesis is needed, but the matrix-binding identities
must be established, not passed over as an informal notation change.

For each emitted c=(lambda,mu,nu), the pointwise inequality is

    sum_q t_q*(sum_i lambda_i*H_iq-nu_q)
      <= sum_i lambda_i*b_i - sum_i lambda_i*a_i(x).

Use accepted exact original-H support witnesses alpha_c>=0 and x_c in R with
objective equality and complementary slackness to replace the universal x
with the sharp scalar right side sum_i(lambda_i-alpha_ci)*b_i. Those witnesses
remain explicit finite data. A loose dual upper bound is only sufficient and
must not be labeled the exact scale region.

For independent shape blocks, finite generator support inequalities give the
reverse set inclusion. Overlapping general resource budgets need the matching
support certificate for their actual allocation image; do not automatically
identify that image with a Minkowski sum of independent shapes.

A finished adapter should expose an equivalence for the concrete finite
checker output and the actual set decomposition. Passing a pre-existing
pointwise-equivalence premise would repeat #227 rather than complete this
connection. Even a complete adapter validates proposed decompositions; it
would not provide useful shapes or short ordinary-edge routes for arbitrary
high-dimensional carriers.
