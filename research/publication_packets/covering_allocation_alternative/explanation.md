# Allocation with covering resource budgets

## Statement and contribution

For real row families a on R^k and B on R^k, suppose nonnegative weights rho
satisfy B^T rho >= 1 coordinatewise. For arbitrary real right sides b,t:

    exists theta>=0, a(theta)<=b, B(theta)<=t
      iff
    every w,mu,nu>=0 with a^T w+B^T nu-mu=0 has w.b+nu.t>=0.

The conclusion uses only the actual constraints. There is no synthetic total
budget in the returned dual test and no assumed feasible allocation or Farkas
oracle. Individual B coefficients and the right sides may be negative. The
coverage condition is an explicit finite hypothesis, not a claim about every
unbounded allocation system. Empty index sets and infeasible systems are included.

This is a project-specific reduction of a classical linear-inequality alternative,
not a new classical duality or ordinary-edge diameter theorem. It extends the
accepted single-simplex allocation helper from #219 to separate and overlapping
budgets, without replacing the actual constraints by a relaxation or enumerating
the vertices of a product of simplices.

## Proof

Put d=B^T rho and T=rho.t. Nonnegativity and coverage give

    sum(theta) <= d.theta = rho.B(theta) <= T

at every feasible allocation. Therefore a global bound sum(theta)<=T may be
ADDED while all original B rows are retained. Under the actual-row dual
hypothesis, choose (w,mu,nu)=(0,d,rho) to obtain T>=0. If T<0, this triple
is an explicit violated nonnegative dual witness, not an excluded case.

Apply #219's already-proved bounded-simplex alternative to the combined a and
B rows with bound T. Its augmented dual condition has an extra eta>=0:

    a^T w+B^T nu-mu+eta*1=0.

Define nu'=nu+eta*rho and mu'=mu+eta*(d-1). Both are nonnegative because
rho>=0 and d>=1. Their original-row combination is zero, and their cost is

    w.b+nu'.t = w.b+nu.t+eta*T.

Thus every augmented test follows from an actual-row test. The accepted helper
supplies one theta satisfying all rows simultaneously. Drop only the redundant
global bound, not the actual B rows. Necessity follows by evaluating the
nonnegative weighted combination at any feasible theta.

For overlapping budgets the mu correction is essential: with
B=[[1,1,0],[0,1,1]], rho=(1,1), one has d=(1,2,1). Absorbing eta must also
change the middle nonnegativity multiplier. Omitting that correction produces
a nonzero residual row. Signed B is genuinely allowed; for
B=[[1,-1],[-1,2]], rho=(3,2) gives d=(1,1).

## Reuse, representation and exact scope

The compact-separation and single-simplex helper bodies are copied byte-for-byte
from accepted #219 proof head9d3aea2f4120f44a6c43b882d79c9f6f7fcb00c6,
source blob05926a8a263bde88f5d6bb29395d32f4ff97ccf8. They do not import a
placeholder theorem. The standalone source preserves the original Mathlib pin
c5ea00351c28e24afc9f0f84379aa41082b1188f and Lean4.30.0. Its public statement
preamble has only import/open commands and its top-level theorem is solution.

For multiple simplex candidates, B is the block-incidence matrix and rho=1
covers all allocation coordinates. Empty blocks and dependent generators cause
no problem. A collection of32 triangles needs64 allocation coordinates and32
budget rows, not an explicit list of3^32 Cartesian vertex choices. That is a
representation saving, not a polynomial bound on subsequent circuit enumeration.
The finite circuit catalogue and original-H support budgets still need their
explicit formal composition with this alternative. The uncompiled one-block
checked-output packet is not upgraded by this result.

## Actual computational evidence and verification distinction

The exact-rational regression was rerun in this continuation. It compares480
primal/dual cases against independent Fourier--Motzkin elimination (224 feasible,
256 infeasible), checks484 multiplier absorptions and2904 preserved-cost
identities, and tests110 negative-total obstructions. Five joint geometric models
supply43 exact original-row support witnesses,416 vertex-allocation checks and128
joint-region comparisons. Six invalid controls are rejected. These tests use
#229's existing checker unchanged and are not Lean verification.

The code and receipt are provided separately. The large32-block test covers
only the coverage and absorption identities; no large circuit catalogue or
polytope graph was enumerated. Python/JSON decoding is not Lean-extracted.

The originating container has no local Lean/Lake and toolchain-host DNS failed.
The prepared proof has not been described as locally compiled. A separate final
comment gate is responsible for actual compilation, transitive axiom auditing,
frozen artifacts and authenticated publication. Consult its recorded receipts
for the resulting status; successful numerical tests alone imply no acceptance.

No arbitrary-carrier routing result, universal shape-selection theorem, or
Polynomial Hirsch proof is asserted.
