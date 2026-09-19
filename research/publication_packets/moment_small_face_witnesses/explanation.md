# Exact small-face witnesses for mean-centered moment inequalities

## Formal statement and geometric role

The target is `Hirsch.moment_curve_exact_small_face_witnesses`. For a finite
index type with m labels, an injective real parameter map a, and a proper
selected finite set S with |S| <= k, the theorem constructs h > 0 and a point
x in R^(2k) satisfying, for EVERY original label i,

    sum_j (a_i^(j+1) - average_l a_l^(j+1)) * x_j
      = 1 - product_(s in S)(a_i-a_s)^2 / h.

It additionally states all original inequalities are <= 1, with equality
if and only if i is in S. The positive number h is explicitly the average of
the product evaluations. No optimizer, feasible point, supporting functional,
rank assumption, or precomputed face list is supplied.

This is the constructive proper-subset feasibility side of the moment-curve
application of research #267 and accepted finite counting theorem #281. It
DOES NOT prove the incompatibility of candidate (k+1)-sets, count those
minimal nonfaces, assert boundedness or full dimension for arbitrary input
parameters, or prove Polynomial Hirsch. Those are separate interfaces. The
construction is classical moment-curve neighborliness, not a novelty claim.

## Complete mathematical construction

Let p(T) = product_(s in S)(T-a_s)^2. It is monic with degree 2|S| <= 2k.
For every real t its value is nonnegative. Injectivity of the parameters gives
p(a_i)=0 exactly when i belongs to S. Since S is proper, some i lies outside
S; p(a_i)>0 there. Thus m>0 and

    h = (sum_i p(a_i))/m > 0.

Expand p(T)=c_0+sum_(j=0..2k-1)c_(j+1) T^(j+1), allowing zero coefficients
above its degree. Define x_j=-c_(j+1)/h. The constant coefficient cancels on
subtracting the average evaluation, giving

    sum_j (a_i^(j+1)-average_l a_l^(j+1))*c_(j+1) = p(a_i)-h.

Multiplication by -1/h proves the exact row identity. Nonnegativity of p
proves feasibility. Since h is nonzero, equality at row i is equivalent to
p(a_i)=0, hence to i in S. No strict slack conclusion is presumed: it follows
from the explicit feasibility and equality characterization.

The source separately proves polynomial evaluation, its exact zero set,
monic degree, finite coefficient expansion, average expansion, and centered
evaluation before assembling the witness. Finite sums include the empty
set. For k=0 the selected set is empty, p=1, h=1, and the empty-dimensional
point satisfies every row strictly. The properness condition rules out an
empty index type without assuming an extra nonempty instance.

## Packet and interpretation checks

The public statement uses only Mathlib types and the explicit original
inequality coefficients. The preamble contains only `import Mathlib` and
`open scoped BigOperators`. Helper definitions occur only in the solution;
the registered target does not redeclare separate copies of custom types.
The top-level proof is named `solution`, its signature exactly matches
problem.json, and no own target is imported. Five transitive axiom printouts
cover the polynomial degree, average, centered identity, witness and root.

The supplied exact-rational regression constructs 3,671 small witnesses,
checks 60,104 original inequalities and 47,106 strict unselected rows, and
uses 86,426 independent polynomial-evaluation probes. It includes empty S,
k=0, ten malformed/invalid controls, and 26 saved producer-disabled audits.
Three larger samples in dimensions 16,32,64 evaluate 33,65,129 original
rows without a complete vertex graph. Proper-subset applications do not
claim that this test proves whole-set incompatibility. These checks are
supporting arithmetic, not Lean verification or verified Python extraction.

## Publication history and trust boundary

This 210-line candidate was prepared in the preceding conversation turn but
remained LOCAL ONLY because GitHub writes were not exposed. No earlier PR,
comment, registration or submission exists for this target. In the current
resumption, comment/write discovery succeeds; live main was checked at
fcc7f68febc372ccce3c8a8c4649638758c25374, including accepted #284. Accepted
#281 and #284 and other agents' branches are not resubmitted or modified.

Local Lean/Lake is still absent. A fresh network preflight cannot resolve
GitHub or the toolchain download host. The existing pinned GitHub comment
gate is therefore used for the user-requested prepared final attempt, not
as an assertion that local arithmetic tests already establish compilation.
Lean4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f are unchanged.
No new workflow, permission, credentials or trusted-publisher split is used.
Only the actual compile/axiom output and authenticated publisher receipt
establish those later statuses. This explanation alone claims neither.

    /prove2me publish research/publication_packets/moment_small_face_witnesses

This must be a NEW top-level comment on this packet's own OPEN same-repository
PR. Do not repeat it while its run or publication is pending. Preserve any
compiler diagnosis rather than weakening the theorem or inventing a verdict.

## Sources

This is the squared-root support argument in the project's
`research/STELLAR_NONFACE_PERSISTENCE.md` (research #267); the finite
persistence count is separately accepted in #281. Mathlib's polynomial
monic-product degree, evaluation over a coefficient range, and finite-sum
identities are used at the committed pin. No external theorem asserting
these particular witnesses or the intended conjecture is assumed.
