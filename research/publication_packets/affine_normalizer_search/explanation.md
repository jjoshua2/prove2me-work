# Complete finite synthesis of positive affine normalizers

## Exact formal result

The inputs are an ambient dimension d, a finite set C in R^d, arbitrary scalar
numerator data s, and an anchor u in C. Thus C is nonempty. No denominator,
coincidence partition, rank, independent basis, selected test set or small
spectrum is a premise. Numerator values may be positive, negative or zero;
C need not span the ambient space or be a vertex set.

Define the FINITE family

    F = {B subset of C x C : |B| <= d}.

For every B in F the theorem constructs a linear functional pick(B). Its
anchored affine denominator 1+pick(B)(x-u) is positive for every x in C. If
B's explicit linear equations admit ANY such positive solution, pick(B)
satisfies those equations. For every positive affine denominator a+D(x),
some member of this fixed catalogue preserves ALL its ratio coincidences:

    s(x)/(a+D(x)) = s(y)/(a+D(y))
       => s(x)/(1+pick(B)(x-u)) = s(y)/(1+pick(B)(y-u)).

Consequently this member's spectrum cardinality is no greater. The theorem
also returns a catalogue member whose spectrum cardinality is no greater
than that of EVERY positive affine denominator, with arbitrary real
coefficients. This is an optimum over the continuous domain, not merely a
sampled, capped or heuristically generated list.

For infeasible B the chosen denominator is the constant one. It need not
satisfy B's equations, but remains positive and cannot invalidate coverage.
The public theorem states the equation-solving obligation conditionally on
feasibility; it does NOT assert that every subset is feasible.

The Lean construction uses classical finite choice, not executable extraction
of a linear-programming algorithm. The separately implemented rational search
below supplies witnesses and infeasibility certificates. Python and its JSON
parser are not kernel-verified.

## 1. Anchor without losing any positive affine normalizer

Given q(x)=a+D(x)>0 on C, let t=q(u)>0 and E=D/t. Then

    1+E(x-u) = q(x)/t,
    s(x)/(1+E(x-u)) = t*s(x)/q(x).

Multiplication by the same positive scalar preserves all equalities (and the
number of distinct values). Thus normalized slopes in the d-dimensional dual
space suffice; the extra affine intercept is eliminated rather than counted
as a d+1 parameter. Positivity at the anchor is why u in C is explicit.

## 2. Ratio ties are affine linear equations in the slope

For positive anchored denominators at x,y, cross multiplication gives

    s(x)/(1+E(x-u)) = s(y)/(1+E(y-u))

if and only if

    E(s(x)*(y-u)-s(y)*(x-u)) = s(y)-s(x).

The contrast vector is determined by C,s,u. Its right-hand side is fixed too.
There is no unknown ratio-level variable, nonlinear partition fitting, or
choice of a common projective coordinate chart. Positivity cannot be dropped:
Lean's division by zero must not be treated as a valid ratio coincidence.

## 3. Derive at most d tests preserving every existing tie

Fix any positive anchored slope E0. Let T contain ALL original ordered pairs
whose ratios under E0 coincide. Choose a linearly independent spanning subset
of their contrast vectors, using labels from T, and call its labels B. Finite
linear algebra derives |B|<=d. No independent-basis hypothesis is supplied.

Both E0 and any solution E of B's affine equations have the same values on
those basis contrasts. Therefore E-E0 annihilates their span and hence every
contrast in T. It follows that E satisfies ALL E0's tie equations, including
ones omitted from B. If E is positive on C, the cross-multiplication lemma
turns these equations back into ratio coincidences.

E can merge additional classes. This is intentional: its value partition
COARSENS E0's partition. A separately proved finite-image surjection shows
that coarsening cannot increase the number of values. Exact equality of the
whole partition is neither needed nor asserted.

## 4. One witness per feasible system suffices for global optimality

For every B in F, choose a positive solution of its affine equations if one
exists; otherwise choose the zero slope. This is a finite fixed catalogue,
constructed before comparing it with arbitrary a,D. The basis B extracted
from any E0 is feasible because E0 itself solves it. Hence the catalogue's
chosen solution for that B preserves all E0 ties and has no larger spectrum.

The empty subset belongs to F, even when d=0, so the catalogue is nonempty.
Minimize spectrum cardinality on this finite family. Coverage proves that
its minimum is at most that of every real positive affine denominator. The
returned minimum is itself positive, so this is actual attainment, not an
infimum or limiting zero-denominator argument.

Zero-dimensional data, singleton C, collinear/lower-dimensional C, zero or
signed numerator values, and arbitrarily small positive denominators are all
retained. No generic-position, strict convexity, nonzero-numerator or numerical
conditioning assumption is introduced.

## 5. Original-edge application after accepted #333

This paragraph is a WRITTEN composition with accepted #333, not another Lean
public route theorem. Use C equal to the COMPLETE set of actual original
vertices and set s_i(x)=b_i-A_i(x). Run the finite synthesis separately for
each original row. For every collection of supplied positive affine
denominators, the synthesized rowwise optima have no greater individual
spectrum weights. Consequently the minimum determining-row budget from #333
with these synthesized denominators is no larger than any such competing
rowwise choice. Apply #333's actual original-edge route theorem to them.

The rowwise choices are independent because #333 permits different positive
affine denominators for different rows. There is no assertion that they form
a common invertible projective chart. The selected target-row equations and
actual-edge geometry are still those of the ORIGINAL H system.

Exact finite H/hull equality and actual endpoint extremality remain necessary
for this application. The formal search theorem itself only sees finite
points and scalar data; it neither discovers the full vertex set from H nor
assumes that a partial visited set is complete. Do not substitute samples for
C and claim a universal original-edge certificate.

## 6. Complexity and the remaining mission gap

For N=|C| the formal index family has size

    sum_(k=0..min(d,N^2)) binom(N^2,k).

This elementary count describes the explicit powerset filter; it is not a
separate formal asymptotic theorem. The rational implementation removes
self-pairs, reverse duplicates, zero/zero tautologies and cross-sign pairs,
but its worst-case search remains exponential in d. N itself may be exponential
in the original number of facets. No polynomial-time original-H optimizer or
H-to-V algorithm is claimed, and no universal polynomial upper bound on the
optimal spectrum is established. This is NOT Polynomial Hirsch, a shortest-
path result or a proof that every positive slack can be made binary.

The result closes a finite-completeness/denominator-choice obligation left by
#333, rather than asserting a new small-cost premise. The next substantive
problem is to control these optimum costs in terms of original input size or
to use a different route-local invariant. #332's written all-order raw-cost
obstruction remains intact. #204's homogeneous bipartition discovery concerns
projective PRODUCT structure, not this rowwise ratio-spectrum optimization.
Classical finite-dimensional span compression and linear feasibility are the
sources of the argument; no historical-priority claim is made.

## 7. Executed exact synthesis and independent checking

normalizer_synthesis.py uses Fraction arithmetic throughout. It enumerates
at-most-d subsets of unordered same-nonzero-sign pairs. Cross-sign ties are
impossible under positive denominators, zero/zero ties impose no constraint,
and reverse-pair equations are negatives, so those reductions preserve the
completeness argument. It stops early only upon reaching the universal count
of numerator sign classes, a valid lower bound independent of any denominator.
Otherwise it exhausts the reduced catalogue.

Equality elimination returns either a particular solution and complete kernel,
or a left multiplier annihilating every coefficient with nonzero RHS. Strict
Fourier--Motzkin elimination then checks positivity within the affine solution
space. A failed strict system returns nonzero lambda>=0 annihilating all kernel
motions with weighted positivity constant <=0. A feasible system returns an
explicit rational slope. Strict open intervals use exact rational midpoints;
no floating tolerance, tiny-epsilon substitution or boundary rounding is used.
System and intermediate-row caps raise an error marked NOT an exclusion or
optimum; a solver limit is never counted as a negative certificate.

The consumer recomputes every original equation and denominator, verifies each
positive slope or dual exclusion, and checks nullspace completeness with a
separate SymPy rank calculation. It independently enumerates the required
basis labels for an exhaustive result and validates every claimed early lower
bound. Saved certificate replay disables equality elimination, feasibility,
normalizer optimization, route generation and improving-edge generation.
The consumer still performs exact arithmetic and independent rank; it is not
an untrusted assertion-only replay.

Twenty original-H reference hulls check 136 synthesized original rows through
1300 systems:613 positive witnesses and687 certified exclusions.31 rows require
exhaustive completion;24 rows have fewer values than the unnormalized slack.
Synthesized denominators feed the UNCHANGED accepted #333 route producer and
independent whole-original-edge consumer.721 endpoint routes contain867 original
edge occurrences versus862 shortest edges; all4 nonshortest routes remain.
Projective and nontrivially affine-transformed projective cubes are recognized
from point/slack data without a supplied family denominator. Generic polygon
cases retain nonbinary optimum spectra, with certified exclusions.

Five additional finite-data cases include signed, zero, collinear and2^-80
rational perturbation data. They check26 further systems,22 positive and4 excluded,
with optimum value counts1,2,3,3,1. Ten malformed controls are rejected, including
false completeness, false early termination, zero denominators, invalid duals,
incomplete nullspaces and altered spectra. These tests are not extra Lean
instances, formal parser correctness or an all-real proof by sampling.

The two new scripts and three unchanged prior dependencies reproduce the FULL
report and fixture byte-for-byte in a clean five-script workspace. Complete
JSON outputs accompany the export and regenerate; repository summaries are
explicitly derived. The formal source contains no custom axioms, admissions
or target import. The public preamble contains only imports/options and its
Mathlib-only type matches the top-level solution exactly. Six final transitive
reports are requested. Local lean/lake/elan and checked caches were absent and
toolchain hosts failed DNS; static/Python checks are NOT Lean compilation.
Use one complete prepared pinned final gate and preserve its actual outcome.
