# A regularized objective sweep through genuine zonotope edge faces

Let Z=sum_i[0,w_i], with arbitrary finite real generators, including repeated,
opposite and zero vectors. The two supplied linear objectives f,g are nonzero
on every nonzero generator. We construct k with the same generator signs and
whole maximizing face as g. For h_t=(1-t)f+t*k, the exact exceptional set T of
nonzero-generator ties lies in (0,1), has at most m elements, and every such
time exposes a whole nondegenerate ORIGINAL edge of Z with extreme endpoints.
Every other time in [0,1] exposes a singleton actual extreme point.

The perturbation is derived, not assumed generic. Form the finite vector set
containing every w_i and every contrast f(w_i)w_j-f(w_j)w_i. Pinned Mathlib's
finite proper-subspace argument supplies a linear functional h nonzero on every
nonzero member. An explicit finite-margin proof chooses e>0 small enough that
k=g+e*h preserves all nonzero g signs while resolving every nonzero contrast.
In particular it preserves the endpoint chamber and therefore the whole target
support face. It does not perturb the original generators or their polytope.

If w_i and a nonzero w_j tie simultaneously at t>0, their two affine scalar
equations imply k(f(w_i)w_j-f(w_j)w_i)=0. The constructed regularity forces that
contrast to vanish, and f(w_j)!=0 gives w_i=(f(w_i)/f(w_j))*w_j. Thus every
simultaneous tie lies on one line. Parallel and antiparallel ties are allowed;
they are not incorrectly treated as separate independent-direction crossings.

Each nonzero generator has at most one zero along the sweep, at
f(w_i)/(f(w_i)-k(w_i)). Filtering the image of these m explicit ratios gives
EXACTLY all interior nonzero ties, so its cardinality is at most m. There is
no supplied finite crossing list or cardinality oracle. The accepted #312
whole-face theorem then constructs both endpoints of each exceptional edge.
Away from T, coefficient saturation makes every maximizing representation equal
to the sign-selected point (zero generators contribute nothing), so the face is
a singleton actual extreme point. No coefficient-cube edge is silently called
an original zonotope edge.

The complete 425-line accepted #312 namespace prefix is reused byte-for-byte,
excluding its former public root and print suffix. All five frozen dependency
hashes and the original verified ZIP digest were checked. The new standalone
packet recompiles the whole dependency chain and requests five transitive axiom
reports. No accepted target is submitted again.

This target supplies the regularity, exceptional-time count and actual face
geometry needed for a subsequent route assembly. It does NOT yet enumerate the
crossings in increasing order, prove the adjoining chamber vertices are the
two endpoints of each edge, or derive regular exposing objectives for arbitrary
specified vertices. Those are separate remaining formal obligations, not hidden
hypotheses asserting a short path. The explicit endpoint-objective regularity
premises remain. Moreover m counts segment generators, not original H facets;
no polynomial H-presentation bound or unrestricted Polynomial Hirsch theorem is
claimed. The classical zonotope/hyperplane-arrangement viewpoint is credited to
Deza--Pournin, A linear optimization oracle for zonotope computation,
arXiv:1912.02439. No historical novelty or improved classical bound is claimed.

The Fraction-only supporting suite checks 165 finite sweeps, including 46
parallel-tie events and 39 zero generators. It checks entire small support
faces against all Boolean representations, not only selected endpoints. Four
larger selected systems reach ambient dimension64 without full body enumeration.
Saved records audit with perturbation construction disabled; malformed crossing
and endpoint data are rejected. A naive unperturbed square sweep has a genuine
independent simultaneous tie, retained as a negative control. Sample walks in
the Python tests are not an additional Lean all-pairs route theorem.

Local Lean/Lake was unavailable and compiler-host DNS failed. These source and
rational checks are not Lean verification. The complete packet receives one
prepared new top-level PR comment for the existing pinned compiler/axiom gate
and authenticated publication. Preserve any actual failure, without speculative
repeated Actions editing. Pins, workflows, protocol guard, actor allowlist,
duplicate safeguards, credential isolation and other owned branches are unchanged.
