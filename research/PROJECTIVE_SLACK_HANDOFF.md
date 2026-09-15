# Projective slack-share research handoff

Base: main `9456445941adbbfd6464d8bd1d559599d6f3ea18`, merged #253.
Branch: research/projective-slack-share-acquisition.
Coordination: #253 comment5674253350. Existing projected-face and core/fibre
proof owners are untouched. This is an add-only RESEARCH packet, not Lean.

## The three precise claims

At a phase anchor p normalize each missing target slack by its slack at p.
The shares r_j=z_j/sum(z) and rho=min(r_j) are invariant under every invertible
projective map positive on the whole polytope. The scale factor D(p)/D(x)
cancels. Fixed row labels and the entire path tie signature are preserved.

An inspected acquisition-free polygon has its minimum rho at a vertex, by
positive S-weighted barycentric coordinates. There is a rho-decreasing
incident ray whenever needed: use a minimum coordinate j and a vertex w!=target
on its target facet, then the derivative numerator is -z_j(x)S(w)<0. The
eligible tangent cone spans w-x. This is derived, not assumed as a helpful
neighbor. Full-face minimization thus supports the old permanent retirement
proof. A shortest boundary arc may be used even without intermediate score
monotonicity. Both types of macro cost at most a=floor((e+2)/2), giving

    a * [r + sum_(h=3..r) floor(binom(e,h-2)/(h-1))].

The endpoint-only monotonicity argument also improves the old linear-potential
macro bound if it uses shortest arcs. Do not attribute that coefficient change
uniquely to the new share score; its distinct advantage is projective invariance.
No third-policy ablation was executed here.

The face count is STILL EXPONENTIAL in general. This is not a solution of
Polynomial Hirsch or an improved best-known general diameter bound.

A positive projective map with D=epsilon+(1-epsilon)Q/h turns old gap fraction
alpha into epsilon*alpha/(1-(1-epsilon)*alpha), while retaining the original
face lattice. On a fixed3D/14-facet truncated octahedron the old first fallback's
7/18 becomes7/(11*2^k+7), tested k8,40,120,240. The full new six-edge route is
projectively identical, with first macro rho1/3 to4/25. This only excludes a
uniform numerical fraction of the OLD gap; it does not prove a new gap rate.

## Honest experimental conclusion

Both complete-face policies were rerun on the same1016 pairs. Old2506 edges,
new2517, shortest2490. Six improve,thirteen worsen,997tie; nonshortest16 versus23.
Do NOT replace those mixed results by the favorable local six-edge example.
The new code stays an alternative, not the default. Product examples remain
shortest even after projective changes, with no supplied factor chart.

The local mathematical relaxation permits intermediate rho increases, but
NONE occurred in this executed sample. It did contain124 old-objective
 decreases. Seven genuine fallback decisions retire21 faces. No loop erasure
was required on the tested paths. State these coverage limits accurately.

## Reproduce

    python3 -m py_compile scripts/projective_slack_acquisition.py scripts/test_projective_slack_acquisition.py
    python3 scripts/test_projective_slack_acquisition.py

For a smaller run use --graph truncated_octahedron. --aux covers transforms,
large products and negatives; --assemble requires all source-matching stages.
The complete run has a costly exact12D projective product, not a whole graph.
The full report and pair tables regenerate; no candidate Python should be sent
through a Lean or publication workflow.

Original-edge verification, all polygon neighbors and face coverage are reused
from #253 unchanged. The new auditor also checks phase alignment, exact rho
minimization, shortest arc, original target-row acquisition, h-1 fresh retired
face labels and the route budget. An audit with inverse/basis/face discovery
disabled passes. There is no runtime LP or rank oracle in that audit.

The simple bounded full-dimensional ORIGINAL-H class is an input premise,
not certified globally by a local basis. Genuine facet counts use irredundant
original rows. Redundant strictly inactive rows only support the larger row-count
bound. No arbitrary projected-image or nonsimple solver is claimed here.

## Next useful mathematical work

The note supplies an exact projective roof normal form: original target-slack
coordinates z become u=z/sum(z), t=1/sum(z), with
u>=0, sum(u)=1, t>=max_i(B_i u/beta_i). Boundedness of the original polytope
forces t>0. Acquisition is reaching the simplex boundary. This is a general
reformulation, not an easy subclass; proving polynomial boundary-reaching
paths would require new control on the roof subdivision.

A useful next result would compress the retired facet-subset supply, identify
a genuinely controlled angular invariant, or produce a counterexample to a
specific proposed uniform angular decrease. More favorable tests or an
assumed phase bound are not enough. No proof backlog or accepted packet is
resubmitted in this research turn.

## Follow-up completed before delivery

The separate ANGULAR_ROOF_STALL.md/test_angular_roof_barrier.py now refute a
uniform fractional decrease of the NEW score too: first relative gain
13*delta on a fixed3D/12-facet/20-simple-vertex combinatorial type. The whole
parameter interval0<delta<=1/64 is covered by60 equalities/180 strict rational
slack certificates with nonnegative Bernstein coefficients, plus the
3-polytope upper bound v<=2f-4. Five complete numerical instances through
2^-240 use6 edges versus shortest5. This is a genuine deformation, not a
positive-projective re-encoding or a long-path counterexample. The new
score is invariant but is NOT a uniform contraction cure. Seek a genuinely
global invariant rather than reattempting that now-refuted local claim.
