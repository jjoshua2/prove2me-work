# One uniform finite coordinate catalogue for all cut vertices

## Exact conclusion

Let S be a generating set in R^d. There are m actual linear cuts C_j(y)<=b_j.
Let Omega be a finite cover of the WHOLE m-component vector (C_j(v))_j for
every v in S, and Lambda a finite cover of all coordinates of all v in S.
The theorem constructs ONE finite scalar set K, before choosing any cut vertex
or coordinate, with

    |K| <= 2^m * sum_(n=0..min(d+1,m+1)) |Omega|^n |Lambda|^n,

and every coordinate of every actual extreme point of
convexHull(S) intersect {y : forall j, C_j(y)<=b_j} belongs to K.

No cut-vertex enumeration, support list, positive weights, active-image
independence, row selector, or proposed output catalogue is supplied. The
complete support and active-equation uniqueness result accepted in #291 is
used to prove that all genuine coordinates are decoded by finite recipes.
The number m here is the number of added cut rows, NOT an automatically
identified total number of genuine facets of the original polytope.

The result is a uniform catalogue/count theorem rather than just a separate
existence statement for each vertex. It remains an overcover: inconsistent
recipes output zero, and consistent but underdetermined recipes choose an
arbitrary solution. Extraneous values need not be attained or even lie in the
base coordinate interval. The n=0 term is harmless counting padding; real
positive supports are nonempty. Empty generating sets, no cuts, redundant
active cuts and dimension zero need no special exclusion in the statement.

## Proof mechanism

For each n from zero through min(d+1,m+1), a finite code consists of an
m-bit active mask, an ordered n-tuple from Omega, and an ordered n-tuple from
Lambda. These data specify the mass-one equation and the selected cut-value
equations using the fixed right-hand side b. Fix one solution for each
consistent code's linear equations; use zero weights if no solution exists.
Dot the chosen weights with the scalar tuple to decode a real number.

The image of this finite code type is K. Counting masks, image tuples and
scalar tuples gives its cardinal upper bound. No injectivity of the decoder
is assumed: duplicate decoded values only make K smaller.

Now choose an arbitrary extreme point x of the ACTUAL cut set. Accepted #291
constructs v_i in S and positive w_i with total one and barycentre x. Its
support size is at most both d+1 and active_cuts+1, hence at most m+1. The
same theorem proves that total mass and all actual active cut equations
uniquely recover w, even among signed real alternatives.

For coordinate k, form the code from that actual active mask, the vectors
(C_j(v_i))_j in Omega, and the numbers v_i(k) in Lambda. The weights w solve
that code, so its chosen solution exists. Uniqueness on this genuine support
forces the arbitrary chosen solution to be w itself. The decoded scalar is
therefore sum_i w_i*v_i(k)=x(k). This works for EVERY x and k using the SAME K.
The output is not selected after inspecting x.

The construction is classical and noncomputable in Lean: consistency and a
choice of solution are used as logical definitions. This is not a verified
Gaussian-elimination implementation or a polynomial-time runtime claim.

## Dependencies, coordination and remaining quantitative work

The entire accepted #291 solution is reused, with only its top-level solution
and print name changed to accepted_positive_support. Its source has SHA256
7dc54444294016077ebd86c7132a1a26e5250af584a7311e49067f364891c2cb. All five
frozen dependency files were checked against the available original verified
archive, and the live repository acceptance receipt was read. It is theorem
1043e661-f761-4ee3-9d75-2822a58c77f9, submission
ac775547-35a3-498c-ab38-ad117c2a4d11. That theorem is not resubmitted.

The concurrently resumed #294 square-row extraction is left untouched,
including its publication command5720225598. Coordination for this distinct
catalogue is comment5720255040 on #294. This first bound deliberately counts
all active masks; it does not compete with or assume the sharper extraction.
It closes the support-to-ONE-global-catalogue implication while leaving
sharper catalogue accounting as a subsequent composition.

For a fixed number m of cuts, the expression is polynomial in the two input
catalogue sizes and has exponent at most m+1, not d+1 when d is larger. But
2^m and the varying exponent are not uniformly polynomial in unrestricted m.
The proof does not provide small Omega or Lambda for arbitrary carriers.
The previously established global-alphabet obstructions are not contradicted.
No edge walk, dimension-free contraction, or unconditional Polynomial Hirsch
bound is asserted. This formalizes a finite-enumeration interface using
classical convex geometry, not a historical novelty claim.

## Prepared verification and separate supporting computation

The standalone source has419 lines and imports only Mathlib at the committed
Lean4.30.0/Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f pin. The public
target is extracted exactly from its top-level solution, with imports/open/
options only in the preamble. The reused dependency and both new proof endpoints
have explicit transitive axiom reports. No proof admission or target import is
present. Runtime inspection found no local Lean/Lake, and toolchain-host DNS
failed. Source checks and Python are NOT local Lean compilation. This packet
is prepared for the user's requested actual comment-triggered final gate.
Only that gate's real compile/audit and authenticated publisher verdict can
establish verification or acceptance; no outcome is presumed here.

The independent exact rational test enumerates26397 complete finite recipes
across seven models, solving3636 recipe systems including2766 consistent
rank-deficient ones. It independently reconstructs39 cut vertices from188
original H-systems and checks all98 coordinates and39 positive-support
recoveries against the single catalogue for each input. Incomplete cut-image
covers and nonextreme points give explicit countercontrols; inconsistent empty
recipes and zero dimension are also checked. These are supporting arithmetic,
not Lean-extracted code, a formalized parser or the basis of platform acceptance.

    python3 scripts/test_uniform_cut_catalogue.py

No existing source, pending/accepted packet, pin, workflow, permission, API key
handling or trusted-main publisher isolation is changed by this contribution.
