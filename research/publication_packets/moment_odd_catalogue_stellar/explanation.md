# The concrete odd moment catalogue meets the accepted stellar count

## Exact theorem

The target is Hirsch.moment_odd_catalogue_stellar_bound. Its initial complex is
not a supplied combinatorial incidence table: it is the family of actual
feasible tight-row intersections for the explicit real inequality system

  sum_(j=1..2k) [n^j - average_(i=0..4k) i^j] x_j <= 1,
  n=0,...,4k.

After any t actual forward stellar subdivisions at genuine faces of size at
least two, with fresh vertices and the stated finite supports, suppose every
terminal inclusion-minimal nonface has cardinality two. The theorem proves

  choose(2k,k+1) + t <= choose(4k+1+t,2).

The public statement contains both the original-H definition of the initial
face family and the actual stellar face-membership rule. It does NOT take a
catalogue, a large nonface count, a separator chain, an incompatibility oracle,
or a persistence/count-growth assumption as input.

## Constructing every catalogue member

Choose S from powersetCard (k+1) (range (2k)) and map each index s to 2s+1.
These are k+1 distinct original odd labels. Mathlib's sorted order embedding
orderEmbOfFin enumerates S; its membership and strict monotonicity are proved
properties of that construction, not additional hypotheses.

For each enumerated s, construct left label 2s+1 and right label 2s+2. Both are
less than 4k+1. Successive pairs interleave strictly because distinct increasing
integer indices differ by at least one. Thus all pairs are selected from the
ORIGINAL row labels; no larger auxiliary inequality system is introduced.

The accepted interleaved-polynomial lemma from #287 then forces a strictly
positive slack at some selected odd label whenever the original point is
feasible. The original slack polynomial has degree at most 2k, is nonnegative
at every original label, and its average over ALL 4k+1 labels is one. Hence it
is nonzero. This proves that the full odd-label image is not a face.

Every proper subset of that image has at most k labels. To use the accepted
small-face witness, the proof constructs its Fin(4k+1) representative by filtering
the full finite label universe and proves that its natural-label image is exactly
the supplied subset. Injectivity preserves cardinality. The accepted squared-
root-polynomial construction yields an original feasible point with exactly
those tight rows. The new code therefore derives inclusion-minimality, not only
incompatibility or a list of sampled proper faces.

## Exact cardinality and assembly

The odd-label map is injective, so the induced image map on finite subsets is
injective as well. The catalogue is defined as the finite image of the actual
powersetCard family. Its cardinality is exactly choose(2k,k+1), by Mathlib's
finite subset-count theorem. No enumeration count is supplied as a hypothesis.

Each catalogue element is supported on range(4k+1) and is a genuine minimal
nonface of the initial original-row face family. These are the inputs needed
by accepted #281's finite_sequence_bound. The theorem invokes that PROVED body,
which derives distinct descendants and one additional born nonface per step.
Substitution of the derived catalogue cardinality and initial vertex-set size
gives the displayed inequality.

The #285/#286 moment helper namespaces (present in accepted #288), the accepted
#287 interleaved-polynomial namespace, and the corrected accepted #281 finite
stellar namespace are copied as actual proof code. Their public solution targets
are omitted; no old theorem is submitted again. Helper definitions do not enter
the import/open-only public preamble. No target theorem is imported as an axiom.

## Scope and geometric boundary

This closes the previously separate separator-construction, full-catalogue,
cardinality and finite-stellar-count assembly interfaces. The assertion is
universal in k and t, not inferred from numerical tests. k=0 is included with
an empty catalogue; for nontrivial families k>=1 the odd subsets exist.

The public conclusion is still a count for the explicit original-H face family.
It does NOT independently formalize the moment hull's full-dimensionality,
bounded polar realization, irredundancy, simplicity or a numerical/asymptotic
square-root lower bound on final size. In particular it is not an original-edge
diameter lower bound or a solution of Polynomial Hirsch. The intended obstruction
concerns TOTAL size of full forward stellar flagification, not the number of
labels a chosen route visits. Inverse stellar moves and non-stellar subdivisions
are outside the given sequence definition.

Downward closure and support for the sequence are explicit. There is no theorem
here that a sequence ending in flagness exists with any prescribed small t.
The conditional count does not assert such existence or hide a route assumption.

## Actual verification boundary

The originating runtime has no Lean/Lake executable, and fresh DNS resolution
for GitHub and the toolchain host fails. Local exact arithmetic and signature
checks are NOT Lean verification. The user explicitly requested a new top-level
comment to try publication, so the existing pinned comment gate is the intended
single prepared final attempt. No new workflow, toolchain, permission, credential
or trusted-main secret split is introduced. The real compiler/axiom/publisher
result must be read back before reporting verification or acceptance.

The standalone rational test explicitly enumerates all small catalogue members,
checks independently evaluated original-row witnesses and barycentric moment
relations, and tracks catalogue roots through literal stellar subdivisions on
small original moment face systems. Large samples are individually checked;
complete exponential catalogues are not claimed enumerated. Python and JSON
are not Lean-extracted. Any receipt added later must identify the exact frozen
proof SHA and preserve these scope limits.

## Reproduction and attribution

  python3 scripts/test_moment_catalogue.py

The normal publication request, on this packet's own OPEN same-repository PR:

  /prove2me publish research/publication_packets/moment_odd_catalogue_stellar

Do not post this on #281/#287/#288 or any other accepted packet's PR. Do not
repeat it while the new attempt is pending. Classical interpolation and moment-
curve geometry are not claimed historically novel. Accepted dependencies and
Mathlib's finite sorting/counting APIs are reused with their exact pinned version:
Lean4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
