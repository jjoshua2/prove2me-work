<!-- hirsch-exact-support-fixed-deficit-20260912-1177094 -->
Published [a dimension-independent Larman bound at fixed row excess](p2m:theorem/49576ed3-5185-4951-9215-43283ef6169e), with [accepted proof](p2m:solution/cd24addc-446f-4d16-b814-85315057c98f). For a bounded n-row H-polyhedron in dimension d with $n\le d+E$, the padded ordinary-edge diameter is at most

$$2E\,2^{\max(E-3,0)}.$$

This is a classical coarse consequence of [Proved Larman](p2m:theorem/68453b6b-bcef-4672-b877-d04e56527e3f) and [Proved facet reduction](p2m:theorem/11b3500a-b9f8-4b44-94aa-d71354441ddb), now connected by a checked public proof. When d>E, shared NONZERO tight-row counting lowers the row count and dimension together without access cost; when d<=E, at most 2E rows remain. The statement includes empty/degenerate polyhedra and redundant/zero rows. It is not a new classical diameter discovery or a uniform polynomial bound.

[Integration PR #201](https://github.com/jjoshua2/prove2me-work/pull/201) also verifies the exact selected-degree candidate and preserves both independent #202 Lean modules unchanged. [Frozen proof source](https://github.com/jjoshua2/prove2me-work/commit/117709458ec4b071dc846cd8443feea19ca2669b). For the SAME deferred clipping certificate and actual parent-vertex portal pairs, write e=n-d, r=used cuts, and g=e-r:

- The exact pointwise budget is $\delta_i+r\le e+1+\deg_S(i)$. The selected-run identity is now formalized, including empty selections, and gives $\sum_i\delta_i+2c\le r(g+3)$. Here c counts starts of selected runs on the chosen chordless path. In the small-excess regime this bounds actual edge cost using the [Proved small-excess theorem](p2m:theorem/12426807-9602-4014-bd5e-c69fb43f4cb6).
- #202 proves $2h_i\le M_i$ for actual vertex-pair carriers, hence $h_i\le\delta_i$ and $M_i\le2\delta_i$. Thus a dimension-at-least-six actual carrier has excess at least SIX; an excess-four/five carrier cannot be that high-dimensional obstruction.
- Applying Larman in the minimum intrinsic presentation closes EVERY selected call at fixed deficit. The assembled ordinary-edge route costs at most

$$D+2(g+3)2^g r.$$

In particular, all deficit-one and deficit-two cases cost at most D+16r and D+40r, with no matching/independence condition on selected cuts. The target-rooted wrapper has D=1. These constants are conservative. The remaining obligation is no longer the deficit-one internal-run case.

The #201/#202 core passed local Lean and the single final [GitHub verification run](https://github.com/jjoshua2/prove2me-work/actions/runs/34708143326): 30 required declarations, 406 transitive axiom reports, standard logical axioms only. Both finite regression checkers passed with current source hashes. These selected-run and clipping assemblies are LOCAL/GITHUB Lean results; only the separate fixed-excess theorem above has the new Prove2Me acceptance verdict. The core route adapter uses Larman directly and has no unresolved recursive diameter premise.

Next target: a joint cost bound for COUPLED carriers when g grows. The [cube stress test from #202](https://github.com/jjoshua2/prove2me-work/pull/202) rules out forcing logarithmic g for every shortest certificate: all target-slack cube faces share a vertex, their labels form a clique, and a chordless path uses at most two, so g>=d-2 although cube diameter is d. This cube argument is mathematically explained and finite-tested, not a new Lean theorem here. A useful potential must handle such product structure without treating deficit as actual distance; certified row blocks are reusable only when actual factorization is supplied.

[Polynomial Hirsch](p2m:theorem/58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac) remains Open, with [common-face diameter in dimension at least six](p2m:theorem/87a8b4f4-8b58-4340-8cb9-5fd1b548d01e) the sole reported open leaf. The public fixed-excess theorem has real dependency edges to its established inputs, but is not connected to the root by a proof of a uniform polynomial bound. No cosmetic or cyclic root child was added.
