# Cactus refinement continuation handoff

## Exact result and scope

Frozen starting main: `2c517a877e8aab885ae1583d97fc2e2ae6d9b017`. Read current main, STATUS, live PR heads and comments before changing anything. Coordination was actually posted to #263, comment `5689175929`, and read back. #264's mixed-defect/plateau research and #244/#238/#250/#255/#208/#210 remain unchanged.

This contribution is **written mathematics and exact Python research**, not Lean verification or a Prove2Me theorem. No theorem/submission ID, axiom audit or Actions publication is created for it. It should not receive a publication trigger just because a mathematical note is complete. A future formalization must include real simplicial-complex operations and a legitimate dependency on the normal-flag theorem, not a numerical recurrence with assumed route existence.

For the COMPLETE higher-minimal-nonface family of a finite complex, let W=sum(|N|−2) and ell be the number of incidence cycles of length at least6. If the bipartite incidence graph is a CACTUS, a complete prescribed stellar schedule satisfies

    subdivisions <= W+ell <= h−2c,

where h is its supported-label count and c its nonempty component count. Cycles may share articulation labels OR high nodes, and their number per component is unbounded. This strictly extends the preceding local one-cycle-per-component pseudoforest class. The older sharper t<=W bound remains useful on that narrower class; the new estimate is not claimed numerically sharper there.

A twin step preserves cactus structure and decreases W. Without twins, take a peripheral cycle in the graph's TWO-CORE. Nonarticulation high nodes there are triples with a unique private label. A long-cycle opening either kills one defect or replaces it by one copy, but always replaces that long block by a tree/four-cycle. Thus W+ell decreases even in a neutral-W move. In a peripheral four-cycle the newly created pair blocks the prospective copy, giving strict W descent. A valid next move always exists; no successful-macro oracle is assumed.

Rooting the block-cut forest at one high node/component gives q>=c+beta+ell, while W=h−q−c+beta. This proves the linear initial budget. For a simple d-polytope with m genuine facets, the classical Adiprasito–Benedetti bound and prior exact carrier transport give diameter<=m−d+W+ell<=2m−d−2c. Polytopality/normality is NOT inferred for arbitrary antichain tests.

## Exact reuse

`scripts/stellar_defect_budget.py` from #262 is imported UNCHANGED: blob `b51e2c3edec2c85026344566978561eb430050ec`, SHA256 `3d28385cc4cd6b31605e0918042bdee2fec280be8bf84f9c9ec897749a8bfdef`. Its exact mixed accounting and carrier maps are not new results here. No selector or proof on main is overwritten.

`cactus_reference_segments.py` is the attributed, unchanged dependency excerpt of #258's distances/Segment/ledger bodies, inherited from the previous local pseudoforest bundle; SHA256 `32e5bf925ff44acd1822e9832a514d0557d38486cc5f6d6b9409bb96c1f821ba`. The production default uses the repository's original Segment; the tests pass the identical standalone excerpt explicitly. This is NOT a new routing algorithm.

New code is the cactus graph analysis/selector/potential and independent verifier, plus new tests and saved-record replay. The independently written test classifier uses spanning-tree fundamental cycles, not production Tarjan blocks. The verifier never reruns the move selector.

## Geometric evidence and limitations

New selected stacked facets of a capped4r-antiprism form r loose high-triple cycles sharing the bottom pole. The polar has11r+2 genuine facets. A direct shielded3r-step schedule gives its flag certificate; these special3D bounds are not claimed best known. The r1/2/3 instances contain22/44/66 original vertices. The first two get complete independent supporting-triple enumeration; the third uses the exact known base and strict stacking transport.

IMPORTANT: those polytopal openings are shielded. Existing #262 strict-budget code finishes the same examples in the same3r steps. No empirical dominance over #262/#264 is claimed. The neutral-copy demonstrations are abstract complexes, not alleged polytopal spheres.

The32D test wedges29 facets of the r3 base and uses opposite endpoint wedge sides. It has64 genuine facets and no shared endpoint facet. All29 twin steps and9 cactus steps are verified;102 refined vertices give the structural all-pairs bound70. The actual route has36 original edges, not claimed shortest, and270237 membership queries. No refined maximal facets or full original high-dimensional graph are enumerated. All original edges and64 relative-interior facet witnesses are checked exactly. Stronger classical bounds may apply to this particular wedged family.

Abstract tests:114 four-vertex antichains,109 accepted;1504 literal face checks;163 pure carrier checks;160 generated cactus systems with5877 steps and468 neutral openings;5991 independent graph comparisons;24 bouquet cases up to16 cycles;13 invalid/unsupported controls. The120 small original endpoint pairs give606 edges and37 nonshortest routes. These adverse outputs are retained. Saved audit disables all planners/producers, validates four geometry/refinement records and53 original edges, and rejects two forgeries. It does not re-evaluate BFS distances.

The raw reports and four full fixtures regenerate from the scripts and are hash-bound in the source/replay records. Exact software tests are not Lean extraction or formal parser correctness. Complete minimal-nonface discovery from arbitrary H-data is not supplied and can be exponential.

## Remaining conjecture-facing gap

Non-cycle biconnected incidence blocks remain unsupported. A theta block or overlapping cycles cannot be treated as a cactus merely because each individual cycle is short. Such a block can send an opening's descendant into several independent cycles, destroying the local long-cycle payment. Neither a universal cactus reduction nor a polynomial size bound for those blocks is proved.

Potential useful next work must bound that exact block interaction, or use a different original-edge route. Do not state a small non-cactus kernel or a successful macro horizon as an already-solved premise. Existing #263/#264 moves can be used as genuine tested alternatives, but their universal completion is not known from this work.

## Reproduction

    python3 scripts/test_cactus_defect_refinement.py --stage abstract --out abstract.json
    python3 scripts/test_cactus_defect_refinement.py --stage geometry --out geometry.json --fixtures fixtures
    python3 scripts/test_cactus_defect_refinement.py --stage wedge --out wedge.json --fixtures fixtures
    python3 scripts/audit_cactus_refinement.py fixtures --out saved-audit.json

Use the exact #262 dependency from the bundle or current repository, not a similarly named incomplete local copy. No credentials, private files, Lean cache, workflow or pin change is needed.
