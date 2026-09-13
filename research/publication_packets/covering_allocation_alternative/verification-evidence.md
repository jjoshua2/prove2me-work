# Unchanged covering-budget proof: successful first gate

The 427-line solution at exact proof head
fb182322048816ba626cb6f1c821d4cb332224d3 passed its FIRST prepared compile and
axiom-audit gate in run34790733652. Driver, solution and statement exit codes
are all zero. All four audited declarations use only propext, Classical.choice
and Quot.sound. No proof edits or additional hosted compile attempts were needed.

Command: https://github.com/jjoshua2/prove2me-work/pull/234#issuecomment-5657140740
Run: https://github.com/jjoshua2/prove2me-work/actions/runs/34790733652

The original verified artifact10328760255 was downloaded and its ZIP digest
independently recomputed as829dd5af9b4422302609e83e8eafc59831054ede9718660480dbaf2f7915e6f1.
All five frozen file hashes were recomputed and match the manifest. The solution
also matches the previously prepared local source byte-for-byte. Its Git blob
is31e76f46f20a60e1b7d9ce4ee8595aa73a0848de. The exact downloaded packet-audit
and artifact manifest are preserved beside this note; artifact-readback.json
is explicitly a locally derived check, not a fabricated raw API response.
Full compiler logs remain in the original downloaded archive and conversation bundle.

This verification closes the former UNCOMPILED state of the covering reduction.
It does not by itself establish Prove2Me acceptance; consult the separate
publication receipt. The prepared source-manifest.json records pre-gate status
historically and has not been edited to misrepresent when verification occurred.

No local Lean/Lake was available in the originating container. The accepted
#219 helper bodies were compared to its frozen verified source; the numerical
regression was rerun, but neither static comparisons nor Python were treated
as Lean verification. The source was compiled by the pinned Actions environment.

The theorem handles signed and overlapping budget rows under explicit finite
nonnegative coverage. It retains every real budget and absorbs the synthetic
global-bound multiplier. It does not certify arbitrary circuit enumeration,
JSON parsing, original-polytope edge routes, or the full checked-budget geometric
composition. #233 is a separate accepted catalogue-to-dual bridge.
