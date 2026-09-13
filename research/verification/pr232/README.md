# Successful clean integration check of two repaired modules

Run34789669353 checked exact integration head
3de29caf666037ebf7de60608792f8b0e8792b27. The gate, both Lake targets, artifact
upload and result-comment callback succeeded. Publication was skipped.

The posted command was:

    /prove2me verify --targets=Solutions.PolynomialSeparatedFacetStars,Solutions.PolynomialSimplexLiftObstructions

The result comment is https://github.com/jjoshua2/prove2me-work/pull/232#issuecomment-5657026622.

Artifact10328035863 was downloaded and its SHA-256 recomputed independently as
65618aafab60ee9a571d5230f0dd6ffd88121deb676f3f028345de8bf81c5ee6.
verified-artifact.json is the unchanged artifact.json from that ZIP. readback.json
is explicitly derived from the archive and observed jobs. The original archive
contains only artifact.json and pr-comment.md: it does NOT contain source hashes,
transitive axiom lists, a publication receipt, or an authenticated theorem verdict.
None of those absent forms of evidence is claimed here.

The source was transplanted using its original Git blob identifiers. Those
identifiers and historical successful source-run IDs are in
research/PR210_REPAIRED_LEAF_CORES_INTEGRATION.md. This fresh clean-main gate
confirms compatibility of the unchanged repaired modules. The follow-up commit
preserves evidence only and changes neither source file.

This is integration of previously proved lemmas, not a new classical result or
Prove2Me publication. In particular, the simplex module's exact membership
reduction does not assume or prove the complete dual-feasibility sufficiency
needed by the separate covering-budget candidate. That candidate is not included.
