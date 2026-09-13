# First-gate verification evidence

The unchanged 711-line candidate passed its first prepared hosted gate.

- PR: #233.
- Command comment: https://github.com/jjoshua2/prove2me-work/pull/233#issuecomment-5657075611
- Frozen proof head: `8da78fd4f3d880fa053446d8170e11aa501cb43e`.
- Actions run: `34790147221`.
- Verify job: `103812755871`, completed successfully.
- Lean `v4.30.0`, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Driver, solution and statement compile exit codes: all zero.
- Printed new declarations: `Hirsch.CheckedCatalogue.checked_linear_tests`, `Hirsch.CheckedCatalogue.checked_rhs_tests`, and `solution`.
- Their transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Verified packet artifact: `10328146323`.
- Independently recomputed ZIP SHA-256: `92fb13e42048416f30aced2aae806a15ec5a09bcac1d1d9099ee081b17107266`.
- All five frozen packet hashes were independently recomputed and matched.
- Frozen solution bytes exactly match the pre-gate prepared source and read-back Git blob `7e96ab326fe36b96626cd8f46bff1fcbd7680d64`.
- Solution SHA-256: `5f661c7b4bff18859b12611e4f2b3b8f72be0100bd99a75a3fcd09a6609d1897`.

`packet-audit.json` and `verified-artifact.json` preserve the downloaded JSON records. This Markdown is a derived inspection summary. The statement-only file intentionally contains the target placeholder; the solution and its transitive audited dependencies have no sorryAx.

At this inspection, the trusted publish job was still running. Compilation is not an authenticated Prove2Me verdict. Consult the later publication receipt before claiming ACCEPTED or resuming anything. No source edit, retry, workflow change or second problem registration was made.
