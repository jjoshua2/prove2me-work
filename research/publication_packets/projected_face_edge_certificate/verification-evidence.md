# Successful original-image edge verification

The corrected 245-line source at proof head
3b6ebc129873cc4d19462e0efc2ec3e66d6cb878 passed the pinned Lean 4.30.0 gate
in run34862741785. Solution, audit driver and statement exited zero. All three
printed declarations use only propext, Classical.choice and Quot.sound.

The first run34861824296 reported exactly one addition-order mismatch in
row_bound at line85 and skipped publication. The one-line correction replaces
add_le_add_right h₁ _ by add_le_add h₁ le_rfl. No theorem type, assumption,
problem.json, or explanation changed. The derived diagnostic is preserved in
research/PROJECTED_FACE_FIRST_GATE.json. No theorem was registered/submitted
by that failed run. No further speculative edit loop was used.

Verified artifact10355631618 was downloaded and independently hashed:
7db00e21c83e841ea3526995d02fe7c621d45884640ccfda6c8cffc238cdb44d.
All five frozen file hashes were recomputed, and the original solution, problem
and explanation match the local and committed bytes. The raw audit and artifact
manifest are preserved unchanged. artifact-readback.json is an explicitly local
derived check, not a fabricated raw API result. Full compiler logs and the ZIP
are preserved in the downloadable bundle.

This is proof verification, not yet a platform verdict. The trusted publication
job is separate; read its actual later receipt before claiming acceptance or
requesting a resume. The originating runtime has no local Lean/Lake. Numerical
and source checks were not described as compilation.

The independent Python producer/auditor and tests are supporting executable
material. They are not Lean-extracted and accepting the generic theorem does
not automatically certify every future JSON input or the numerical fixtures.
The theorem applies to finite row witnesses and concludes a genuine image edge;
it does not promise a short sequence or universal efficient witness discovery.

PR241 remains uncompiled after its comment was blocked before posting. This
new proof does not contain that source or retry that blocked operation. PR244's
independent fibre-route work remains untouched.
