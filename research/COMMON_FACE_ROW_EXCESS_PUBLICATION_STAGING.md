# Common-face row-excess publication staging

The theorem source is already merged and kernel-verified. This branch contains only the reviewed standalone publisher plus this proof-neutral trigger.

The first publication workflow stopped before authentication because the standalone Lean invocation had not built `Definitions.Def_Hirsch_common_face_geometry`. The corrected retry builds that public definition module first, then independently compiles and axiom-audits the exact same generated root-level `solution` before authentication or any Prove2Me write. No proof bytes changed.
