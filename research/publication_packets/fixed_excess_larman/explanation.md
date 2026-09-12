For a fixed excess cap $E$, induct on the ambient dimension $d$.

If $d\le E$, then $n\le2E$. Apply the already-Proved Larman bound and pad its walk:
$$n2^{\max(d-3,0)}\le2E2^{\max(E-3,0)}.$$
An empty polyhedron has no vertex pair and the diameter assertion is vacuous.

If $d>E$, then $n\le d+E<2d$. The nonzero tight row normals at each vertex span
the ambient space: otherwise a small feasible perturbation in both signs would
contradict extremality. Consequently each endpoint has at least $d$ distinct
nonzero tight rows. The two sets intersect because $n<2d$. Explicitly counting
nonzero rows excludes tautological zero inequalities from this intersection.

Choose a nonzero row tight at both endpoints. The endpoints remain extreme in
its equality section. The already-Proved facet-reduction theorem removes that
row and lowers dimension by one. The resulting $n-1$ row description satisfies
$n-1\le(d-1)+E$, so the induction hypothesis applies with the SAME budget.
Both endpoints already lie in the section: transporting its walk adds no access
step and no multiplicative factor. This is classical shared-facet dimension
descent, with a conservative Larman base, including degenerate H-descriptions.

The submitted source contains the vertex spanning, nonzero-row counting, padding,
and induction proofs. Its only imported theorem dependencies are the already-Proved
Larman and equality-section reduction statements. The local audit driver treats
these as explicit propositions and has only standard logical axioms; the platform
checks the unconditional composition. The separate GitHub clipping assembly
uses the estimate on actual selected carriers, but is not part of this public
theorem's statement. No unresolved Hirsch ancestor is imported.
