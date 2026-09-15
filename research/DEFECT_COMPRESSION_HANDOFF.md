# Continue from safe higher-defect incidence compression

Read the LIVE STATUS, current main SHA and PR queue. The first index still named
#259; a commit-level check revealed newly merged #260. Do not duplicate its flat
block criterion, simplex hierarchical example, or coupled-triangle family.
This new work extends them with a safe stellar recurrence and bounded residual
higher-incidence types. It is written research/exact Python, not Lean/Prove2Me.

Core definition: higher defects are inclusion-minimal empty ORIGINAL facet
intersections of cardinality>=3. For a current edge E={u,v} and new z, all new
minimal nonfaces are the minimal members of {E}, old N not containing E, and
{z}+(N-E) for old N meeting E. If u,v have the same NONEMPTY higher incidence,
every high defect contains both or neither. The only high updates are replacing
the pair by z and dropping descendants that become missing pairs. No high
splitting occurs. Old u,v stay in the subdivided sphere; no original H rows are
deleted or identified.

With q initial higher defects, union size k, t safe moves, and residual size h:
  t<=k-h, q'<=q, h<=2^q'-1<=2^q-1.
Finish by #260's one residual-block barycentric refinement, all other labels
singleton. If f_B is its number of nonempty residual faces, then
  M=m+t-h+f_B, diameter(original)<=M-d.
The coarse bound is e+t+2^h-h-1, e=m-d. This is linear in original facet count
for FIXED q with a potentially double-exponential additive constant. No small-q
premise is supplied for arbitrary inputs. In practice quote exact M, not merely
the weak worst case. The same-dimensional stellar carrier proof ensures every
refined step becomes an original edge or stationary step. Compatible endpoint
lifts keep the smallest original common face.

Disjoint high supports resolve in sum(|N|-2) moves. A nonempty-core sunflower
with q petals resolves in k-q-1 moves; at most two high defects always resolve
with the corresponding disjoint/overlap counts. Mixed incidence is NOT safe:
the join of two triangle boundaries subdivided across factors doubles the high
count2->4. Actual cyclic-polar4D examples have no safe twin at all; their expensive
residual fallback remains in tests. Do not advertise universal compression.

The all-dimensional family extends #260's p2 triangles to p-simplex factors:
  x_ij>=0, u_i=sum_j x_ij<=1,
  u_i+u_(i+1)<=2-10^(-(i+1)).
For p,r>=2: d=pr,m=(p+2)r-1,q=3r-2,all original labels in higher defects.
The p lower labels per block are incidence twins. Exactly r(p-1) safe moves
leave a flag refinement with M=(2p+1)r-1, giving diameter<=(p+1)r-1.
The connected high-minimal-nonface hypergraph excludes combinatorial products.
The shallow-cut/grid proof and full nonface update are in the main note.
Every valid FLAT block partition must have at least2^ceil((p+1)/2)-1 refined
vertices. Hierarchy is polynomial in p,r while that lower bound can be
exponential in p. This is a comparison of certificate size, not a diameter
lower bound or a best-known bound for these easy/few-excess test instances.

Reproduce:
  python3 scripts/test_defect_incidence_compression.py --stage abstract
  python3 scripts/test_defect_incidence_compression.py --stage geometry
  python3 scripts/test_defect_incidence_compression.py --stage family

Generic producer input is only A,b,start,target. It classifies ALL minimal
nonfaces through d+1 with exact original-H witnesses; that can be exponential
and can enumerate all original vertices. Caps fail honestly. The consumer
replays classification, BFS and carrier routes but no geometric LP/inversion.
Neither Python nor JSON decoding is Lean-extracted. All original-H global
simplicity/facet assumptions are independently verified only on test models.

Abstract tests:114 complexes,438 edge updates,114 safe updates,1110 carrier
adjacencies,533 two-defect,42 sunflower and120 disjoint cases. Geometric tests:
80 pairs,141 new edges vs140 raw#258/BFS,one nonshortest;160 refined edges,19
stationary steps;1754 LP calls,5737 pivots. Eight search-disabled audits and12
negative controls. Six family instances reach dimension32, but only the first
two have a separate exhaustive H-classification/BFS reference; larger ones use
the exact proved structural construction plus original-edge certificates.
No published exponential combinatorial-segment family was executed here.

The classical AB flag bound is imported, not republished; Lutz--Nevo is general
stellar background, not authority for a false arbitrary-edge monotonicity rule.
Use the exact recurrence in this work. Full reports/fixtures regenerate and are
bundled. The repository compact summary/replay/source identities are derived
records, not platform verdicts. No existing selector, theorem, pin, workflow,
credential or other agent's active branch is modified.

Next actual research: control the irreducible higher-incidence types or allow
mixed subdivisions with a bounded defect-growth budget. Do not insert small q,
small h or a polynomial residual refinement as an unproved premise. Research
contributions need no speculative Actions compile. Re-read ownership before
opening another same-line PR or repeating the already finished flat refinement.
