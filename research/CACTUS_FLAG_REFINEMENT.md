# A complete linear-size flag refinement for cactus higher-incidence graphs

## 0. Status, provenance, and exact scope

This is a written mathematical proof and executed exact research software. It is **not** a Lean compilation, axiom audit, Prove2Me acceptance, or solution of unrestricted Polynomial Hirsch. The frozen repository baseline is `2c517a877e8aab885ae1583d97fc2e2ae6d9b017`.

The preceding local pseudoforest result handled at most one incidence cycle per connected component. The present theorem allows arbitrarily many cycles per component, including cycles sharing a higher-defect node, provided the incidence graph is a cactus. It proves an actual terminating schedule; it does not assume successful bounded-horizon macros or a cheap residual refinement.

Merged #261 already supplied safe equal-incidence compression. Merged #262 already supplied the exact stellar update, the mixed-defect balance and shielding criterion. #263 and active #264 supplied distinct polytopal plateaus and bounded-macro examples. Those operations and examples are not new contributions here. The production code imports the **unchanged #262** `scripts/stellar_defect_budget.py`, Git blob `b51e2c3edec2c85026344566978561eb430050ec`. Its exact account and carrier routines are reused, not copied into a competing implementation.

The external diameter ingredient is Adiprasito–Benedetti, *The Hirsch conjecture holds for normal flag complexes*, arXiv:1303.3598v3, Theorem 1.4. A normal flag complex of dimension d−1 with M vertices has facet-ridge diameter at most M−d. This classical theorem is not reproved or republished. Lutz–Nevo, arXiv:1302.5197, supplies background on stellar refinements, not the count proved below. No claim of historical priority is made for all equivalent class consequences.

## 1. Definition and theorem

Let K be a finite simplicial complex with every named vertex present, specified by its **complete** antichain of minimal nonfaces. Let H be the higher minimal nonfaces, those of size at least three. Missing pairs remain part of the input and all updates. Define

    q = |H|, h = |union H|, W = sum_{N in H} (|N|−2).

The bipartite higher-incidence graph has one node for each supported label and one for each N in H, with membership edges. Let c be its number of nonempty components. A graph is a cactus when each biconnected block is a single edge or a simple cycle; equivalently two distinct simple cycles share at most one vertex. This is not the one-skeleton of K or its facet-ridge graph.

Let beta count the incidence cycles and let ell count the **long** cycles, with at least six edges. A four-cycle has two higher-defect nodes and is short. The graph is bipartite, so these cover all cycles.

**Theorem.** If the higher-incidence graph is a cactus, K has a flag refinement obtained by at most

    t <= Psi(K) := W(K)+ell(K) <= h−2c                       (1)

stellar subdivisions of face edges. The proof constructs a legal next move whenever a higher defect remains. Every old vertex remains; every move adds exactly one refined vertex. No residual barycentric subdivision is needed.

For a simple d-polytope P with m genuine ORIGINAL facets and such a dual boundary, the normal-flag theorem and carrier transport give

    diam(P) <= m−d+W+ell <= m−d+h−2c <= 2m−d−2c.            (2)

If H is empty then h=c=W=ell=0 and the usual flag bound m−d applies. Arbitrary abstract test complexes receive the refinement conclusion only: purity, normality and polytopality are not inferred.

Neither q nor the number of cycles must be a fixed small constant. The restriction is the cactus **block structure**. A theta block, or other overlapping-cycle block, is not covered even if it has small cycle rank.

## 2. Why the initial potential is linear

Write E for the number of graph edges. Euler counting gives

    beta = E−h−q+c,   W = E−2q = h−q−c+beta.                (3)

Root the block-cut tree of each nonempty component at a higher-defect node. There is at least one root high node per component. A cycle with r high nodes contributes at least r−1 previously uncounted high nodes: only its parent articulation can have appeared earlier. If the parent is a label node it contributes all r. A short four-cycle contributes at least one new high node; a long cycle contributes at least two. Tree edges may introduce still more high nodes and do not weaken the bound. Therefore

    q >= c + beta + ell.                                  (4)

Combine (3) and (4): W+ell<=h−2c. The same reasoning works when cycles share a high node, not just when they share label nodes. The software checks the exact graph identities, while its tests independently reconstruct fundamental cycles using a spanning forest rather than trusting the production block decomposition.

## 3. The exact operation and twin moves

For a face edge E={u,v}, introduce z by stellar subdivision. The new minimal nonfaces are the inclusion-minimal members of

    {E},
    {N old minimal nonface : E is not contained in N},
    {{z} union (N minus E) : N old minimal nonface, N meets E}. (5)

This is the existing #261/#262 membership identity. Its complete residue minimization is executed by #262's unchanged `account`, including all missing-pair blockers. Raw candidate descendants must not be counted as surviving higher defects.

If u,v have identical nonempty incidence among higher defects, they are twins. E is a face because it is a proper subset of a higher minimal nonface. Its subdivision creates no new higher defect; a containing higher nonface shrinks by one, and a descendant pair leaves H. W decreases by the number r of higher defects containing E.

In a cactus r<=2: three common high neighbors already form overlapping cycles. For r=1 the twins are two label leaves at a high node. Their merger cannot create a cycle; if the high node shortens to a pair and leaves the incidence graph, only a tree branch is removed. For r=2, the twins are the two label nodes of one four-cycle. The operation turns that block into a path, or removes part of it if a high node disappears. Other blocks attach only at its nodes. Hence cactus structure is preserved and no long cycle is created. In either case Psi drops by at least one.

The proof and implementation first take an available twin. This is reuse of #261's safe operation, not a new result claimed for equal incidences.

## 4. Every remaining cactus has an eligible peripheral cycle

Suppose H is nonempty and no twins remain. A connected tree incidence component would contain twins: root at a high node and choose a farthest high node. All but its parent neighbor are label leaves, and its degree is at least three, giving two private labels. Thus every remaining component contains a cycle.

Delete degree-zero and degree-one graph nodes repeatedly to form the two-core. No high node can lie outside this core: a farthest high node in one of its attached trees would again have at least two private labels. Every branch outside the core therefore consists just of private label leaves attached to high nodes of the core.

A cactus two-core has a peripheral cycle block with at most one articulation **in the two-core**. Articulations in the full graph are not the right criterion: a private leaf can make an otherwise peripheral high node a full-graph articulation.

Every nonarticulation high node of this peripheral cycle has exactly two cycle neighbors and exactly one private label. At least one private label is required because a high node has degree at least three; two would be twins. Every nonarticulation cycle label has degree exactly two in the full incidence graph.

If the peripheral cycle is long, choose two adjacent nonarticulation high nodes N and M and their shared nonarticulation cycle label x. Such a choice exists even if the unique articulation is a high node: a long cycle has at least three high nodes, so two adjacent other ones remain. If the articulation is a label, avoid that label. Let y be N's private label. Both N and M are triples. The move is E={y,x}.

For a peripheral four-cycle, if its attachment is a high node or there is no attachment, the two shared label nodes are twins, a contradiction. Thus in a twin-free four-cycle its sole attachment is a label a; the other label x has degree two, and its two high nodes have private labels. Again choose E={private label of N,x}.

This proves that a next move exists. It is not an assumed enumeration oracle or a bounded search-success condition.

## 5. Long-cycle openings: the missing charge is topological

For a long peripheral block, only N and M meet E={y,x}. N contains both endpoints and becomes a missing pair. M meets just x and may produce the new triple

    M' = {z} union (M minus {x}).

Every other higher defect survives unchanged. Missing pairs can suppress M', but cannot create a different higher descendant. There are two possibilities.

**No surviving copy.** W decreases by one. The old long cycle opens into a tree path, so one long cycle disappears.

**A surviving copy.** W is unchanged: N was removed and M' added. However, the old long cycle is replaced by the four-cycle between M, M' and the two labels of M minus {x}. One of these shared labels is M's old private label; the other is its other old cycle label. All remaining old parts attach through at most the latter. The old x becomes a private leaf of M; the new z is a private leaf of M'. Thus the replacement graph is still a cactus. Other long cycle blocks are unchanged and exactly one long cycle disappears.

In both cases, Psi=W+ell decreases by at least one. This avoids requiring W itself to decrease on every move. It also avoids the prior one-cycle proof's need to reserve a particular future double-hit in the same original component: many neutral openings can be paid immediately by the distinct long cycles they eliminate.

## 6. Four-cycle openings and termination

For the twin-free peripheral four-cycle, write

    N={x,a,y}, M={x,a,v},

where a is the possible attachment and y,v are private. Subdivide {y,x}. N becomes the pair {z,a}. The potential descendant of M is {z,a,v}, which contains this new missing pair and therefore is NOT a minimal higher nonface. Thus W decreases by one, the four-cycle disappears, and no long cycle is created. Again Psi decreases.

Twin moves and peripheral openings preserve cactus structure. Whenever a higher defect remains, Section 4 supplies a move. Psi is a nonnegative integer, so the process terminates at a flag complex in at most its initial value. This proves (1) without a presumed successful macro trace. Long cycles can share articulation labels or high nodes, and connected components can have arbitrarily many cycles.

For example, three abstract loose triangles sharing one label require three neutral openings in the implemented schedule. Their later reductions complete in 11 subdivisions from W=9 and Psi=12. This is a schedule example, not a lower bound on every possible refinement. The abstract no-shield examples are NOT claimed polytopal spheres.

## 7. Original edges and a twin prelude

Use the existing #262 carrier map for each stellar edge subdivision. A refined maximal simplex containing z carries `(F minus {z}) union E`; a maximal simplex omitting z carries itself. The common ridge of two adjacent refined maximal simplices has an old carrier with at least d−1 labels. Consequently their old carriers are equal or adjacent, not unrelated endpoints of a chord.

Compose these maps backward through every step and remove consecutive repetitions. A route in the flag subdivision becomes an ordinary-edge route in the original simple polytope, with no length increase. Compatible lifts preserve the original common endpoint facets: when just one endpoint contains E, drop an E-label absent from the other endpoint; when both contain E, drop the same label. Run the flag route in the link of their common refined face. The code audits every backward carrier transition, then independently checks the final coordinates on the original H-system.

An initial sequence of valid nonempty-incidence twin moves may start from a graph that is not cactus. If it reaches a cactus with residual support h1 and c1 nonempty components, #261 gives t0<=h0−h1, while (1) gives t1<=h1−2c1. Therefore

    t0+t1 <= h0−2c1.                                      (6)

The prelude is supplied and its twin identities checked; no claim says every input has such a prelude. The production implementation rejects unsupported residual graphs. The prior sharper one-cycle count t<=W remains available for that narrower class; the new general cactus estimate is not asserted numerically sharper on every pseudoforest instance.

## 8. Rational polytopes with arbitrarily many interacting cycles

Take a capped q-antiprism with q=4r>=4: bottom ring x_i, upper ring y_i, and poles B,T. Its triangular facets are

    {B,x_i,x_(i+1)}, {T,y_i,y_(i+1)},
    {x_i,x_(i+1),y_i}, {x_(i+1),y_i,y_(i+1)}.

This is the flag base used in the preceding local pseudoforest work; it is not a new base family. The new selection stacks, for j=0,...,r−1 and a=4j, the three facets

    {B,x_a,x_(a+1)},
    {x_(a+1),x_(a+2),y_(a+1)},
    {B,x_(a+2),x_(a+3)}.                                  (7)

Stacking a triangular facet of a simplicial 3-polytope creates that old triangle as one higher minimal nonface. A new stack vertex has missing pairs to every vertex outside its triangle, and creates no other higher nonface. Previously selected facets remain triangles until stacked. Thus (7) is exactly the complete higher family: r loose three-defect cycles sharing only B. For r>=2 the connected incidence graph is outside the old pseudoforest class but inside the new cactus class.

The polar simple 3-polytope has m=11r+2 genuine facets and 22r vertices. Its high support has h=5r+1, W=3r, ell=r and Psi=4r. There is a direct 3r-move schedule on this family: in each cycle first subdivide {x_a,x_(a+1)}. The old missing pair {x_a,x_(a+2)} suppresses its potential copy. Then compress the two now-private labels of the middle triple, followed by the private pair of the last triple. This retains the shared B and does not affect other cycles. Hence this particular family has a flag-refinement bound 14r−1, sharper than the generic 15r−1 obtained by Psi. These are certificate-size bounds, not new best 3D diameter estimates.

The numerical producer proposes rational ring coordinates by rounding trigonometric values, and verifies every strict supporting inequality exactly. Each stacked point is an explicitly bounded positive outward perturbation of its facet centroid, beyond that facet and strictly beneath every other one. For each fixed r a sufficiently close rational realization exists; the fixed rounding precision is not asserted to work for every r without checking. Executed r=1,2,3 cases pass; r=1,2 also have independent complete supporting-triple enumeration. All original facets have explicit relative-interior witnesses.

**Important negative comparison:** these polytopal examples have missing-pair shields. Their computed openings do not create surviving new high defects, and #262's existing strict-budget code completes them in the same 3r steps. They demonstrate a new complete multi-cycle class theorem and its geometric applicability, NOT empirical dominance over #262/#264. The many neutral-copy tests are abstract complexes and receive no unsupported polytopal-diameter claim.

## 9. A full 32-dimensional original carrier

For r=3, take two disjoint endpoint triples in the 35-facet polar. Wedge each of the 29 original facets absent from both endpoints. A wedge replaces row `a_i x<=1` by `a_i x+t_i<=1` and `-t_i<=0`, adding one dimension and one genuine facet. Complete minimal nonfaces transform by replacing the chosen label with its upper/lower pair. These pairs are nonempty-incidence twins; compressing them restores the base incidence pattern.

The result has dimension32 and64 genuine original facets. The endpoints choose opposite wedge sides and share NO original facet, so the smallest common face is the whole high-dimensional polytope. The certified schedule has29 prelude steps and9 cactus-tail steps, yielding102 refined vertices. The classical flag/carrier bound is therefore70 for every endpoint pair.

The actual computed flag route has36 original edges and36 refined steps. It performs270237 clique-membership queries, no refined maximal-facet enumeration and no full original-graph enumeration. All64 genuine-facet anchors and every route edge are checked against the final original rational inequalities, full active systems and maximal feasible ratios. This is not a shortest-path claim. Wedges of fixed low-dimensional bases can have stronger classical diameter bounds, so the numerical value70 is not marketed as a record; its role is an actual full-carrier certificate through multiple residual cycles.

## 10. Execution, adverse results, and exact remaining gap

The abstract suite checks all114 labelled four-vertex antichains (109 in the cactus class),1504 literal face identities and163 pure-carrier adjacencies. It then constructs160 seeded cacti with bridges, cycles joined at labels AND high nodes, varying high-node degrees and missing-pair blockers. Their5877 subdivisions include468 neutral openings. A spanning-forest fundamental-cycle checker independently agrees with the production Tarjan analysis on5991 graph states. Twenty-four bouquet families reach16 cycles, including shared high nodes. Thirteen malformed/unsupported controls fail. Theta incidence and the actual C(7,4) boundary are rejected, not assigned a false diameter conclusion.

The three exact polytopal models supply120 sampled endpoint pairs and606 original edges from620 refined edges. Thirty-seven are nonshortest against the separately reconstructed complete original graphs. This is not a shortest-route algorithm or benchmark winner. The exact prior #262 strict-budget baseline is run and reported separately. The32D case adds36 original edges. Four saved certificates replay with selectors, family construction and route production disabled;53 original edges are checked and two forged saved records fail. Saved replay does not recompute BFS distances.

A clean directory reproduces all three full test reports, the saved-audit report and all four complete fixture files byte-for-byte. Frozen dependency hashes and new source identities are in the manifest. The production code imports #262 unchanged. The flag-path reference is an attributed unchanged excerpt of #258, not a newly authored routing algorithm. Exact Python and JSON parsing are not Lean-extracted or formally verified.

The theorem uses a complete minimal-nonface list. Discovering that list from arbitrary original H inequalities can be exponential. No generic efficient-recognition claim follows merely because cactus incidence implies a small list once its completeness is known.

The remaining unrestricted obstruction is now a NON-CYCLE BICONNECTED incidence block: overlapping cycles can share paths, so an opening may copy into several interacting cycles instead of replacing one peripheral long cycle by a four-cycle. Neither cactus reduction, a small number of such blocks, nor cheap treatment of them is established for arbitrary carriers. This paper does not relabel those missing assertions as a solution of Polynomial Hirsch.

Reproduce with `python3 scripts/test_cactus_defect_refinement.py --stage abstract|geometry|wedge --out FILE --fixtures DIR`, then `python3 scripts/audit_cactus_refinement.py DIR --out FILE`. No Actions or publication gate is needed for this research-only contribution.

Primary references: https://arxiv.org/html/1303.3598v3 ; https://arxiv.org/abs/1302.5197 . Repository predecessors are named in Section0 with exact frozen provenance. The withdrawn arXiv1303.5885 is not used.
