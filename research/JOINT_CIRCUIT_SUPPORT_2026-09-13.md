# External joint-circuit support and zero-deficit rigidity

## 1. Scope and verification

The standalone 197-line proof in `publication_packets/joint_circuit_support_deficits/solution.lean` is the previously local candidate, unchanged. The first prepared comment gate, run34791096717 at e78b966247f66bbe3906851395a1fd63bfb243b0, compiled the driver, solution and exact target statement with exit codes zero. All four printed declarations use only propext, Classical.choice and Quot.sound. Read the packet's publication receipt for the separate authenticated platform verdict; compilation alone is not acceptance.

The sign argument formalizes section4 of the retained `FINITE_SUMMAND_PACKING_2026-09-13.md` at historical #210 head11172b1165b31a81e8755bd9f88651a2a9ed4b8c. The zero-deficit interface is its exact finite support consequence. No historical novelty or uniform ordinary-edge bound is claimed. No #210 source is changed.

## 2. Exact block support from external minimality

Write lambda_i for original-row multipliers, mu_lj for the nonnegativity rows, and nu_l for each block's total-allocation row. All multipliers are nonnegative and satisfy

    -sum_i lambda_i*a(i,l,j) - mu_lj + nu_l = 0.

Externality means some original lambda_i is nonzero. Minimality is among ALL nonzero nonnegative null multipliers of these same equations, not merely negative certificates or an incomplete sample. Define f_l(j)=sum_i lambda_i*a(i,l,j).

The internal vector e_l is one on nu_l and every mu_lj and zero elsewhere. It is nonzero, nonnegative and null. If every auxiliary coordinate of block l in w were nonzero, support(e_l) would lie in support(w). Minimality would force support(w) inside support(e_l), contradicting externality. Therefore nu_l=0 or some mu_lj=0. Nullness gives nu_l>=f_l(j), nonnegativity gives nu_l>=0, and the zero auxiliary coordinate gives attainment. Thus

    nu_l = max(0, max_j f_l(j)).

The anchor remains present even for an empty generator list. No rank, independence, normalization, boundedness or feasibility hypothesis is needed.

## 3. Nonnegative deficits and exact zero pattern

Let nonnegative h_i dominate all a(i,l,j) for this block and put Gamma_l=sum_i lambda_i*h_i-nu_l. At an attaining listed point q, including the anchor, this is

    Gamma_l = sum_i lambda_i*(h_i-a_i(q)).

Every summand is nonnegative. Hence Gamma_l>=0. Equality forces every gap with lambda_i>0 to vanish. Conversely, if one q attains every positively weighted row bound, sum_i lambda_i*h_i=f_l(q)<=nu_l; combine this with Gamma_l>=0. Therefore

    Gamma_l=0 iff one listed q attains every h_i with lambda_i>0.

For exact candidate supports, intersect the maximizing-point bitsets over the positive support of lambda. A nonempty intersection is equivalent to Gamma_l=0. This determines the coefficient's zero pattern without optimizing over the ORIGINAL polytope. It does not compute the scalar right-hand-side support optimum. For conservative bounds, the criterion concerns attainment of those declared bounds, not an alternative support value.

## 4. Internal rows and necessity of minimality

If lambda=0, the pointwise budget is sum_l nu_l*t_l>=0 for nonnegative scales. This is the separately audited `Hirsch.joint_internal_budget_nonnegative`. Such rows are automatic even though their deficits -nu_l need not be nonnegative.

For a=1 with coordinates (lambda,nu,mu), the external circuit (1,1,0) and internal circuit (0,1,1) are null. Their sum (1,2,1) is external and nonnegative but nonminimal. At h=1 its deficit is -1. A two-block negative control has Gamma=(-1,1): its individual zero-RHS inequality accepts (1,1) but rejects the smaller (0,1). This does not contradict downward closure of the COMPLETE extraction region; the tightened valid row already excludes (1,1).

For arbitrary nonnegative null w, set nu'_l=max(0,max_j f_l(j)), mu'_lj=nu'_l-f_l(j), and d_l=nu_l-nu'_l>=0. Keep lambda unchanged. Then w=w'+sum_l d_l*e_l, w' is nonnegative/null with contained support, and

    Budget(w,t)=Budget(w',t)+sum_l d_l*t_l.

This is implemented and checked by `tighten` in the companion script. The universal tightening theorem is a written argument, not an extra Lean theorem in the accepted packet. Tightening does not assert minimality of w'.

## 5. Integration and remaining work

#218 retains actual support-minimality. #229's checked catalogue characterizes real normalized circuits, and #233 proves that its ACTUAL output tests the whole nonnegative kernel. Use those invariants after exact coordinate/null-equation transport. #219's weaker public nonnegative-null invariant alone does not imply minimality. #234 supplies the independent covering-budget alternative; do not duplicate it.

After discarding automatic internal/zero rows, the derived coefficient signs fit `HirschJointExtraction.scaleRegion_downward`. Full composition with the actual checked catalogue and whole-set allocation, original-H support-optimum witnesses, useful candidate selection and arbitrary-carrier ordinary-edge routing remain distinct. No polynomial bound on how many restrictive circuits remain is established.

## 6. Reproduction

    python3 scripts/check_joint_circuit_support.py --out /tmp/joint-circuit-check.json

The committed script is the exact tested source, SHA-256 0ab192816af732c9f3fa36a944f6f722b17803e3c1bfa13223eb1c3ee04ea5e7. The rerun covers59 systems,3509 support candidates,267 circuits,267 independent nonzero-minor rank certificates,278 block-support checks,556 zero-deficit checks,549 downward checks,354 tightening cases and11 rejected controls. Sixty determinant tests compare Bareiss with independent Leibniz expansion. These finite software tests are supporting evidence, not Lean extraction or proof of the Python enumerator's universal correctness.
