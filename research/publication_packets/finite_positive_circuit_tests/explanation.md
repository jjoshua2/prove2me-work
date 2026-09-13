# Finite positive-circuit completeness

Let K={x in R^n: x>=0 and A x=0}. A positive circuit here means a nonzero element of K whose support is minimal among supports of nonzero elements of K. The theorem supplies one fixed representative for each support that occurs, and zero in all other slots. The choice is independent of the tested linear functional.

## The direct proof

First suppose x>=0, y is supported inside x, and y has a positive coordinate. Among the coordinates where y_i>0, take the minimum ratio t=x_i/y_i. Every such x_i is positive, so t>0. Then z=x-t*y is nonnegative, has no new nonzero coordinate, and vanishes at a minimizing coordinate. Thus its support is a strict subset of the support of x. Negative coordinates of y cause no difficulty: they only increase the corresponding entries of z.

Given w in K with b(w)<0, choose a negative member x of K supported inside w having least support cardinality. Consider ANY nonzero y in K supported inside x. If b(y)<0, minimal cardinality and support inclusion force equality of supports. Otherwise b(y)>=0. The preceding minimum-ratio subtraction yields z in K with strictly smaller support and b(z)=b(x)-t*b(y)<0, contradicting minimality. Therefore x is a positive circuit; minimality is against all nonnegative null vectors, not merely the negative ones. Strict negativity is retained.

Next let x be a circuit and let y be any nonzero member of K supported inside x. The same subtraction gives z in K with strictly smaller support. Circuit minimality forces z=0, so x=t*y with t>0. Consequently there is only one nonnegative null ray for a circuit support.

Choose one representative c_s on each occurring circuit support s, independently of b. The forward implication is immediate because each representative lies in K (or is zero). For the converse, if a linear functional is nonnegative on all the chosen representatives but negative at w in K, the negative-circuit lemma gives a negative circuit x. Its representative c_s has the same support, hence x=t*c_s with t>0. Linearity contradicts nonnegativity of b(c_s).

## Quantifiers and scope

The finite family is chosen BEFORE the universal quantification over b. It is not a different witness list for every right-hand side. It has at most one nonzero representative per subset of Fin n, with at most 2^n slots. Empty index types, zero maps, zero rows, and degenerate kernels are included. No boundedness, strict feasibility, simplicity, or full-rank premise is added.

This is the algebraic finite-dual-test ingredient for the allocation systems in the Hirsch extraction work. It neither reproves nor resubmits accepted compact-dual Minkowski theorem a6e2a38d-00e3-46d6-b232-7cddee5e30e1. The latter's tests involve support over a compact convex set, whereas this theorem concerns linear tests on a nonnegative kernel. An explicit allocation/alternative or support-region adapter is still needed to connect the two formal statements. The sharper rank(A)+1 support bound and the correctness of the implemented positive-circuit enumerator are also not asserted by this packet. No ordinary-edge diameter bound or dependency connection to the open Hirsch root is manufactured.

## Verification boundary

The source contains a complete direct Lean candidate with a top-level theorem solution. The problem preamble contains imports/opens only; all helper declarations occur only in the proof source. Its final type uses Mathlib symbols only. No target-theorem placeholder is imported and no new axiom is declared. At preparation time this environment had no lean/lake installation and could not resolve github.com to install the committed environment. Source review and packet consistency checks are not Lean verification. Only the explicit hosted gate and authenticated publication receipts may upgrade these statuses.
