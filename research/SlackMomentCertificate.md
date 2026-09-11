# Exact slack-to-moment certificate

This formalization continues the published normalized two-moment diameter-two theorem and the affine-embedding graph transport in PR90/91. It deliberately does not redo the normalized vertex classification or generalize the mathematical research frontier.

## The new formal contract

Let P={x in R^d : <a_i,x> <= b_i}, with n=d+2 rows. Supply a reference extreme vertex z, positive scalars c_i, and nonconstant scalars t_i such that

- sum_i c_i a_i = 0;
- sum_i t_i c_i a_i = 0;
- sum_i c_i b_i = 1.

The theorem `HirschSlackMoment.hpoly_and_row_faces_diamLE_two_of_normal_relations` concludes `DiamLE P 2`, and intrinsic `DiamLE ... 2` for every row-support subset obtained by setting any selection of original inequalities to equality. There is no assumed graph-diameter bound, assumed routing theorem, or Open theorem import.

## What the proof actually establishes

Define Lx=(c_i<a_i,x>)_i, v=(c_i b_i)_i, C(s)=(sum_i s_i,sum_i t_i s_i), and f(x)=v-Lx. The reference vertex proves that the original tight rows span, so L and f are injective. The two vector identities imply CL=0.

Nonconstancy of t gives an explicit right inverse for C on two selected coordinates. Hence C has rank two. Since L has rank d=n-2, inclusion range(L) <= ker(C) is equality. This is the crucial surjectivity fact: it prevents a one-sided embedding into an easy polytope from being mistaken for an equivalent graph model.

Writing mu=sum_i t_i c_i b_i, the proof obtains

    f '' P = {s : s_i>=0, sum s_i=1, sum t_i s_i=mu}.

Positivity of each c_i reflects feasibility in both directions. Zero slack reflects original row tightness in both directions. Thus selected row-support sets map EXACTLY to coordinate support faces. The already checked injective-affine transport carries the existing normalized diameter bound back, including intrinsic face edges rather than only ambient adjacency.

`PolynomialSlackMomentCertificate.lean` provides the linear rank/image/face lemmas and the certificate using explicit maps. `PolynomialSlackNormalRelations.lean` discharges those map hypotheses using the finite vector identities and reference vertex.

## A nonvacuous exact example

For the square 0<=x,y<=1, order the normals as (-e_x,e_x,-e_y,e_y), take b=(0,1,0,1), c=(1/2,1/2,1/2,1/2), t=(0,0,1,1), and reference vertex (0,0). Both vector sums vanish and sum c_i b_i=1. The resulting mu is 1/2. This is a symbolic witness, not a claim that an extra numerical or Lean example was executed.

## Explicit limitations

This module does NOT yet derive existence of these relation witnesses from boundedness and strict feasibility alone. In particular, the general positive dependence and selection of a second independent relation remain separate normalization work. It also does not assert that arbitrary common circuit carriers have row excess two.

The main d>=4 edge-refinement theorem is not changed, and no new conjectural children are introduced. These are certificate theorems for a structured class, not a global Polynomial Hirsch result.

## Verification record

Candidate source first committed at `0e100f964e5dc66de9c7580910215ef460375164`; final verification request at `404b1922cfdee2681606138afdb352c8c9396835`. The final gate checks all fourteen printed results with only propext, Classical.choice, and Quot.sound allowed. Its completed log, not this document, determines whether the new source is kernel-verified.

The local terminal failed with TransportTimeoutError even for trivial commands after the already-exported public toolchain was downloaded. No local compilation is claimed. The PR uses a frozen verified affine-transport baseline to avoid conflicting with another agent's live publication branch. A single final targeted hosted verification request is used; the temporary workflow has no push or synchronize trigger and uses no Prove2Me credentials. No source here is claimed published until an authenticated ACCEPTED/Proved receipt exists.
