# Accepted image-edge selection: next work must address length, not reprove steps

Read the accepted normalized_tangent_image_edge packet and its raw receipt.
PR248 follows accepted #246/#247. It does not duplicate #244's independently
owned Minkowski core-walk concatenation or #238's support-witness task.

## What to reuse

The accepted proof has five audited declarations:
- feasible_tangent_step: finite strict slack realizes any active-cone vector;
- exact_image_tangent: the image active cone equals scaled actual displacements;
- height_positive_modulo_image_kernel: finite row identities normalize image rays;
- normalized_slice_support_ray: unique normalized support gives an exposed ray;
- solution: maximal length over all lifts turns that ray into an original edge.

The 285-line source imports Mathlib only and passed its first gate unchanged.
Do not rewrite or republish it to remove harmless linter warnings. Exact proof
head7d3c7cfcbbb4a3b7d4eda9aa728330592faf1770, source SHA256
`a1bf73c13e7fd2df2d852e183086a6d20a86c60591236ce6e5bd40ea0704c7dc`.
The normalized-slice support and attained all-lift ray maximum are mathematical
witness hypotheses, not an assumed original edge. The entire witness-production
process is executable but not yet an end-to-end Lean-extracted algorithm.

## Reproduce actual edge selection and independent tests

```
mkdir -p fixtures
python3 -m py_compile scripts/image_tangent_pivot.py scripts/test_image_tangent_pivot.py
python3 scripts/test_image_tangent_pivot.py
python3 scripts/image_tangent_pivot.py input.json --output route.json
```

The input is A,b,G,u,v, with distinct image endpoint vertices (stationary u=v is
also checked). CLI --certificate consumes the INNER certificate object. Optional
--edge-cap bounds search work; hitting it is an incomplete run, not a geometric
negative or a claimed short route. Exact LP pivot caps are separate.

The target's singleton exposed image face supplies a strict target objective.
Each iteration constructs the current fibre's exact active rows and positive
height, solves the height-one tangent slice, maximizes target progress, and
lexicographically optimizes IMAGE coordinates. The resulting image ray receives
its own singleton-face certificate. Its endpoint is optimized over ALL lifts.
Each step is strictly improving, so finite image vertex count gives termination
when the exact routines finish. That argument supplies no polynomial bound.

The normalized tangent image is contained in conv{-W_i/lambda_i}. This establishes
boundedness, not equality with that hull: its actual vertices can be more numerous
than the listed containing-hull points. Do NOT infer an m-ray or m-step bound.
Image linear dependence and source lineality are handled by finite column identities.

## Mandatory counterexamples and count distinctions

An optimal slice point can be a diagonal: for the square cone and h=c=x+y,
(1/2,1/2) is optimal but not an extreme ray. The lex/image-singleton check is
necessary. A source ray can also hit a blocker before the image edge ends:
[0,1]^2 mapped by z1+z2 reaches2 by changing lifts, although a source ray
increasing z1 alone stops at1. Free source coordinates can eliminate ALL source
vertices. Neither scenario prevents the current image selector from succeeding.

Keep the independent hull and disabled-discovery auditor tests. Executed totals:
297 routes/428 image edges; nine small hulls49 vertices/62 edges/291 ordered
distances;1012 checks against all incident normalized edge slopes;32 source
edges that project to nonedges;two nonshortest pentagon routes. Six additional
cases give20 edges,12 premature fixed-source blockers and18 nonedge source-lift
steps. Twenty malformed/capped cases are rejected. These are software tests,
not separately kernel-evaluated instances or a shortest-path theorem.

IMAGE_TANGENT_EXECUTION.json is a labeled compact summary. The script regenerates
the complete stage receipts and seven full fixtures; their clean replay is
byte-identical. New producer SHA256
`4efb3d2d7ea4fe496d0caedbb8c4e88e13f43338cbbcb596db086dafcd171b0e`;
new test SHA256 `8b9fcc0b12312e8e46bb51f10b174b28e18fa48d19436ece8d693fce67ad8246`.
The exact_farkas_lp.py dependency remains byte-identical and is not reintroduced.

## Conjecture-level next target

The accepted geometric implication plus finite producer now CHOOSE actual
improving original-image edges, rather than require neighboring endpoints.
The next task is a valid progress potential/amortized bound for such selected
edges, or a demonstrably better selection rule. Count original IMAGE facets,
not extension inequalities. Ratios may depend on coefficients and geometry;
strict improvement alone cannot be called polynomial progress. Stress-test
normalization changes, degeneracy, multiple lifts and long monotone paths.

The small negative shortestness cases show this local rule is not automatically
a shortest-path algorithm. A universal polynomial bound on selected edges is
not established, and no arbitrary-carrier decomposition premise is smuggled in.
Do not publish a child that assumes the very short-route conclusion being sought.
