# PR #301: all-endpoint monotone route candidate; final assembly not verified

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR heads/comments before continuing. This branch starts at main539e0b0bd255682ff1115cf9d3e1c54b6822db2a. Coordination on #298 is comment5732149225. #300 owns the separated-pair polynomial route; its source and queued run were not modified or triggered. Other owned work, #270's blocked companion and reserved #210 remain untouched.

## Actual gate and stopped publication

The NEW top-level PR conversation comment5732373666 began `/prove2me publish research/publication_packets/moment_monotone_allpairs`. Bot5732376984 resolved proofd06f6e65463a24a1d13434d4cf1e16136de67f42 and run35363756565. Trusted workflow main was539e0b0bd255682ff1115cf9d3e1c54b6822db2a. Gate succeeded; verify job105661161544 FAILED driver compilation; publish and report-verify were skipped. There is no verified-packet artifact, platform theorem/submission ID, authenticated ACCEPTED result or live Proved readback for this target. Exactly ONE gate was triggered.

The new improving_pivot, target_score_strict and finite_ascent declarations emitted standard-only axiom reports (propext, Classical.choice, Quot.sound). The final all_endpoint_route and solution emitted sorryAx because final assembly failed. Do not promote those three helper reports into a passed whole-packet audit or claim the public theorem accepted.

The compiler's primary error at line1134 is inability to infer the implicit dimension in `let f := rowSum a (active a v)`. The proposed correction supplies the local type `(Fin d -> R) ->L[R] R`. Its exact Lean syntax is in verification/moment-monotone/proposed-local-repair.patch. No mathematical statement, assumption or bound is changed. This correction is NOT Lean-tested and the compiler may expose later errors after it.

Two intermediate upload revisions (d740a10746aa408fd285e494362024bd26afd9af and23da6887da192faf1c8a880838182053d38e756b) introduced transcription mismatches outside that intended line. Both were caught by blob comparison BEFORE another gate. The final branch restores the entire original gated solution blob692a0caf76f2629636f6032a45095c830f8b734f, rather than keeping either mismatched upload. Their history is not presented as compiler-tested work. The correct one-line proposal is preserved separately, and the downloadable proposal source has SHA25677c3a33bebf5282580553e525c6e82686a7b6ead62cada666b969ef4df62b245. There was no second hosted run. Keep this PR draft.

## Mathematical argument completed in source

The candidate target is Hirsch.moment_all_endpoint_monotone_routes. For any d<m, injective real parameters and any actual moment-polytope vertices u,v, the intended conclusion is a complete original-edge route of length L<choose(m,d), strictly increasing the fixed sum of v's tight original rows and never losing an already acquired target row. Odd dimensions, d0, identical endpoints, unsorted labels and negative-mean/nonconsecutive vertices are retained. This binomial bound may be exponential and does not solve Polynomial Hirsch or improve known general diameter bounds.

At a source u, use accepted #298 to choose the normalized release direction w_p for each tight row p. The feasible target displacement is exactly v-u=sum_p c_p*w_p with c_p=1-A_p(v)>=0, by source active-evaluation injectivity. Any positive objective gap has a summand c_p*f(w_p)>0. The corresponding first-blocking original edge improves the objective, and c_p>0 excludes releasing a row already tight at v. This derives progress without an improving-edge oracle.

The sum of v's tight original rows uniquely maximizes at v, by accepted target active-evaluation injectivity. The complete accepted #299 root catalogue contains all actual vertices. Count catalogue vertices with strictly larger score; an improving move decreases this natural rank. Strong induction constructs the finite route. That rank is not proved polynomial, and non-target rows may be revisited. No shortestness or full nonrevisiting claim is made.

The accepted prefix through Hirsch.MomentRelease and the exact Hirsch.MomentRootCatalogue namespace are reused unchanged, with shared code deduplicated and old standalone public roots/print suffixes removed. Their live source blobs and authenticated receipts were read. The proposed public type has only Mathlib imports/open/options and explicit original row/P/target-score formulas. It does not assume a vertex catalogue, feasible directions, an improving step, route or termination bound.

## Independent exact tests

Eight complete small original-H graphs come from280 square systems and100 vertices.330 selected endpoint routes use627 edges versus593 shortest-path edges, with33 nonshortest outputs retained. No acquired target row was lost. Six selected routes in dimensions8,12,16 add21 original edges, including wrap-around negative-mean vertices; no full large graph is enumerated. Fifteen saved records/31 edge occurrences replay with route selection and inverse construction disabled. Six malformed controls fail.

The new script test_moment_monotone_routes.py has blob e04c34511b494b52a99888749011daa2aadc5b0a and SHA256d7e7de04592ac9845a6e499cd9c47644fc646eb95825eeae2157fa30f16fe662. It imports the two unchanged test helpers already on main. A clean three-script workspace reproduces all THREE reports and TWO complete fixtures BYTE-FOR-BYTE. The fixtures accompany the export and regenerate; hashes are committed. This is rational arithmetic testing, not Lean-extracted parser or solver verification.

    for s in small large audit; do
      python3 scripts/test_moment_monotone_routes.py --stage "$s" --out /tmp/moment-monotone
    done

The original request archive10554514822 was downloaded and hashed as3fd6c09081817b6f83baeb0e383e1d3a6a98913280baa266c160c28ba777a4fc. Its resolved.json is preserved unchanged. The diagnostic file is explicitly a selected excerpt, not the full runner log. Derived failure/replay records are not platform receipts.

## Next action and general boundary

Compile the proposed one-line annotation and the complete remaining source locally on the exact pinned environment when available; do not assume correcting the first elaboration error validates downstream assembly. Then recheck the live PR, comments and possible registration before a single prepared final gate. Do not publish a duplicate standalone copy of the three already compiled helpers merely to inflate progress.

Beyond closing this formal assembly, the conjecture still needs a polynomial route bound. Target-score increase plus a finite vertex inventory only gives the stated potentially exponential limit. Respect #300's stronger but restricted endpoint work before any composition. No root/leaf mission poll, new main merge, workflow, pin, protocol0.10.4, allowlist, duplicate guard or verify/publish secret-separation change occurred here. Root STATUS is unchanged; this handoff and the completion comment carry the actual result.
