# Common-face row-excess publication retry

The first fresh publication run failed closed before authentication because the standalone compiler had not built the imported local common-face definition module. The owner-only base workflow now builds `Definitions.Def_Hirsch_common_face_geometry` before compiling the unchanged frozen standalone proof. No proof bytes or theorem statement changed.

The second run was canceled during cache restore by an unrelated pull-request event sharing the same workflow concurrency group, again before any authentication. The gate is now scoped by `github.head_ref` so unrelated PRs cannot cancel this exact publication branch. Proof bytes remain unchanged.
