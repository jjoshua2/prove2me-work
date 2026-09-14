# Reproduce the simultaneous-lift route fixture

Run from the repository root:

    python3 scripts/test_simultaneous_minkowski_lift.py --stage large --out /tmp/lift-large.json
    python3 scripts/simultaneous_minkowski_lift.py --verify research/fixtures/simultaneous_lift_32d.json

The first command regenerates the full 32D rational route. The second reads its serialized bytes and rechecks all supporting faces, affine samples, endpoint exposures and counts without invoking route construction or event enumeration. The full JSON is included in the conversation download; it is regenerated rather than committed as a large opaque fixture. Exact hashes are in research/SIMULTANEOUS_LIFT_CHECK.json.

This is a supplied pyramid-plus-triangles presentation, not a newly discovered equality for unrelated original inequalities. The 2^31+1 count is for the CORE, not the final sum; 50 is an actual verified route length, not a shortest-path claim. Python/JSON checking is not Lean extraction.
