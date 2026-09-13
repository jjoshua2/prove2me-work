# Accepted evidence — positive-circuit signed kernel and rank cutoff

Prove2Me accepted `Hirsch.positive_circuit_signed_kernel_and_rank`.

- Theorem ID: `864c87b2-cf47-469a-884a-4a6352e0ab23`
- Submission ID: `f60b3d5d-7617-4b01-a11d-121b24d9ff42`
- Final Actions run: `34783103887`
- Frozen proof head: `c3eff585fd047892f28a5287752ab015767ab29b`
- Authenticated publisher result: `ACCEPTED`, live status `Proved`
- Registration mode on the safe resume: `REUSED`; the timed-out earlier problem registration was not duplicated.
- Solution SHA-256: `5360f2a04a68b580552470ba42d1fa011eec5a73275c1c9b7766475fea028ddc`
- Statement SHA-256: `344e4bbd9fdbc436aa75fa8bd6c65bd4634a1d42e3abc13d89584282e430483b`
- Driver / solution / statement compile exit codes: all `0`
- Axiom audit: only `Classical.choice`, `Quot.sound`, and `propext`
- Verified packet artifact: `10325579396`, archive digest `sha256:485c3b4c47c4a1121bbe7eba88062630c7c9c743f5a877c0da7a8fa9ff494809`
- Publication-receipt artifact: `10325721762`, archive digest `sha256:29acb077f7bb6bf94152b7bd6f0f37c1a1a47934ae42c29f10ce0c7f6bf39d78`

The trusted publisher compares the accepted solution readback byte-for-byte with the frozen packet before returning `ACCEPTED`; the successful receipt therefore certifies the exact frozen solution above. The result proves both the signed-kernel characterization of a support-minimal nonnegative null vector and the sharp `|support| <= finrank(range A)+1` bound. It does not itself certify the executable rational enumerator or prove Polynomial Hirsch.
