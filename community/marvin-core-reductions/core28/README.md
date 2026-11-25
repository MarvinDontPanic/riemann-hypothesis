# Core 28: use the existing CM-place positivity lemma

The near-supremum argument needs only `0 < X.c τ`. The proof already imports the same fact via the majorant construction; it need not depend on the complex fractional-slice machinery for a second proof. Replace the single import and its one use as in [`changes.patch`](changes.patch).

**Source.** The formalization is by Levent Alpöge. The starting solution is Vladyslav Larin / Fortytwo and Codex's [Core 28 source package](https://github.com/vlarin/riemann-hypothesis/tree/a2e6aedc32d7247c71c5fc3c71645addf1f94bbc/community/fortytwo-phase3-4331/core28) corresponding to [Bohrium #103706](https://riemann.verifytask.cn/api/attempt/103706). This patch contributes the import and positivity-lemma substitution only. The frozen target and `Solution.lean` are unchanged.

**One-command reconstruction.** Given the original source checkout and the pinned Fortytwo package linked above, run this from this directory. No Python packages are required; the script uses the native `patch` utility, checks the inputs, and writes the verified proof closure to a new directory.

```sh
python3 materialize.py /path/to/alpoge-original/src /path/to/fortytwo/community/fortytwo-phase3-4331/core28 /path/to/new-proof
```

**Reconstruct.** For each of the 150 paths listed in `verification.json` → `pinned_source_files` in the linked starting package, copy the file below `src/` from [the original tree at 40e56bab](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005/src) to the same relative path in `proof/`. Their SHA-256 values must match the manifest. In `proof/`, apply the starting package's `changes.patch` with `git apply` and copy its `Solution.lean`. Each modified winner file's SHA-256 then matches `modified_files[path].after` in the linked manifest. This is the 151-file, 260,150-token starting tree. Apply [`changes.patch`](changes.patch) in `proof/`. The changed `FdFjNearSupOf.lean` goes from SHA-256 `e61505d60c9f248d473783d26915b9a1b70d4fe3cece5b5d7ee5320cbef01726` to `c9a0723be4be697462b68b94582fbff811f9c28075cbb21165f36bea015407bb`. Retain only the reachable proof sources starting from `Solution.lean`; this omits precisely:

- `ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/GROWCountStatement.lean` (56 tokens)
- `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMeanContinuity.lean` (219)
- `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FractionalSliceDomains.lean` (2,475)
- `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MinimumGrowthBounds.lean` (95)

The unchanged `Solution.lean` has SHA-256 `03aa0b52f127901667031bcbd1560a5d4d51f6bf5b0a91d1ece403c6fc05cb16`. The remaining 147 `.lean` files total 257,305 normalized tokens; the four omitted files account for all 2,845 saved tokens. The local tree digest is `9167bd7fc14c254ccfb1302333fb1285cabdbf65205d5af09a2c0bccb63d53a7` (SHA-256 over lexicographically sorted lines `relative_posix_path SPACE lowercase_file_sha256 LF`, each path relative to `proof/`). This delta applies to the standalone challenge slice, not to the whole RH repository: do not delete the four files from the full library.

The isolated Lean 4.33.1 build, the exact public challenge-statement comparison, and the independent con-ron replay (73,362 declarations) passed locally. No hosted score is claimed.
