# Standalone proof reductions for Cores 12, 28, 36 and 40

Cores 12, 36 and 40 each contain the **entire scored source**: one `Solution.lean`, importing only the frozen interface. Core 28 is distributed as a small delta on the pinned public winning tree, rather than a second copy of 147 files. These are local results, not hosted scores. The standalone challenge files are staged here for review, not imported into `src/`.

| Core | This proof: tokens | Verified leaderboard entry | Strongest prior public source located |
|---|---:|---:|---:|
| [12: Cyclotomic power-series rigidity](core12/Solution.lean) | 1,063 | [1,236](https://riemann.verifytask.cn/api/attempt/101654) | Same public entry |
| [28: Fundamental-domain point bound](core28/README.md) | 257,305 | [260,150](https://riemann.verifytask.cn/api/attempt/103706) | Same pinned public package |
| [36: Pure-family decomposition](core36/Solution.lean) | 248 | [306](https://riemann.verifytask.cn/api/attempt/105760) | [254](https://github.com/vlarin/riemann-hypothesis/blob/a77fbba030230e2c8a7edb1429ccbafcf47f7b17/community/fortytwo-phase3-4331/core36/Solution.lean) |
| [40: Residual-spectrum constant terms](core40/Solution.lean) | 431 | [539](https://riemann.verifytask.cn/api/attempt/104025) | [505](https://github.com/vlarin/riemann-hypothesis/blob/a77fbba030230e2c8a7edb1429ccbafcf47f7b17/community/fortytwo-phase3-4331/core40/Solution.lean) |

- **12:** One Weierstrass division and induction serve both the single-branch and split completeness statements. The proof builds on the published work of Andrew Pullin (#101654), dugbt607 (#100599), LewyM (#99275), and Levent Alpöge.
- **28:** Reusing the existing positivity lemma removes four otherwise necessary source files from the dependency closure, without changing the target. [Patch and reconstruction instructions](core28/README.md).
- **36:** Use the standard submodule closure under natural multiples across the three conclusions. The signed-root and decomposition argument is due to Vincent Liu, Mikko Nyman and Vladyslav Larin / Fortytwo.
- **40:** One torus identity replaces separate comparisons of the positive idèle, diagonal matrices, split centre and lattice. The last two now follow by definition. This builds on Vladyslav Larin / Fortytwo and Mikko Nyman et al. Prior code and contributor credits are in [PR #19](https://github.com/Osgood001/riemann-hypothesis/pull/19).

**Verification.** Comparisons were checked on 2026-11-25 UTC. Token totals above use this repository’s `scripts/pr_lightweight_checks.py` counter. Each candidate passed local Lean elaboration, exact statement comparison with the published Challenge theorem, a standard-axiom audit (`propext`, `Quot.sound`, `Classical.choice`), and replay in con-ron. The comparisons were run locally without a sandbox, not on a hosted worker. The checker used Lean 4.34.1 for Core 12 and 4.33.1 for Cores 28, 36 and 40. Core 12’s frozen statement module was reconstructed from the upstream source with two binder-syntax adaptations; its hash is not attested by the host. As a cross-check, on the original 4.33.1 interface the complete proof also passed both checkers with one extra explicit argument placeholder (1,064 tokens). Cores 36 and 40 use the original pinned frozen imports at [40e56ba](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005).

To check a proof in its matching challenge environment, copy its file to `Solution.lean` and run `lake env lean Solution.lean`. The three single-file proofs are independent modules; do not combine them into one challenge submission. No change to the maintained proof or its toolchain is implied by this staging.
