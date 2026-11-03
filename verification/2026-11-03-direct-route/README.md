# Verification record, November 3, 2026: the direct route

Commit `8a86293f30600825a7dee608fe37e41a67dc2b68`. Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, Lean module system.

This commit makes the library follow the revised manuscript
([docs/MANUSCRIPT.md](../../docs/MANUSCRIPT.md)): Bongartz's three functors are defined on
Kronecker modules of any dimension, their retractions are built directly on `C`, and
Theorem 5.2 is proved for these functors; the extension criterion of version 1 is removed. The
theorem statements are unchanged; `Challenge.lean` and `Solution.lean` changed only in comments.

## Local checks

| Check | Result |
| --- | --- |
| Lean source check | `scripts/check-lean-sources.py` passes |
| Statement sync | `scripts/generate_challenge.py --check` passes |
| Build | `lake build LargeIndecomposable Challenge Solution`: 10,140 jobs; the only `sorry`s are the three Challenge placeholders |
| Axiom audit | `scripts/audit_axioms.py`: 17 declarations, only `propext`, `Classical.choice`, `Quot.sound` |
| Declaration scan | `scripts/scan_axioms.py`: all 60,753 declarations of the library and Solution; no other axiom |
| `lake comparator` | `scripts/verify-comparator.sh` in a `bwrap` sandbox: con-ron (94,007 declarations), NanoDa and the Lean kernel accept; [`comparator-tail.log`](comparator-tail.log) |

## Hosted Palomar preflight

[Workflow run 41619595583](https://github.com/haruhisa-enomoto/third-brauer-thrall-conjecture/actions/runs/41619595583)
ran Palomar's mechanical verification on this commit, pipeline commit
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, profile `palomar-standard-v1`
(GitHub-hosted runner, 4 CPUs, 16 GB). The full report is
[`mechanical-report.json`](mechanical-report.json).

| Check | Result |
| --- | --- |
| Status | `pass`, stage `complete`, no errors or warnings |
| Source requirements | 1,180 Lean files |
| Challenge | 239 lines, trust level `high` |
| Build of the solution | 66 minutes, largest memory use 10.7 GiB |
| `lake comparator` | accepted, 15 minutes |
| Independent kernels | NanoDa accepted; con-ron accepted 94,007 declarations |
| Whole job | 1 h 38 min of the 5.5-hour budget |

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `4dc39ffdb2703b789c2f94d6b2833737987379747d374d3569003e8223ddd689` |
| `Solution.lean` | `f3b55c6ca9ea1fe6429679db22960c61d89175da36e45a25742fadb2f35fe46f` |
| `comparator.json` | `e713cbdb7aedd1bad2d5a215b234857d649294ef1ebd50efacdc5d0a68e39b3a` |

A preflight is a third-party advisory report. It is not a registry submission or
acceptance, and it does not include Palomar's editorial review.
