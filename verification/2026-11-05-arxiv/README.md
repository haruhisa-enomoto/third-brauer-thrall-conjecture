# Verification record, November 5, 2026: the published paper

Commit `57dc7122ead283a759e208fcc007da8f44cf0a05`. Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, Lean module system.

This commit follows the paper as published, [arXiv:2611.06325v1](https://arxiv.org/abs/2611.06325v1)
(the same source as [hexagon:2610.00179v2](https://hexagonmath.org/2610.00179v2); see
[docs/MANUSCRIPT.md](../../docs/MANUSCRIPT.md)). Compared with the
[record of November 3](../2026-11-03-direct-route/README.md), it adds the statements
`CorollaryCount` and `CorollaryCountBounded` (the full Corollary 1.1, with `2^κ` modules and
`n ≤ max(30, 4 dim A)`) and the Göbel–Simson rigid families, and its numbering follows the
published paper.

## Local checks

| Check | Result |
| --- | --- |
| Lean source check | `scripts/check-lean-sources.py` passes |
| Statement sync | `scripts/generate_challenge.py --check` passes |
| Build | `lake build LargeIndecomposable Challenge Solution`: 10,161 jobs; the only `sorry`s are the five Challenge placeholders |
| Axiom audit | `scripts/audit_axioms.py`: 22 declarations, only `propext`, `Classical.choice`, `Quot.sound` |
| Declaration scan | `scripts/scan_axioms.py`: all 61,690 declarations of the library and Solution; no other axiom |
| `lake comparator` | `scripts/verify-comparator.sh` in a `bwrap` sandbox: con-ron (94,978 declarations), NanoDa and the Lean kernel accept; [`comparator-tail.log`](comparator-tail.log) |

## Hosted Palomar preflight

[Workflow run 41975584292](https://github.com/haruhisa-enomoto/third-brauer-thrall-conjecture/actions/runs/41975584292)
ran Palomar's mechanical verification on this commit, pipeline commit
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, profile `palomar-standard-v1`
(GitHub-hosted runner, 4 CPUs, 16 GB). The full report is
[`mechanical-report.json`](mechanical-report.json).

| Check | Result |
| --- | --- |
| Status | `pass`, stage `complete`, no errors or warnings |
| Source requirements | 1,201 Lean files |
| Challenge | 298 lines, trust level `high` |
| Build of the solution | 68 minutes, largest memory use 12.8 GB |
| `lake comparator` | accepted, 14 minutes |
| Independent kernels | NanoDa accepted; con-ron accepted 94,978 declarations |
| Whole job | 1 h 38 min of the 5.5-hour budget |

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `16ce05f49d58ddefae3b2b14379d01ff2f70f21b738483c9291f9ff7a2926e22` |
| `Solution.lean` | `82fc9ec361926d6b1623be8e62863d3f01c4be696569213c9d539addb86f1138` |
| `comparator.json` | `3c94329e3d76a84ae66502c10c26ab7663f2c52f4294bee188fbfb4f6ce84912` |

A preflight is a third-party advisory report. It is not a registry submission or
acceptance, and it does not include Palomar's editorial review.
