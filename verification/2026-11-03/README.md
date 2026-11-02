# Verification record, November 3, 2026

Commit `84a74f0fe1001cdacb936eae9b9a541870f97b06`. Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, Lean module system.

This commit reorganizes the library: unused declarations are removed, names describe
content, the category of finite-dimensional modules is built on `ModuleCat`, and right
modules are modules over the opposite algebra. The theorem statements, `Challenge.lean`,
`Solution.lean` and `comparator.json` are unchanged from the
[first release](../2026-11-01/README.md).

## Local checks

| Check | Result |
| --- | --- |
| Lean source check | `scripts/check-lean-sources.py` passes |
| Statement sync | `scripts/generate_challenge.py --check` passes |
| Build | `lake build LargeIndecomposable Challenge Solution`: 10,139 jobs; the only `sorry`s are the three Challenge placeholders |
| Axiom audit | [`axioms.log`](axioms.log), [`axioms.json`](axioms.json): 16 declarations, only `propext`, `Classical.choice`, `Quot.sound` |
| Declaration scan | [`scan.log`](scan.log): all 60,758 declarations of the library and Solution, internal ones included; no other axiom |
| `lake comparator` | `scripts/verify-comparator.sh` in a `bwrap` sandbox: statement match, axiom boundary, con-ron (93,938 declarations), NanoDa and the Lean kernel accept; [`comparator-tail.log`](comparator-tail.log) |

## Hosted Palomar preflight

[Workflow run 41455964395](https://github.com/haruhisa-enomoto/third-brauer-thrall-conjecture/actions/runs/41455964395)
ran Palomar's mechanical verification on this commit, pipeline commit
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, profile `palomar-standard-v1`
(GitHub-hosted runner, 4 CPUs, 16 GB). The full report is
[`mechanical-report.json`](mechanical-report.json).

| Check | Result |
| --- | --- |
| Status | `pass`, stage `complete`, no errors or warnings |
| Source requirements | 1,179 Lean files |
| Challenge | 237 lines, trust level `high` |
| Build of the solution | 55 minutes, largest memory use 11.4 GiB |
| `lake comparator` | accepted, 15 minutes |
| Independent kernels | NanoDa accepted; con-ron accepted 93,938 declarations |
| Whole job | 1 h 25 min of the 5.5-hour budget |

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `724497633a957cf76bcfed0480de3aafbdd900392712407c58ab2e7d6ecec5ba` |
| `Solution.lean` | `01a4ef593f541bc407e10600208c8dd364cea36444874bb4f0ba89ae7c507a6d` |
| `comparator.json` | `e713cbdb7aedd1bad2d5a215b234857d649294ef1ebd50efacdc5d0a68e39b3a` |

A preflight is a third-party advisory report. It is not a registry submission or
acceptance, and it does not include Palomar's editorial review. The local bubblewrap
binary was the Ubuntu 22.04 package 0.6.1.
