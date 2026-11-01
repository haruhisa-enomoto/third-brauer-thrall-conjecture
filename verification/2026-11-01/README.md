# Verification record, November 1, 2026

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, Lean
module system. The checks ran on the Lean sources of the first commit of this
repository. Later commits change only records, documentation and scripts.

| Check | Result |
| --- | --- |
| Lean source check | `scripts/check-lean-sources.py`: all 1,359 Lean files use the module system, none exceeds 10,000 lines |
| Statement sync | `scripts/generate_challenge.py --check` passes |
| Fresh build | no project artifacts, Mathlib prebuilt at the pinned commit: 10,320 jobs including Challenge and Solution, 49 min 49 s on 20 hardware threads, largest process 6.1 GB; the only `sorry`s are the three Challenge placeholders |
| Axiom audit | [`axioms.log`](axioms.log), [`axioms.json`](axioms.json): 18 declarations, only `propext`, `Classical.choice`, `Quot.sound` |
| Declaration scan | [`scan.log`](scan.log): `scripts/scan_axioms.py` checks all 67,397 declarations of the library and Solution, internal ones included, and finds no other axiom |
| `lake comparator` | `scripts/verify-comparator.sh` in a `bwrap` sandbox: statement match, axiom boundary, con-ron (93,951 declarations), NanoDa and the Lean kernel accept; [`comparator-tail.log`](comparator-tail.log) |

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `724497633a957cf76bcfed0480de3aafbdd900392712407c58ab2e7d6ecec5ba` |
| `Solution.lean` | `01a4ef593f541bc407e10600208c8dd364cea36444874bb4f0ba89ae7c507a6d` |
| `comparator.json` | `e713cbdb7aedd1bad2d5a215b234857d649294ef1ebd50efacdc5d0a68e39b3a` |
| `main.tex` of the paper, version 1 | `8d57d9270f3ef58961cb21697852b01cfdc2195bc79f61e00bfdbe844b3a6e48` |

These are local runs, not registry acceptance. The bubblewrap binary was the Ubuntu
22.04 package 0.6.1.
