# The formalized manuscript

The formalization follows *Representation embeddings and the third
Brauer–Thrall conjecture* by Haruhisa Enomoto, version 1,
[hexagon:2610.00179v1](https://hexagonmath.org/2610.00179v1) (October 10, 2026,
CC BY 4.0). The source and PDF are available there and are not copied here.

Statement numbers and `main.tex` line numbers in the
[correspondence](PAPER-CORRESPONDENCE.md) refer to this version. It is identified
by the SHA-256 hashes of the files that Hexagon serves:

| File | SHA-256 |
| --- | --- |
| `main.tex` | `8d57d9270f3ef58961cb21697852b01cfdc2195bc79f61e00bfdbe844b3a6e48` |
| PDF | `e5e7cb243aea0edb4d5064850d502f3bb6aa1acdf7ebc40afb62121d666271c9` |

The paper cites Bongartz's Theorem 6 and Corollary 1.3 of Göbel and Simson; both
are proved in this repository. At two points of Bongartz's Theorem 6 the formal
proof differs from the literature. These arguments are not in the paper, and they
are written up in [`proofs/`](proofs/): [long lines](proofs/long-lines.md), with
[contours](proofs/contours.md), and the
[critical branch](proofs/critical-branch.md).
