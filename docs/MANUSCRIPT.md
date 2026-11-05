# The formalized manuscript

The formalization follows *Representation embeddings and the third
Brauer–Thrall conjecture* by Haruhisa Enomoto,
[arXiv:2611.06325v1](https://arxiv.org/abs/2611.06325v1) (November 2026), which has
the same source as [hexagon:2610.00179v2](https://hexagonmath.org/2610.00179v2) and
describes this formalization. The first version is
[hexagon:2610.00179v1](https://hexagonmath.org/2610.00179v1) (October 10, 2026,
CC BY 4.0).

Statement numbers and `main.tex` line numbers in the
[correspondence](PAPER-CORRESPONDENCE.md) refer to this version. The `main.tex`
of the arXiv source is identified by its SHA-256 hash; the PDF hash is that of the
author's build of the same source:

| File | SHA-256 |
| --- | --- |
| `main.tex` | `555b29fe3a362d90abaa110f34e12c8ad9ca0cad22f23e416b5337cfd12526a1` |
| PDF | `0aebde92a4965bb7862c1c26dac886c44a0fc2e4b3bd5b6e30b08e1e041fac49` |

This version defines Bongartz's three functors directly on Kronecker modules of
arbitrary dimension and controls their endomorphisms there; the library follows
this route. Version 1 instead extended a functor on finite-dimensional modules
by filtered colimits (`main.tex` SHA-256
`8d57d9270f3ef58961cb21697852b01cfdc2195bc79f61e00bfdbe844b3a6e48`).

The paper cites Bongartz's Theorem 6 and Göbel and Simson's rigid families;
Bongartz's Theorem 6 is proved in this repository, and so are the rigid families
over infinite fields. Corollary 1.1 is formalized in full, with the number `2^κ`
of modules and the bound `n ≤ max(30, 4 dim A)`. At two points of Bongartz's Theorem 6 the formal
proof differs from the literature. These arguments are not in the paper, and they
are written up in [`proofs/`](proofs/): [long lines](proofs/long-lines.md), with
[contours](proofs/contours.md), and the
[critical branch](proofs/critical-branch.md).
