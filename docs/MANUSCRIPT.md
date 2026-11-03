# The formalized manuscript

The formalization follows *Representation embeddings and the third
Brauer–Thrall conjecture* by Haruhisa Enomoto, in the revision that succeeds
version 1, [hexagon:2610.00179v1](https://hexagonmath.org/2610.00179v1)
(October 10, 2026, CC BY 4.0), and that describes this formalization.

Statement numbers and `main.tex` line numbers in the
[correspondence](PAPER-CORRESPONDENCE.md) refer to this revision. It is
identified by the SHA-256 hashes of its files:

| File | SHA-256 |
| --- | --- |
| `main.tex` | `808910a19d0a27150e4e035b9ab68562f762e855e48e613f0cffcd29bbe4a445` |
| PDF | `e533f01a44ff8322cb126d3b9b03871322a691a6a018a2f18f2dd28c3ee96dea` |

The revision defines Bongartz's three functors directly on Kronecker modules of
arbitrary dimension and controls their endomorphisms there; the library follows
this route. Version 1 instead extended a functor on finite-dimensional modules
by filtered colimits (`main.tex` SHA-256
`8d57d9270f3ef58961cb21697852b01cfdc2195bc79f61e00bfdbe844b3a6e48`).

The paper cites Bongartz's Theorem 6 and Göbel and Simson's rigid families;
Bongartz's Theorem 6 is proved in this repository, and so is the form of the
Göbel–Simson result that is used: Kronecker bricks of every infinite dimension.
The number `2^κ` of modules in Corollary 1.1 and the explicit bound
`n ≤ max(30, 4 dim A)` are not formalized. At two points of Bongartz's Theorem 6 the formal
proof differs from the literature. These arguments are not in the paper, and they
are written up in [`proofs/`](proofs/): [long lines](proofs/long-lines.md), with
[contours](proofs/contours.md), and the
[critical branch](proofs/critical-branch.md).
