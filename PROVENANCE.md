# Provenance

The Lean development is maintained by Haruhisa Enomoto. It formalizes
*Representation embeddings and the third Brauer–Thrall conjecture*, version 1
([hexagon:2610.00179v1](https://hexagonmath.org/2610.00179v1)), identified in
[docs/MANUSCRIPT.md](docs/MANUSCRIPT.md). The
[correspondence](docs/PAPER-CORRESPONDENCE.md) describes formal coverage.

## Contributions

According to the paper's provenance statement, the research was done under the
author's direction using GPT-6-Astra, which found and developed the proof and
wrote the earlier drafts, and the final text was revised with Claude Opus 5.5.

The formalization was developed with AI coding agents under Haruhisa Enomoto's
direction, mainly with Claude Opus 5.5. This includes the proofs of the cited
inputs and the two arguments in [docs/proofs](docs/proofs/) that differ from the
literature.

## Dependencies and licences

The package pins Lean 4.35.0-rc3 and Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`). Mathlib is the
only external Lake dependency. Code reused from earlier formalizations is listed
in [VENDORED.md](VENDORED.md). This repository is released under the
[Apache License 2.0](LICENSE).
