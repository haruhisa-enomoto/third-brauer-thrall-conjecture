# The third Brauer–Thrall conjecture over algebraically closed fields

[Website](https://haruhisa-enomoto.github.io/third-brauer-thrall-conjecture/) ·
[Paper](https://hexagonmath.org/2610.00179v1) ·
[Main theorems in Lean](LargeIndecomposable/MainTheorems.lean) ·
[Independent statement](LargeIndecomposable/Statement.lean) ·
[Paper correspondence](docs/PAPER-CORRESPONDENCE.md)

This repository contains a Lean 4 formalization of the principal results of the
paper *Representation embeddings and the third Brauer–Thrall conjecture*
([hexagon:2610.00179v1](https://hexagonmath.org/2610.00179v1); the library
follows the revision described in [MANUSCRIPT.md](docs/MANUSCRIPT.md)), including
the cited inputs that it uses.

Let `k` be an algebraically closed field, `A` a representation-infinite
finite-dimensional `k`-algebra, and `D` the category of Kronecker modules of
arbitrary dimension without a direct summand isomorphic to the simple injective.

**Theorem A.** There is a representation embedding `F : D → Mod A` that sends
finite-dimensional modules to finite-dimensional modules, commutes with arbitrary
direct sums and filtered colimits, and satisfies `dim F(T) = dim T` for
infinite-dimensional `T`.

**Corollary 1.1** (formalized without the number `2^κ` of modules and the
explicit bound on `n`). For every infinite cardinal `κ`, `A` has an
indecomposable module of dimension `κ`, and these modules can be chosen with
`End(M)/rad End(M) ≅ k` and `(rad End(M))ⁿ = 0` for one `n` independent of the
dimension.

## Start reading

- [Main theorems](LargeIndecomposable/MainTheorems.lean): `theoremA`,
  `corollaryDimension` and `corollaryRadical`.
- [Independent statement](LargeIndecomposable/Statement.lean): the three results
  stated with Mathlib alone. The [Challenge](Challenge.lean) is generated from it,
  and [Solution](Solution.lean) proves it.
- [Paper correspondence](docs/PAPER-CORRESPONDENCE.md): every numbered statement
  of the paper with its Lean declarations.
- [Proof notes](docs/proofs/): the two arguments that differ from the literature.

All definitions and proofs are complete. The main statements depend only on the
axioms `propext`, `Classical.choice` and `Quot.sound`. The paper cites Bongartz's
Theorem 6 and Göbel and Simson's rigid families; the library proves Theorem 6 and
the form of the Göbel–Simson result that is used (Kronecker bricks of every
infinite dimension). Two
steps of Bongartz's Theorem 6 have different proofs here: the critical pair avoids
tilting theory, and long lines avoid the classification of large sincere algebras.
Theorem A needs only a weak form of Bongartz's large-line theorem, and the library
does not prove the full theorem.

An independent agent audit of an earlier revision checked the definitions in
`Statement.lean`, the final proof assembly and selected steps of the two proofs. The
theorem statements have not changed since. It was not a line-by-line review, and no human
expert has reviewed the Lean statements or these proofs. Lean checks the proofs; whether
[Challenge.lean](Challenge.lean) says what the paper says is a human judgement.

## Layout

The library is organized by subject under `LargeIndecomposable/`.

| Directory | Content |
| --- | --- |
| `Statement`, `MainTheorems` | the statements, and the proofs of Theorem A and its corollaries |
| `Foundations` | groups, rings, linear algebra, bilinear forms, categories, exact categories, gradings, path categories, convex geometries |
| `Modules` | Krull–Schmidt, idempotents, corners, split basic algebras, Morita equivalence, duality, homological algebra |
| `RepresentationType` | representation-finite algebras, minimal representation-infinite algebras, obstructions, distributive ideal lattices |
| `Quivers` | paths, path algebras, representations, reflection functors, representation type, push-downs |
| `UnitForms` | unit forms, roots, critical forms, Ovsienko's theorem, Drozd's lemma |
| `AuslanderReiten` | almost split sequences, irreducible maps, the translate, the radical, tau-categories, Iyama's ladders |
| `DirectedAlgebras` | directing modules, preprojective components, Euler forms, sincere directing modules, the separation theorem |
| `RayCategories` | ray categories, linearizations, ray tables, contours, closed chains, Roiter's vanishing theorem |
| `FundamentalGroups` | cocycles, free fundamental groups, Fischbacher's reduction |
| `Coverings` | universal and Galois covers, graded modules, Gabriel's covering theorem, convex pieces |
| `Cleaving` | cleaving functors, thin and tree diagrams, zigzags, the families of representation-infinite shapes |
| `MultiplicativeBases` | twisted and normed multiplicative bases, scalar presentations |
| `StandardForm` | the standard form of a representation-finite algebra: deformations, Hochschild cohomology, weights, integral lifting |
| `MeshCategories`, `PreprojectiveAlgebras` | mesh categories, periodic components, star models, traces, preprojective algebras |
| `Crowns`, `MildContours` | long morphisms and crowns; mild contours, dumb-bells, diamonds, penny-farthings |
| `KroneckerModules`, `KroneckerBricks` | Kronecker modules; bricks of every infinite dimension |
| `RepresentationEmbeddings` | the quotient, covering and walk constructions on Kronecker modules of any dimension, control by retractions, and the embedding theorem |
| `BongartzTheorem` | Bongartz's Theorem 6: reduction, critical pieces, contour exclusion, simply connected covers, long lines |

Conventions: modules are left modules. The field, the algebra and the modules live
in one universe. Dimensions are cardinals, given by `Module.rank`.

## Build and verify

Lean is pinned to `v4.35.0-rc3` and Mathlib to its `v4.35.0-rc3` tag, commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, the only external dependency. Every
Lean file uses the Lean module system.

```sh
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/scan_axioms.py
```

The statement check uses the `lake comparator` shipped with the toolchain, with
the Lean kernel and the bundled NanoDa and con-ron checkers. It needs `bwrap`
(bubblewrap) on the path, and `.lake/packages` must be a real directory:

```sh
python3 scripts/check-lean-sources.py
./scripts/verify-comparator.sh
```

[docs/VERIFICATION.md](docs/VERIFICATION.md) describes the checks, and the records
are in [verification](verification/).

## Palomar

The repository follows the layout of the
[Palomar registry](https://palomar-registry.org): the statement of record is
[Challenge.lean](Challenge.lean), proved in [Solution.lean](Solution.lean), with
[comparator.json](comparator.json) and the metadata in
[formalization.yaml](formalization.yaml). The workflow
[Palomar preflight](.github/workflows/palomar-preflight.yml) runs Palomar's
mechanical verification for a chosen commit. It
[passed](verification/2026-11-03/README.md) for the current commit. This is an advisory
report; the formalization has not been submitted to the registry.

## Website

The [website](https://haruhisa-enomoto.github.io/third-brauer-thrall-conjecture/)
presents the theorems, the independent statement, a proof guide, a library
overview and the searchable Lean API. See [website/README.md](website/README.md)
for building and publishing it.

## Provenance

See [PROVENANCE.md](PROVENANCE.md) for the sources of the paper and the Lean files,
and [VENDORED.md](VENDORED.md) for reused code. Licensed under the
[Apache License 2.0](LICENSE).
