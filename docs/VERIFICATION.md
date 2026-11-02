# Verification

The library proves Theorem A, Corollary 1.1 and Corollary 5.3 of [the paper](MANUSCRIPT.md),
together with the inputs the paper cites. The [correspondence](PAPER-CORRESPONDENCE.md)
lists the declarations. Records are in [`verification/`](../verification/).

## Independent statement

`LargeIndecomposable/Statement.lean` states the three results with Mathlib alone:
Kronecker modules as functors from `WalkingParallelPair`, the category `D`, representation
embeddings, representation-finite algebras and dimensions as cardinals.
`Challenge.lean` is generated from it with three deliberate `sorry` placeholders.
`Solution.lean` proves them and does not import the Challenge.

## Results

The [record of November 3, 2026](../verification/2026-11-03/README.md) gives the local
results, the hosted Palomar preflight (passed on a 4-CPU, 16 GB runner) and the hashes
for the current library. A preflight is an advisory report, not registry acceptance.
Earlier records are in [`verification/`](../verification/README.md).

An independent agent audit of an earlier revision checked the definitions in
`Statement.lean`, the final proof assembly and selected steps of the proofs in
[`proofs/`](proofs/). The theorem statements have not changed since. It was not a
line-by-line review, and no human expert has reviewed the Lean statements or these proofs.
Lean checks the proofs; whether `Challenge.lean` says what the paper says is a human
judgement.

## Reproduce the checks

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/scan_axioms.py
python3 scripts/generate_challenge.py --check
lake build Challenge Solution
./scripts/verify-comparator.sh
```

A fresh build takes about 50 minutes on 20 hardware threads. Each Lean process stays
below 6.2 GB.

`audit_axioms.py` and `scan_axioms.py` generate non-module Lean files, because a `module`
file sees theorems without their proofs. `verify-comparator.sh` follows the Palomar
template: it runs the `lake comparator` bundled with the toolchain, with the Lean kernel
and the bundled NanoDa and con-ron checkers, inside a `bwrap` (bubblewrap) sandbox. `bwrap`
must be on the path, and `.lake/packages` must be a real directory, not a symlink.

The workflow [Palomar preflight](../.github/workflows/palomar-preflight.yml) runs Palomar's
mechanical verification for a chosen commit.
