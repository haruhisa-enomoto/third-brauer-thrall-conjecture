# Contours excluded by a root chain

This note proves that a large sincere directing module excludes contours. The form part is `false_of_anchors` (`UnitForms/Roots.lean`), the polygons are in `DirectedAlgebras/Sincere/PolyBuild.lean`, and the final contradiction is `RayCat.noContour_of_large` (`BongartzTheorem/ContourExclusion/ContourFree.lean`). The whole argument is in [long lines](long-lines.md).

Conventions: `q` weakly positive unit form with polar form `B`, root = positive vector with `q = 1`.

## Root chain

Let `t₁, t₂` be roots with `B(t₁, t₂) = 0`, and `z ≥ t₁ + t₂` a root. Take a root `y` minimal with `y ≥ t₁ + t₂`, and put `a = y - t₁ - t₂`. Then `a ≠ 0`, since `q(t₁ + t₂) = 2`. Minimality gives `B(y, e_k) ≤ 0` for `k` in the support of `a`, so `B(y, a) ≤ 0`. From `q(y) = 1` we get `B(t₁ + t₂, a) = -1 - q(a)`, hence `B(y, a) = q(a) - 1`. So `q(a) = 1`, and `B(t_i, a) = -1` for both `i`, because `q(t_i + a) ≥ 1`.

## Anchors

An *anchor* is a set of vectors `e_α, e_β, r_j` (`j ∈ J`, `|J| ≥ 2`) with `r_j` roots, `t = e_α + e_β + Σ r_j` a root, `B(e_α, r_j) = B(e_β, r_j) = -1`, and `B(r_i, r_j) = 0` for `i ≠ j`. Then `B(t, r_j) = 0`.

**Lemma.** If `a` is a root with `B(t, a) = -1`, there is `G ≥ 0` supported in `t` with `q(G) ≤ 2` and `B(a, G) ≤ -2`.

Proof. `B(a, -) ≥ -1` on all the vectors above.

- Some `B(a, r_j) = -1`: take `G = t + r_j`.
- Some `B(a, r_j) ≥ 1`: take `G = t - r_j`.
- All `B(a, r_j) = 0`: then `B(a, e_α) + B(a, e_β) = -1`, so one of them is `-1`, say `α`. Take `G = 2e_α + r_i + r_j`.

**Theorem.** Two anchors with orthogonal supports are never below a common root.

Proof. With `a` from the chain, `v = 2a + G₁ + G₂` is positive and `q(v) = 4 + q(G₁) + q(G₂) + 2B(a, G₁) + 2B(a, G₂) ≤ 0`.

## Anchors from contours

Choose a nonzero morphism `w` of `P` with two distinct paths, and proper factors with unique paths. Lift it to `w : α → β` in the cover, acting nonzero on a sincere directing module. Let `H` be the set of points through which `w` factors. Minimality makes `H` a union of `{α, β}` and internally disjoint chains (arms), at least 2 of them. Chords do not matter.

All values of `B` come from indecomposable thin modules, each a quotient of a projective or a submodule of an injective, so each has `q = 1`:

- `q(e_α + r_j) = 1` gives `B(e_α, r_j) = -1`, and dually for `β`.
- `q(e_α + r_i + r_j) = 1` gives `B(r_i, r_j) = 0`.
- `t = 1_H` is the image of `P_α → I_β`.

## Conclusion for contours

Let `U` be sincere directing and large, on `C`. Let `w` be as above, killed by no large indecomposable, by minimality of the algebra. Take a lift `H₀` acting nonzero on `U`. Let `E` be the points of `C` with no directed path to or from `H₀`. It is convex, and its complement is bounded, since directed paths in `C` have bounded length and degrees are bounded. A summand `Y` of `U|_E` through a far point must reach the complement (else `Y` splits off `U`), so `Y` is large. So `w` has a lift `H₁` acting nonzero on `Y`, hence on `U`. Points with no directed path between them have `B = 0`. So `H₀, H₁` are orthogonal anchors below `dim U`, a contradiction. Thus `P` has no contours.
