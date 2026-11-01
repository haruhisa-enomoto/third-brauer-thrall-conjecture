# The critical branch without tilting theory

This note gives the proof of `RayCat.pointBrickNode'` (`BongartzTheorem/CriticalPieces/PieceCritical.lean`). It produces the point and brick of Bongartz's Lemma 4 ([arXiv:1611.02017v5](https://arxiv.org/abs/1611.02017v5), §4.2) for a critical convex piece. The argument uses no tilting theory, tame hereditary theory or tubes, and it never identifies the quotient `B` below as tame concealed. The Lean proof is the proof of record. An independent agent audit checked selected steps; no human has reviewed the mathematics.

## The idea

BO23 applies Vossieck's argument to a homogeneous regular module `N`, and this needs the tame concealed structure. Vossieck's own theorem is about preprojective modules. So use a large sincere directing module `U` instead of `N`. Its dimension vector is close to a multiple of the radical vector, and that is all the argument needs.

## Conventions

Modules are left modules, `P_x = Ae_x`, `M(x) = e_x M`. A morphism `x → y` is an element of `e_y A e_x`. A *chain* is a sequence of nonzero non-bijective maps between nonzero indecomposables (Lean: `Reach₁`). `x` is a *sink* if no nonzero morphism leaves it, so `P_x = S_x`. It is a *source* if none enters it, so `I_x = S_x`.

## Proof

Let `C` be a critical piece and `A = kC`.

**Step 0.** All projectives of `A` lie in the preprojective component: the points whose projective lies in the component form an arrow-closed, hence convex, set. Choose `Z` maximal such that the indecomposables of `B = A/Ae_Z A` have unbounded dimension. Every proper quotient of `B` by vertices then has bounded indecomposables. The vertex count of `B` is at least 3, because `Hom` dimensions are at most 1.

**Step 1 (ASS IX.5.2).** Chains ending at projective `A`-modules have bounded length. Pullbacks lift a chain ending at a projective of `R = A/AeA` to one of the same length over `A`. So the same bound holds over every such `R`.

**Step 2 (bounded chains give a preprojective class).** Let `𝒫(R)` be the indecomposables with bounded chains ending at them, and `n(W)` that bound. It contains all projectives and is closed under predecessors. It is closed under irreducible successors, by induction on `n(W)`. Let `W → Y` be irreducible with `Y` nonprojective and AR sequence `0 → τY → E → Y → 0`. Then `τY → W` is irreducible, so `n(τY) < n(W)`. Induction puts every summand of `E` in `𝒫(R)`. Each map into `Y` factors through `E`, so `Y ∈ 𝒫(R)`.

So `𝒫(R)` satisfies `PreprojComp`, apart from nonemptiness when `R` is zero. Members are directing. If its dimensions are bounded, it is a `ClosedClass` containing all projectives, so it is everything. This gives two facts:

- If `R` has bounded indecomposables, all its indecomposables are directing.
- `𝒫(B)` is unbounded. Nonsincere `B`-modules are bounded, so `B` has sincere directing modules of unbounded dimension.

**Lemma 3 (no tilting).** Let `U` be a sincere directing `B`-module, `W` indecomposable with a chain or isomorphism `W → U`, and `0 → K → P → W → 0` exact with `P` projective. Then `K` is projective.

*Proof.* If not, `Ext¹(K, S_c) ≠ 0` for some `c`, by induction on length. Take a nonsplit `0 → S_c → E → K → 0`. Extend `S_c ⊂ I_c` to `E → I_c`, which induces `K → Q = I_c/S_c`. Pushing `K ⊂ P` out along this map gives `0 → Q → D → W → 0`. If this split, the map `K → Q` would extend to `P`, then lift to `P → I_c`, and subtracting would give a retraction of `S_c → E`. So it is nonsplit, and it stays nonsplit for an indecomposable summand `Q_j` of `Q`. A nonsplit extension gives a chain `Q_j → E_i → W`. Sincerity gives `U → I_c ≠ 0`. So `U → I_c → Q_j → E_i → W → U` is a cycle through `U`. ∎

Every submodule of a projective has summands mapping nonzero to some `P_c`, and `P_c → U ≠ 0`. So `gl.dim B ≤ 2`, and for all `X, Y`:

```text
⟨X, Y⟩ ≥ dim Hom(X, Y) − dim Ext¹(X, Y).        (E)
```

**Lemma 4 (Vossieck, without τ).** For sincere directing `U` and any nonzero morphism `v : a → b` with `a ≠ b`, the map `U(v)` is injective or surjective.

*Proof.* Let `V = Ae_a/Av`, which has simple top, so it is indecomposable. Then `ker U(v) ≅ Hom(V, U)`. Suppose this is nonzero. Lemma 3 says `Av` is projective, hence `Av ≅ P_b`, so `P_b → P_a` is injective. Then `coker U(v) = Ext¹(V, U)`. If that is nonzero, a nonsplit extension gives a chain `U → V`, and with `V → U` this is a cycle. ∎

Vossieck's published theorem gives the same statement for `U` in a preprojective component, using τ. So this lemma has a second, published proof.

**Lemma 5 (minimum at a source or sink).** Let `U` be sincere directing and `m` the minimum of `d = dim U`. Then some vertex with `d = m` is a source or a sink.

*Proof.* On the set `L` where `d = m`, order vertices by "`a = b`, or there is `v : a → b` with `U(v)` bijective". This is a partial order. Take `x₀` minimal and `x₁ ≥ x₀` maximal in it. If neither is an extreme vertex, take nonzero `y → x₀` and `x₁ → y'`. Lemma 4 forces every morphism between vertices of `L` to act bijectively, so `y, y' ∉ L` and `d(y), d(y') > m`. So `y → x₀` acts surjectively, `x₁ → y'` injectively, and the composite has rank `m`. It is then a nonzero morphism acting neither injectively nor surjectively, which contradicts Lemma 4. ∎

**Step 6 (the form is critical).** Let `χ` be the Euler form of `B`. It is not weakly positive, by `not_weaklyPositive_of_unbounded`. Let `v` be positive with `v_i = 0`, and take `X` of dimension `v` with `dim End X` minimal. Then `X` is a module over `B/Be_iB`, whose indecomposables are directing by Step 2, so they have no self-extensions. Extensions between `B/Be_iB`-modules stay in that module category. `extVanish_of_minEnd` then gives `Ext¹_B(X, X) = 0`. By (E), `χ(v) ≥ dim End X ≥ 1`.

So `χ` is critical. `Critical.ovsienko` gives `χ ≥ 0`, a positive radical vector `z`, a vertex `c` with `z_c = 1`, and `χ(x) = 0 ⟹ x = x_c z`.

**Step 7 (choice of `x`).** For `U` sincere directing, `χ(d) = 1` by `euler_directing`. Write `d = d_c z + r` with `r_c = 0`, so `χ(r) = 1`. The form is positive definite on `x_c = 0`, so `r` lies in a finite set. Take `d_c` large. Then every minimum of `d` lies where `z = 1`. Lemma 5 gives a source or sink `x` of `B` with `z_x = 1`.

**Step 8 (the brick).** Let `w = z − e_x`, so `χ(w) = 1`. Take `V` of dimension `w` with minimal `dim End V`. By Step 6's argument, `1 = χ(w) ≥ dim End V ≥ 1`, so `V` is a brick.

**Step 9 (two extensions).** `z` radical gives `⟨w, e_x⟩ + ⟨e_x, w⟩ = −2`.

- At a sink, `⟨e_x, w⟩ = w_x = 0`, so `⟨V, S_x⟩ = −2` and (E) gives `dim Ext¹(V, S_x) ≥ 2`.
- At a source, `⟨w, e_x⟩ = ⟨V, I_x⟩ = 0`, so `dim Ext¹(S_x, V) ≥ 2`.

**Step 10 (inflate).** Inflation along `A → B` is fully faithful and exact and preserves bricks. An extension of `A`-modules killed by `e_Z` is itself killed by `e_Z`, so it comes from `B`. The supports of `S_x` and `V` are disjoint, so the two independent classes of Step 9 give two independent cocycles on `C`. Take `Sp = C` and apply `pointBrick'_of_cocycles`.
