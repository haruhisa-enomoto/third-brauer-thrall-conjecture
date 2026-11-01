module

public import LargeIndecomposable.Cleaving.Zigzags.ZigzagFork
public import LargeIndecomposable.RayCategories.Basic.ThreeArrows
public import LargeIndecomposable.Crowns.Basic.CrownSeq

/-!
# BO13a Lemma 5 a): the zigzag case

* `Crown.toZChain`: the `ℕ`-indexed chain of a crown.
* `MulBasis.not_zigzag_arrow_forks`: the zigzag-with-forks contradiction when
  the forks are pairs of distinct arrows and the end morphisms factor through
  none of them (BO13a figure 5.1).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- The `ℕ`-indexed chain of a crown: `ρ t` at position `2t`, `σ t` at `2t + 1`. -/
def Crown.toZChain (C : Crown P) : ZChain P where
  x t := (C.f (2 * t)).1
  z t := (C.f (2 * t)).2.1
  ρ t := (C.f (2 * t)).2.2
  σ t := midMor (C.peak t) (C.valley t)
  ρ_ne t := C.ne _
  σ_ne t := midMor_ne (C.peak t) (C.valley t) (C.ne _)
  peak₁ t := midMor_peak₁ (C.peak t) (C.valley t)
  peak₂ t := midMor_peak₂ (C.peak t) (C.valley t)
  valley₁ t := midMor_valley₁ (C.peak t) (C.valley t)
  valley₂ t := midMor_valley₂ (C.peak t) (C.valley t)

omit [IsRayCategory P] in
/-- Factoring through an arrow on the right, both ways: if `f` (non-invertible,
nonzero) does not factor through the irreducible `α`, then `α` does not factor
through `f` either. -/
lemma not_comp_eq_irr {x y y' : P} {f : x ⟶ y} {α : x ⟶ y'} (hα : IsIrreducible α)
    (hf : ¬IsIso f) (hfα : ¬∃ g, α ≫ g = f) : ¬∃ g, f ≫ g = α := by
  rintro ⟨g, hg⟩
  rcases hα.2.2 _ f g hg.symm with h | h
  · exact hf h
  · exact hfα ⟨inv g, by rw [← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id]⟩

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a figure 5.1** with arrows as forks. -/
theorem not_zigzag_arrow_forks
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (hτr : ¬IsIrreducible τ) (Z : ZChain P) (p L : ℕ)
    (F : Fin 2 → BMor (Z.x p)) (G : Fin 2 → BMor (Z.x (p + L + 1)))
    (hFi : ∀ i, IsIrreducible (F i).2) (hGi : ∀ i, IsIrreducible (G i).2)
    (hF01 : F 0 ≠ F 1) (hG01 : G 0 ≠ G 1)
    (hρ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.ρ (p + j)))
    (hσ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.σ (p + j)))
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p)
    (hGσ : ∀ i, ¬∃ g, (G i).2 ≫ g = Z.σ (p + L)) : False := by
  have hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2 := fun i i' hii' hg ↦ by
    have := eq_of_bLe_irr (hFi i) (hFi i') hg
    fin_cases i <;> fin_cases i' <;> simp_all
  have hGG : ∀ i i', i ≠ i' → ¬∃ g, (G i).2 ≫ g = (G i').2 := fun i i' hii' hg ↦ by
    have := eq_of_bLe_irr (hGi i) (hGi i') hg
    fin_cases i <;> fin_cases i' <;> simp_all
  exact B.not_zigzag_forks hmin hL hR τ hτ hτ0 Z p L F G hρ hσ
    (fun i ↦ not_factorsThrough_irr hτ hτ0 hτr (hFi i))
    (fun i ↦ not_factorsThrough_irr hτ hτ0 hτr (hGi i)) (fun i ↦ (hFi i).2.1)
    (fun i ↦ (hGi i).2.1) hFF hGG hFρ
    (fun i ↦ not_comp_eq_irr (hFi i) (Z.ρ_not_isIso p) (hFρ i)) hGσ
    (fun i ↦ not_comp_eq_irr (hGi i) (Z.σ_not_isIso (p + L)) (hGσ i))

end MulBasis

end RayQuiver

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- A long morphism (BO13a): nonzero, not invertible, not irreducible, and
maximal for the two-sided factorization order. -/
def IsLong {a b : P} (μ : a ⟶ b) : Prop :=
  μ ≠ 0 ∧ ¬IsIso μ ∧ ¬IsIrreducible μ ∧ IsLongAt μ

/-- A nonzero multiple of a long morphism is long (it is the same morphism). -/
lemma IsLong.of_factorsThrough {a b x y : P} {μ : a ⟶ b} (hμ : IsLong μ) {f : x ⟶ y}
    (hf : f ≠ 0) (h : FactorsThroughMorphism μ f) : IsLong f := by
  obtain ⟨hx, hy, rfl⟩ := hμ.2.2.2 f hf h
  subst hx hy
  simpa using hμ

lemma not_factorsThrough_of_not_isLong {a b x y : P} {μ : a ⟶ b} (hμ : IsLong μ) {f : x ⟶ y}
    (hf : f ≠ 0) (hl : ¬IsLong f) : ¬FactorsThroughMorphism μ f := fun h ↦
  hl (hμ.of_factorsThrough hf h)

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a), figure 5.1.** Let `σ s` be long, and let the chain
morphisms `ρ (s+1), σ (s+1), …, ρ (s+1+L), σ (s+1+L)` be non-long. If `ρ (s+1)`
factors through neither of two distinct arrows `F` out of `x (s+1)` and
`σ (s+1+L)` through neither of two distinct arrows `G` out of `x (s+L+2)`, we
get a cleaving `D̃` diagram in `P/σ s`. -/
theorem lemma5a_zigzag
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (Z : ZChain P) (s L : ℕ) (hσ : IsLong (Z.σ s))
    (hnρ : ∀ j ≤ L, ¬IsLong (Z.ρ (s + 1 + j))) (hnσ : ∀ j ≤ L, ¬IsLong (Z.σ (s + 1 + j)))
    (F : Fin 2 → BMor (Z.x (s + 1))) (G : Fin 2 → BMor (Z.x (s + 1 + L + 1)))
    (hFi : ∀ i, IsIrreducible (F i).2) (hGi : ∀ i, IsIrreducible (G i).2)
    (hF01 : F 0 ≠ F 1) (hG01 : G 0 ≠ G 1)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ (s + 1))
    (hGσ : ∀ i, ¬∃ g, (G i).2 ≫ g = Z.σ (s + 1 + L)) : False :=
  B.not_zigzag_arrow_forks hmin hL hR (Z.σ s) hσ.2.1 hσ.1 hσ.2.2.1 Z (s + 1) L F G hFi hGi
    hF01 hG01 (fun j hj ↦ not_factorsThrough_of_not_isLong hσ (Z.ρ_ne _) (hnρ j hj))
    (fun j hj ↦ not_factorsThrough_of_not_isLong hσ (Z.σ_ne _) (hnσ j hj)) hFρ hGσ

end MulBasis

end RayQuiver

end LargeIndecomposable
