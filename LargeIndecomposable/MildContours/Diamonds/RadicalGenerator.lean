module

public import LargeIndecomposable.MildContours.Diamonds.Closure2
public import LargeIndecomposable.MildContours.Diamonds.Generators

/-!
# Diamond: `σ = γ η` generates the radical of `End x`

Given the generator `ρ = ω' α` at `y` and some generator `π` at `x`, `σ = γ η` is a
generator at `x` (`genσ`): `π` begins with `γ` or `δ` (`X1`); `δ` is excluded by
`nL'`; if `σ = π^m` with `m ≥ 2`, then `η` has at least three arrows, excluded by
`s_le_two` (the case `a = x` is excluded by `X1` applied to `α`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

namespace DiamondData

variable (D : DiamondData P)

/-- An irreducible loop at `y` is impossible. -/
lemma no_loop_y (hρ : ∀ f : D.y ⟶ D.y, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow (D.ω' ≫ D.α) n)
    (f : D.y ⟶ D.y) (hf : IsIrreducible f) : False := by
  obtain ⟨m, hm, hfm⟩ := hρ f hf.2.1
  obtain ⟨m, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rcases hf.2.2 _ D.ω' (D.α ≫ rpow (D.ω' ≫ D.α) m) (by rw [hfm, rpow_succ', Category.assoc])
    with h | h
  · exact D.hω' h
  · exact D.hα.2.1 (ray_isIso_factors D.α (rpow (D.ω' ≫ D.α) m)).1

/-- A morphism with at least three arrows written as `μ ≫ γ ≫ ν` with `μ, ν` not
invertible gives the shape of `s_le_two`. -/
lemma three_arrows (hM : MildHyp k P) (μ : D.a ⟶ D.x) (ν : D.a ⟶ D.x)
    (hμ : ¬IsIso μ) (hν0 : ν ≠ 0) (hν : ¬IsIso ν) (hη : D.η = μ ≫ D.γ ≫ ν) : False := by
  obtain ⟨c₂, p₂, e₂, hp₂⟩ := MildContour.exists_last_arrow ν hν0 hν
  by_cases h1 : IsIso (pathVal p₂)
  · exact D.s_le_two hM μ (D.γ ≫ pathVal p₂) e₂.1 hμ (isIrreducible_comp_iso D.hγ _) e₂.2
      (by rw [hη, hp₂]; simp)
  · have h10 : pathVal p₂ ≠ 0 := fun h ↦ hν0 (by rw [hp₂, h, zero_comp])
    obtain ⟨c₁, p₁, e₁, hp₁⟩ := MildContour.exists_last_arrow (pathVal p₂) h10 h1
    exact D.s_le_two hM (μ ≫ D.γ ≫ pathVal p₁) e₁.1 e₂.1
      (not_isIso_comp_left' _ hμ) e₁.2 e₂.2 (by rw [hη, hp₂, hp₁]; simp)

/-- **`σ = γ η` generates the radical of `End x`.** -/
theorem genσ (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ)
    (hρ : ∀ f : D.y ⟶ D.y, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow (D.ω' ≫ D.α) n)
    (π : D.x ⟶ D.x) (hπ : ∀ f : D.x ⟶ D.x, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow π n) :
    ∀ f : D.x ⟶ D.x, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow (D.γ ≫ D.η) n := by
  have hL : LeftCancel P := hM.left
  have hτ0 := D.τ_ne_zero
  have hσn : ¬IsIso (D.γ ≫ D.η) := not_isIso_comp_left' _ D.hγ.2.1
  have hσ0 : D.γ ≫ D.η ≠ 0 := fun h ↦ hτ0 (by rw [D.τ_η, ← Category.assoc, h, zero_comp])
  obtain ⟨m, hm, hσm⟩ := hπ _ hσn
  suffices h : m = 1 by
    intro f hf
    obtain ⟨n, hn, rfl⟩ := hπ f hf
    exact ⟨n, hn, by rw [hσm, h]; simp [rpow_succ]⟩
  by_contra hm1
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hπn : ¬IsIso π := by
    intro h
    obtain ⟨hh0, he⟩ := RayQuiver.eq_id_of_isIso π
    apply hσn
    rw [hσm, he, eqToHom_refl, MildContour.rpow_id]; infer_instance
  have hπ0 : π ≠ 0 := fun h ↦ hσ0 (by rw [hσm, h, rpow_succ]; simp)
  obtain ⟨c, e, r, he, hr⟩ := exists_first_arrow' π hπ0 hπn
  have hσ' : D.γ ≫ D.η = π ≫ rpow π (j + 1) := by rw [hσm, rpow_succ']
  rcases D.X1 hM hMo e he with ⟨h, hh⟩ | ⟨h, hh⟩
  · -- `π = γ ≫ μ`
    set μ := h ≫ r with hμ
    have hπμ : π = D.γ ≫ μ := by rw [hr, ← hh, hμ, Category.assoc]
    have hημ : D.η = μ ≫ D.γ ≫ μ ≫ rpow π j := by
      apply hL D.γ
      · rw [hσ', rpow_succ', hπμ]; simp
      · exact hσ0
    by_cases hμi : IsIso μ
    · have hax := eq_of_isIso hμi
      have hirr : IsIrreducible (inv μ ≫ D.α) := isIrreducible_iso_comp (inv μ) D.hα
      rcases D.X1 hM hMo _ hirr with ⟨g, hg⟩ | ⟨g, hg⟩
      · rcases hirr.2.2 _ D.γ g hg.symm with h' | h'
        · exact D.hγ.2.1 h'
        · exact D.no_loop_y hρ (inv g ≫ D.α) (isIrreducible_iso_comp _ D.hα)
      · rcases hirr.2.2 _ D.δ g hg.symm with h' | h'
        · exact D.hδ.2.1 h'
        · exact D.no_loop_y hρ (inv g ≫ D.β) (isIrreducible_iso_comp _ D.hβ)
    · have hν0 : μ ≫ rpow π j ≠ 0 := fun h0 ↦ hσ0 (by
        rw [hσ', hπμ]; rw [hπμ] at hσm
        calc (D.γ ≫ μ) ≫ rpow (D.γ ≫ μ) (j + 1) = D.γ ≫ D.η := by rw [← hπμ, ← hσ']
          _ = D.γ ≫ μ ≫ D.γ ≫ (μ ≫ rpow π j) := by rw [hημ]
          _ = 0 := by rw [h0]; simp)
      exact D.three_arrows hM μ (μ ≫ rpow π j) hμi hν0 (not_isIso_comp_left' _ hμi) hημ
  · exact D.nL' ⟨h ≫ r ≫ rpow π (j + 1), by rw [← Category.assoc, hh, ← Category.assoc, ← hr, hσ']⟩

end DiamondData

end RayCat

end LargeIndecomposable
