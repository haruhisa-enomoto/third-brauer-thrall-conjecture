module

public import LargeIndecomposable.MildContours.Diamonds.Closure1
public import LargeIndecomposable.Cleaving.Diagrams.ToolsMod
public import LargeIndecomposable.Cleaving.Shapes.ShapeOut3

/-!
# Diamond closure facts: arrows after `γ` and after `ω`

* `X2`: an arrow `φ` out of `a` with `γ ≫ φ` nonzero in `P/τ` is `α` or begins `η`
  (the `D̃₄` star `Out3` at `a`).
* `X4`: an arrow `e` out of `y` with `ω ≫ e` nonzero in `P/τ` begins `ω'` (the `D̃₄`
  star `MD4B` at `y`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

/-- A nonzero non-invertible morphism begins with an arrow. -/
lemma exists_first_arrow' {a b : P} (f : a ⟶ b) (hf0 : f ≠ 0) (hf : ¬IsIso f) :
    ∃ (c : P) (e : a ⟶ c) (r : c ⟶ b), IsIrreducible e ∧ f = e ≫ r := by
  obtain ⟨c, e, r, hr⟩ := path_first_arrow (pathOf f hf0)
    (Nat.pos_iff_ne_zero.1 (length_pathOf_pos f hf0 hf))
  refine ⟨c.out, e.1, pathVal r, e.2, ?_⟩
  rw [← pathVal_pathOf f hf0, hr, pathVal_comp]; change (𝟙 _ ≫ e.1) ≫ _ = _; simp

namespace DiamondData

variable (D : DiamondData P)

/-- Arrows out of the same object that do not factor are apart, given that neither
factors into a fixed target through the other's continuation. -/
lemma ftm_of_comp_left {c d e : P} (f : c ⟶ d) (g : d ⟶ e)
    (h : ¬FactorsThroughMorphism D.τ (f ≫ g)) : ¬FactorsThroughMorphism D.τ g :=
  fun h' ↦ h (ftm_comp_left h' f)

/-- **After `ω`, only the first arrow of `ω'`.** -/
theorem X4 (hM : MildHyp k P) {c : P} (e : D.y ⟶ c) (he : IsIrreducible e)
    (h0 : ¬FactorsThroughMorphism D.τ ((D.γ ≫ D.α) ≫ e)) : ∃ h, e ≫ h = D.ω' := by
  by_contra hne
  have hτ0 := D.τ_ne_zero
  have hω'0 : D.ω' ≠ 0 := fun h ↦ hτ0 (by change D.γ ≫ D.α ≫ D.ω' ≫ D.α = 0; simp [h])
  obtain ⟨d, e₁, r, he₁, hr⟩ := exists_first_arrow' D.ω' hω'0 D.hω'
  have n1 : ¬∃ g, e ≫ g = e₁ := by
    rintro ⟨g, hg⟩
    exact hne ⟨g ≫ r, by rw [← Category.assoc, hg, hr]⟩
  have n2 : ¬∃ g, e₁ ≫ g = e := by
    rintro ⟨g, hg⟩
    rcases he.2.2 _ e₁ g hg.symm with h | h
    · exact he₁.2.1 h
    · exact hne ⟨inv g ≫ r, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hr]⟩
  have hτ1 : D.τ = D.γ ≫ (D.α ≫ e₁) ≫ r ≫ D.α := by
    change D.γ ≫ D.α ≫ D.ω' ≫ D.α = _; rw [hr]; simp
  have hτ2 : D.τ = D.δ ≫ (D.β ≫ e₁) ≫ r ≫ D.α := by rw [D.τ_w, hr]; simp
  exact hM.not_md4b D.τ D.τ_not_isIso hτ0 D.α D.β e₁ e
    (D.irr_not_ftm' e₁ he₁) (D.irr_not_ftm' e he) (D.irr_not_ftm' D.α D.hα)
    (nfp hτ0 D.γ (D.α ≫ e₁) (r ≫ D.α) (Or.inl D.hγ.2.1) hτ1.symm)
    (fun h ↦ h0 (by simpa using ftm_comp_left h D.γ))
    (D.irr_not_ftm' D.β D.hβ)
    (nfp hτ0 D.δ (D.β ≫ e₁) (r ≫ D.α) (Or.inl D.hδ.2.1) hτ2.symm)
    (fun h ↦ h0 (by rw [D.hval]; simpa using ftm_comp_left h D.δ))
    D.hα.2.1 D.hβ.2.1 he₁.2.1 he.2.1 n2 n1 D.apαβ D.apβα

/-- **After `γ`, only `α` and the first arrow of `η`.** -/
theorem X2 (hM : MildHyp k P) {c : P} (φ : D.a ⟶ c) (hφ : IsIrreducible φ)
    (h0 : ¬FactorsThroughMorphism D.τ (D.γ ≫ φ)) :
    (∃ h, φ ≫ h = D.α) ∨ (∃ h, φ ≫ h = D.η) := by
  by_contra hne
  push Not at hne
  obtain ⟨hn1, hn2⟩ := hne
  have hτ0 := D.τ_ne_zero
  have hη0 : D.η ≠ 0 := fun h ↦ hτ0 (by rw [D.τ_η, h]; simp)
  obtain ⟨d, e₁, r, he₁, hr⟩ := exists_first_arrow' D.η hη0 D.hη
  have nB' := D.nB'
  have a1 : ¬∃ g, D.α ≫ g = e₁ := fun ⟨g, hg⟩ ↦ nB' ⟨g ≫ r, by rw [← Category.assoc, hg, hr]⟩
  have a2 : ¬∃ g, e₁ ≫ g = D.α := by
    rintro ⟨g, hg⟩
    rcases D.hα.2.2 _ e₁ g hg.symm with h | h
    · exact he₁.2.1 h
    · exact nB' ⟨inv g ≫ r, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hr]⟩
  have a3 : ¬∃ g, D.α ≫ g = φ := by
    rintro ⟨g, hg⟩
    rcases hφ.2.2 _ D.α g hg.symm with h | h
    · exact D.hα.2.1 h
    · exact hn1 (inv g) (by rw [← hg]; simp)
  have a4 : ¬∃ g, φ ≫ g = D.α := fun ⟨g, hg⟩ ↦ hn1 g hg
  have a5 : ¬∃ g, e₁ ≫ g = φ := by
    rintro ⟨g, hg⟩
    rcases hφ.2.2 _ e₁ g hg.symm with h | h
    · exact he₁.2.1 h
    · exact hn2 (inv g ≫ r) (by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hr])
  have a6 : ¬∃ g, φ ≫ g = e₁ := fun ⟨g, hg⟩ ↦ hn2 (g ≫ r) (by rw [← Category.assoc, hg, hr])
  have hτ1 : D.τ = D.γ ≫ e₁ ≫ r ≫ D.γ ≫ D.α := by rw [D.τ_η, hr]; simp
  refine hM.not_out3 D.τ D.τ_not_isIso hτ0 D.γ D.α e₁ φ
    (D.irr_not_ftm' D.α D.hα) (D.irr_not_ftm' e₁ he₁) (D.irr_not_ftm' φ hφ)
    (D.irr_not_ftm' D.γ D.hγ)
    (nfp hτ0 (𝟙 _) (D.γ ≫ D.α) (D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hω')) (by simp))
    (nfp hτ0 (𝟙 _) (D.γ ≫ e₁) (r ≫ D.γ ≫ D.α)
      (Or.inr (not_isIso_comp_right' _ (not_isIso_comp_left' _ D.hγ.2.1))) (by rw [hτ1]; simp))
    h0 D.hγ.2.1 D.hα.2.1 he₁.2.1 hφ.2.1 a1 a3 a2 a5 a4 a6

end DiamondData

end RayCat

end LargeIndecomposable
