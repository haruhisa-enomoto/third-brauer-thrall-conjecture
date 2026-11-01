module

public import LargeIndecomposable.MildContours.Diamonds.Data

/-!
# Diamond closure facts, first part

For diamond data `D` (`DiamondData`), with `τ = γ α ω' α`:
* `crownE`: no `θ` with `δ ≫ θ = γ ≫ η ≫ δ` (the crown `Ã(α, ηδ, θ, β)`, [mild] PD).
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

namespace DiamondData

variable (D : DiamondData P)

/-- The killed morphism `τ = γ α ω' α`. -/
abbrev τ : D.x ⟶ D.y := D.γ ≫ D.α ≫ D.ω' ≫ D.α

lemma τ_ηδ : D.τ = D.γ ≫ D.η ≫ D.δ ≫ D.β := by
  change D.γ ≫ D.α ≫ D.ω' ≫ D.α = _; rw [D.τ_eq, D.hval]

lemma τ_w : D.τ = D.δ ≫ D.β ≫ D.ω' ≫ D.α := by
  change D.γ ≫ D.α ≫ D.ω' ≫ D.α = _
  rw [← Category.assoc D.γ, D.hval]; simp

lemma τ_η : D.τ = D.γ ≫ D.η ≫ D.γ ≫ D.α := D.τ_eq

lemma τ_ne_zero : D.τ ≠ 0 := D.hτ0

lemma τ_not_isIso : ¬IsIso D.τ := not_isIso_comp_left' _ D.hγ.2.1

lemma ηω : D.η ≫ D.γ ≫ D.α = D.α ≫ D.ω' ≫ D.α := by
  rw [← Category.assoc, ← D.hD]; simp

lemma op_τ : D.op.τ = D.τ.op := by
  change D.α.op ≫ D.γ.op ≫ D.η.op ≫ D.γ.op = (D.γ ≫ D.α ≫ D.ω' ≫ D.α).op
  rw [D.τ_eq]; simp

/-- An arrow does not factor through `τ`. -/
lemma irr_not_ftm' {c d : P} (e : c ⟶ d) (he : IsIrreducible e) :
    ¬FactorsThroughMorphism D.τ e := by
  rintro ⟨u, v, rfl⟩
  rcases he.2.2 _ (u ≫ D.γ) (D.α ≫ D.ω' ≫ D.α ≫ v) (by simp) with h | h
  · exact D.hγ.2.1 (ray_isIso_factors u D.γ).2
  · exact D.hα.2.1 (ray_isIso_factors D.α (D.ω' ≫ D.α ≫ v)).1

/-- **No `δ ≫ θ = γ ≫ η ≫ δ`**: the crown `Ã(α, ηδ, θ, β)`. -/
theorem crownE (hM : MildHyp k P) : ¬∃ θ, D.δ ≫ θ = D.γ ≫ D.η ≫ D.δ := by
  rintro ⟨θ, hθ⟩
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hτ0 := D.τ_ne_zero
  have hγηδ : D.γ ≫ D.η ≫ D.δ ≠ 0 := fun h ↦ hτ0 (by
    rw [D.τ_ηδ, show D.γ ≫ D.η ≫ D.δ ≫ D.β = (D.γ ≫ D.η ≫ D.δ) ≫ D.β by simp, h, zero_comp])
  have hδθ : D.δ ≫ θ ≠ 0 := by rw [hθ]; exact hγηδ
  have hηn := D.hη
  have hδn := D.hδ.2.1
  have hγη : D.γ ≫ D.η ≠ 0 := fun h ↦ hγηδ (by rw [← Category.assoc, h, zero_comp])
  -- `θ` is not invertible
  have hθn : ¬IsIso θ := by
    intro h
    obtain ⟨hh, he⟩ := RayQuiver.eq_id_of_isIso θ
    rw [he, eqToHom_refl, Category.comp_id] at hθ
    rcases D.hδ.2.2 _ D.γ (D.η ≫ D.δ) hθ with h1 | h1
    · exact D.hγ.2.1 h1
    · exact hηn (ray_isIso_factors D.η D.δ).1
  refine hM.not_crown2 D.τ D.τ_not_isIso hτ0 D.α D.β θ (D.η ≫ D.δ)
    (nfp hτ0 D.γ D.α (D.ω' ≫ D.α) (Or.inl D.hγ.2.1) rfl)
    (nfp hτ0 D.δ D.β (D.ω' ≫ D.α) (Or.inl hδn) D.τ_w.symm) ?_
    (nfp hτ0 D.γ (D.η ≫ D.δ) D.β (Or.inl D.hγ.2.1) (by rw [D.τ_ηδ]; simp))
    D.apβα D.apαβ ?_ ?_ ?_ ?_ ?_ D.nC'
  · rintro ⟨u, v, huv⟩
    have e : D.τ = (D.δ ≫ u) ≫ D.τ ≫ (v ≫ D.β) := by
      conv_lhs => rw [D.τ_ηδ, show D.γ ≫ D.η ≫ D.δ ≫ D.β = (D.γ ≫ D.η ≫ D.δ) ≫ D.β by simp,
        ← hθ, huv]
      simp
    obtain ⟨-, h⟩ := IsRayCategory.eq_id_of_two_sided _ hτ0 _ _ e
    have : IsIso (v ≫ D.β) := by rw [h]; infer_instance
    exact D.hβ.2.1 (ray_isIso_factors v D.β).2
  · rintro ⟨c, hc⟩
    have e : (D.δ ≫ c ≫ D.η) ≫ D.δ = (D.γ ≫ D.η) ≫ D.δ := by
      rw [Category.assoc, Category.assoc, hc, hθ]; simp
    have e2 := hR _ _ _ e (by rw [e]; simpa using hγηδ)
    have e3 : (D.δ ≫ c) ≫ D.η = D.γ ≫ D.η := by rw [Category.assoc]; exact e2
    exact D.apδγ ⟨c, hR _ _ _ e3 (by rw [e3]; exact hγη)⟩
  · rintro ⟨c, hc⟩
    have e : (D.γ ≫ c) ≫ θ = D.δ ≫ θ := by rw [Category.assoc, hc, hθ]
    exact D.apγδ ⟨c, hR _ _ _ e (by rw [e]; exact hδθ)⟩
  · rintro ⟨c, hc⟩
    have e : D.γ ≫ (D.α ≫ c) = D.γ ≫ (D.η ≫ D.δ) := by
      rw [← Category.assoc, D.hval, Category.assoc, hc, hθ]
    exact D.nC' ⟨c, hL _ _ _ e (by rw [e]; exact hγηδ)⟩
  · rintro ⟨c, hc⟩
    have e : D.γ ≫ (D.η ≫ D.δ ≫ c) = D.γ ≫ D.α := by
      rw [D.hval, ← hc, ← Category.assoc D.δ, hθ]; simp
    have e2 := hL _ _ _ e (by rw [e]; intro h0; apply hτ0
                              rw [show D.τ = (D.γ ≫ D.α) ≫ D.ω' ≫ D.α by simp, h0, zero_comp])
    rcases D.hα.2.2 _ D.η (D.δ ≫ c) e2.symm with h | h
    · exact hηn h
    · exact hδn (ray_isIso_factors D.δ c).1
  · rintro ⟨c, hc⟩
    rcases D.hα.2.2 _ D.η (D.δ ≫ c) (by rw [← hc]; simp) with h | h
    · exact hηn h
    · exact hδn (ray_isIso_factors D.δ c).1



/-- No `g ≫ β = β ≫ ρ` (else `δ ≫ g = γ ≫ η ≫ δ`). -/
lemma no_βρ (hM : MildHyp k P) : ¬∃ g, g ≫ D.β = (D.β ≫ D.ω') ≫ D.α := by
  rintro ⟨g, hg⟩
  apply D.crownE hM
  refine ⟨g, hM.right _ _ D.β ?_ ?_⟩
  · rw [Category.assoc, hg]; simp only [Category.assoc]; rw [← D.τ_w, D.τ_ηδ]
  · rw [Category.assoc, hg]; simp only [Category.assoc]; rw [← D.τ_w]; exact D.τ_ne_zero

end DiamondData

end RayCat

end LargeIndecomposable
