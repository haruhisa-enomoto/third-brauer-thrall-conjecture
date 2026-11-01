module

public import LargeIndecomposable.MildContours.Diamonds.Closure5
public import LargeIndecomposable.Cleaving.Shapes.ShapeDM5C
public import LargeIndecomposable.Cleaving.Shapes.ShapeDM5D

/-!
# Diamond closure facts: inside `η` and `ω'`

* `t_le_two`: `ω'` has at most two arrows (`s_le_two` for the dual diamond).
* `X6`: with `ω' = ω₁ ω₂`, after `ω ω₁` only `ω₂` (a `D̃₅`).
* `X5`: with `η = η₁ η₂`, after `γ η₁` only `η₂` ([mild] figure 4.9, first diagram; the
  condition `α g = η₁ φ` by `X4`, `X6` and `bhv85`).
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

/-- **`ω'` has at most two arrows.** -/
theorem t_le_two (hMo : MildHyp k Pᵒᵖ) {d₁ d₂ : P} (e₁ : D.y ⟶ d₁) (e₂ : d₁ ⟶ d₂)
    (r : d₂ ⟶ D.a) (he₁ : IsIrreducible e₁) (he₂ : IsIrreducible e₂) (hr : ¬IsIso r)
    (hω : D.ω' = e₁ ≫ e₂ ≫ r) : False := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  exact D.op.s_le_two hMo r.op e₂.op e₁.op (fun h ↦ hr ((isIso_op_iff r).1 h))
    ((isIrreducible_op e₂).2 he₂) ((isIrreducible_op e₁).2 he₁)
    (by change D.ω'.op = _; rw [hω, op_comp, op_comp, Category.assoc]; exact rfl)

/-- **After `ω ω₁`, only `ω₂`.** -/
theorem X6 (hM : MildHyp k P) {d z : P} (ω₁ : D.y ⟶ d) (ω₂ : d ⟶ D.a) (k₁ : IsIrreducible ω₁)
    (k₂ : IsIrreducible ω₂) (hω : D.ω' = ω₁ ≫ ω₂) (φ : d ⟶ z) (hφ : IsIrreducible φ)
    (h0 : ¬FactorsThroughMorphism D.τ ((D.γ ≫ D.α) ≫ ω₁ ≫ φ)) : ∃ h, ω₂ ≫ h = φ := by
  by_contra hne
  have hτ0 := D.τ_ne_zero
  have n2 : ¬∃ g, φ ≫ g = ω₂ := by
    rintro ⟨g, hg⟩
    rcases k₂.2.2 _ φ g hg.symm with h | h
    · exact hφ.2.1 h
    · exact hne ⟨inv g, by rw [← hg]; simp⟩
  have hτ1 : D.τ = D.γ ≫ D.α ≫ ω₁ ≫ ω₂ ≫ D.α := by
    change D.γ ≫ D.α ≫ D.ω' ≫ D.α = _; rw [hω]; simp
  have hτ2 : D.τ = D.δ ≫ D.β ≫ ω₁ ≫ ω₂ ≫ D.α := by rw [D.τ_w, hω]; simp
  have hγn := D.hγ.2.1
  have hδn := D.hδ.2.1
  exact hM.not_dm5d D.τ D.τ_not_isIso hτ0 D.α D.β ω₁ ω₂ φ
    (D.irr_not_ftm' ω₁ k₁)
    (nfp hτ0 (D.γ ≫ D.α) (ω₁ ≫ ω₂) D.α (Or.inl (not_isIso_comp_left' _ hγn)) (by rw [hτ1]; simp))
    (fun h ↦ h0 (by simpa using ftm_comp_left h (D.γ ≫ D.α)))
    (D.irr_not_ftm' ω₂ k₂) (D.irr_not_ftm' φ hφ) (D.irr_not_ftm' D.α D.hα)
    (nfp hτ0 D.γ (D.α ≫ ω₁) (ω₂ ≫ D.α) (Or.inl hγn) (by rw [hτ1]; simp))
    (nfp hτ0 D.γ ((D.α ≫ ω₁) ≫ ω₂) D.α (Or.inl hγn) (by rw [hτ1]; simp))
    (fun h ↦ h0 (by simpa using ftm_comp_left h D.γ))
    (D.irr_not_ftm' D.β D.hβ)
    (nfp hτ0 D.δ (D.β ≫ ω₁) (ω₂ ≫ D.α) (Or.inl hδn) (by rw [hτ2]; simp))
    (nfp hτ0 D.δ ((D.β ≫ ω₁) ≫ ω₂) D.α (Or.inl hδn) (by rw [hτ2]; simp))
    (fun h ↦ h0 (by rw [D.hval]; simpa using ftm_comp_left h D.δ))
    D.hα.2.1 D.hβ.2.1 k₁.2.1 k₂.2.1 hφ.2.1 hne n2 D.apαβ D.apβα

/-- **After `γ η₁`, only `η₂`** ([mild] figure 4.9, first diagram). -/
theorem X5 (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {c z : P} (η₁ : D.a ⟶ c) (η₂ : c ⟶ D.x)
    (h₁ : IsIrreducible η₁) (h₂ : IsIrreducible η₂) (hη : D.η = η₁ ≫ η₂) (φ : c ⟶ z)
    (hφ : IsIrreducible φ) (h0 : ¬FactorsThroughMorphism D.τ (D.γ ≫ η₁ ≫ φ)) :
    ∃ h, η₂ ≫ h = φ := by
  by_contra hne
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hτ0 := D.τ_ne_zero
  have hγn := D.hγ.2.1
  have n2 : ¬∃ g, φ ≫ g = η₂ := by
    rintro ⟨g, hg⟩
    rcases h₂.2.2 _ φ g hg.symm with h | h
    · exact hφ.2.1 h
    · exact hne ⟨inv g, by rw [← hg]; simp⟩
  have n1 : ¬∃ g, D.α ≫ g = η₁ := fun ⟨g, hg⟩ ↦ D.nB' ⟨g ≫ η₂, by rw [← Category.assoc, hg, hη]⟩
  have n3 : ¬∃ g, η₁ ≫ g = D.α := by
    rintro ⟨g, hg⟩
    rcases D.hα.2.2 _ η₁ g hg.symm with h | h
    · exact h₁.2.1 h
    · exact D.nB' ⟨inv g ≫ η₂, by rw [hη, ← hg]; simp⟩
  have hη₁φ0 : η₁ ≫ φ ≠ 0 := fun h ↦ h0 (by rw [h]; exact ⟨0, 0, by simp⟩)
  -- the condition `α ≫ g = η₁ ≫ φ`
  have key : ∀ g : D.y ⟶ z, (∃ g', g = D.ω' ≫ g') → D.α ≫ g = η₁ ≫ φ → False := by
    rintro g ⟨g', rfl⟩ hg
    have e : η₁ ≫ (η₂ ≫ D.γ ≫ g') = η₁ ≫ φ := by
      rw [← hg, ← Category.assoc D.α, D.hD, hη]; simp
    have e2 := hL _ _ _ e (by rw [e]; exact hη₁φ0)
    rcases hφ.2.2 _ η₂ (D.γ ≫ g') e2.symm with h | h
    · exact h₂.2.1 h
    · exact hγn (ray_isIso_factors D.γ g').1
  have hard : ¬∃ g, D.α ≫ g = η₁ ≫ φ := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hη₁φ0 (by rw [← hg, h, comp_zero])
    by_cases hgi : IsIso g
    · rcases D.hα.2.2 _ η₁ (φ ≫ inv g) (by rw [← Category.assoc, ← hg]; simp) with h | h
      · exact h₁.2.1 h
      · exact hφ.2.1 (ray_isIso_factors φ (inv g)).1
    obtain ⟨d, e, g', he, hge⟩ := exists_first_arrow' g hg0 hgi
    have h0e : ¬FactorsThroughMorphism D.τ ((D.γ ≫ D.α) ≫ e) := by
      intro h; apply h0
      rw [← hg, hge]; simpa using ftm_comp_right h g'
    obtain ⟨h, hh⟩ := D.X4 hM e he h0e
    by_cases hi : IsIrreducible D.ω'
    · rcases hi.2.2 _ e h hh.symm with h' | h'
      · exact he.2.1 h'
      · exact key g ⟨inv h ≫ g', by rw [hge, ← hh]; simp⟩ hg
    · have hhn : ¬IsIso h := fun h' ↦ hi (by rw [← hh]; exact isIrreducible_comp_iso he h)
      by_cases hhi : IsIrreducible h
      · by_cases hg'i : IsIso g'
        · exact D.bhv85 hM η₁ η₂ e h h₁ h₂ he hhi hη hh.symm (φ ≫ inv g')
            (by rw [← Category.assoc, ← hg, hge]; simp)
        have hg'0 : g' ≠ 0 := fun h' ↦ hg0 (by rw [hge, h', comp_zero])
        obtain ⟨d', e₂, g'', he₂, hg''⟩ := exists_first_arrow' g' hg'0 hg'i
        obtain ⟨h₃, hh₃⟩ := D.X6 hM e h he hhi hh.symm e₂ he₂ (by
          intro h'; apply h0
          rw [← hg, hge, hg'']; simpa using ftm_comp_right h' g'')
        rcases he₂.2.2 _ h h₃ hh₃.symm with h' | h'
        · exact hhn h'
        · exact key g ⟨h₃ ≫ g'', by rw [hge, hg'', ← hh₃, ← hh]; simp⟩ hg
      · -- `ω'` would have three arrows
        have hh0 : h ≠ 0 := fun h' ↦ D.hω' (by
          exfalso; apply hτ0; change D.γ ≫ D.α ≫ D.ω' ≫ D.α = 0; rw [← hh, h']; simp)
        obtain ⟨d', e₂, r, he₂, hr⟩ := exists_first_arrow' h hh0 hhn
        have hrn : ¬IsIso r := fun h' ↦ hhi (by rw [hr]; exact isIrreducible_comp_iso he₂ r)
        exact D.t_le_two hMo e e₂ r he he₂ hrn (by rw [← hh, hr])
  have hτ1 : D.τ = D.γ ≫ η₁ ≫ η₂ ≫ D.γ ≫ D.α := by rw [D.τ_η, hη]; simp
  have hγη₁ := not_isIso_comp_left' η₁ hγn
  exact hM.not_dm5c D.τ D.τ_not_isIso hτ0 D.γ D.α η₁ η₂ φ
    (D.irr_not_ftm' D.α D.hα) (D.irr_not_ftm' η₁ h₁)
    (nfp hτ0 D.γ (η₁ ≫ η₂) (D.γ ≫ D.α) (Or.inl hγn) (by rw [hτ1]; simp))
    (fun h ↦ h0 (ftm_comp_left h D.γ))
    (D.irr_not_ftm' η₂ h₂) (D.irr_not_ftm' φ hφ) (D.irr_not_ftm' D.γ D.hγ)
    (nfp hτ0 (𝟙 _) (D.γ ≫ D.α) (D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hω')) (by simp))
    (nfp hτ0 (𝟙 _) (D.γ ≫ η₁) (η₂ ≫ D.γ ≫ D.α)
      (Or.inr (not_isIso_comp_left' _ h₂.2.1)) (by rw [hτ1]; simp))
    (nfp hτ0 (𝟙 _) ((D.γ ≫ η₁) ≫ η₂) (D.γ ≫ D.α) (Or.inr (not_isIso_comp_left' _ hγn))
      (by rw [hτ1]; simp))
    (by simpa using h0)
    hγn D.hα.2.1 h₁.2.1 h₂.2.1 hφ.2.1 n1 (fun ⟨g, hg⟩ ↦ D.nB' ⟨g, by rw [hg, hη]⟩) hard n3 hne n2

end DiamondData

end RayCat

end LargeIndecomposable
