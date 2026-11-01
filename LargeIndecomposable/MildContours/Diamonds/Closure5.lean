module

public import LargeIndecomposable.MildContours.Diamonds.Closure3
public import LargeIndecomposable.Cleaving.Families.FamMD47
public import LargeIndecomposable.Cleaving.Families.FamMB85

/-!
# Diamond closure facts: the lengths of `η` and `ω'`

* `s_le_two`: `η` has at most two arrows ([mild] figure 4.7, part: `MD47`); dually
  for `ω'`.
* `bhv85`: if `η = η₁ η₂` and `ω' = ω₁ ω₂` (arrows), then `η₁ ≫ ξ = α ≫ ω₁` is impossible
  (BHV list number 85, [mild] figure 4.8, first diagram; the condition
  `g ≫ ξ = β ≫ ω₁` by the crown `Ã(β, g, η₁, α)`).
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

lemma αω'_ne_zero : D.α ≫ D.ω' ≠ 0 := fun h ↦ D.τ_ne_zero (by
  change D.γ ≫ D.α ≫ D.ω' ≫ D.α = 0; rw [← Category.assoc D.α, h]; simp)

/-- **`η` has at most two arrows** ([mild] figure 4.7, part). -/
theorem s_le_two (hM : MildHyp k P) {c₁ c₂ : P} (η' : D.a ⟶ c₁) (e₁ : c₁ ⟶ c₂) (e₂ : c₂ ⟶ D.x)
    (hη' : ¬IsIso η') (he₁ : IsIrreducible e₁) (he₂ : IsIrreducible e₂)
    (hη : D.η = η' ≫ e₁ ≫ e₂) : False := by
  have hR : RightCancel P := hM.right
  have hτ0 := D.τ_ne_zero
  have hγη' := not_isIso_comp_left' η' D.hγ.2.1
  have hγη'e₁ := not_isIso_comp_left' e₁ hγη'
  have hτ1 : D.τ = (D.γ ≫ η') ≫ ((e₁ ≫ e₂) ≫ D.γ) ≫ D.α := by rw [D.τ_η, hη]; simp
  have hτ2 : D.τ = (D.γ ≫ η') ≫ ((e₁ ≫ e₂) ≫ D.δ) ≫ D.β := by rw [D.τ_ηδ, hη]; simp
  have hαω := D.αω'_ne_zero
  have hD' : η' ≫ e₁ ≫ e₂ ≫ D.γ = D.α ≫ D.ω' := by rw [D.hD, hη]; simp
  refine hM.not_md47 D.τ D.τ_not_isIso hτ0 D.β D.ω' e₁ e₂ D.γ D.δ D.α D.β
    MD47.not_isRepresentationFinite (by simp [D.hval]) (by simp [D.hval]) D.hval.symm
    (D.irr_not_ftm' D.α D.hα) (D.irr_not_ftm' D.β D.hβ)
    (nfp hτ0 D.δ (D.β ≫ D.ω') D.α (Or.inl D.hδ.2.1) (by rw [D.τ_w]; simp))
    (nfp hτ0 D.δ ((D.β ≫ D.ω') ≫ D.α) (𝟙 _) (Or.inl D.hδ.2.1) (by rw [D.τ_w]; simp))
    (D.irr_not_ftm' D.β D.hβ)
    (nfp hτ0 (D.γ ≫ η') ((e₁ ≫ e₂) ≫ D.γ) D.α (Or.inl hγη') hτ1.symm)
    (nfp hτ0 (D.γ ≫ η') ((e₁ ≫ e₂) ≫ D.δ) D.β (Or.inl hγη') hτ2.symm)
    (D.irr_not_ftm' e₁ he₁)
    (nfp hτ0 (D.γ ≫ η') (e₁ ≫ e₂) (D.γ ≫ D.α) (Or.inl hγη') (by rw [hτ1]; simp))
    (nfp hτ0 (D.γ ≫ η') (((e₁ ≫ e₂) ≫ D.γ) ≫ D.α) (𝟙 _) (Or.inl hγη') (by rw [hτ1]; simp))
    (nfp hτ0 (D.γ ≫ η' ≫ e₁) (e₂ ≫ D.γ) D.α (Or.inl (by simpa using hγη'e₁)) (by rw [hτ1]; simp))
    (nfp hτ0 (D.γ ≫ η' ≫ e₁) (e₂ ≫ D.δ) D.β (Or.inl (by simpa using hγη'e₁)) (by rw [hτ2]; simp))
    (D.irr_not_ftm' e₂ he₂)
    (nfp hτ0 (D.γ ≫ η' ≫ e₁) ((e₂ ≫ D.γ) ≫ D.α) (𝟙 _) (Or.inl (by simpa using hγη'e₁))
      (by rw [hτ1]; simp))
    (D.irr_not_ftm' D.γ D.hγ) (D.irr_not_ftm' D.δ D.hδ)
    (nfp hτ0 (𝟙 _) (D.γ ≫ D.α) (D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hω')) (by simp))
    (nfp hτ0 (D.γ ≫ D.α) D.ω' D.α (Or.inl (not_isIso_comp_left' _ D.hγ.2.1)) (by simp))
    (nfp hτ0 (D.γ ≫ D.α) (D.ω' ≫ D.α) (𝟙 _) (Or.inl (not_isIso_comp_left' _ D.hγ.2.1))
      (by simp))
    D.hβ.2.1 D.hω' he₁.2.1 he₂.2.1 D.hγ.2.1 D.hδ.2.1 D.hα.2.1 D.hβ.2.1
    D.apγδ D.apδγ D.apαβ (D.no_βρ hM) D.nL D.apβα D.nC D.nB ?_ ?_ D.nA
  · rintro ⟨g, hg⟩
    have e : (η' ≫ g) ≫ D.ω' = D.α ≫ D.ω' := by rw [Category.assoc, hg, ← hD']; simp
    have e2 := hR _ _ _ e (by rw [e]; exact hαω)
    rcases D.hα.2.2 _ η' g e2.symm with h | h
    · exact hη' h
    · exact D.nB' ⟨inv g ≫ e₁ ≫ e₂, by rw [hη, ← e2]; simp⟩
  · rintro ⟨g, hg⟩
    have e : (η' ≫ e₁ ≫ g) ≫ D.ω' = D.α ≫ D.ω' := by
      rw [Category.assoc, Category.assoc, hg, ← hD']
    have e2 := hR _ _ _ e (by rw [e]; exact hαω)
    rcases D.hα.2.2 _ η' (e₁ ≫ g) e2.symm with h | h
    · exact hη' h
    · exact he₁.2.1 (ray_isIso_factors e₁ g).1

/-- **BHV number 85**: with `η = η₁ η₂` and `ω' = ω₁ ω₂` (arrows), no `ξ` with
`η₁ ≫ ξ = α ≫ ω₁`. -/
theorem bhv85 (hM : MildHyp k P) {c d : P} (η₁ : D.a ⟶ c) (η₂ : c ⟶ D.x) (ω₁ : D.y ⟶ d)
    (ω₂ : d ⟶ D.a) (h₁ : IsIrreducible η₁) (h₂ : IsIrreducible η₂) (k₁ : IsIrreducible ω₁)
    (k₂ : IsIrreducible ω₂) (hη : D.η = η₁ ≫ η₂) (hω : D.ω' = ω₁ ≫ ω₂) (ξ : c ⟶ d)
    (hξ : η₁ ≫ ξ = D.α ≫ ω₁) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hτ0 := D.τ_ne_zero
  have hαω := D.αω'_ne_zero
  have hD' : η₁ ≫ η₂ ≫ D.γ = D.α ≫ ω₁ ≫ ω₂ := by rw [← Category.assoc, ← hη, ← D.hD, hω]
  have hc3 : η₂ ≫ D.γ = ξ ≫ ω₂ := by
    apply hL η₁
    · rw [hD', ← Category.assoc η₁, hξ, Category.assoc]
    · rw [hD', ← hω]; exact hαω
  have hτ1 : D.τ = D.γ ≫ η₁ ≫ η₂ ≫ D.γ ≫ D.α := by rw [D.τ_η, hη]; simp
  have hτ2 : D.τ = D.γ ≫ η₁ ≫ ξ ≫ ω₂ ≫ D.α := by
    rw [hτ1, ← Category.assoc η₂, hc3]; simp
  have hτ3 : D.τ = D.γ ≫ D.α ≫ ω₁ ≫ ω₂ ≫ D.α := by
    change D.γ ≫ D.α ≫ D.ω' ≫ D.α = _; rw [hω]; simp
  have hτ4 : D.τ = D.δ ≫ D.β ≫ ω₁ ≫ ω₂ ≫ D.α := by rw [D.τ_w, hω]; simp
  have hτ5 : D.τ = D.γ ≫ η₁ ≫ η₂ ≫ D.δ ≫ D.β := by rw [D.τ_ηδ, hη]; simp
  have hγn := D.hγ.2.1
  have hγη₁ := not_isIso_comp_left' η₁ hγn
  have hξn : ¬IsIso ξ := by
    intro h
    rcases h₁.2.2 _ D.α (ω₁ ≫ inv ξ) (by rw [← Category.assoc, ← hξ]; simp) with h' | h'
    · exact D.hα.2.1 h'
    · exact k₁.2.1 (ray_isIso_factors ω₁ (inv ξ)).1
  have hξ0 : η₁ ≫ ξ ≠ 0 := by rw [hξ]; intro h0; apply hαω; rw [hω, ← Category.assoc, h0]; simp
  -- `α g = η₁` and `η₁ g = α` are impossible
  have n1 : ¬∃ g, D.α ≫ g = η₁ := fun ⟨g, hg⟩ ↦ D.nB' ⟨g ≫ η₂, by rw [← Category.assoc, hg, hη]⟩
  have n2 : ¬∃ g, η₁ ≫ g = D.α := by
    rintro ⟨g, hg⟩
    rcases D.hα.2.2 _ η₁ g hg.symm with h | h
    · exact h₁.2.1 h
    · exact D.nB' ⟨inv g ≫ η₂, by rw [hη, ← hg]; simp⟩
  have n3 : ¬∃ g, g ≫ ω₁ = ξ := by
    rintro ⟨g, hg⟩
    exact n2 ⟨g, hR _ _ _ (show (η₁ ≫ g) ≫ ω₁ = D.α ≫ ω₁ by rw [Category.assoc, hg, hξ])
      (by rw [Category.assoc, hg, hξ, ← hξ]; exact hξ0)⟩
  have n4 : ¬∃ g, g ≫ ξ = ω₁ := by
    rintro ⟨g, hg⟩
    exact n1 ⟨g, hR _ _ _ (show (D.α ≫ g) ≫ ξ = η₁ ≫ ξ by rw [Category.assoc, hg, hξ])
      (by rw [Category.assoc, hg, ← hξ]; exact hξ0)⟩
  have n5 : ¬∃ g, η₂ ≫ g = ξ := by
    rintro ⟨g, hg⟩
    have e : (η₁ ≫ η₂) ≫ (g ≫ ω₂) = (η₁ ≫ η₂) ≫ D.γ := by
      rw [← Category.assoc, Category.assoc η₁, hg, hξ]; simp [hD']
    have e2 := hL _ _ _ e (by rw [e, ← hη, ← D.hD]; exact hαω)
    rcases D.hγ.2.2 _ g ω₂ e2.symm with h | h
    · exact D.nB ⟨ω₁ ≫ inv g, by rw [hω, Category.assoc, ← e2]; simp⟩
    · exact k₂.2.1 h
  refine hM.not_mb85 D.τ D.τ_not_isIso hτ0 η₁ η₂ D.δ D.β ω₁ ω₂ D.α ξ D.γ
    MB85.not_isRepresentationFinite hD' (by rw [← Category.assoc D.α, ← hξ, Category.assoc]) hξ hc3
    (nfp hτ0 D.γ ((D.α ≫ ω₁) ≫ ω₂) D.α (Or.inl hγn) (by rw [hτ3]; simp))
    (nfp hτ0 D.γ ((η₁ ≫ η₂) ≫ D.δ) D.β (Or.inl hγn) (by rw [hτ5]; simp))
    (D.irr_not_ftm' η₁ h₁)
    (nfp hτ0 D.γ (D.α ≫ ω₁) (ω₂ ≫ D.α) (Or.inl hγn) (by rw [hτ3]; simp))
    (nfp hτ0 D.γ (η₁ ≫ η₂) (D.γ ≫ D.α) (Or.inl hγn) (by rw [hτ1]; simp))
    (D.irr_not_ftm' D.α D.hα)
    (nfp hτ0 D.δ ((D.β ≫ ω₁) ≫ ω₂) D.α (Or.inl D.hδ.2.1) (by rw [hτ4]; simp))
    (nfp hτ0 D.δ (D.β ≫ ω₁) (ω₂ ≫ D.α) (Or.inl D.hδ.2.1) (by rw [hτ4]; simp))
    (D.irr_not_ftm' D.β D.hβ)
    (nfp hτ0 (D.γ ≫ η₁) (ξ ≫ ω₂) D.α (Or.inl hγη₁) (by rw [hτ2]; simp))
    (nfp hτ0 (D.γ ≫ η₁) (η₂ ≫ D.δ) D.β (Or.inl hγη₁) (by rw [hτ5]; simp))
    (nfp hτ0 (D.γ ≫ η₁) ξ (ω₂ ≫ D.α) (Or.inl hγη₁) (by rw [hτ2]; simp))
    (D.irr_not_ftm' η₂ h₂) (D.irr_not_ftm' ω₂ k₂) (D.irr_not_ftm' D.γ D.hγ)
    (D.irr_not_ftm' D.δ D.hδ)
    (nfp hτ0 (D.γ ≫ D.α) (ω₁ ≫ ω₂) D.α (Or.inl (not_isIso_comp_left' _ hγn)) (by rw [hτ3]; simp))
    (D.irr_not_ftm' ω₁ k₁)
    h₁.2.1 h₂.2.1 D.hδ.2.1 D.hβ.2.1 k₁.2.1 k₂.2.1 D.hα.2.1 hξn hγn
    n2 n1 (fun ⟨g, hg⟩ ↦ D.nB' ⟨g, by rw [hg, hη]⟩) (fun ⟨g, hg⟩ ↦ D.nC' ⟨g, by rw [hg, hη]⟩)
    ?_ ?_ n5 D.apγδ D.apδγ D.apαβ D.apβα ?_ n4 ?_
    (fun ⟨g, hg⟩ ↦ D.nC ⟨g, by rw [hg, hω]; simp⟩) (fun ⟨g, hg⟩ ↦ D.nB ⟨g, by rw [hg, hω]⟩)
    (fun ⟨g, hg⟩ ↦ D.nB ⟨ω₁ ≫ g, by rw [Category.assoc, hg, hω]⟩) n3
  · -- `ξ ≫ g = η₂`
    rintro ⟨g, hg⟩
    have e : (η₁ ≫ ξ) ≫ (g ≫ D.γ) = (η₁ ≫ ξ) ≫ ω₂ := by
      rw [← Category.assoc, Category.assoc η₁, hg, Category.assoc, hc3]; simp
    have e2 := hL _ _ _ e (by rw [e, hξ, Category.assoc, ← hω]; exact hαω)
    exact D.nB ⟨ω₁ ≫ g, by rw [Category.assoc, e2, hω]⟩
  · -- `ξ ≫ g = η₂ ≫ δ`
    rintro ⟨g, hg⟩
    exact D.nC' ⟨ω₁ ≫ g, by rw [← Category.assoc, ← hξ, Category.assoc, hg, hη]; simp⟩
  · -- `g ≫ ξ = β ≫ ω₁`: the crown `Ã(β, g, η₁, α)`
    rintro ⟨g, hg⟩
    have hgξ : g ≫ ξ ≠ 0 := by rw [hg]; intro h0; apply hτ0; rw [hτ4, ← Category.assoc D.β, h0]; simp
    refine hM.not_crown2 D.τ D.τ_not_isIso hτ0 D.β D.α η₁ g (D.irr_not_ftm' D.β D.hβ)
      (D.irr_not_ftm' D.α D.hα) (D.irr_not_ftm' η₁ h₁) ?_ D.apαβ D.apβα ?_ ?_ n1 n2 ?_ ?_
    · rintro ⟨u, v, huv⟩
      have e : D.τ = (D.δ ≫ u) ≫ D.τ ≫ (v ≫ ξ ≫ ω₂ ≫ D.α) := by
        conv_lhs => rw [hτ4, ← Category.assoc D.β, ← hg, huv]
        simp
      obtain ⟨-, h⟩ := IsRayCategory.eq_id_of_two_sided _ hτ0 _ _ e
      have : IsIso ((v ≫ ξ ≫ ω₂) ≫ D.α) := by simp only [Category.assoc]; rw [h]; infer_instance
      exact D.hα.2.1 (ray_isIso_factors (v ≫ ξ ≫ ω₂) D.α).2
    · rintro ⟨c', hc'⟩
      exact D.apβα ⟨c', hR _ _ _ (show (c' ≫ D.β) ≫ ω₁ = D.α ≫ ω₁ by
        rw [Category.assoc, ← hg, ← Category.assoc, hc', hξ]) (by
          rw [Category.assoc, ← hg, ← Category.assoc, hc']; exact hξ0)⟩
    · rintro ⟨c', hc'⟩
      exact D.apαβ ⟨c', hR _ _ _ (show (c' ≫ D.α) ≫ ω₁ = D.β ≫ ω₁ by
        rw [Category.assoc, ← hξ, ← Category.assoc, hc', hg]) (by
          rw [Category.assoc, ← hξ, ← Category.assoc, hc', hg, ← hg]; exact hgξ)⟩
    · rintro ⟨c', hc'⟩
      exact n3 ⟨c', hL _ _ _ (show g ≫ (c' ≫ ω₁) = g ≫ ξ by
        rw [← Category.assoc, hc', hg]) (by rw [← Category.assoc, hc', ← hg]; exact hgξ)⟩
    · rintro ⟨c', hc'⟩
      exact n4 ⟨c', hL _ _ _ (show D.β ≫ (c' ≫ ξ) = D.β ≫ ω₁ by
        rw [← Category.assoc, hc', hg]) (by rw [← Category.assoc, hc', hg, ← hg]; exact hgξ)⟩

  · -- `g ≫ ω₂ = γ`
    rintro ⟨g, hg⟩
    have e : (D.η ≫ g) ≫ ω₂ = (D.α ≫ ω₁) ≫ ω₂ := by
      rw [Category.assoc, hg, ← D.hD, hω]; simp
    have e2 := hR _ _ _ e (by rw [e, Category.assoc, ← hω]; exact hαω)
    exact n5 ⟨g, hL _ _ _ (show η₁ ≫ (η₂ ≫ g) = η₁ ≫ ξ by
      rw [← Category.assoc, ← hη, e2, hξ]) (by rw [← Category.assoc, ← hη, e2, ← hξ]; exact hξ0)⟩
end DiamondData

end RayCat

end LargeIndecomposable
