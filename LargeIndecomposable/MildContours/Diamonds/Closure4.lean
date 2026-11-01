module

public import LargeIndecomposable.MildContours.Diamonds.Closure1
public import LargeIndecomposable.Cleaving.Families.FamMD29C

/-!
# Diamond closure facts: after `δ`, only `β`

[mild] PD: the only arrow `ε` out of `b` with `δ ≫ ε` nonzero in `P/τ` is `β`
(figure 2.9, third diagram, a thin diagram with `ω' ≫ η = 0` in `P/τ`).
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

/-- **The only arrow `ε` out of `b` with `δ ≫ ε` nonzero in `P/τ` is `β`** ([mild] PD,
figure 2.9, third diagram). -/
theorem X3 (hM : MildHyp k P) {c : P} (ε : D.b ⟶ c) (hε : IsIrreducible ε)
    (h0 : ¬FactorsThroughMorphism D.τ (D.δ ≫ ε)) : ∃ g, D.β ≫ g = ε := by
  by_contra hne
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hτ0 := D.τ_ne_zero
  have hδε : D.δ ≫ ε ≠ 0 := fun h ↦ h0 (by rw [h]; exact ⟨0, 0, by simp⟩)
  have hne2 : ¬∃ g, ε ≫ g = D.β := by
    rintro ⟨g, hg⟩
    rcases D.hβ.2.2 _ ε g hg.symm with h | h
    · exact hε.2.1 h
    · exact hne ⟨inv g, by rw [← hg]; simp⟩
  have hcr : ¬∃ g, D.γ ≫ g = D.δ ≫ ε := by
    rintro ⟨g, hg⟩
    refine hM.not_crown2 D.τ D.τ_not_isIso hτ0 D.α D.β ε g
      (nfp hτ0 D.γ D.α (D.ω' ≫ D.α) (Or.inl D.hγ.2.1) rfl)
      (nfp hτ0 D.δ D.β (D.ω' ≫ D.α) (Or.inl D.hδ.2.1) D.τ_w.symm)
      (fun h ↦ h0 (ftm_comp_left h _)) (fun h ↦ h0 (by rw [← hg]; exact ftm_comp_left h _))
      D.apβα D.apαβ ?_ ?_ (fun ⟨c', hc'⟩ ↦ hne ⟨c', hc'⟩) hne2 ?_ ?_
    · rintro ⟨c', hc'⟩
      have e : (D.δ ≫ c') ≫ g = D.γ ≫ g := by rw [Category.assoc, hc', hg]
      exact D.apδγ ⟨c', hR _ _ _ e (by rw [e, hg]; exact hδε)⟩
    · rintro ⟨c', hc'⟩
      have e : (D.γ ≫ c') ≫ ε = D.δ ≫ ε := by rw [Category.assoc, hc', hg]
      exact D.apγδ ⟨c', hR _ _ _ e (by rw [e]; exact hδε)⟩
    · rintro ⟨c', hc'⟩
      have e : D.δ ≫ (ε ≫ c') = D.δ ≫ D.β := by
        rw [← Category.assoc, ← hg, Category.assoc, hc', D.hval]
      have hne0 : D.δ ≫ D.β ≠ 0 := by
        rw [← D.hval]; intro h0'; apply hτ0
        rw [show D.τ = (D.γ ≫ D.α) ≫ D.ω' ≫ D.α by simp, h0', zero_comp]
      exact hne2 ⟨c', hL _ _ _ e (by rw [e]; exact hne0)⟩
    · rintro ⟨c', hc'⟩
      have e : D.δ ≫ (D.β ≫ c') = D.δ ≫ ε := by
        rw [← Category.assoc, ← D.hval, Category.assoc, hc', hg]
      exact hne ⟨c', hL _ _ _ e (by rw [e]; exact hδε)⟩
  have hz := D.zero
  have hηn := D.hη
  have hγn := D.hγ.2.1
  have hδn := D.hδ.2.1
  refine hM.not_md29c D.τ D.τ_not_isIso hτ0 D.γ D.δ D.α D.β ε D.β D.ω' D.η D.δ
    MD29C.not_isRepresentationFinite D.hval.symm
    (by simpa using ftm_comp_right (ftm_comp_left hz D.β) D.δ)
    (by simpa using ftm_comp_left hz D.β)
    (by simpa using ftm_comp_right hz D.δ) hz
    (nfp hτ0 D.γ (D.η ≫ D.δ) D.β (Or.inl hγn) (by rw [D.τ_ηδ]; simp))
    (nfp hτ0 D.γ D.η (D.γ ≫ D.α) (Or.inl hγn) D.τ_η.symm)
    (nfp hτ0 D.γ D.α (D.ω' ≫ D.α) (Or.inl hγn) rfl)
    (nfp hτ0 D.δ (D.β ≫ D.ω') D.α (Or.inl hδn) (by rw [D.τ_w]; simp))
    (nfp hτ0 D.δ D.β (D.ω' ≫ D.α) (Or.inl hδn) D.τ_w.symm)
    (nfp hτ0 D.δ ((D.β ≫ D.ω') ≫ D.α) (𝟙 _) (Or.inl hδn) (by rw [D.τ_w]; simp))
    (fun h ↦ h0 (ftm_comp_left h _))
    (nfp hτ0 D.δ D.β (D.ω' ≫ D.α) (Or.inl hδn) D.τ_w.symm)
    (nfp hτ0 (D.γ ≫ D.η) D.δ D.β (Or.inl (not_isIso_comp_left' _ hγn)) (by rw [D.τ_ηδ]; simp))
    (nfp hτ0 (𝟙 _) D.γ (D.α ≫ D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hα.2.1)) (by simp))
    (nfp hτ0 (𝟙 _) ((D.γ ≫ D.η) ≫ D.δ) D.β (Or.inr D.hβ.2.1) (by rw [D.τ_ηδ]; simp))
    (nfp hτ0 (𝟙 _) D.δ (D.β ≫ D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hβ.2.1))
      (by rw [D.τ_w]; simp))
    h0
    (nfp hτ0 (𝟙 _) (D.γ ≫ D.η) (D.δ ≫ D.β) (Or.inr (not_isIso_comp_left' _ hδn))
      (by rw [D.τ_ηδ]; simp))
    (nfp hτ0 (𝟙 _) (D.γ ≫ D.α) (D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hω'))
      (by simp))
    (nfp hτ0 (D.γ ≫ D.α) D.ω' D.α (Or.inl (not_isIso_comp_left' _ hγn)) (by simp))
    (nfp hτ0 (D.γ ≫ D.α) (D.ω' ≫ D.α) (𝟙 _) (Or.inl (not_isIso_comp_left' _ hγn)) (by simp))
    hγn hδn D.hα.2.1 D.hβ.2.1 hε.2.1 D.hβ.2.1 D.hω' hηn hδn
    D.nA' D.nB' D.nC' hne2 hne D.apγδ hcr D.apδγ D.nL'
    (by simpa using D.crownE hM) D.apαβ D.apβα (D.no_βρ hM) D.nL D.nC D.nB D.nA

end DiamondData

end RayCat

end LargeIndecomposable
