module

public import LargeIndecomposable.Crowns.Section225.Split
public import LargeIndecomposable.Cleaving.Zigzags.ZigzagArmsSrc
public import LargeIndecomposable.Cleaving.Shapes.ShapeF94S

/-!
# BO13a §2.2.5: no third long morphism

Two long entries `σ (s+2)` and the next long entry, both split at one point, give a
cleaving diagram of type `D̃` in `P/τ` for any third long morphism `τ`.

* `MulBasis.b2_third`: the next long entry is `ρ (s+3+L+1)` (BO13a figure 9.4;
  `not_zigzag_arms`, or the tree `F94S` for `L = 0`).
* `MulBasis.b3_third`: the next long entry is `σ (s+3+L+1)` (BO13a figure 9.5;
  `not_zigzag_arms_src`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **No third long morphism, case `σ₁ … ρⱼ`** (BO13a figure 9.4). -/
theorem b2_third
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (Z : ZChain P) (s L : ℕ)
    (hnρ : ∀ i ≤ L, ¬IsLong (Z.ρ (s + 3 + i))) (hnσ : ∀ i ≤ L, ¬IsLong (Z.σ (s + 3 + i)))
    {a c' : P} (V₁ : Z.x (s + 3) ⟶ a) (V₂ : a ⟶ Z.z (s + 2)) (ρ₁' : a ⟶ Z.z (s + 3))
    (hV : V₁ ≫ V₂ = Z.σ (s + 2)) (hρ₁' : V₁ ≫ ρ₁' = Z.ρ (s + 3)) (hiV₁ : ¬IsIso V₁)
    (hiV₂ : ¬IsIso V₂)
    (V₁' : Z.x (s + 3 + L + 1) ⟶ c') (V₂' : c' ⟶ Z.z (s + 3 + L + 1))
    (σ' : c' ⟶ Z.z (s + 3 + L)) (hV' : V₁' ≫ V₂' = Z.ρ (s + 3 + L + 1))
    (hσ' : V₁' ≫ σ' = Z.σ (s + 3 + L)) (hiV₁' : ¬IsIso V₁') (hiV₂' : ¬IsIso V₂')
    (L8a : ¬∃ c, c ≫ ρ₁' = Z.σ (s + 3)) (L8c : ¬∃ c, c ≫ σ' = Z.ρ (s + 3 + L))
    {a' b' : P} (τ : a' ⟶ b') (hτ : IsLong τ)
    (hτ1 : ¬FactorsThroughMorphism τ (Z.σ (s + 2)))
    (hτ2 : ¬FactorsThroughMorphism τ (Z.ρ (s + 3 + L + 1))) : False := by
  have hσ0 : V₁ ≫ V₂ ≠ 0 := by rw [hV]; exact Z.σ_ne _
  have hρ0 : V₁ ≫ ρ₁' ≠ 0 := by rw [hρ₁']; exact Z.ρ_ne _
  have hlam0 : V₁' ≫ V₂' ≠ 0 := by rw [hV']; exact Z.ρ_ne _
  have hσj0 : V₁' ≫ σ' ≠ 0 := by rw [hσ']; exact Z.σ_ne _
  have hsu : ¬∃ g, ρ₁' ≫ g = V₂ := fun ⟨g, hg⟩ ↦
    Z.valley₂ (s + 2) ⟨g, by rw [← hρ₁', Category.assoc, hg, hV]⟩
  have hus : ¬∃ g, V₂ ≫ g = ρ₁' := fun ⟨g, hg⟩ ↦
    Z.valley₁ (s + 2) ⟨g, by rw [← hV, Category.assoc, hg, hρ₁']⟩
  have hsv : ¬∃ g, σ' ≫ g = V₂' := fun ⟨g, hg⟩ ↦
    Z.valley₁ (s + 3 + L) ⟨g, by rw [← hσ', Category.assoc, hg, hV']⟩
  have hvs : ¬∃ g, V₂' ≫ g = σ' := fun ⟨g, hg⟩ ↦
    Z.valley₂ (s + 3 + L) ⟨g, by rw [← hV', Category.assoc, hg, hσ']⟩
  have hiρ₁' : ¬IsIso ρ₁' := fun _ ↦ hsu ⟨inv ρ₁' ≫ V₂, by simp⟩
  have hiσ' : ¬IsIso σ' := fun _ ↦ hsv ⟨inv σ' ≫ V₂', by simp⟩
  have h0ρ₁ : ¬FactorsThroughMorphism τ (V₁ ≫ ρ₁') := by
    rw [hρ₁']; exact not_factorsThrough_of_not_isLong hτ (Z.ρ_ne _) (hnρ 0 (by omega))
  have h0σj : ¬FactorsThroughMorphism τ (V₁' ≫ σ') := by
    rw [hσ']; exact not_factorsThrough_of_not_isLong hτ (Z.σ_ne _) (hnσ L le_rfl)
  rcases Nat.eq_zero_or_pos L with rfl | hL1
  · exact B.not_f94s hmin hL hR τ hτ.2.1 hτ.1 V₁ V₂ ρ₁' σ' V₁' V₂'
      (h0_a_y₀ := not_ftm_suffix_of_long hτ hiV₁ hσ0)
      (h0_a_y₁ := not_ftm_suffix_of_long hτ hiV₁ hρ0)
      (h0_x_a := not_ftm_prefix_of_long hτ hiV₂ hσ0) (h0_x_y₀ := by rw [hV]; exact hτ1)
      (h0_x_y₁ := h0ρ₁) (h0_c'_y₁ := not_ftm_suffix_of_long hτ hiV₁' hσj0)
      (h0_c'_z₂ := not_ftm_suffix_of_long hτ hiV₁' hlam0)
      (h0_x₂_c' := not_ftm_prefix_of_long hτ hiV₂' hlam0) (h0_x₂_y₁ := h0σj)
      (h0_x₂_z₂ := by rw [hV']; exact hτ2)
      (hi_V₁ := hiV₁) (hi_V₂ := hiV₂) (hi_ρ₁' := hiρ₁') (hi_σ₂' := hiσ') (hi_V₁' := hiV₁')
      (hi_V₂' := hiV₂') (hl_V₂_ρ₁'_y₁ := hus) (hl_ρ₁'_V₂_y₀ := hsu) (hl_σ₂'_V₂'_z₂ := hsv)
      (hl_V₂'_σ₂'_y₁ := hvs)
      (hr_ρ₁'_σ₂'_c' := fun ⟨g, hg⟩ ↦ L8a ⟨V₁' ≫ g, by rw [Category.assoc, hg, hσ']⟩)
      (hr_ρ₁'_σ₂'_x₂ := fun ⟨g, hg⟩ ↦ L8a ⟨g, by rw [hg, hσ']⟩)
      (hr_σ₂'_ρ₁'_a := fun ⟨g, hg⟩ ↦ L8c ⟨V₁ ≫ g, by rw [Category.assoc, hg, hρ₁']⟩)
      (hr_σ₂'_ρ₁'_x := fun ⟨g, hg⟩ ↦ L8c ⟨g, by rw [hg, hρ₁']⟩)
  · exact B.not_zigzag_arms hmin hL hR τ hτ.2.1 hτ.1 Z (s + 3) L hL1 ρ₁' V₁ V₂ σ' V₁' V₂'
      (fun i hi ↦ not_factorsThrough_of_not_isLong hτ (Z.ρ_ne _)
        (by rw [show s + 3 + i + 1 = s + 3 + (i + 1) by ring]; exact hnρ (i + 1) (by omega)))
      (fun i hi ↦ not_factorsThrough_of_not_isLong hτ (Z.σ_ne _) (hnσ i (by omega)))
      (not_ftm_suffix_of_long hτ hiV₁ hρ0) (not_ftm_prefix_of_long hτ hiV₂ hσ0)
      (not_ftm_suffix_of_long hτ hiV₁ hσ0) (by rw [hV]; exact hτ1) h0ρ₁
      (not_ftm_suffix_of_long hτ hiV₁' hσj0) (not_ftm_prefix_of_long hτ hiV₂' hlam0)
      (not_ftm_suffix_of_long hτ hiV₁' hlam0) (by rw [hV']; exact hτ2) h0σj
      hiρ₁' hiV₁ hiV₂ hiσ' hiV₁' hiV₂' hsu hus hsv hvs
      (fun ⟨g, hg⟩ ↦ Z.peak₁ (s + 3) ⟨V₁ ≫ g, by rw [Category.assoc, hg, hρ₁']⟩)
      (fun ⟨g, hg⟩ ↦ Z.peak₁ (s + 3) ⟨g, by rw [hg, hρ₁']⟩) L8a
      (fun ⟨g, hg⟩ ↦ Z.peak₂ (s + 3 + L) ⟨V₁' ≫ g, by rw [Category.assoc, hg, hσ']⟩)
      (fun ⟨g, hg⟩ ↦ Z.peak₂ (s + 3 + L) ⟨g, by rw [hg, hσ']⟩) L8c

include B in
/-- **No third long morphism, case `σ₁ … σⱼ`** (BO13a figure 9.5). -/
theorem b3_third
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (Z : ZChain P) (s L : ℕ)
    (hnρ : ∀ i ≤ L + 1, ¬IsLong (Z.ρ (s + 3 + i))) (hnσ : ∀ i ≤ L, ¬IsLong (Z.σ (s + 3 + i)))
    {a c' : P} (V₁ : Z.x (s + 3) ⟶ a) (V₂ : a ⟶ Z.z (s + 2)) (ρ₁' : a ⟶ Z.z (s + 3))
    (hV : V₁ ≫ V₂ = Z.σ (s + 2)) (hρ₁' : V₁ ≫ ρ₁' = Z.ρ (s + 3)) (hiV₁ : ¬IsIso V₁)
    (hiV₂ : ¬IsIso V₂)
    (V₁' : Z.x (s + 3 + L + 1 + 1) ⟶ c') (V₂' : c' ⟶ Z.z (s + 3 + L + 1))
    (r' : Z.x (s + 3 + L + 1) ⟶ c') (hV' : V₁' ≫ V₂' = Z.σ (s + 3 + L + 1))
    (hr' : r' ≫ V₂' = Z.ρ (s + 3 + L + 1)) (hiV₁' : ¬IsIso V₁') (hiV₂' : ¬IsIso V₂')
    (L8a : ¬∃ c, c ≫ ρ₁' = Z.σ (s + 3)) (L8d : ¬∃ c, r' ≫ c = Z.σ (s + 3 + L))
    {a' b' : P} (τ : a' ⟶ b') (hτ : IsLong τ)
    (hτ1 : ¬FactorsThroughMorphism τ (Z.σ (s + 2)))
    (hτ2 : ¬FactorsThroughMorphism τ (Z.σ (s + 3 + L + 1))) : False := by
  have hσ0 : V₁ ≫ V₂ ≠ 0 := by rw [hV]; exact Z.σ_ne _
  have hρ0 : V₁ ≫ ρ₁' ≠ 0 := by rw [hρ₁']; exact Z.ρ_ne _
  have hlam0 : V₁' ≫ V₂' ≠ 0 := by rw [hV']; exact Z.σ_ne _
  have hr0 : r' ≫ V₂' ≠ 0 := by rw [hr']; exact Z.ρ_ne _
  have hsu : ¬∃ g, ρ₁' ≫ g = V₂ := fun ⟨g, hg⟩ ↦
    Z.valley₂ (s + 2) ⟨g, by rw [← hρ₁', Category.assoc, hg, hV]⟩
  have hus : ¬∃ g, V₂ ≫ g = ρ₁' := fun ⟨g, hg⟩ ↦
    Z.valley₁ (s + 2) ⟨g, by rw [← hV, Category.assoc, hg, hρ₁']⟩
  have hrv : ¬∃ g, g ≫ r' = V₁' := fun ⟨g, hg⟩ ↦
    Z.peak₂ (s + 3 + L + 1) ⟨g, by rw [← hr', ← Category.assoc, hg, hV']⟩
  have hvr : ¬∃ g, g ≫ V₁' = r' := fun ⟨g, hg⟩ ↦
    Z.peak₁ (s + 3 + L + 1) ⟨g, by rw [← hV', ← Category.assoc, hg, hr']⟩
  have hiρ₁' : ¬IsIso ρ₁' := fun _ ↦ hsu ⟨inv ρ₁' ≫ V₂, by simp⟩
  have hir' : ¬IsIso r' := fun _ ↦ hrv ⟨V₁' ≫ inv r', by simp⟩
  exact B.not_zigzag_arms_src hmin hL hR τ hτ.2.1 hτ.1 Z (s + 3) L ρ₁' V₁ V₂ r' V₁' V₂'
    (fun i hi ↦ not_factorsThrough_of_not_isLong hτ (Z.ρ_ne _)
      (by rw [show s + 3 + i + 1 = s + 3 + (i + 1) by ring]; exact hnρ (i + 1) (by omega)))
    (fun i hi ↦ not_factorsThrough_of_not_isLong hτ (Z.σ_ne _) (hnσ i hi))
    (not_ftm_suffix_of_long hτ hiV₁ hρ0) (not_ftm_prefix_of_long hτ hiV₂ hσ0)
    (not_ftm_suffix_of_long hτ hiV₁ hσ0) (by rw [hV]; exact hτ1)
    (by rw [hρ₁']; exact not_factorsThrough_of_not_isLong hτ (Z.ρ_ne _) (hnρ 0 (by omega)))
    (not_ftm_prefix_of_long hτ hiV₂' hr0) (not_ftm_prefix_of_long hτ hiV₂' hlam0)
    (not_ftm_suffix_of_long hτ hiV₁' hlam0)
    (by rw [hr']; exact not_factorsThrough_of_not_isLong hτ (Z.ρ_ne _) (hnρ (L + 1) le_rfl))
    (by rw [hV']; exact hτ2) hiρ₁' hiV₁ hiV₂ hir' hiV₁' hiV₂' hsu hus
    (fun ⟨g, hg⟩ ↦ Z.peak₁ (s + 3) ⟨V₁ ≫ g, by rw [Category.assoc, hg, hρ₁']⟩)
    (fun ⟨g, hg⟩ ↦ Z.peak₁ (s + 3) ⟨g, by rw [hg, hρ₁']⟩) L8a
    (fun ⟨g, hg⟩ ↦ Z.valley₁ (s + 3 + L) ⟨g ≫ V₂', by rw [← Category.assoc, hg, hr']⟩)
    (fun ⟨g, hg⟩ ↦ Z.valley₁ (s + 3 + L) ⟨g, by rw [hg, hr']⟩) L8d hrv hvr

end MulBasis

end RayQuiver

end LargeIndecomposable
