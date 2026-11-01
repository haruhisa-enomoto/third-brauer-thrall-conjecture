module

public import LargeIndecomposable.Crowns.Lemma8.Setup

/-!
# BO13a Lemma 8, permeable case

`MulBasis.l8_perm`: for a long `σ₁ = σ (s+2)` with contour `(v₁ v₂, w₁ ω)`,
`ρ₁ = v₁ ≫ ρ₁'`, `σ₂ = σ₂' ≫ ρ₁'` and `ρₙ` through `ω`, one of figures 8.1–8.4
is cleaving in a proper quotient. Reconstruction:
`notes/2026-10-30-074207-bo13a-lemma8-reconstruction.md`.
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
/-- **BO13a Lemma 8, permeable case** (figures 8.1–8.4). -/
theorem l8_perm
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (h4 : NoCrown4 P) (Z : ZChain P) (s : ℕ) (hσ : IsLong (Z.σ (s + 2)))
    (hρ₁l : ¬IsLong (Z.ρ (s + 3))) (hρnl : ¬IsLong (Z.ρ (s + 2)))
    (hnbr : IsLong (Z.ρ (s + 4)) → ¬IsLong (Z.σ (s + 3)) ∧ ¬IsLong (Z.σ (s + 4)))
    {a' b' : P} (τ' : a' ⟶ b') (hτ' : IsLong τ')
    (hτσ : (⟨_, _, Z.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, τ'⟩)
    {a b : RayVert P} (v₁ : Quiver.Path (RayVert.mk (Z.x (s + 3))) a)
    (v₂ : Quiver.Path a (RayVert.mk (Z.z (s + 2))))
    (w₁ : Quiver.Path (RayVert.mk (Z.x (s + 3))) b) (ω : b ⟶ RayVert.mk (Z.z (s + 2)))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length) (hw₁ : 0 < w₁.length)
    (hv : pathVal (v₁.comp v₂) = Z.σ (s + 2)) (hw : pathVal (w₁.cons ω) = Z.σ (s + 2))
    (hni : ¬Interlaced (v₁.comp v₂) (w₁.cons ω))
    (ρ₁' : a.out ⟶ Z.z (s + 3)) (hρ₁' : pathVal v₁ ≫ ρ₁' = Z.ρ (s + 3))
    (σ₂' : Z.x (s + 4) ⟶ a.out) (hσ₂' : σ₂' ≫ ρ₁' = Z.σ (s + 3))
    (hω : ∃ g, g ≫ ω.1 = Z.ρ (s + 2))
    (hD83 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F83.thin) k))
    (hD84 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F84.thin) k)) :
    False := by
  have hσ0 := hσ.1
  have hv1 : ¬∃ c, Z.σ (s + 2) ≫ c = Z.ρ (s + 3) := Z.valley₁ (s + 2)
  have hv2 : ¬∃ c, Z.ρ (s + 3) ≫ c = Z.σ (s + 2) := Z.valley₂ (s + 2)
  have hp1 : ¬∃ c, c ≫ Z.σ (s + 3) = Z.ρ (s + 3) := Z.peak₁ (s + 3)
  have hp2 : ¬∃ c, c ≫ Z.ρ (s + 3) = Z.σ (s + 3) := Z.peak₂ (s + 3)
  have hw1 : ¬∃ c, Z.σ (s + 3) ≫ c = Z.ρ (s + 4) := Z.valley₁ (s + 3)
  have hw2 : ¬∃ c, Z.ρ (s + 4) ≫ c = Z.σ (s + 3) := Z.valley₂ (s + 3)
  have hs1 : ¬∃ c, c ≫ Z.σ (s + 4) = Z.ρ (s + 4) := Z.peak₁ (s + 4)
  have hs2 : ¬∃ c, c ≫ Z.ρ (s + 4) = Z.σ (s + 4) := Z.peak₂ (s + 4)
  have hq1 : ¬∃ c, c ≫ Z.σ (s + 2) = Z.ρ (s + 2) := Z.peak₁ (s + 2)
  have hq2 : ¬∃ c, c ≫ Z.ρ (s + 2) = Z.σ (s + 2) := Z.peak₂ (s + 2)
  have hu1 : ¬∃ c, Z.σ (s + 1) ≫ c = Z.ρ (s + 2) := Z.valley₁ (s + 1)
  have hu2 : ¬∃ c, Z.ρ (s + 2) ≫ c = Z.σ (s + 1) := Z.valley₂ (s + 1)
  have hρ₁0 := Z.ρ_ne (s + 3)
  have hσ₂0 := Z.σ_ne (s + 3)
  have hρ₂0 := Z.ρ_ne (s + 4)
  have hσ₃0 := Z.σ_ne (s + 4)
  have hρn0 := Z.ρ_ne (s + 2)
  have hσn0 := Z.σ_ne (s + 1)
  have hV : pathVal v₁ ≫ pathVal v₂ = Z.σ (s + 2) := by rw [← pathVal_comp]; exact hv
  have hW : pathVal w₁ ≫ ω.1 = Z.σ (s + 2) := hw
  have hiV₁ := not_isIso_pathVal v₁ hv₁
  have hiV₂ := not_isIso_pathVal v₂ hv₂
  have hiW₁ := not_isIso_pathVal w₁ hw₁
  -- the contour
  have hval : pathVal (v₁.comp v₂) = pathVal (w₁.cons ω) := hv.trans hw.symm
  have h0v : pathVal (v₁.comp v₂) ≠ 0 := by rw [hv]; exact hσ0
  have h0w : pathVal (w₁.cons ω) ≠ 0 := by rw [hw]; exact hσ0
  have hWV : ¬∃ g, pathVal w₁ ≫ g = pathVal v₁ :=
    prefix_cross hL hR (w₁.cons ω) (v₁.comp v₂) hval.symm h0w (fun h ↦ hni h.symm) w₁
      ω.toPath v₁ v₂ rfl rfl hw₁ hv₂
  have hVW : ¬∃ g, pathVal v₁ ≫ g = pathVal w₁ :=
    prefix_cross hL hR (v₁.comp v₂) (w₁.cons ω) hval h0v hni v₁ v₂ w₁ ω.toPath rfl rfl hv₁
      (by simp)
  have hWV₂ : ¬∃ g, g ≫ ω.1 = pathVal v₂ := by
    have := (contour_cross hL hR v₁ v₂ w₁ ω.toPath hval h0v hni hv₁ (by simp)).1
    simpa only [pathVal_toPath] using this
  have hVW₂ : ¬∃ g, g ≫ pathVal v₂ = ω.1 := by
    have := (contour_cross hL hR w₁ ω.toPath v₁ v₂ hval.symm h0w (fun h ↦ hni h.symm) hw₁
      hv₂).1
    simpa only [pathVal_toPath] using this
  have hWρ : ¬∃ g, pathVal w₁ ≫ g = Z.ρ (s + 3) := by
    rintro ⟨g, hg⟩
    obtain ⟨_, α₀, v₁', rfl⟩ := exists_first_arrow v₁ hiV₁
    obtain ⟨_, β₀, w₁', rfl⟩ := exists_first_arrow w₁ hiW₁
    refine B.not_factors_both hmin hL hR α₀ β₀ (v₁'.comp v₂) (w₁'.cons ω)
      (by rw [← Quiver.Path.comp_assoc]; exact hval) (by rw [← Quiver.Path.comp_assoc]; exact h0v)
      (by rw [← Quiver.Path.comp_assoc]; exact hni) ⟨_, Z.ρ (s + 3)⟩ hρ₁0 ?_ ?_
      ⟨pathVal v₁' ≫ ρ₁', ?_⟩ ⟨pathVal w₁' ≫ g, ?_⟩
    · rintro ⟨c, hc⟩
      rw [← Quiver.Path.comp_assoc, hv] at hc
      exact hv1 ⟨c, hc⟩
    · rintro ⟨c, hc⟩
      change Z.ρ (s + 3) ≫ c = _ at hc
      rw [← Quiver.Path.comp_assoc, hv] at hc
      exact hv2 ⟨c, hc⟩
    · change α₀.1 ≫ _ = _
      rw [← hρ₁', pathVal_comp, pathVal_toPath]
      simp only [Category.assoc]
      rfl
    · change β₀.1 ≫ _ = _
      rw [← hg, pathVal_comp, pathVal_toPath]
      simp only [Category.assoc]
      rfl
  have hρnV₂ : ¬∃ g, g ≫ pathVal v₂ = Z.ρ (s + 2) := by
    rintro ⟨g, hg⟩
    obtain ⟨_, v₂', e, rfl⟩ := exists_last_arrow v₂ hiV₂
    exact B.not_factors_both_last hmin hL hR e ω (v₁.comp v₂') w₁ hval h0v hni (Z.ρ (s + 2))
      hρn0 (fun ⟨c, hc⟩ ↦ hq1 ⟨c, by rw [← hc]; exact congrArg (c ≫ ·) hv.symm⟩)
      (fun ⟨c, hc⟩ ↦ hq2 ⟨c, hc.trans hv⟩)
      ⟨g ≫ pathVal v₂', by rw [Category.assoc]; exact hg⟩ hω
  obtain ⟨r, hr⟩ := hω
  have hir : ¬IsIso r := fun h ↦ hq2 ⟨pathVal w₁ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, hW]⟩
  -- figure 2.1: `σ₂' ≫ v₂ = 0`
  have hz : σ₂' ≫ pathVal v₂ = 0 := by
    by_contra hne0
    exact no_fig21 hL hR h4 (pathVal v₁) σ₂' (pathVal v₂) ρ₁'
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hρ₁', ← hg, ← Category.assoc, hV]⟩)
      (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hV, ← hg, ← hρ₁', Category.assoc]⟩)
      (by rw [hV]; exact hσ0) hne0 (by rw [hσ₂']; exact hσ₂0) (by rw [hρ₁']; exact hρ₁0)
  -- a long morphism dividing none of `ρ₂, σ₂, σ₃`
  obtain ⟨_, _, τ, hτ, hτρ₂, hτσ₂, hτσ₃⟩ : ∃ (a b : P) (τ : a ⟶ b), IsLong τ ∧
      ¬FactorsThroughMorphism τ (Z.ρ (s + 4)) ∧ ¬FactorsThroughMorphism τ (Z.σ (s + 3)) ∧
        ¬FactorsThroughMorphism τ (Z.σ (s + 4)) := by
    by_cases hσρ₂ : FactorsThroughMorphism (Z.σ (s + 2)) (Z.ρ (s + 4))
    · have hρ₂l := hσ.of_factorsThrough hρ₂0 hσρ₂
      obtain ⟨hσ₂l, hσ₃l⟩ := hnbr hρ₂l
      refine ⟨_, _, τ', hτ', fun h ↦ not_ftm_of_ne hτ' hσ0 hτσ
        (ftm_trans_long hσ hρ₂0 hσρ₂ h), not_factorsThrough_of_not_isLong hτ' hσ₂0 hσ₂l,
        not_factorsThrough_of_not_isLong hτ' hσ₃0 hσ₃l⟩
    · exact ⟨_, _, Z.σ (s + 2), hσ, hσρ₂,
        not_ftm_valley_peak hQ hσ hρ₁0 hσ₂0 hv1 hv2 hp1 hp2, Z.not_ftm_σ_add_two h4 (s + 2) hσ⟩
  have g0 : ∀ {X Y : P} (f : X ⟶ Y), ¬IsLong f → f ≠ 0 → ¬FactorsThroughMorphism τ f :=
    fun f hl h0 ↦ not_factorsThrough_of_not_isLong hτ h0 hl
  by_cases hP1 : ∃ g, σ₂' ≫ g = Z.ρ (s + 4)
  swap
  · -- figure 8.1
    exact B.l8_f81 hmin hL hR hp1 hp2 hw2 hs1 hs2 hq1 hq2 hv2 (Z.ρ_not_isIso _)
      (Z.σ_not_isIso _) (pathVal v₁) (pathVal v₂) hV hiV₁ (pathVal w₁) ω.1 hW hiW₁ hWV hVW hWρ
      ρ₁' hρ₁' σ₂' hσ₂' r hr hP1 τ hτ
      (not_ftm_suffix_of_long hτ hiV₁ (by rw [hρ₁']; exact hρ₁0))
      (not_ftm_prefix_of_long hτ ω.2.2.1 (by rw [hW]; exact hσ0))
      (not_ftm_prefix_of_long hτ hiV₂ (by rw [hV]; exact hσ0)) (g0 _ hρ₁l hρ₁0)
      (not_ftm_prefix_of_long hτ ω.2.2.1 (by rw [hr]; exact hρn0))
      (not_ftm_prefix_of_long hτ (fun h ↦ hv2 ⟨inv ρ₁' ≫ pathVal v₂, by
        rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc, hV]⟩) (by rw [hσ₂']; exact hσ₂0))
      hτσ₂ hτρ₂ hτσ₃
  obtain ⟨ρ₂', hρ₂'⟩ := hP1
  have hir₁' : ¬IsIso ρ₁' := fun h ↦ hv2 ⟨inv ρ₁' ≫ pathVal v₂, by
    rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc, hV]⟩
  have hir₂' : ¬IsIso ρ₂' := fun h ↦ hw2 ⟨inv ρ₂' ≫ ρ₁', by
    rw [← hρ₂', Category.assoc, IsIso.hom_inv_id_assoc, hσ₂']⟩
  have hiσ₂' : ¬IsIso σ₂' := fun h ↦ hp1 ⟨pathVal v₁ ≫ inv σ₂', by
    rw [← hρ₁', ← hσ₂']; simp⟩
  -- figure 2.1: `v₁ ≫ ρ₂' = 0`
  have hz' : pathVal v₁ ≫ ρ₂' = 0 := by
    by_contra hne0
    exact no_fig21 hL hR h4 (pathVal v₁) σ₂' ρ₁' ρ₂'
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂', Category.assoc, hg, hρ₂']⟩)
      (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂']⟩)
      (by rw [hρ₁']; exact hρ₁0) (by rw [hσ₂']; exact hσ₂0) (by rw [hρ₂']; exact hρ₂0) hne0
  by_cases hP2a : ∃ s', r ≫ s' = Z.σ (s + 1)
  · -- figure 8.2, in `P/σ₁`
    obtain ⟨s', hs'⟩ := hP2a
    exact B.l8_f82 hmin hL hR hv1 hv2 hw1 hw2 hq2 hu1 hu2 hσ0 hρ₂0 (pathVal v₁) (pathVal v₂) hV
      hiV₂ (pathVal w₁) ω.1 hW ω.2.2.1 hWV₂ hVW₂ hρnV₂ ρ₁' hρ₁' σ₂' hσ₂' ρ₂' hρ₂' hz hz' r hr s'
      hs' (Z.σ (s + 2)) hσ
      (not_ftm_suffix_of_long hσ hir (by rw [hs']; exact hσn0))
      (not_ftm_suffix_of_long hσ hiW₁ (by rw [hW]; exact hσ0))
      (not_ftm_prefix_of_long hσ ω.2.2.1 (by rw [hr]; exact hρn0))
      (l6_not_ftm_nbr hQ hσ hρn0 hσn0 hq1 hq2 hu1 hu2)
      (not_factorsThrough_of_not_isLong hσ hρn0 hρnl)
      (not_ftm_suffix_of_long hσ hiV₁ (by rw [hV]; exact hσ0))
      (not_ftm_suffix_of_long hσ hiV₁ (by rw [hρ₁']; exact hρ₁0))
      (not_ftm_suffix_of_long hσ hiσ₂' (by rw [hρ₂']; exact hρ₂0))
  -- the morphism `φ` out of `xₙ`
  obtain ⟨t, φ, hiφ, hrφ, hφρ, h0φ⟩ : ∃ (t : P) (φ : Z.x (s + 2) ⟶ t), ¬IsIso φ ∧
      (¬∃ g, r ≫ g = φ) ∧ (¬∃ g, φ ≫ g = Z.ρ (s + 2)) ∧
        ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬FactorsThroughMorphism μ φ := by
    by_cases hσnl : IsLong (Z.σ (s + 1))
    · obtain ⟨T, φ, hφ, hφρ⟩ := B.exists_first_not hmin hL hR hσnl (hcont _ hσnl) (Z.ρ (s + 2))
        hρn0 hu1 hu2
      refine ⟨T, φ, hφ.2.1, ?_, hφρ, fun μ hμ ↦ not_factorsThrough_irr hμ.2.1 hμ.1 hμ.2.2.1 hφ⟩
      rintro ⟨g, hg⟩
      rcases hφ.2.2 _ r g hg.symm with h | h
      · exact hir h
      · exact hφρ ⟨inv g ≫ ω.1, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hr]⟩
    · exact ⟨_, Z.σ (s + 1), Z.σ_not_isIso _, hP2a, hu1,
        fun μ hμ ↦ not_factorsThrough_of_not_isLong hμ hσn0 hσnl⟩
  by_cases hP2b : ∃ g, g ≫ ρ₂' = Z.σ (s + 4)
  · -- figure 8.4
    obtain ⟨σ₃', hσ₃'⟩ := hP2b
    have hz₃ : σ₃' ≫ ρ₁' = 0 := by
      by_contra hne0
      exact no_fig21 hL hR h4 σ₂' σ₃' ρ₁' ρ₂'
        (fun ⟨g, hg⟩ ↦ hs2 ⟨g, by rw [← hσ₃', ← hg, Category.assoc, hρ₂']⟩)
        (fun ⟨g, hg⟩ ↦ hs1 ⟨g, by rw [← hρ₂', ← hg, Category.assoc, hσ₃']⟩)
        (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂', Category.assoc, hg, hρ₂']⟩)
        (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂']⟩)
        (by rw [hσ₂']; exact hσ₂0) hne0 (by rw [hσ₃']; exact hσ₃0) (by rw [hρ₂']; exact hρ₂0)
    have hiσ₃' : ¬IsIso σ₃' := fun h ↦ hs1 ⟨σ₂' ≫ inv σ₃', by rw [← hρ₂', ← hσ₃']; simp⟩
    exact B.l8_f84 hmin hL hR hv2 hp1 hp2 hw1 hw2 hs1 hs2 hq1 hq2 hρ₁0 hσ₃0 (pathVal v₁)
      (pathVal v₂) hV hiV₁ (pathVal w₁) ω.1 hW hiW₁ hWV hVW hWρ ρ₁' hρ₁' σ₂' hσ₂' ρ₂' hρ₂' hz'
      σ₃' hσ₃' hz₃ r hr φ hiφ hrφ hφρ τ hτ
      (not_ftm_suffix_of_long hτ hiV₁ (by rw [hρ₁']; exact hρ₁0))
      (not_ftm_suffix_of_long hτ hiσ₂' (by rw [hρ₂']; exact hρ₂0))
      (not_ftm_prefix_of_long hτ ω.2.2.1 (by rw [hW]; exact hσ0))
      (not_ftm_prefix_of_long hτ hiV₂ (by rw [hV]; exact hσ0)) (g0 _ hρ₁l hρ₁0)
      (not_ftm_prefix_of_long hτ ω.2.2.1 (by rw [hr]; exact hρn0)) (h0φ τ hτ)
      (not_ftm_prefix_of_long hτ hir₁' (by rw [hσ₂']; exact hσ₂0)) hτσ₂ hτρ₂
      (not_ftm_prefix_of_long hτ hir₂' (by rw [hσ₃']; exact hσ₃0)) hτσ₃ hD84
  · -- figure 8.3
    exact B.l8_f83 hmin hL hR hv1 hv2 hw1 hw2 hs1 hq2 hp1 hσ0 hρ₂0 (Z.σ_not_isIso _)
      (pathVal v₁) (pathVal v₂) hV hiV₂ (pathVal w₁) ω.1 hW ω.2.2.1 hWV₂ hVW₂ hρnV₂ ρ₁' hρ₁' σ₂'
      hσ₂' ρ₂' hρ₂' hz hz' r hr φ hiφ hrφ hφρ hP2b τ hτ
      (not_ftm_suffix_of_long hτ hiW₁ (by rw [hW]; exact hσ0))
      (not_ftm_suffix_of_long hτ hiV₁ (by rw [hV]; exact hσ0))
      (not_ftm_suffix_of_long hτ hiV₁ (by rw [hρ₁']; exact hρ₁0))
      (not_ftm_suffix_of_long hτ hiσ₂' (by rw [hρ₂']; exact hρ₂0))
      (not_ftm_prefix_of_long hτ ω.2.2.1 (by rw [hr]; exact hρn0)) (h0φ τ hτ)
      (g0 _ hρnl hρn0) (not_ftm_prefix_of_long hτ hir₁' (by rw [hσ₂']; exact hσ₂0)) hτσ₂ hτρ₂
      hτσ₃ hD83

end MulBasis

end RayQuiver

end LargeIndecomposable
