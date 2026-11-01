module

public import LargeIndecomposable.Crowns.Lemma8.Permeable
public import LargeIndecomposable.Cleaving.Shapes.ShapeF8R1A
public import LargeIndecomposable.Cleaving.Shapes.ShapeF8S13
public import LargeIndecomposable.Cleaving.Shapes.ShapeF8R1C
public import LargeIndecomposable.Cleaving.Shapes.ShapeF8R1D
public import LargeIndecomposable.Cleaving.Shapes.ShapeF86
public import LargeIndecomposable.Cleaving.Shapes.ShapeF87
public import LargeIndecomposable.Cleaving.Shapes.ShapeF88

/-!
# BO13a Lemma 8, reflecting case: the claim `ρₙ = ρₙ' ≫ v₂`

`MulBasis.l8_claim`: for a reflecting contour, `ρₙ` factors through all of `v₂`
(BO13a: the `D̃₅`, the two `D̃₄` stars, the `Ẽ₆` and the `Ẽ₇` with two zero
relations).
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
/-- **BO13a Lemma 8, reflecting case, the claim**: `ρₙ` factors through `v₂`. -/
theorem l8_claim
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (h4 : NoCrown4 P) (Z : ZChain P) (s : ℕ) (hσ : IsLong (Z.σ (s + 2)))
    (hρ₁l : ¬IsLong (Z.ρ (s + 3))) (hρnl : ¬IsLong (Z.ρ (s + 2)))
    {a' b' : P} (τ' : a' ⟶ b') (hτ' : IsLong τ')
    (hτσ : (⟨_, _, Z.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, τ'⟩)
    {a c d : RayVert P} (v₁ : Quiver.Path (RayVert.mk (Z.x (s + 3))) a)
    (v₂' : Quiver.Path a c) (e : c ⟶ RayVert.mk (Z.z (s + 2)))
    (β : RayVert.mk (Z.x (s + 3)) ⟶ d) (w' : Quiver.Path d (RayVert.mk (Z.z (s + 2))))
    (hv₁ : 0 < v₁.length)
    (hv : pathVal (v₁.comp (v₂'.cons e)) = Z.σ (s + 2))
    (hw : pathVal (β.toPath.comp w') = Z.σ (s + 2))
    (hni : ¬Interlaced (v₁.comp (v₂'.cons e)) (β.toPath.comp w'))
    (hβρ : ¬∃ g, β.1 ≫ g = Z.ρ (s + 3))
    (ρ₁' : a.out ⟶ Z.z (s + 3)) (hρ₁' : pathVal v₁ ≫ ρ₁' = Z.ρ (s + 3))
    (σ₂' : Z.x (s + 4) ⟶ a.out) (hσ₂' : σ₂' ≫ ρ₁' = Z.σ (s + 3))
    (hz : σ₂' ≫ pathVal (v₂'.cons e) = 0) (he : ∃ g, g ≫ e.1 = Z.ρ (s + 2))
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F8R1D.thin) k)) :
    ∃ r, r ≫ pathVal (v₂'.cons e) = Z.ρ (s + 2) := by
  by_contra hno
  have hσ0 := hσ.1
  have hv1 : ¬∃ c, Z.σ (s + 2) ≫ c = Z.ρ (s + 3) := Z.valley₁ (s + 2)
  have hv2 : ¬∃ c, Z.ρ (s + 3) ≫ c = Z.σ (s + 2) := Z.valley₂ (s + 2)
  have hp1 : ¬∃ c, c ≫ Z.σ (s + 3) = Z.ρ (s + 3) := Z.peak₁ (s + 3)
  have hp2 : ¬∃ c, c ≫ Z.ρ (s + 3) = Z.σ (s + 3) := Z.peak₂ (s + 3)
  have hw1 : ¬∃ c, Z.σ (s + 3) ≫ c = Z.ρ (s + 4) := Z.valley₁ (s + 3)
  have hw2 : ¬∃ c, Z.ρ (s + 4) ≫ c = Z.σ (s + 3) := Z.valley₂ (s + 3)
  have hq1 : ¬∃ c, c ≫ Z.σ (s + 2) = Z.ρ (s + 2) := Z.peak₁ (s + 2)
  have hq2 : ¬∃ c, c ≫ Z.ρ (s + 2) = Z.σ (s + 2) := Z.peak₂ (s + 2)
  have hρ₁0 := Z.ρ_ne (s + 3)
  have hσ₂0 := Z.σ_ne (s + 3)
  have hρ₂0 := Z.ρ_ne (s + 4)
  have hρn0 := Z.ρ_ne (s + 2)
  have hiV₁ := not_isIso_pathVal v₁ hv₁
  -- the longest suffix of `v₂` through which `ρₙ` factors
  obtain ⟨_, _, a₀, ea, b₀, hsplit, hb₀, ⟨r, hr⟩, hmx⟩ := exists_max_suffix (x := a)
    (y := RayVert.mk (Z.z (s + 2))) (Z.ρ (s + 2)) v₂' e.toPath (by simp)
    (by obtain ⟨g, hg⟩ := he; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩)
    (fun ⟨g, hg⟩ ↦ hno ⟨g, hg⟩)
  have hv₂ : v₂'.cons e = (a₀.cons ea).comp b₀ := hsplit.symm
  rw [hv₂] at hv hni hz
  obtain ⟨Am, hAm⟩ : ∃ Am, Am = pathVal (a₀.cons ea) := ⟨_, rfl⟩
  have hAB : Am ≫ pathVal b₀ = pathVal ((a₀.cons ea).comp b₀) := by rw [hAm, pathVal_comp]
  have hσv : pathVal v₁ ≫ Am ≫ pathVal b₀ = Z.σ (s + 2) := by
    rw [hAB, ← pathVal_comp]; exact hv
  have hiA : ¬IsIso Am := by rw [hAm]; exact not_isIso_pathVal _ (by simp)
  have hiB : ¬IsIso (pathVal b₀) := not_isIso_pathVal _ hb₀
  have hiVA : ¬IsIso (pathVal v₁ ≫ Am) := fun h ↦ not_split_mono hiV₁
    ⟨Am ≫ inv (pathVal v₁ ≫ Am), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have hrA : ¬∃ g, g ≫ Am = r := by
    rintro ⟨g, hg⟩
    refine hmx ⟨g ≫ pathVal a₀, ?_⟩
    rw [← hr, ← hg, hAm]
    change _ = (g ≫ (pathVal a₀ ≫ ea.1)) ≫ _
    simp only [Category.assoc]
  have hir : ¬IsIso r := fun h ↦ hq2 ⟨pathVal v₁ ≫ Am ≫ inv r, by
    rw [← hr]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]; exact hσv⟩
  have hAr : ¬∃ g, g ≫ r = Am := fun ⟨g, hg⟩ ↦ hq2 ⟨pathVal v₁ ≫ g, by
    rw [← hr, Category.assoc, ← Category.assoc g, hg]; exact hσv⟩
  have hVAr : ¬∃ g, g ≫ r = pathVal v₁ ≫ Am := fun ⟨g, hg⟩ ↦ hq2 ⟨g, by
    rw [← hr, ← Category.assoc, hg, Category.assoc]; exact hσv⟩
  have hρ₁V : ¬∃ g, Z.ρ (s + 3) ≫ g = pathVal v₁ ≫ Am ≫ pathVal b₀ := fun ⟨g, hg⟩ ↦
    hv2 ⟨g, by rw [hg]; exact hσv⟩
  -- crossings in the contour
  have hval : pathVal (v₁.comp ((a₀.cons ea).comp b₀)) = pathVal (β.toPath.comp w') :=
    hv.trans hw.symm
  have h0w : pathVal (β.toPath.comp w') ≠ 0 := by rw [hw]; exact hσ0
  have hw'pos : 0 < w'.length := by
    by_contra h0
    have hl : w'.length = 0 := by omega
    cases w' with
    | cons _ _ => simp at hl
    | nil =>
      apply hσ.2.2.1
      rw [← hw, Quiver.Path.comp_nil, pathVal_toPath]
      exact β.2
  have hβw : β.1 ≫ pathVal w' = Z.σ (s + 2) := by rw [← hw, pathVal_comp, pathVal_toPath]
  have hVW : ¬∃ g, pathVal v₁ ≫ g = β.1 := by
    have := prefix_cross hL hR _ _ hval (by rw [hv]; exact hσ0) hni v₁ _ β.toPath w' rfl rfl hv₁
      hw'pos
    simpa only [pathVal_toPath] using this
  have hWV : ¬∃ g, β.1 ≫ g = pathVal v₁ := by
    have := prefix_cross hL hR _ _ hval.symm h0w (fun h ↦ hni h.symm) β.toPath w' v₁
      ((a₀.cons ea).comp b₀) rfl rfl (by simp) (by simp)
    simpa only [pathVal_toPath] using this
  have hWVA : ¬∃ g, β.1 ≫ g = pathVal v₁ ≫ Am := by
    have := prefix_cross hL hR _ _ hval.symm h0w (fun h ↦ hni h.symm) β.toPath w'
      (v₁.comp (a₀.cons ea)) b₀ rfl (by rw [Quiver.Path.comp_assoc]) (by simp) hb₀
    rw [pathVal_comp, ← hAm, pathVal_toPath] at this
    exact this
  have hzA : σ₂' ≫ Am ≫ pathVal b₀ = 0 := by rw [hAB]; exact hz
  have hiAB : ¬IsIso (Am ≫ pathVal b₀) := fun h ↦ not_split_mono hiA
    ⟨pathVal b₀ ≫ inv (Am ≫ pathVal b₀), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have hAB0 : Am ≫ pathVal b₀ ≠ 0 := fun h ↦ hσ0 (by rw [← hσv, h, comp_zero])
  have hVAB0 : pathVal v₁ ≫ Am ≫ pathVal b₀ ≠ 0 := by rw [hσv]; exact hσ0
  have hVA0 : (pathVal v₁ ≫ Am) ≫ pathVal b₀ ≠ 0 := by rw [Category.assoc]; exact hVAB0
  have hir₁' : ¬IsIso ρ₁' := fun h ↦ hv2 ⟨inv ρ₁' ≫ Am ≫ pathVal b₀, by
    rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc]; exact hσv⟩
  have hiσ₂' : ¬IsIso σ₂' := fun h ↦ hp1 ⟨pathVal v₁ ≫ inv σ₂', by
    rw [← hρ₁', ← hσ₂']; simp⟩
  have hn1 : ¬FactorsThroughMorphism (Z.σ (s + 2)) (Z.ρ (s + 3)) :=
    not_factorsThrough_of_not_isLong hσ hρ₁0 hρ₁l
  have hn2 : ¬FactorsThroughMorphism (Z.σ (s + 2)) (Z.σ (s + 3)) :=
    not_ftm_valley_peak hQ hσ hρ₁0 hσ₂0 hv1 hv2 hp1 hp2
  -- the `D̃₅` in `P/τ'`
  by_cases hAρ : ∃ g, Am ≫ g = ρ₁'
  swap
  · exact B.not_f8r1a hmin hL hR τ' hτ'.2.1 hτ'.1 (pathVal v₁) Am (pathVal b₀) r ρ₁'
      (not_ftm_prefix_of_long hτ' hiB hAB0) (not_ftm_suffix_of_long hτ' hiV₁ hVAB0)
      (not_ftm_suffix_of_long hτ' hiV₁ (by rw [hρ₁']; exact hρ₁0))
      (not_ftm_prefix_of_long hτ' hiAB hVAB0) (not_ftm_prefix_of_long hτ' hiB hVA0)
      (fun h ↦ not_ftm_of_ne hτ' hσ0 hτσ (by simpa only [Category.assoc, hσv] using h))
      (by rw [hρ₁']; exact not_factorsThrough_of_not_isLong hτ' hρ₁0 hρ₁l)
      (not_ftm_suffix_of_long hτ' hiVA hVA0) (not_ftm_prefix_of_long hτ' hiB (by rw [hr]; exact hρn0))
      (by rw [hr]; exact not_factorsThrough_of_not_isLong hτ' hρn0 hρnl)
      hiV₁ hiA hiB hir hir₁' hAρ
      (fun ⟨g, hg⟩ ↦ hv2 ⟨g ≫ pathVal b₀, by
        rw [← hρ₁', Category.assoc, ← Category.assoc ρ₁', hg]; exact hσv⟩)
      (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ₁', Category.assoc, hg]; exact hσv⟩) hrA hAr hVAr
  obtain ⟨ρ₁'', hρ₁''⟩ := hAρ
  have hρ₁v : pathVal v₁ ≫ Am ≫ ρ₁'' = Z.ρ (s + 3) := by rw [hρ₁'']; exact hρ₁'
  have hiρ₁'' : ¬IsIso ρ₁'' := fun h ↦ hv2 ⟨inv ρ₁'' ≫ pathVal b₀, by
    rw [← hρ₁v]; simp only [Category.assoc, IsIso.hom_inv_id_assoc]; exact hσv⟩
  have hσ₂v : σ₂' ≫ Am ≫ ρ₁'' = Z.σ (s + 3) := by rw [hρ₁'']; exact hσ₂'
  have hiσ₂'A : ¬IsIso (σ₂' ≫ Am) := fun h ↦ not_split_mono hiσ₂'
    ⟨Am ≫ inv (σ₂' ≫ Am), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  -- the star `A, ρₙ' ; v₂'', ρ₁''`: `ρₙ' ≫ ρ₁'' = 0`
  have hzr : r ≫ ρ₁'' = 0 := by
    by_contra hne0
    have star : ∀ {a₁ b₁ : P} (τ : a₁ ⟶ b₁), IsLong τ →
        ¬FactorsThroughMorphism τ (r ≫ ρ₁'') → False := by
      intro a₁ b₁ τ hτ hτr
      exact B.not_s4s hmin hL hR τ hτ.2.1 hτ.1 r Am (pathVal b₀) ρ₁''
        (not_ftm_suffix_of_long hτ hiVA hVA0)
        (not_ftm_suffix_of_long hτ hiVA (by rw [Category.assoc, hρ₁v]; exact hρ₁0))
        (not_ftm_prefix_of_long hτ hiB (by rw [hr]; exact hρn0))
        (by rw [hr]; exact not_factorsThrough_of_not_isLong hτ hρn0 hρnl) hτr
        (not_ftm_prefix_of_long hτ hiB hAB0) (not_ftm_suffix_of_long hτ hiV₁ hVAB0)
        (not_ftm_suffix_of_long hτ hiV₁ (by rw [hρ₁v]; exact hρ₁0)) hir hiA hiB hiρ₁''
        (fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hρ₁v, ← hg, ← hσv]; simp only [Category.assoc]⟩)
        (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hσv, ← hg, ← hρ₁v]; simp only [Category.assoc]⟩)
        hAr hrA
    by_cases hσf : FactorsThroughMorphism (Z.σ (s + 2)) (r ≫ ρ₁'')
    · exact star τ' hτ' (fun h ↦ not_ftm_of_ne hτ' hσ0 hτσ (ftm_trans_long hσ hne0 hσf h))
    · exact star _ hσ hσf
  -- `ρ₂` long or not through `σ₂'`: the `Ẽ₆`
  by_cases hR1c : IsLong (Z.ρ (s + 4)) ∨ ¬∃ g, σ₂' ≫ g = Z.ρ (s + 4)
  · obtain ⟨t, φ, hiφ, hφσ₂, hσ₂'φ, h0φ⟩ : ∃ (t : P) (φ : Z.x (s + 4) ⟶ t), ¬IsIso φ ∧
        (¬∃ g, φ ≫ g = Z.σ (s + 3)) ∧ (¬∃ g, σ₂' ≫ g = φ) ∧
          ¬FactorsThroughMorphism (Z.σ (s + 2)) φ := by
      by_cases hl : IsLong (Z.ρ (s + 4))
      · obtain ⟨T, φ, hφ, hφσ⟩ := B.exists_first_not hmin hL hR hl (hcont _ hl) (Z.σ (s + 3))
          hσ₂0 hw2 hw1
        refine ⟨T, φ, hφ.2.1, hφσ, ?_, not_factorsThrough_irr hσ.2.1 hσ0 hσ.2.2.1 hφ⟩
        rintro ⟨g, hg⟩
        rcases hφ.2.2 _ σ₂' g hg.symm with h | h
        · exact hiσ₂' h
        · exact hφσ ⟨inv g ≫ ρ₁', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hσ₂']⟩
      · exact ⟨_, Z.ρ (s + 4), Z.ρ_not_isIso _, hw2, hR1c.resolve_left hl,
          not_factorsThrough_of_not_isLong hσ hρ₂0 hl⟩
    exact B.not_f8r1c hmin hL hR (Z.σ (s + 2)) hσ.2.1 hσ0 (pathVal v₁) β.1 σ₂' φ Am ρ₁''
      (not_ftm_prefix_of_long hσ hiB hAB0)
      (not_ftm_suffix_of_long hσ hiV₁ (by rw [hρ₁v]; exact hρ₁0))
      (not_ftm_prefix_of_long hσ hiAB hVAB0) (not_ftm_prefix_of_long hσ hiB hVA0)
      (by simpa only [Category.assoc, hρ₁v] using hn1)
      (not_ftm_prefix_of_long hσ (not_isIso_pathVal w' hw'pos) (by rw [hβw]; exact hσ0))
      (not_ftm_prefix_of_long hσ hir₁' (by rw [hσ₂']; exact hσ₂0))
      (not_ftm_prefix_of_long hσ hiρ₁'' (by rw [Category.assoc, hσ₂v]; exact hσ₂0))
      (by simpa only [Category.assoc, hσ₂v] using hn2) h0φ
      (not_ftm_suffix_of_long hσ hiVA (by rw [Category.assoc, hρ₁v]; exact hρ₁0))
      hiV₁ β.2.2.1 hiσ₂' hiφ hiA hiρ₁'' hVW hWV hWVA
      (fun ⟨g, hg⟩ ↦ hβρ ⟨g, by rw [hg]; exact hρ₁v⟩) hσ₂'φ
      (fun ⟨g, hg⟩ ↦ hφσ₂ ⟨g ≫ ρ₁', by rw [← Category.assoc, hg, hσ₂']⟩)
      (fun ⟨g, hg⟩ ↦ hφσ₂ ⟨g ≫ ρ₁'', by rw [← Category.assoc, hg, Category.assoc, hσ₂v]⟩)
      (fun ⟨g, hg⟩ ↦ hφσ₂ ⟨g, by rw [hg]; exact hσ₂v⟩)
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
  push Not at hR1c
  obtain ⟨hρ₂l, ρ₂', hρ₂'⟩ := hR1c
  have hiρ₂' : ¬IsIso ρ₂' := fun h ↦ hw2 ⟨inv ρ₂' ≫ ρ₁', by
    rw [← hρ₂', Category.assoc, IsIso.hom_inv_id_assoc, hσ₂']⟩
  by_cases hAρ₂ : ∃ g, Am ≫ g = ρ₂'
  · -- the star `A ; v₂'', ρ₁'', ρ₂''` at `c`
    obtain ⟨ρ₂'', hρ₂''⟩ := hAρ₂
    have hρ₂v : σ₂' ≫ Am ≫ ρ₂'' = Z.ρ (s + 4) := by rw [hρ₂'']; exact hρ₂'
    have hz2 : pathVal v₁ ≫ Am ≫ ρ₂'' = 0 := by
      by_contra hne0
      exact no_fig21 hL hR h4 (pathVal v₁ ≫ Am) (σ₂' ≫ Am) ρ₁'' ρ₂''
        (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by
          rw [← hρ₁v, ← hσ₂v, ← Category.assoc σ₂', ← hg]
          simp only [Category.assoc]⟩)
        (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by
          rw [← hρ₁v, ← hσ₂v, ← Category.assoc (pathVal v₁), ← hg]
          simp only [Category.assoc]⟩)
        (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂v, ← hρ₂v, ← hg]; simp only [Category.assoc]⟩)
        (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hσ₂v, ← hρ₂v, ← hg]; simp only [Category.assoc]⟩)
        (by rw [Category.assoc, hρ₁v]; exact hρ₁0) (by rw [Category.assoc, hσ₂v]; exact hσ₂0)
        (by rw [Category.assoc, hρ₂v]; exact hρ₂0) (by rw [Category.assoc]; exact hne0)
    exact B.not_f8s13 hmin hL hR (Z.σ (s + 2)) hσ.2.1 hσ0 Am (pathVal b₀) ρ₁'' ρ₂''
      (not_ftm_suffix_of_long hσ hiVA hVA0)
      (not_ftm_suffix_of_long hσ hiVA (by rw [Category.assoc, hρ₁v]; exact hρ₁0))
      (not_ftm_suffix_of_long hσ hiσ₂'A (by rw [Category.assoc, hρ₂v]; exact hρ₂0))
      (not_ftm_prefix_of_long hσ hiB hAB0) (not_ftm_suffix_of_long hσ hiV₁ hVAB0)
      (not_ftm_suffix_of_long hσ hiV₁ (by rw [hρ₁v]; exact hρ₁0))
      (not_ftm_suffix_of_long hσ hiσ₂' (by rw [hρ₂v]; exact hρ₂0)) hiA hiB hiρ₁''
      (fun h ↦ hw2 ⟨inv ρ₂'' ≫ ρ₁'', by
        rw [← hρ₂v]; simp only [Category.assoc, IsIso.hom_inv_id_assoc]; exact hσ₂v⟩)
      (fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hρ₁v, ← hg, ← hσv]; simp only [Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hρ₂0 (by
        rw [← hρ₂v, ← hg, ← Category.assoc, ← Category.assoc, Category.assoc σ₂', hzA, zero_comp]))
      (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hσv, ← hg, ← hρ₁v]; simp only [Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂v, ← hρ₂v, ← hg]; simp only [Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hσ0 (by
        rw [← hσv, ← hg, ← Category.assoc, ← Category.assoc, Category.assoc (pathVal v₁), hz2,
          zero_comp]))
      (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hσ₂v, ← hρ₂v, ← hg]; simp only [Category.assoc]⟩)
  · -- the `Ẽ₇` with `ρₙ' ≫ ρ₁'' = v₁ ≫ ρ₂' = 0`
    have hzV : pathVal v₁ ≫ ρ₂' = 0 := by
      by_contra hne0
      exact no_fig21 hL hR h4 (pathVal v₁) σ₂' ρ₁' ρ₂'
        (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
        (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
        (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂', Category.assoc, hg, hρ₂']⟩)
        (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂']⟩)
        (by rw [hρ₁']; exact hρ₁0) (by rw [hσ₂']; exact hσ₂0) (by rw [hρ₂']; exact hρ₂0) hne0
    refine B.not_f8r1d hmin hL hR (Z.σ (s + 2)) hσ.2.1 hσ0 β.1 (pathVal v₁) Am r ρ₁'' σ₂' ρ₂' hD
      hzV hzr (not_ftm_prefix_of_long hσ hiB hAB0)
      (not_ftm_suffix_of_long hσ hiV₁ (by rw [hρ₁v]; exact hρ₁0))
      (not_ftm_suffix_of_long hσ hiσ₂' (by rw [hρ₂']; exact hρ₂0))
      (not_ftm_suffix_of_long hσ hiVA (by rw [Category.assoc, hρ₁v]; exact hρ₁0))
      (not_ftm_prefix_of_long hσ hiAB hVAB0) (not_ftm_prefix_of_long hσ hiB hVA0) ?_
      (by simpa only [Category.assoc, hρ₁v] using hn1)
      (not_ftm_prefix_of_long hσ hiB (by rw [hr]; exact hρn0))
      (not_ftm_prefix_of_long hσ hir₁' (by rw [hσ₂']; exact hσ₂0))
      (not_ftm_prefix_of_long hσ hiρ₁'' (by rw [Category.assoc, hσ₂v]; exact hσ₂0))
      (by simpa only [Category.assoc, hσ₂v] using hn2)
      (by rw [hρ₂']; exact not_factorsThrough_of_not_isLong hσ hρ₂0 hρ₂l)
      β.2.2.1 hiV₁ hiA hir hiρ₁'' hiσ₂' hiρ₂' hAρ₂
      (fun ⟨g, hg⟩ ↦ hσ0 (by
        rw [← hσv, ← hg]; simp only [← Category.assoc, hzV, zero_comp]))
      (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg]; exact hσ₂v⟩)
      hVW hWV hWVA (fun ⟨g, hg⟩ ↦ hβρ ⟨g, by rw [hg, Category.assoc]; exact hρ₁v⟩) hrA
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩) hVAr hAr
      (fun ⟨g, hg⟩ ↦ hσ₂0 (by rw [← hσ₂v, ← Category.assoc, ← hg, Category.assoc, hzr,
        comp_zero]))
      (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
    exact not_ftm_prefix_of_long hσ (not_isIso_pathVal w' hw'pos) (by rw [hβw]; exact hσ0)

include B in
/-- **BO13a Lemma 8, reflecting case, figures 8.5–8.8**: with `ρₙ = ρₙ' ≫ v₂`, everything
but the final situation `hR5` (`σₙ = ρₙ' ≫ σₙ'`) is contradictory. -/
theorem l8_mid
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (h4 : NoCrown4 P) (Z : ZChain P) (s : ℕ) (hσ : IsLong (Z.σ (s + 2)))
    (hρ₁l : ¬IsLong (Z.ρ (s + 3))) (hρnl : ¬IsLong (Z.ρ (s + 2)))
    (hnbr : IsLong (Z.ρ (s + 1)) → ¬IsLong (Z.σ (s + 1)) ∧ ¬IsLong (Z.σ s))
    {a' b' : P} (τ' : a' ⟶ b') (hτ' : IsLong τ')
    (hτσ : (⟨_, _, Z.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, τ'⟩)
    {a d : RayVert P} (v₁ : Quiver.Path (RayVert.mk (Z.x (s + 3))) a)
    (v₂ : Quiver.Path a (RayVert.mk (Z.z (s + 2))))
    (β : RayVert.mk (Z.x (s + 3)) ⟶ d) (w' : Quiver.Path d (RayVert.mk (Z.z (s + 2))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = Z.σ (s + 2))
    (hw : pathVal (β.toPath.comp w') = Z.σ (s + 2))
    (hni : ¬Interlaced (v₁.comp v₂) (β.toPath.comp w'))
    (hβρ : ¬∃ g, β.1 ≫ g = Z.ρ (s + 3))
    (ρ₁' : a.out ⟶ Z.z (s + 3)) (hρ₁' : pathVal v₁ ≫ ρ₁' = Z.ρ (s + 3))
    (σ₂' : Z.x (s + 4) ⟶ a.out) (hσ₂' : σ₂' ≫ ρ₁' = Z.σ (s + 3))
    (hz : σ₂' ≫ pathVal v₂ = 0) (r : Z.x (s + 2) ⟶ a.out) (hr : r ≫ pathVal v₂ = Z.ρ (s + 2))
    (hD86 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F86.thin) k))
    (hD87 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F87.thin) k))
    (hR5 : ∀ (s' : a.out ⟶ Z.z (s + 1)) (ρ₂' : a.out ⟶ Z.z (s + 4)), r ≫ s' = Z.σ (s + 1) →
      σ₂' ≫ ρ₂' = Z.ρ (s + 4) → r ≫ ρ₁' = 0 → pathVal v₁ ≫ ρ₂' = 0 → pathVal v₁ ≫ s' = 0 →
        ¬IsLong (Z.ρ (s + 4)) → False) : False := by
  have hσ0 := hσ.1
  have hv1 : ¬∃ c, Z.σ (s + 2) ≫ c = Z.ρ (s + 3) := Z.valley₁ (s + 2)
  have hv2 : ¬∃ c, Z.ρ (s + 3) ≫ c = Z.σ (s + 2) := Z.valley₂ (s + 2)
  have hp1 : ¬∃ c, c ≫ Z.σ (s + 3) = Z.ρ (s + 3) := Z.peak₁ (s + 3)
  have hp2 : ¬∃ c, c ≫ Z.ρ (s + 3) = Z.σ (s + 3) := Z.peak₂ (s + 3)
  have hw1 : ¬∃ c, Z.σ (s + 3) ≫ c = Z.ρ (s + 4) := Z.valley₁ (s + 3)
  have hw2 : ¬∃ c, Z.ρ (s + 4) ≫ c = Z.σ (s + 3) := Z.valley₂ (s + 3)
  have hq1 : ¬∃ c, c ≫ Z.σ (s + 2) = Z.ρ (s + 2) := Z.peak₁ (s + 2)
  have hq2 : ¬∃ c, c ≫ Z.ρ (s + 2) = Z.σ (s + 2) := Z.peak₂ (s + 2)
  have hu1 : ¬∃ c, Z.σ (s + 1) ≫ c = Z.ρ (s + 2) := Z.valley₁ (s + 1)
  have hu2 : ¬∃ c, Z.ρ (s + 2) ≫ c = Z.σ (s + 1) := Z.valley₂ (s + 1)
  have hρ₁0 := Z.ρ_ne (s + 3)
  have hσ₂0 := Z.σ_ne (s + 3)
  have hρ₂0 := Z.ρ_ne (s + 4)
  have hρn0 := Z.ρ_ne (s + 2)
  have hσn0 := Z.σ_ne (s + 1)
  have hiV₁ := not_isIso_pathVal v₁ hv₁
  have hiV₂ := not_isIso_pathVal v₂ hv₂
  have hV : pathVal v₁ ≫ pathVal v₂ = Z.σ (s + 2) := by rw [← pathVal_comp]; exact hv
  have hw'pos : 0 < w'.length := by
    by_contra h0
    have hl : w'.length = 0 := by omega
    cases w' with
    | cons _ _ => simp at hl
    | nil =>
      apply hσ.2.2.1
      rw [← hw, Quiver.Path.comp_nil, pathVal_toPath]
      exact β.2
  have hβw : β.1 ≫ pathVal w' = Z.σ (s + 2) := by rw [← hw, pathVal_comp, pathVal_toPath]
  have hval : pathVal (v₁.comp v₂) = pathVal (β.toPath.comp w') := hv.trans hw.symm
  have hVW : ¬∃ g, pathVal v₁ ≫ g = β.1 := by
    have := prefix_cross hL hR _ _ hval (by rw [hv]; exact hσ0) hni v₁ v₂ β.toPath w' rfl rfl
      hv₁ hw'pos
    simpa only [pathVal_toPath] using this
  have hWV : ¬∃ g, β.1 ≫ g = pathVal v₁ := by
    have := prefix_cross hL hR _ _ hval.symm (by rw [hw]; exact hσ0) (fun h ↦ hni h.symm)
      β.toPath w' v₁ v₂ rfl rfl (by simp) hv₂
    simpa only [pathVal_toPath] using this
  have hir₁' : ¬IsIso ρ₁' := fun h ↦ hv2 ⟨inv ρ₁' ≫ pathVal v₂, by
    rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc, hV]⟩
  have hiσ₂' : ¬IsIso σ₂' := fun h ↦ hp1 ⟨pathVal v₁ ≫ inv σ₂', by
    rw [← hρ₁', ← hσ₂']; simp⟩
  have hir : ¬IsIso r := fun h ↦ hq2 ⟨pathVal v₁ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, hV]⟩
  have hn1 : ¬FactorsThroughMorphism (Z.σ (s + 2)) (Z.ρ (s + 3)) :=
    not_factorsThrough_of_not_isLong hσ hρ₁0 hρ₁l
  have hn2 : ¬FactorsThroughMorphism (Z.σ (s + 2)) (Z.σ (s + 3)) :=
    not_ftm_valley_peak hQ hσ hρ₁0 hσ₂0 hv1 hv2 hp1 hp2
  -- figure 2.1: `ρₙ' ≫ ρ₁' = 0`
  have hzr : r ≫ ρ₁' = 0 := by
    by_contra hne0
    exact no_fig21 hL hR h4 (pathVal v₁) r (pathVal v₂) ρ₁'
      (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hr, ← hg, Category.assoc, hV]⟩)
      (fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hV, ← hg, ← hr, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hρ₁', ← hg, ← Category.assoc, hV]⟩)
      (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hV, ← hg, ← hρ₁', Category.assoc]⟩)
      (by rw [hV]; exact hσ0) (by rw [hr]; exact hρn0) hne0 (by rw [hρ₁']; exact hρ₁0)
  have hrσ₂' : ¬∃ g, g ≫ r = σ₂' := fun ⟨g, hg⟩ ↦ hσ₂0 (by
    rw [← hσ₂', ← hg, Category.assoc, hzr, comp_zero])
  have hσ₂'r : ¬∃ g, g ≫ σ₂' = r := fun ⟨g, hg⟩ ↦ hρn0 (by
    rw [← hr, ← hg, Category.assoc, hz, comp_zero])
  -- `ρ₂` long or not through `σ₂'`: figure 8.6
  by_cases hR3 : IsLong (Z.ρ (s + 4)) ∨ ¬∃ g, σ₂' ≫ g = Z.ρ (s + 4)
  · obtain ⟨t, φ, hiφ, hφσ₂, hσ₂'φ, h0φ⟩ : ∃ (t : P) (φ : Z.x (s + 4) ⟶ t), ¬IsIso φ ∧
        (¬∃ g, φ ≫ g = Z.σ (s + 3)) ∧ (¬∃ g, σ₂' ≫ g = φ) ∧
          ¬FactorsThroughMorphism (Z.σ (s + 2)) φ := by
      by_cases hl : IsLong (Z.ρ (s + 4))
      · obtain ⟨T, φ, hφ, hφσ⟩ := B.exists_first_not hmin hL hR hl (hcont _ hl) (Z.σ (s + 3))
          hσ₂0 hw2 hw1
        refine ⟨T, φ, hφ.2.1, hφσ, ?_, not_factorsThrough_irr hσ.2.1 hσ0 hσ.2.2.1 hφ⟩
        rintro ⟨g, hg⟩
        rcases hφ.2.2 _ σ₂' g hg.symm with h | h
        · exact hiσ₂' h
        · exact hφσ ⟨inv g ≫ ρ₁', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hσ₂']⟩
      · exact ⟨_, Z.ρ (s + 4), Z.ρ_not_isIso _, hw2, hR3.resolve_left hl,
          not_factorsThrough_of_not_isLong hσ hρ₂0 hl⟩
    exact B.not_f86 hmin hL hR (Z.σ (s + 2)) hσ.2.1 hσ0 β.1 (pathVal v₁) r ρ₁' σ₂' φ hD86 hzr
      (not_ftm_suffix_of_long hσ hiV₁ (by rw [hρ₁']; exact hρ₁0))
      (not_ftm_prefix_of_long hσ hiV₂ (by rw [hV]; exact hσ0))
      (not_ftm_prefix_of_long hσ (not_isIso_pathVal w' hw'pos) (by rw [hβw]; exact hσ0))
      (by rw [hρ₁']; exact hn1) (not_ftm_prefix_of_long hσ hiV₂ (by rw [hr]; exact hρn0))
      (not_ftm_prefix_of_long hσ hir₁' (by rw [hσ₂']; exact hσ₂0)) h0φ (by rw [hσ₂']; exact hn2)
      β.2.2.1 hiV₁ hir hir₁' hiσ₂' hiφ hVW hWV
      (fun ⟨g, hg⟩ ↦ hβρ ⟨g, by rw [hg]; exact hρ₁'⟩) hσ₂'φ
      (fun ⟨g, hg⟩ ↦ hφσ₂ ⟨g ≫ ρ₁', by rw [← Category.assoc, hg, hσ₂']⟩)
      (fun ⟨g, hg⟩ ↦ hφσ₂ ⟨g, by rw [hg, hσ₂']⟩)
      (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hr, ← hg, Category.assoc, hV]⟩)
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hV, ← hg, ← hr, Category.assoc]⟩) hrσ₂'
      (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩) hσ₂'r
  push Not at hR3
  obtain ⟨hρ₂l, ρ₂', hρ₂'⟩ := hR3
  have hzV : pathVal v₁ ≫ ρ₂' = 0 := by
    by_contra hne0
    exact no_fig21 hL hR h4 (pathVal v₁) σ₂' ρ₁' ρ₂'
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂', Category.assoc, hg, hρ₂']⟩)
      (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂']⟩)
      (by rw [hρ₁']; exact hρ₁0) (by rw [hσ₂']; exact hσ₂0) (by rw [hρ₂']; exact hρ₂0) hne0
  by_cases hR4 : ∃ s', r ≫ s' = Z.σ (s + 1)
  · obtain ⟨s', hs'⟩ := hR4
    refine hR5 s' ρ₂' hs' hρ₂' hzr hzV ?_ hρ₂l
    by_contra hne0
    exact no_fig21 hL hR h4 (pathVal v₁) r (pathVal v₂) s'
      (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hr, ← hg, Category.assoc, hV]⟩)
      (fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hV, ← hg, ← hr, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hu2 ⟨g, by rw [← hr, Category.assoc, hg, hs']⟩)
      (fun ⟨g, hg⟩ ↦ hu1 ⟨g, by rw [← hs', Category.assoc, hg, hr]⟩)
      (by rw [hV]; exact hσ0) (by rw [hr]; exact hρn0) (by rw [hs']; exact hσn0) hne0
  -- `σₙ` not through `ρₙ'`: figure 8.7 (or 8.8)
  have hσnr : ¬∃ g, Z.σ (s + 1) ≫ g = r := fun ⟨g, hg⟩ ↦ hu1 ⟨g ≫ pathVal v₂, by
    rw [← Category.assoc, hg, hr]⟩
  have f87 : ∀ {a₁ b₁ : P} (τ : a₁ ⟶ b₁), IsLong τ → ¬FactorsThroughMorphism τ (Z.ρ (s + 3)) →
      ¬FactorsThroughMorphism τ (Z.σ (s + 3)) → ¬FactorsThroughMorphism τ (Z.σ (s + 1)) →
      ¬FactorsThroughMorphism τ (Z.ρ (s + 1)) → ¬FactorsThroughMorphism τ (Z.σ s) → False := by
    intro a₁ b₁ τ hτ t1 t2 t3 t4 t5
    exact B.not_f87 hmin hL hR τ hτ.2.1 hτ.1 β.1 (pathVal v₁) σ₂' ρ₁' r (Z.σ (s + 1))
      (Z.ρ (s + 1)) (Z.σ s) hD87 hzr
      (not_ftm_suffix_of_long hτ hiV₁ (by rw [hρ₁']; exact hρ₁0))
      (not_ftm_prefix_of_long hτ hiV₂ (by rw [hV]; exact hσ0))
      (not_ftm_prefix_of_long hτ (not_isIso_pathVal w' hw'pos) (by rw [hβw]; exact hσ0))
      (by rw [hρ₁']; exact t1) (not_ftm_prefix_of_long hτ hiV₂ (by rw [hr]; exact hρn0)) t3 t4
      t5 (not_ftm_prefix_of_long hτ hir₁' (by rw [hσ₂']; exact hσ₂0)) (by rw [hσ₂']; exact t2)
      β.2.2.1 hiV₁ hiσ₂' hir₁' hir (Z.σ_not_isIso _) (Z.ρ_not_isIso _) (Z.σ_not_isIso _) hVW hWV
      (fun ⟨g, hg⟩ ↦ hβρ ⟨g, by rw [hg]; exact hρ₁'⟩) hR4 hσnr (Z.valley₂ s) (Z.valley₁ s)
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hr, ← hg, Category.assoc, hV]⟩)
      (fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hV, ← hg, ← hr, Category.assoc]⟩) hrσ₂' (Z.peak₁ (s + 1))
      (Z.peak₂ (s + 1)) (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
      hσ₂'r
  by_cases hρn1 : FactorsThroughMorphism (Z.σ (s + 2)) (Z.ρ (s + 1))
  · have hρn1l : IsLong (Z.ρ (s + 1)) := hσ.of_factorsThrough (Z.ρ_ne _) hρn1
    obtain ⟨hσnl, hσn1l⟩ := hnbr hρn1l
    by_cases hσ₂l : IsLong (Z.σ (s + 3))
    · -- figure 8.8 in `P/σ₂`
      obtain ⟨T, φ, hφ, hφρ⟩ := B.exists_first_not hmin hL hR hσ₂l (hcont _ hσ₂l) (Z.ρ (s + 4))
        hρ₂0 hw1 hw2
      have hφσ : ¬∃ g, φ ≫ g = σ₂' := fun ⟨g, hg⟩ ↦ hφρ ⟨g ≫ ρ₂', by
        rw [← Category.assoc, hg, hρ₂']⟩
      refine B.not_f88 hmin hL hR (Z.σ (s + 3)) hσ₂l.2.1 hσ₂0 (pathVal v₁) β.1 σ₂' φ r
        (Z.σ (s + 1)) (not_ftm_prefix_of_long hσ₂l hiV₂ (by rw [hV]; exact hσ0))
        (not_ftm_prefix_of_long hσ₂l (not_isIso_pathVal w' hw'pos) (by rw [hβw]; exact hσ0))
        (not_ftm_prefix_of_long hσ₂l hir₁' (by rw [hσ₂']; exact hσ₂0))
        (not_factorsThrough_irr hσ₂l.2.1 hσ₂0 hσ₂l.2.2.1 hφ)
        (not_ftm_prefix_of_long hσ₂l hiV₂ (by rw [hr]; exact hρn0))
        (not_factorsThrough_of_not_isLong hσ₂l hσn0 hσnl) hiV₁ β.2.2.1 hiσ₂' hφ.2.1 hir
        (Z.σ_not_isIso _) hVW hWV ?_ hφσ hR4 hσnr
        (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
        (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hr, ← hg, Category.assoc, hV]⟩)
        (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩) hσ₂'r
        (fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hV, ← hg, ← hr, Category.assoc]⟩) hrσ₂'
      rintro ⟨g, hg⟩
      rcases hφ.2.2 _ σ₂' g hg.symm with h | h
      · exact hiσ₂' h
      · exact hφσ ⟨inv g, by rw [← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id]⟩
    · -- figure 8.7 in `P/τ'`
      exact f87 τ' hτ' (not_factorsThrough_of_not_isLong hτ' hρ₁0 hρ₁l)
        (not_factorsThrough_of_not_isLong hτ' hσ₂0 hσ₂l)
        (not_factorsThrough_of_not_isLong hτ' hσn0 hσnl)
        (fun h ↦ not_ftm_of_ne hτ' hσ0 hτσ (ftm_trans_long hσ (Z.ρ_ne _) hρn1 h))
        (not_factorsThrough_of_not_isLong hτ' (Z.σ_ne _) hσn1l)
  · -- figure 8.7 in `P/σ₁`
    refine f87 _ hσ hn1 hn2 (l6_not_ftm_nbr hQ hσ hρn0 hσn0 hq1 hq2 hu1 hu2) hρn1 ?_
    intro h
    have hσsl : IsLong (Z.σ s) := hσ.of_factorsThrough (Z.σ_ne _) h
    obtain ⟨hx, hy, he⟩ := hσ.2.2.2 _ (Z.σ_ne _) h
    exact Z.not_ftm_σ_add_two h4 s hσsl ⟨eqToHom hx.symm, eqToHom hy, by rw [he]; simp⟩

end MulBasis

end RayQuiver

end LargeIndecomposable
