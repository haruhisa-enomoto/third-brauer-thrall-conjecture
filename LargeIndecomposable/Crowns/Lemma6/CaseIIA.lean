module

public import LargeIndecomposable.Crowns.Lemma6.Split
public import LargeIndecomposable.Cleaving.Shapes.ShapeF67
public import LargeIndecomposable.Cleaving.Shapes.ShapeF68
public import LargeIndecomposable.Cleaving.Shapes.ShapeF69
public import LargeIndecomposable.Cleaving.Shapes.ShapeF610
public import LargeIndecomposable.Cleaving.Shapes.ShapeF611
public import LargeIndecomposable.Cleaving.Shapes.ShapeF612
public import LargeIndecomposable.Cleaving.Shapes.ShapeF613

/-!
# BO13a Lemma 6, case II.A: `ρₙ` factors through `w` (figures 6.7–6.13)

Abstract instantiations: `σ`, `ρ` long neighbours with the data of figure 6.0,
a split `β w = p₁ p₂` (`L6WSplit`) with `ρₙ = ρₙ' ≫ w₂`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [IsFiniteRayCategory P]

/-- Two incomparable long neighbours `σ, ρ` out of `x`: `ρ` divides no nonzero
morphism into the codomain of `σ`. -/
lemma l6_ρ_not_to_y₀ (hQ : OneSidedCyclic P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ) {X : P}
    (f : X ⟶ y₀) (hf : f ≠ 0) : ¬FactorsThroughMorphism ρ f := by
  intro h
  obtain ⟨hx, hy, -⟩ := hρ.2.2.2 f hf h
  subst hx hy
  refine not_parallel hQ σ ρ hσ.1 hρ.1 hv1 hv2 ?_ ?_
  · rintro ⟨c, hc⟩
    obtain ⟨h1, h2, he⟩ := hσ.2.2.2 ρ hρ.1 ⟨c, 𝟙 _, by rw [Category.comp_id, hc]⟩
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    exact hv1 ⟨𝟙 _, by rw [Category.comp_id, he]⟩
  · rintro ⟨c, hc⟩
    obtain ⟨h1, h2, he⟩ := hρ.2.2.2 σ hσ.1 ⟨c, 𝟙 _, by rw [Category.comp_id, hc]⟩
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    exact hv2 ⟨𝟙 _, by rw [Category.comp_id, he]⟩

/-- `σ` does not divide the other crown neighbour `σₙ` of its neighbour `ρₙ`. -/
lemma l6_not_ftm_nbr (hQ : OneSidedCyclic P) {x y₀ x' zn : P} {σ : x ⟶ y₀} (hσ : IsLong σ)
    {ρn : x' ⟶ y₀} {σn : x' ⟶ zn} (hρn0 : ρn ≠ 0) (hσn0 : σn ≠ 0)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (hq1 : ¬∃ c, σn ≫ c = ρn) (hq2 : ¬∃ c, ρn ≫ c = σn) : ¬FactorsThroughMorphism σ σn := by
  intro h
  obtain ⟨hx, hy, he⟩ := hσ.2.2.2 σn hσn0 h
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  rw [he] at hq1 hq2
  exact not_parallel hQ σ ρn hσ.1 hρn0 hq1 hq2 hp1 hp2

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a figure 6.7** (category 11): `u₂'` is not a composite `d ≫ eu`. -/
theorem l6_f67
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) (S : L6WSplit D) {x' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0)
    (hρnl : ¬IsLong ρn) (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (r : x' ⟶ S.c.out) (hr : r ≫ S.w₂ = ρn) {c : RayVert P} (u'' : Quiver.Path D.m c)
    (eu : c ⟶ RayVert.mk y₁) (hu : D.u₂' = u''.cons eu) (hu'' : 0 < u''.length)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F67.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρβ := B.l6_ρβ hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hσβ' := B.l6_σβ' hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hρw₁ := B.l6s_ρ_w₁ hmin hL hR hσ0 hρ0 hv1 hv2 S
  have hw₂U := S.w₂_U hL hR hσ0
  set d := pathVal u'' with hd
  have hdeu : d ≫ eu.1 = D.U' := by change _ = pathVal D.u₂'; rw [hu]; rfl
  have hρd : D.ψ ≫ d ≫ eu.1 = ρ := by rw [hdeu, D.ψU']
  have hid : ¬IsIso d := not_isIso_pathVal u'' hu''
  have hρσ := not_ftm_long_dom hρ hσ0 hv2
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨S.w₁ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, S.w₁w₂]⟩
  -- crossing in the contour `(β' w', ψ u'' eu)`
  have hcross : ¬∃ g, D.β'.1 ≫ g = D.ψ ≫ d := by
    have hval : pathVal (D.β'.toPath.comp D.w') =
        pathVal (((D.α.toPath.comp D.χ).comp u'').comp eu.toPath) := by
      rw [D.hρw, Quiver.Path.comp_assoc (D.α.toPath.comp D.χ) u'' eu.toPath]
      change ρ = pathVal ((D.α.toPath.comp D.χ).comp (u''.cons eu))
      rw [← hu, D.hρu]
    have := (contour_cross hL hR D.β'.toPath D.w' ((D.α.toPath.comp D.χ).comp u'') eu.toPath
      hval (by rw [D.hρw]; exact hρ0)
      (by rw [Quiver.Path.comp_assoc (D.α.toPath.comp D.χ) u'' eu.toPath]
          change ¬Interlaced _ ((D.α.toPath.comp D.χ).comp (u''.cons eu))
          rw [← hu]; exact fun h ↦ D.hniρ h.symm) (by simp) (by simp)).2
    rwa [pathVal_toPath, pathVal_comp (D.α.toPath.comp D.χ) u''] at this
  refine B.not_f67 hmin hL hR ρ hρ.2.1 hρ0 S.w₁ D.ψ S.w₂ D.U r D.β'.1 d hD
    (hc0 := by rw [D.ψU, S.w₁w₂])
    (h0_b_y₀ := fun h ↦ hρσ (by rw [← S.w₁w₂]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_c := not_ftm_mid hρ0 D.ψ_not_isIso hρd)
    (h0_m_y₀ := fun h ↦ hρσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _))
    (h0_x_b := fun h ↦ hρσ (by rw [← S.w₁w₂]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_b' := not_ftm_prefix hρ0 (D.W'_not_isIso hρ.2.2.1) D.βW')
    (h0_x_c := not_ftm_prefix hρ0 eu.2.2.1 (by rw [Category.assoc]; exact hρd))
    (h0_x_m := not_ftm_prefix hρ0 D.U'_not_isIso D.ψU')
    (h0_x_y₀ := by rw [S.w₁w₂]; exact hρσ)
    (h0_x'_b := fun h ↦ hρnl (hρ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x'_y₀ := by rw [hr]; exact not_factorsThrough_of_not_isLong hρ hρn0 hρnl)
    (hi_w₁ := S.w₁_not_isIso) (hi_ψ := D.ψ_not_isIso) (hi_w₂ := S.w₂_not_isIso)
    (hi_U := D.U_not_isIso) (hi_r := hir) (hi_v := D.β'.2.2.1) (hi_d := hid)
    (hlft_m_c_y₀ := by
      rintro ⟨g, hg⟩
      have hle := D.hmax ⟨_, D.ψ ≫ d⟩ ⟨pathVal D.χ ≫ d, by
        change D.α.1 ≫ pathVal D.χ ≫ d = D.ψ ≫ d
        simp only [L6Data.ψ]
        rw [pathVal_comp D.α.toPath D.χ, pathVal_toPath, Category.assoc]⟩
        ⟨g, by change (D.ψ ≫ d) ≫ g = σ; rw [Category.assoc, hg, D.ψU]⟩
        ⟨eu.1, by change (D.ψ ≫ d) ≫ eu.1 = ρ; rw [Category.assoc, hρd]⟩
      obtain ⟨k', hk'⟩ := hle
      change (D.ψ ≫ d) ≫ k' = D.ψ at hk'
      have hdk : d ≫ k' = 𝟙 _ := hL D.ψ _ _ (by rw [Category.comp_id, ← Category.assoc, hk'])
        (by rw [← Category.assoc, hk']; exact fun h ↦ hσ0 (by rw [← D.ψU, h, zero_comp]))
      exact not_split_mono hid ⟨k', hdk⟩)
    (hlft_m_y₀_c := fun ⟨g, hg⟩ ↦ hv1 ⟨g ≫ eu.1, by
      rw [← D.ψU, Category.assoc, ← Category.assoc D.U, hg, hρd]⟩)
    (hlft_x_b_m := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩)
    (hlft_x_b_b' := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ D.W', by rw [← Category.assoc, hg, D.βW']⟩)
    (hlft_x_b_c := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ eu.1, by
      rw [← Category.assoc, hg, Category.assoc, hρd]⟩)
    (hlft_x_b'_b := fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ S.w₂, by rw [← Category.assoc, hg, S.w₁w₂]⟩)
    (hlft_x_b'_m := fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩)
    (hlft_x_b'_y₀ := fun ⟨g, hg⟩ ↦ hσβ' ⟨g, by rw [hg, S.w₁w₂]⟩)
    (hlft_x_b'_c := hcross)
    (hlft_x_m_b := S.ψ_w₁ hL hR hσ0)
    (hlft_x_m_b' := fun ⟨g, hg⟩ ↦ by
      rcases D.β'.2.2.2 _ D.ψ g hg.symm with h | h
      · exact D.ψ_not_isIso h
      · exact hσβ' ⟨inv g ≫ D.U, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU]⟩)
    (hrgt_m_b_y₀ := hw₂U.1) (hrgt_b_m_y₀ := hw₂U.2)
    (hrgt_x'_m_y₀ := by
      rw [hr]
      exact fun hU ↦ B.l6s_not_w₂_and_U hmin hL hR hσ S ρn hρn0 hp1 hp2 ⟨r, hr⟩ hU)
    (hrgt_x'_x_b := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, S.w₁w₂]⟩)
    (hrgt_x_x'_b := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← S.w₁w₂, ← hg, Category.assoc, hr]⟩)

include B in
/-- **BO13a figure 6.8** (category 93), in `P/τ` for a third long morphism `τ`. -/
theorem l6_f68
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) (S : L6WSplit D) (S' : L6WSplit D.swap)
    {x' x'' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ) (r : x' ⟶ S.c.out) (hr : r ≫ S.w₂ = ρn)
    (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂)
    (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂) (t : x'' ⟶ S'.c.out) (ht : t ≫ S'.w₂ = σ₂)
    {a b : P} (τ : a ⟶ b) (hτ : IsLong τ) (hτσ : ¬FactorsThroughMorphism τ σ)
    (hτρ : ¬FactorsThroughMorphism τ ρ)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F68.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρw₁ := B.l6s_ρ_w₁ hmin hL hR hσ0 hρ0 hv1 hv2 S
  have hσv := B.l6s_ρ_w₁ hmin hL hR hρ0 hσ0 hv2 hv1 S'
  have hw₂U := S.w₂_U hL hR hσ0
  have hv₂U' := S'.w₂_U hL hR hρ0
  have hvv : S'.w₁ ≫ S'.w₂ = ρ := S'.w₁w₂
  have hρnτ := not_factorsThrough_of_not_isLong hτ hρn0 hρnl
  have hσ₂τ := not_factorsThrough_of_not_isLong hτ hσ₂0 hσ₂l
  refine B.not_f68 hmin hL hR τ hτ.2.1 hτ.1 S.w₁ D.ψ S'.w₁ S.w₂ D.U D.U' S'.w₂ r t hD
    (hc0 := by rw [D.ψU, S.w₁w₂]) (hc1 := by rw [hvv, D.ψU'])
    (h0_b_y₀ := fun h ↦ hτσ (by rw [← S.w₁w₂]; exact FactorsThroughMorphism.comp_left h _))
    (h0_b'_y₁ := fun h ↦ hτρ (by rw [← hvv]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_y₀ := fun h ↦ hτσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_y₁ := fun h ↦ hτρ (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
    (h0_x_b := fun h ↦ hτσ (by rw [← S.w₁w₂]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_b' := fun h ↦ hτρ (by rw [← hvv]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_m := fun h ↦ hτσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_y₀ := by rw [S.w₁w₂]; exact hτσ) (h0_x_y₁ := by rw [D.ψU']; exact hτρ)
    (h0_x'_b := fun h ↦ hρnτ (by rw [← hr]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x'_y₀ := by rw [hr]; exact hρnτ)
    (h0_x''_b' := fun h ↦ hσ₂τ (by rw [← ht]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x''_y₁ := by rw [ht]; exact hσ₂τ)
    (hi_w₁ := S.w₁_not_isIso) (hi_ψ := D.ψ_not_isIso) (hi_v := S'.w₁_not_isIso)
    (hi_w₂ := S.w₂_not_isIso) (hi_U := D.U_not_isIso) (hi_U' := D.U'_not_isIso)
    (hi_v₂ := S'.w₂_not_isIso)
    (hi_r := fun h ↦ hp2 ⟨S.w₁ ≫ inv r, by
      rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, S.w₁w₂]⟩)
    (hi_t := fun h ↦ hm1 ⟨S'.w₁ ≫ inv t, by
      rw [← ht, Category.assoc, IsIso.inv_hom_id_assoc, hvv]⟩)
    (hlft_m_y₀_y₁ := D.U_U' hv1) (hlft_m_y₁_y₀ := D.U'_U hv2)
    (hlft_x_b_m := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩)
    (hlft_x_b_b' := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ S'.w₂, by rw [← Category.assoc, hg, hvv]⟩)
    (hlft_x_b_y₁ := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g, by rw [hg, D.ψU']⟩)
    (hlft_x_b'_b := fun ⟨g, hg⟩ ↦ hσv ⟨g ≫ S.w₂, by rw [← Category.assoc, hg, S.w₁w₂]⟩)
    (hlft_x_b'_m := fun ⟨g, hg⟩ ↦ hσv ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩)
    (hlft_x_b'_y₀ := fun ⟨g, hg⟩ ↦ hσv ⟨g, by rw [hg, S.w₁w₂]⟩)
    (hlft_x_m_b := S.ψ_w₁ hL hR hσ0) (hlft_x_m_b' := S'.ψ_w₁ hL hR hρ0)
    (hrgt_m_b_y₀ := hw₂U.1) (hrgt_m_b'_y₁ := hv₂U'.1) (hrgt_b_m_y₀ := hw₂U.2)
    (hrgt_x'_m_y₀ := by
      rw [hr]
      exact fun hU ↦ B.l6s_not_w₂_and_U hmin hL hR hσ S ρn hρn0 hp1 hp2 ⟨r, hr⟩ hU)
    (hrgt_b'_m_y₁ := hv₂U'.2)
    (hrgt_x''_m_y₁ := by
      rw [ht]
      exact fun hU ↦ B.l6s_not_w₂_and_U hmin hL hR hρ S' σ₂ hσ₂0 hm2 hm1 ⟨t, ht⟩ hU)
    (hrgt_x'_x_b := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, S.w₁w₂]⟩)
    (hrgt_x''_x_b' := fun ⟨g, hg⟩ ↦ hm2 ⟨g, by rw [← ht, ← hg, Category.assoc, hvv]⟩)
    (hrgt_x_x'_b := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← S.w₁w₂, ← hg, Category.assoc, hr]⟩)
    (hrgt_x_x''_b' := fun ⟨g, hg⟩ ↦ hm1 ⟨g, by rw [← hvv, ← hg, Category.assoc, ht]⟩)

include B in
/-- **BO13a figure 6.9** (`D̃₈`), in `P/σ`. -/
theorem l6_f69
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) (S : L6WSplit D) (S' : L6WSplit D.swap)
    {x' x'' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ) (r : x' ⟶ S.c.out) (hr : r ≫ S.w₂ = ρn)
    (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂)
    (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂) (t : x'' ⟶ S'.c.out) (ht : t ≫ S'.w₂ = σ₂)
    {c₁ c₁' : RayVert P} (f₁ : RayVert.mk x ⟶ c₁) (q : Quiver.Path c₁ S.c)
    (hq : S.p₁ = f₁.toPath.comp q) (hql : 0 < q.length) (hra : ¬∃ g, g ≫ pathVal q = r)
    (f₁' : RayVert.mk x ⟶ c₁') (q' : Quiver.Path c₁' S'.c)
    (hq' : S'.p₁ = f₁'.toPath.comp q') (hql' : 0 < q'.length)
    (hta : ¬∃ g, g ≫ pathVal q' = t) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hw₂U := S.w₂_U hL hR hσ0
  have hv₂U' := S'.w₂_U hL hR hρ0
  have hvv : S'.w₁ ≫ S'.w₂ = ρ := S'.w₁w₂
  have hσq : f₁.1 ≫ pathVal q ≫ S.w₂ = σ := by
    have := S.w₁w₂
    change pathVal S.p₁ ≫ _ = σ at this
    rw [hq, pathVal_comp, pathVal_toPath, Category.assoc] at this
    exact this
  have hρq : f₁'.1 ≫ pathVal q' ≫ S'.w₂ = ρ := by
    have := hvv
    change pathVal S'.p₁ ≫ _ = ρ at this
    rw [hq', pathVal_comp, pathVal_toPath, Category.assoc] at this
    exact this
  have hσρ := not_ftm_long_dom hσ hρ0 hv1
  refine B.not_f69 hmin hL hR σ hσ.2.1 hσ0 r (pathVal q) S.w₂ D.U D.U' S'.w₂ (pathVal q') t
    (h0_x'_b := fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x'_y₀ := by rw [hr]; exact not_factorsThrough_of_not_isLong hσ hρn0 hρnl)
    (h0_c_b := not_ftm_mid hσ0 f₁.2.2.1 hσq)
    (h0_c_y₀ := not_ftm_suffix hσ0 f₁.2.2.1 hσq)
    (h0_b_y₀ := not_ftm_suffix hσ0 S.w₁_not_isIso S.w₁w₂)
    (h0_m_y₀ := not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU)
    (h0_m_y₁ := fun h ↦ hσρ (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
    (h0_b'_y₁ := fun h ↦ hσρ (by rw [← hvv]; exact FactorsThroughMorphism.comp_left h _))
    (h0_c'_b' := fun h ↦ hσρ (by
      rw [← hρq, ← Category.assoc]
      exact FactorsThroughMorphism.comp_right (FactorsThroughMorphism.comp_left h _) _))
    (h0_c'_y₁ := fun h ↦ hσρ (by
      rw [← hρq]; exact FactorsThroughMorphism.comp_left h _))
    (h0_x''_b' := fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 (by
      rw [← ht]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x''_y₁ := by rw [ht]; exact not_factorsThrough_of_not_isLong hσ hσ₂0 hσ₂l)
    (hi_r := fun h ↦ hp2 ⟨S.w₁ ≫ inv r, by
      rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, S.w₁w₂]⟩)
    (hi_a := not_isIso_pathVal q hql) (hi_W := S.w₂_not_isIso) (hi_U := D.U_not_isIso)
    (hi_U' := D.U'_not_isIso) (hi_W' := S'.w₂_not_isIso) (hi_a' := not_isIso_pathVal q' hql')
    (hi_t := fun h ↦ hm1 ⟨S'.w₁ ≫ inv t, by
      rw [← ht, Category.assoc, IsIso.inv_hom_id_assoc, hvv]⟩)
    (hl_U_U'_y₁ := D.U_U' hv1) (hl_U'_U_y₀ := D.U'_U hv2)
    (hr_W_U_m := hw₂U.1)
    (hr_U_W_x' := by
      rw [hr]
      exact fun hU ↦ B.l6s_not_w₂_and_U hmin hL hR hσ S ρn hρn0 hp1 hp2 ⟨r, hr⟩ hU)
    (hr_U_W_c := S.U_tail hL hR hσ0 f₁ q hq) (hr_U_W_b := hw₂U.2)
    (hr_r_a_c := fun ⟨g, hg⟩ ↦ hp2 ⟨f₁.1 ≫ g, by
      rw [← hσq, ← hg, ← hr]; simp only [Category.assoc]⟩)
    (hr_a_r_x' := hra) (hr_U'_W'_b' := hv₂U'.2)
    (hr_U'_W'_c' := S'.U_tail hL hR hρ0 f₁' q' hq')
    (hr_U'_W'_x'' := by
      rw [ht]
      exact fun hU ↦ B.l6s_not_w₂_and_U hmin hL hR hρ S' σ₂ hσ₂0 hm2 hm1 ⟨t, ht⟩ hU)
    (hr_W'_U'_m := hv₂U'.1) (hr_a'_t_x'' := hta)
    (hr_t_a'_c' := fun ⟨g, hg⟩ ↦ hm1 ⟨f₁'.1 ≫ g, by
      rw [← hρq, ← hg, ← ht]; simp only [Category.assoc]⟩)

include B in
/-- **BO13a figure 6.10** (category 11): `σ₂ = σ₂' ≫ u₂'` forces `σ₂' ≫ u₂ = 0`. -/
theorem l6_f610
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) (S : L6WSplit D)
    {x' x'' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ) (r : x' ⟶ S.c.out) (hr : r ≫ S.w₂ = ρn)
    (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂)
    (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂) (t : x'' ⟶ D.m.out) (ht : t ≫ D.U' = σ₂)
    (htU : t ≫ D.U ≠ 0)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F610.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρw₁ := B.l6s_ρ_w₁ hmin hL hR hσ0 hρ0 hv1 hv2 S
  have hσβ' := B.l6_σβ' hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hw₂U := S.w₂_U hL hR hσ0
  have hρσ := not_ftm_long_dom hρ hσ0 hv2
  have hp1' : ¬∃ c, c ≫ σ = t ≫ D.U := by
    rintro ⟨c, hc⟩
    have h := hR (c ≫ D.ψ) t D.U (by rw [Category.assoc, D.ψU, hc]) (by
      rw [Category.assoc, D.ψU, hc]; exact htU)
    exact hm2 ⟨c, by rw [← ht, ← h, Category.assoc, D.ψU']⟩
  have hp2' : ¬∃ c, c ≫ (t ≫ D.U) = σ := by
    rintro ⟨c, hc⟩
    have h := hR (c ≫ t) D.ψ D.U (by rw [Category.assoc, hc, D.ψU]) (by
      rw [Category.assoc, hc]; exact hσ0)
    exact hm1 ⟨c, by rw [← D.ψU', ← h, Category.assoc, ht]⟩
  refine B.not_f610 hmin hL hR ρ hρ.2.1 hρ0 S.w₁ D.ψ S.w₂ D.U r D.β'.1 t hD
    (hc0 := by rw [D.ψU, S.w₁w₂])
    (h0_b_y₀ := fun h ↦ hρσ (by rw [← S.w₁w₂]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_y₀ := fun h ↦ hρσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _))
    (h0_x_b := fun h ↦ hρσ (by rw [← S.w₁w₂]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_b' := not_ftm_prefix hρ0 (D.W'_not_isIso hρ.2.2.1) D.βW')
    (h0_x_m := not_ftm_prefix hρ0 D.U'_not_isIso D.ψU')
    (h0_x_y₀ := by rw [S.w₁w₂]; exact hρσ)
    (h0_x'_b := fun h ↦ hρnl (hρ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x'_y₀ := by rw [hr]; exact not_factorsThrough_of_not_isLong hρ hρn0 hρnl)
    (h0_x''_m := fun h ↦ hσ₂l (hρ.of_factorsThrough hσ₂0 (by
      rw [← ht]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x''_y₀ := l6_ρ_not_to_y₀ hQ hσ hρ hv1 hv2 _ htU)
    (hi_w₁ := S.w₁_not_isIso) (hi_ψ := D.ψ_not_isIso) (hi_w₂ := S.w₂_not_isIso)
    (hi_U := D.U_not_isIso)
    (hi_r := fun h ↦ hp2 ⟨S.w₁ ≫ inv r, by
      rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, S.w₁w₂]⟩)
    (hi_v := D.β'.2.2.1)
    (hi_t := fun h ↦ hm1 ⟨D.ψ ≫ inv t, by
      rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc, D.ψU']⟩)
    (hlft_x_b_m := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩)
    (hlft_x_b_b' := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ D.W', by rw [← Category.assoc, hg, D.βW']⟩)
    (hlft_x_b'_b := fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ S.w₂, by rw [← Category.assoc, hg, S.w₁w₂]⟩)
    (hlft_x_b'_m := fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩)
    (hlft_x_b'_y₀ := fun ⟨g, hg⟩ ↦ hσβ' ⟨g, by rw [hg, S.w₁w₂]⟩)
    (hlft_x_m_b := S.ψ_w₁ hL hR hσ0)
    (hlft_x_m_b' := fun ⟨g, hg⟩ ↦ by
      rcases D.β'.2.2.2 _ D.ψ g hg.symm with h | h
      · exact D.ψ_not_isIso h
      · exact hσβ' ⟨inv g ≫ D.U, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU]⟩)
    (hrgt_m_b_y₀ := hw₂U.1)
    (hrgt_x''_b_y₀ := fun hW ↦ B.l6s_not_w₂_and_U hmin hL hR hσ S _ htU hp1' hp2' hW ⟨t, rfl⟩)
    (hrgt_b_m_y₀ := hw₂U.2)
    (hrgt_x'_m_y₀ := by
      rw [hr]
      exact fun hU ↦ B.l6s_not_w₂_and_U hmin hL hR hσ S ρn hρn0 hp1 hp2 ⟨r, hr⟩ hU)
    (hrgt_x'_x_b := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, S.w₁w₂]⟩)
    (hrgt_x''_x_m := fun ⟨g, hg⟩ ↦ hm2 ⟨g, by rw [← ht, ← hg, Category.assoc, D.ψU']⟩)
    (hrgt_x_x'_b := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← S.w₁w₂, ← hg, Category.assoc, hr]⟩)
    (hrgt_x_x''_m := fun ⟨g, hg⟩ ↦ hm1 ⟨g, by rw [← D.ψU', ← hg, Category.assoc, ht]⟩)

include B in
/-- **BO13a figure 6.11** (category 12), in `P/σ`. -/
theorem l6_f611
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) (S : L6WSplit D) (S' : L6WSplit D.swap)
    {x' x'' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ) (r : x' ⟶ S.c.out) (hr : r ≫ S.w₂ = ρn)
    (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂)
    (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂) (t : x'' ⟶ D.m.out) (ht : t ≫ D.U' = σ₂)
    {z₂ : P} (φ : x'' ⟶ z₂) (h0φ : ¬FactorsThroughMorphism σ φ) (hiφ : ¬IsIso φ)
    (hφ1 : ¬∃ g, t ≫ g = φ) (hφ2 : ¬∃ g, φ ≫ g = σ₂)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F611.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρw₁ := B.l6s_ρ_w₁ hmin hL hR hσ0 hρ0 hv1 hv2 S
  have hσv := B.l6s_ρ_w₁ hmin hL hR hρ0 hσ0 hv2 hv1 S'
  have hv₂U' := S'.w₂_U hL hR hρ0
  have hvv : S'.w₁ ≫ S'.w₂ = ρ := S'.w₁w₂
  have hσρ := not_ftm_long_dom hσ hρ0 hv1
  refine B.not_f611 hmin hL hR σ hσ.2.1 hσ0 D.ψ S'.w₁ D.U' S'.w₂ S.w₁ r t φ hD
    (hc0 := by rw [hvv, D.ψU'])
    (h0_b'_y₁ := fun h ↦ hσρ (by rw [← hvv]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_y₁ := fun h ↦ hσρ (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
    (h0_x_b := not_ftm_prefix hσ0 S.w₂_not_isIso S.w₁w₂)
    (h0_x_b' := fun h ↦ hσρ (by rw [← hvv]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_m := not_ftm_prefix hσ0 D.U_not_isIso D.ψU)
    (h0_x_y₁ := by rw [D.ψU']; exact hσρ)
    (h0_x'_b := fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x''_m := fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 (by
      rw [← ht]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x''_y₁ := by rw [ht]; exact not_factorsThrough_of_not_isLong hσ hσ₂0 hσ₂l)
    (h0_x''_z₂ := h0φ)
    (hi_ψ := D.ψ_not_isIso) (hi_v := S'.w₁_not_isIso) (hi_U' := D.U'_not_isIso)
    (hi_v₂ := S'.w₂_not_isIso) (hi_w₁ := S.w₁_not_isIso)
    (hi_r := fun h ↦ hp2 ⟨S.w₁ ≫ inv r, by
      rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, S.w₁w₂]⟩)
    (hi_t := fun h ↦ hm1 ⟨D.ψ ≫ inv t, by
      rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc, D.ψU']⟩) (hi_φ := hiφ)
    (hlft_x_b_m := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩)
    (hlft_x_b_b' := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g ≫ S'.w₂, by rw [← Category.assoc, hg, hvv]⟩)
    (hlft_x_b_y₁ := fun ⟨g, hg⟩ ↦ hρw₁ ⟨g, by rw [hg, D.ψU']⟩)
    (hlft_x_b'_m := fun ⟨g, hg⟩ ↦ hσv ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩)
    (hlft_x_b'_b := fun ⟨g, hg⟩ ↦ hσv ⟨g ≫ S.w₂, by rw [← Category.assoc, hg, S.w₁w₂]⟩)
    (hlft_x_m_b' := S'.ψ_w₁ hL hR hρ0) (hlft_x_m_b := S.ψ_w₁ hL hR hσ0)
    (hlft_x''_m_z₂ := hφ1)
    (hlft_x''_z₂_m := fun ⟨g, hg⟩ ↦ hφ2 ⟨g ≫ D.U', by rw [← Category.assoc, hg, ht]⟩)
    (hlft_x''_z₂_y₁ := by rw [ht]; exact hφ2)
    (hrgt_m_b'_y₁ := hv₂U'.1)
    (hrgt_x''_b'_y₁ := by
      rw [ht]
      exact fun hW ↦ B.l6s_not_w₂_and_U hmin hL hR hρ S' σ₂ hσ₂0 hm2 hm1 hW ⟨t, ht⟩)
    (hrgt_b'_m_y₁ := hv₂U'.2)
    (hrgt_x'_x_b := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, S.w₁w₂]⟩)
    (hrgt_x''_x_m := fun ⟨g, hg⟩ ↦ hm2 ⟨g, by rw [← ht, ← hg, Category.assoc, D.ψU']⟩)
    (hrgt_x_x'_b := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← S.w₁w₂, ← hg, Category.assoc, hr]⟩)
    (hrgt_x_x''_m := fun ⟨g, hg⟩ ↦ hm1 ⟨g, by rw [← D.ψU', ← hg, Category.assoc, ht]⟩)

include B in
/-- The `D̃₄` star `ψ, σ₂' ; ρ₂', u₂'` at `m` in `P/σ` (forces `ψ ≫ ρ₂' = 0`). -/
theorem l6_star_t
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (D : L6Data σ ρ) {x'' z₂ : P} (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂)
    (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂) (ρ₂ : x'' ⟶ z₂) (hρ₂0 : ρ₂ ≠ 0)
    (hs1 : ¬∃ c, σ₂ ≫ c = ρ₂) (hs2 : ¬∃ c, ρ₂ ≫ c = σ₂) (hσρ₂ : ¬FactorsThroughMorphism σ ρ₂)
    (t : x'' ⟶ D.m.out) (ht : t ≫ D.U' = σ₂) (htU : t ≫ D.U = 0) (q : D.m.out ⟶ z₂)
    (hq : t ≫ q = ρ₂) (hψq : D.ψ ≫ q ≠ 0) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hσρ := not_ftm_long_dom hσ hρ0 hv1
  refine B.not_s4s hmin hL hR σ hσ.2.1 hσ0 t D.ψ q D.U' ?_ ?_ ?_ (by rw [hq]; exact hσρ₂)
    (by rw [ht]; exact not_factorsThrough_of_not_isLong hσ hσ₂0 hσ₂l)
    (not_ftm_prefix hσ0 D.U_not_isIso D.ψU) ?_ (by rw [D.ψU']; exact hσρ) ?_
    D.ψ_not_isIso ?_ D.U'_not_isIso ?_ ?_ ?_ ?_
  · exact fun h ↦ hσρ₂ (by rw [← hq]; exact FactorsThroughMorphism.comp_left h _)
  · exact fun h ↦ hσρ (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _)
  · exact fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 (by
      rw [← ht]; exact FactorsThroughMorphism.comp_right h _))
  · -- `ψ ≫ ρ₂' ≅ σ` would give `ρ₂' = u₂` and `ρ₂ = σ₂' ≫ u₂ = 0`
    intro h
    obtain ⟨hx, hy, he⟩ := hσ.2.2.2 _ hψq h
    subst hy
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    have hqU : q = D.U := hL D.ψ q D.U (by rw [he, D.ψU]) hψq
    exact hρ₂0 (by rw [← hq, hqU, htU])
  · exact fun h ↦ hm1 ⟨D.ψ ≫ inv t, by rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc, D.ψU']⟩
  · exact fun h ↦ hs2 ⟨inv q ≫ D.U', by rw [← hq, Category.assoc, IsIso.hom_inv_id_assoc, ht]⟩
  · exact fun ⟨g, hg⟩ ↦ hs2 ⟨g, by rw [← hq, Category.assoc, hg, ht]⟩
  · exact fun ⟨g, hg⟩ ↦ hs1 ⟨g, by rw [← ht, Category.assoc, hg, hq]⟩
  · exact fun ⟨g, hg⟩ ↦ hm1 ⟨g, by rw [← D.ψU', ← hg, Category.assoc, ht]⟩
  · exact fun ⟨g, hg⟩ ↦ hm2 ⟨g, by rw [← ht, ← hg, Category.assoc, D.ψU']⟩

include B in
/-- **BO13a figure 6.12** (`Ẽ₈`-type with `σ₂' ≫ u₂ = 0`), in `P/σ`. -/
theorem l6_f612
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) (S : L6WSplit D) (S' : L6WSplit D.swap)
    {x' x'' zn z₂ : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ) (r : x' ⟶ S.c.out) (hr : r ≫ S.w₂ = ρn)
    (σn : x' ⟶ zn) (hσn0 : σn ≠ 0) (hiσn : ¬IsIso σn) (hq1 : ¬∃ c, σn ≫ c = ρn)
    (hq2 : ¬∃ c, ρn ≫ c = σn) (hrσn : ¬∃ g, r ≫ g = σn)
    (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂)
    (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂) (ρ₂ : x'' ⟶ z₂) (hρ₂0 : ρ₂ ≠ 0)
    (hs1 : ¬∃ c, σ₂ ≫ c = ρ₂) (hs2 : ¬∃ c, ρ₂ ≫ c = σ₂) (hσρ₂ : ¬FactorsThroughMorphism σ ρ₂)
    (t : x'' ⟶ D.m.out) (ht : t ≫ D.U' = σ₂) (htU : t ≫ D.U = 0) (q : D.m.out ⟶ z₂)
    (hq : t ≫ q = ρ₂) (hψq : D.ψ ≫ q = 0)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F612.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hw₂U := S.w₂_U hL hR hσ0
  have hv₂U' := S'.w₂_U hL hR hρ0
  have hvv : S'.w₁ ≫ S'.w₂ = ρ := S'.w₁w₂
  have hσρ := not_ftm_long_dom hσ hρ0 hv1
  refine B.not_f612 hmin hL hR σ hσ.2.1 hσ0 σn r S.w₂ D.U q D.U' S'.w₂ t hD (hz0 := htU)
    (h0_b_y₀ := not_ftm_suffix hσ0 S.w₁_not_isIso S.w₁w₂)
    (h0_b'_y₁ := fun h ↦ hσρ (by rw [← hvv]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_y₀ := not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU)
    (h0_m_y₁ := fun h ↦ hσρ (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_z₂ := fun h ↦ hσρ₂ (by rw [← hq]; exact FactorsThroughMorphism.comp_left h _))
    (h0_x'_b := fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x'_y₀ := by rw [hr]; exact not_factorsThrough_of_not_isLong hσ hρn0 hρnl)
    (h0_x'_zn := l6_not_ftm_nbr hQ hσ hρn0 hσn0 hp1 hp2 hq1 hq2)
    (h0_x''_m := fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 (by
      rw [← ht]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x''_y₁ := by rw [ht]; exact not_factorsThrough_of_not_isLong hσ hσ₂0 hσ₂l)
    (h0_x''_z₂ := by rw [hq]; exact hσρ₂)
    (hi_σn := hiσn)
    (hi_r := fun h ↦ hp2 ⟨S.w₁ ≫ inv r, by
      rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, S.w₁w₂]⟩)
    (hi_W := S.w₂_not_isIso) (hi_U := D.U_not_isIso)
    (hi_ρ₂' := fun h ↦ hs2 ⟨inv q ≫ D.U', by rw [← hq, Category.assoc, IsIso.hom_inv_id_assoc, ht]⟩)
    (hi_U' := D.U'_not_isIso) (hi_W' := S'.w₂_not_isIso)
    (hi_t := fun h ↦ hm1 ⟨D.ψ ≫ inv t, by
      rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc, D.ψU']⟩)
    (hlft_m_y₀_z₂ := fun ⟨g, hg⟩ ↦ hρ₂0 (by rw [← hq, ← hg, ← Category.assoc, htU, zero_comp]))
    (hlft_m_y₀_y₁ := D.U_U' hv1) (hlft_m_y₁_y₀ := D.U'_U hv2)
    (hlft_m_y₁_z₂ := fun ⟨g, hg⟩ ↦ hs1 ⟨g, by rw [← ht, Category.assoc, hg, hq]⟩)
    (hlft_m_z₂_y₀ := fun ⟨g, hg⟩ ↦ hσ0 (by rw [← D.ψU, ← hg, ← Category.assoc, hψq, zero_comp]))
    (hlft_m_z₂_y₁ := fun ⟨g, hg⟩ ↦ hs2 ⟨g, by rw [← hq, Category.assoc, hg, ht]⟩)
    (hlft_x'_b_zn := hrσn)
    (hlft_x'_zn_b := fun ⟨g, hg⟩ ↦ hq1 ⟨g ≫ S.w₂, by rw [← Category.assoc, hg, hr]⟩)
    (hlft_x'_zn_y₀ := by rw [hr]; exact hq1)
    (hrgt_m_b_y₀ := hw₂U.1) (hrgt_m_b'_y₁ := hv₂U'.1)
    (hrgt_x''_b'_y₁ := by
      rw [ht]
      exact fun hW ↦ B.l6s_not_w₂_and_U hmin hL hR hρ S' σ₂ hσ₂0 hm2 hm1 hW ⟨t, ht⟩)
    (hrgt_x'_m_y₀ := by
      rw [hr]
      exact fun hU ↦ B.l6s_not_w₂_and_U hmin hL hR hσ S ρn hρn0 hp1 hp2 ⟨r, hr⟩ hU)
    (hrgt_b_m_y₀ := hw₂U.2) (hrgt_b'_m_y₁ := hv₂U'.2)

include B in
/-- **BO13a figure 6.13** (`D̃₆`), in `P/σ`. -/
theorem l6_f613
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) (S : L6WSplit D)
    {x' x'' zn z₂ : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ) (r : x' ⟶ S.c.out) (hr : r ≫ S.w₂ = ρn)
    (σn : x' ⟶ zn) (hσn0 : σn ≠ 0) (hq1 : ¬∃ c, σn ≫ c = ρn)
    (hq2 : ¬∃ c, ρn ≫ c = σn) (s : S.c.out ⟶ zn) (hs : r ≫ s = σn)
    (σ₂ : x'' ⟶ y₁) (ρ₂ : x'' ⟶ z₂) (hρ₂0 : ρ₂ ≠ 0)
    (hs1 : ¬∃ c, σ₂ ≫ c = ρ₂) (hs2 : ¬∃ c, ρ₂ ≫ c = σ₂) (hσρ₂ : ¬FactorsThroughMorphism σ ρ₂)
    (t : x'' ⟶ D.m.out) (ht : t ≫ D.U' = σ₂) (htU : t ≫ D.U = 0) (q : D.m.out ⟶ z₂)
    (hq : t ≫ q = ρ₂) (hψq : D.ψ ≫ q = 0) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hw₂U := S.w₂_U hL hR hσ0
  have hσρ := not_ftm_long_dom hσ hρ0 hv1
  have hσσn := l6_not_ftm_nbr hQ hσ hρn0 hσn0 hp1 hp2 hq1 hq2
  refine B.not_f613 hmin hL hR σ hσ.2.1 hσ0 r s S.w₂ D.U D.U' q
    (h0_x'_b := fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x'_zn := by rw [hs]; exact hσσn)
    (h0_x'_y₀ := by rw [hr]; exact not_factorsThrough_of_not_isLong hσ hρn0 hρnl)
    (h0_b_zn := fun h ↦ hσσn (by rw [← hs]; exact FactorsThroughMorphism.comp_left h _))
    (h0_b_y₀ := not_ftm_suffix hσ0 S.w₁_not_isIso S.w₁w₂)
    (h0_m_y₀ := not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU)
    (h0_m_y₁ := fun h ↦ hσρ (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_z₂ := fun h ↦ hσρ₂ (by rw [← hq]; exact FactorsThroughMorphism.comp_left h _))
    (hi_r := fun h ↦ hp2 ⟨S.w₁ ≫ inv r, by
      rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, S.w₁w₂]⟩)
    (hi_s := fun h ↦ hq1 ⟨inv s ≫ S.w₂, by
      rw [← hs, Category.assoc, IsIso.hom_inv_id_assoc, hr]⟩)
    (hi_W := S.w₂_not_isIso) (hi_U := D.U_not_isIso) (hi_U' := D.U'_not_isIso)
    (hi_q := fun h ↦ hs2 ⟨inv q ≫ D.U', by rw [← hq, Category.assoc, IsIso.hom_inv_id_assoc, ht]⟩)
    (hl_s_W_y₀ := fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hs, Category.assoc, hg, hr]⟩)
    (hl_W_s_zn := fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hr, Category.assoc, hg, hs]⟩)
    (hl_U_U'_y₁ := D.U_U' hv1)
    (hl_U_q_z₂ := fun ⟨g, hg⟩ ↦ hρ₂0 (by rw [← hq, ← hg, ← Category.assoc, htU, zero_comp]))
    (hl_U'_U_y₀ := D.U'_U hv2)
    (hl_U'_q_z₂ := fun ⟨g, hg⟩ ↦ hs1 ⟨g, by rw [← ht, Category.assoc, hg, hq]⟩)
    (hl_q_U_y₀ := fun ⟨g, hg⟩ ↦ hσ0 (by rw [← D.ψU, ← hg, ← Category.assoc, hψq, zero_comp]))
    (hl_q_U'_y₁ := fun ⟨g, hg⟩ ↦ hs2 ⟨g, by rw [← hq, Category.assoc, hg, ht]⟩)
    (hr_W_U_m := hw₂U.1)
    (hr_U_W_x' := by
      rw [hr]
      exact fun hU ↦ B.l6s_not_w₂_and_U hmin hL hR hσ S ρn hρn0 hp1 hp2 ⟨r, hr⟩ hU)
    (hr_U_W_b := hw₂U.2)

end MulBasis

end RayQuiver

end LargeIndecomposable
