module

public import LargeIndecomposable.Crowns.Lemma6.CaseIU
public import LargeIndecomposable.Cleaving.Shapes.ShapeF64
public import LargeIndecomposable.Cleaving.Shapes.ShapeF66

/-!
# BO13a Lemma 6, case I.2.c: figures 6.4 and 6.6

`ρₙ = ρₙ' ≫ u₂`, `ρₙ' ≫ u₂' = 0`, `σₙ` does not factor through `ρₙ'`, and
* `σ₂ = σ₂' ≫ q₂` for a split `w' = q₁' q₂` of the rest of the contour path of
  `ρ` (figure 6.4, `MulBasis.l6_f64`);
* `σ₂ = σ₂' ≫ a'` for a split `u₂' = d ≫ a'` with `ρₙ' ≫ d = 0` and `σ₂` not
  through `u₂'` (figure 6.6, `MulBasis.l6_f66`).
The quotient `τ` is a long morphism dividing none of the diagram morphisms.
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
/-- **BO13a figure 6.4.** -/
theorem l6_f64
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) {x'' : P} (μ : x'' ⟶ y₁) (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ)
    {x' zn : P} (ρn : x' ⟶ y₀) (σn : x' ⟶ zn) (hρn0 : ρn ≠ 0) (hp1 : ¬∃ c, c ≫ σ = ρn)
    (hp2 : ¬∃ c, c ≫ ρn = σ) (hq1 : ¬∃ c, σn ≫ c = ρn) (hq2 : ¬∃ c, ρn ≫ c = σn)
    (hiσn : ¬IsIso σn) (r : x' ⟶ D.m.out) (hr : r ≫ D.U = ρn) (hrσn : ¬∃ g, r ≫ g = σn)
    {b'' : RayVert P} (q₁ : Quiver.Path D.b' b'') (q₂ : Quiver.Path b'' (RayVert.mk y₁))
    (hq : q₁.comp q₂ = D.w') (hq₂ : 0 < q₂.length) (t : x'' ⟶ b''.out)
    (ht : t ≫ pathVal q₂ = μ)
    {a b : P} (τ : a ⟶ b) (hτ : IsLong τ) (h0σn : ¬FactorsThroughMorphism τ σn)
    (h0w : ¬FactorsThroughMorphism τ (D.β'.1 ≫ pathVal q₁))
    (h0t : ¬FactorsThroughMorphism τ t) (h0σ : ¬FactorsThroughMorphism τ σ)
    (h0ρn : ¬FactorsThroughMorphism τ ρn)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F64.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρβ := B.l6_ρβ hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hσβ' := B.l6_σβ' hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hWU := D.W_U hL hR hσ0 hσ.2.2.1
  set w₁ := D.β'.1 ≫ pathVal q₁ with hw₁
  have hw₁q : w₁ ≫ pathVal q₂ = ρ := by
    rw [hw₁, Category.assoc, ← pathVal_comp, hq, D.βW']
  have hσw₁ : ¬∃ g, w₁ ≫ g = σ := fun ⟨g, hg⟩ ↦ hσβ' ⟨pathVal q₁ ≫ g, by
    rw [← Category.assoc]; exact hg⟩
  -- crossing in the contour `(ψ u₂', β' q₁ q₂)`
  have hcross : ¬∃ g, D.ψ ≫ g = w₁ := by
    have hval : pathVal ((D.α.toPath.comp D.χ).comp D.u₂') =
        pathVal ((D.β'.toPath.comp q₁).comp q₂) := by
      rw [D.hρu, Quiver.Path.comp_assoc D.β'.toPath q₁ q₂, hq, D.hρw]
    have := (contour_cross hL hR (D.α.toPath.comp D.χ) D.u₂' (D.β'.toPath.comp q₁) q₂ hval
      (by rw [D.hρu]; exact hρ0) (by rw [Quiver.Path.comp_assoc D.β'.toPath q₁ q₂, hq]; exact D.hniρ)
      (by rw [Quiver.Path.length_comp]; simp) hq₂).2
    rwa [pathVal_comp D.β'.toPath q₁, pathVal_toPath] at this
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.ψ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.ψU]⟩
  have hit : ¬IsIso t := fun h ↦ hm1 ⟨w₁ ≫ inv t, by
    rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc, hw₁q]⟩
  have hiw₁ : ¬IsIso w₁ := fun h ↦ D.β'.2.2.1 (by
    have : IsIso (D.β'.1 ≫ pathVal q₁) := h
    exact isIso_of_isIso_comp _ _ D.β'.2.1 this)
  refine B.not_f64 hmin hL hR τ hτ.2.1 hτ.1 D.β.1 D.ψ D.W D.U σn r w₁ t hD
    (hc0 := by rw [D.ψU, D.βW])
    (h0_b_y₀ := fun h ↦ h0σ (by rw [← D.βW]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_y₀ := fun h ↦ h0σ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _))
    (h0_x_b := fun h ↦ h0σ (by rw [← D.βW]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_b'' := h0w)
    (h0_x_m := fun h ↦ h0σ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_y₀ := by rw [D.βW]; exact h0σ)
    (h0_x'_m := fun h ↦ h0ρn (by rw [← hr]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x'_y₀ := by rw [hr]; exact h0ρn) (h0_x'_zn := h0σn) (h0_x''_b'' := h0t)
    (hi_β := D.β.2.2.1) (hi_ψ := D.ψ_not_isIso) (hi_W := D.W_not_isIso hσ.2.2.1)
    (hi_U := D.U_not_isIso) (hi_σn := hiσn) (hi_r := hir) (hi_w₁ := hiw₁) (hi_t := hit)
    (hlft_x_b_m := fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩)
    (hlft_x_b_b'' := fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ pathVal q₂, by rw [← Category.assoc, hg, hw₁q]⟩)
    (hlft_x_b''_b := fun ⟨g, hg⟩ ↦ hσw₁ ⟨g ≫ D.W, by rw [← Category.assoc, hg, D.βW]⟩)
    (hlft_x_b''_m := fun ⟨g, hg⟩ ↦ hσw₁ ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩)
    (hlft_x_b''_y₀ := fun ⟨g, hg⟩ ↦ hσw₁ ⟨g, by rw [hg, D.βW]⟩)
    (hlft_x_m_b := fun ⟨g, hg⟩ ↦ by
      rcases D.β.2.2.2 _ D.ψ g hg.symm with h | h
      · exact D.ψ_not_isIso h
      · exact hρβ ⟨inv g ≫ D.U', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU']⟩)
    (hlft_x_m_b'' := hcross) (hlft_x'_m_zn := hrσn)
    (hlft_x'_zn_m := fun ⟨g, hg⟩ ↦ hq1 ⟨g ≫ D.U, by rw [← Category.assoc, hg, hr]⟩)
    (hlft_x'_zn_y₀ := by rw [hr]; exact hq1)
    (hrgt_m_b_y₀ := hWU.1)
    (hrgt_x'_b_y₀ := by
      rw [hr]
      exact fun hW ↦ B.l6_not_W_and_U hmin hL hR hσ D ρn hρn0 hp1 hp2 hW ⟨r, hr⟩)
    (hrgt_b_m_y₀ := hWU.2)
    (hrgt_x''_x_b'' := fun ⟨g, hg⟩ ↦ hm2 ⟨g, by rw [← ht, ← hg, Category.assoc, hw₁q]⟩)
    (hrgt_x'_x_m := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, D.ψU]⟩)
    (hrgt_x_x'_m := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← D.ψU, ← hg, Category.assoc, hr]⟩)
    (hrgt_x_x''_b'' := fun ⟨g, hg⟩ ↦ hm1 ⟨g, by rw [← hw₁q, ← hg, Category.assoc, ht]⟩)

include B in
/-- **BO13a figure 6.6** (category 20 with the zero relation `ρₙ' ≫ d = 0`). -/
theorem l6_f66
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) {x'' : P} (μ : x'' ⟶ y₁) (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ)
    {x' zn : P} (ρn : x' ⟶ y₀) (σn : x' ⟶ zn) (hρn0 : ρn ≠ 0) (hp1 : ¬∃ c, c ≫ σ = ρn)
    (hp2 : ¬∃ c, c ≫ ρn = σ) (hq1 : ¬∃ c, σn ≫ c = ρn) (hq2 : ¬∃ c, ρn ≫ c = σn)
    (hiσn : ¬IsIso σn) (r : x' ⟶ D.m.out) (hr : r ≫ D.U = ρn) (hrσn : ¬∃ g, r ≫ g = σn)
    {c : RayVert P} (dp : Quiver.Path D.m c) (ap : Quiver.Path c (RayVert.mk y₁))
    (hdap : dp.comp ap = D.u₂') (hdp : 0 < dp.length) (hap : 0 < ap.length)
    (hrd : r ≫ pathVal dp = 0) (t : x'' ⟶ c.out) (ht : t ≫ pathVal ap = μ)
    (hμU' : ¬∃ g, g ≫ D.U' = μ)
    {a b : P} (τ : a ⟶ b) (hτ : IsLong τ) (h0σn : ¬FactorsThroughMorphism τ σn)
    (h0β' : ¬FactorsThroughMorphism τ D.β'.1) (h0d : ¬FactorsThroughMorphism τ (pathVal dp))
    (h0ψd : ¬FactorsThroughMorphism τ (D.ψ ≫ pathVal dp))
    (h0t : ¬FactorsThroughMorphism τ t) (h0σ : ¬FactorsThroughMorphism τ σ)
    (h0ρn : ¬FactorsThroughMorphism τ ρn)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F66.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρβ := B.l6_ρβ hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hσβ' := B.l6_σβ' hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hWU := D.W_U hL hR hσ0 hσ.2.2.1
  set d := pathVal dp with hd
  set a' := pathVal ap with ha'
  have hda : d ≫ a' = D.U' := by rw [hd, ha', ← pathVal_comp, hdap]
  have hid : ¬IsIso d := not_isIso_pathVal dp hdp
  have hia' : ¬IsIso a' := not_isIso_pathVal ap hap
  have hρd : D.ψ ≫ d ≫ a' = ρ := by rw [hda, D.ψU']
  -- crossing in the contour `(β' w', ψ d a')`
  have hcross : ¬∃ g, D.β'.1 ≫ g = D.ψ ≫ d := by
    have hval : pathVal (D.β'.toPath.comp D.w') =
        pathVal (((D.α.toPath.comp D.χ).comp dp).comp ap) := by
      rw [D.hρw, Quiver.Path.comp_assoc (D.α.toPath.comp D.χ) dp ap, hdap, D.hρu]
    have := (contour_cross hL hR D.β'.toPath D.w' ((D.α.toPath.comp D.χ).comp dp) ap hval
      (by rw [D.hρw]; exact hρ0)
      (by rw [Quiver.Path.comp_assoc (D.α.toPath.comp D.χ) dp ap, hdap]
          exact fun h ↦ D.hniρ h.symm) (by simp) hap).2
    rwa [pathVal_toPath, pathVal_comp (D.α.toPath.comp D.χ) dp] at this
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.ψ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.ψU]⟩
  have hit : ¬IsIso t := fun h ↦ hm1 ⟨D.ψ ≫ d ≫ inv t, by
    rw [Category.assoc, Category.assoc, ← ht, IsIso.inv_hom_id_assoc, hρd]⟩
  refine B.not_f66 hmin hL hR τ hτ.2.1 hτ.1 D.β.1 D.ψ D.W D.U σn r d t D.β'.1 hD
    (hc0 := by rw [D.ψU, D.βW]) (hz0 := hrd)
    (h0_b_y₀ := fun h ↦ h0σ (by rw [← D.βW]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_c := h0d)
    (h0_m_y₀ := fun h ↦ h0σ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _))
    (h0_x_b := fun h ↦ h0σ (by rw [← D.βW]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_b'' := h0β') (h0_x_c := h0ψd)
    (h0_x_m := fun h ↦ h0σ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_y₀ := by rw [D.βW]; exact h0σ)
    (h0_x'_m := fun h ↦ h0ρn (by rw [← hr]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x'_y₀ := by rw [hr]; exact h0ρn) (h0_x'_zn := h0σn) (h0_x''_c := h0t)
    (hi_β := D.β.2.2.1) (hi_ψ := D.ψ_not_isIso) (hi_W := D.W_not_isIso hσ.2.2.1)
    (hi_U := D.U_not_isIso) (hi_σn := hiσn) (hi_r := hir) (hi_d := hid) (hi_t := hit)
    (hi_w₁ := D.β'.2.2.1)
    (hlft_m_c_y₀ := by
      rintro ⟨g, hg⟩
      have hle := D.hmax ⟨_, D.ψ ≫ d⟩ ⟨pathVal D.χ ≫ d, by
        change D.α.1 ≫ pathVal D.χ ≫ d = D.ψ ≫ d
        simp only [L6Data.ψ]
        rw [pathVal_comp D.α.toPath D.χ, pathVal_toPath, Category.assoc]⟩
        ⟨g, by change (D.ψ ≫ d) ≫ g = σ; rw [Category.assoc, hg, D.ψU]⟩
        ⟨a', by change (D.ψ ≫ d) ≫ a' = ρ; rw [Category.assoc, hρd]⟩
      obtain ⟨k', hk'⟩ := hle
      change (D.ψ ≫ d) ≫ k' = D.ψ at hk'
      have hdk : d ≫ k' = 𝟙 _ := hL D.ψ _ _ (by rw [Category.comp_id, ← Category.assoc, hk'])
        (by rw [← Category.assoc, hk']; exact fun h ↦ hσ0 (by rw [← D.ψU, h, zero_comp]))
      exact not_split_mono hid ⟨k', hdk⟩)
    (hlft_m_y₀_c := fun ⟨g, hg⟩ ↦ hv1 ⟨g ≫ a', by
      rw [← D.ψU, Category.assoc, ← Category.assoc D.U, hg, hρd]⟩)
    (hlft_x_b_m := fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩)
    (hlft_x_b_c := fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ a', by rw [← Category.assoc, hg, Category.assoc, hρd]⟩)
    (hlft_x_b_b'' := fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.W', by rw [← Category.assoc, hg, D.βW']⟩)
    (hlft_x_b''_b := fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.W, by rw [← Category.assoc, hg, D.βW]⟩)
    (hlft_x_b''_m := fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩)
    (hlft_x_b''_y₀ := fun ⟨g, hg⟩ ↦ hσβ' ⟨g, by rw [hg, D.βW]⟩)
    (hlft_x_b''_c := hcross)
    (hlft_x_m_b := fun ⟨g, hg⟩ ↦ by
      rcases D.β.2.2.2 _ D.ψ g hg.symm with h | h
      · exact D.ψ_not_isIso h
      · exact hρβ ⟨inv g ≫ D.U', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU']⟩)
    (hlft_x_m_b'' := fun ⟨g, hg⟩ ↦ by
      rcases D.β'.2.2.2 _ D.ψ g hg.symm with h | h
      · exact D.ψ_not_isIso h
      · exact hσβ' ⟨inv g ≫ D.U, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU]⟩)
    (hlft_x'_m_zn := hrσn)
    (hlft_x'_zn_m := fun ⟨g, hg⟩ ↦ hq1 ⟨g ≫ D.U, by rw [← Category.assoc, hg, hr]⟩)
    (hlft_x'_zn_y₀ := by rw [hr]; exact hq1)
    (hrgt_m_b_y₀ := hWU.1)
    (hrgt_x'_b_y₀ := by
      rw [hr]
      exact fun hW ↦ B.l6_not_W_and_U hmin hL hR hσ D ρn hρn0 hp1 hp2 hW ⟨r, hr⟩)
    (hrgt_x''_m_c := fun ⟨g, hg⟩ ↦ hμU' ⟨g, by rw [← hda, ← Category.assoc, hg, ht]⟩)
    (hrgt_b_m_y₀ := hWU.2)
    (hrgt_x'_x_m := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, D.ψU]⟩)
    (hrgt_x_x'_m := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← D.ψU, ← hg, Category.assoc, hr]⟩)
    (hrgt_x_x''_c := fun ⟨g, hg⟩ ↦ hm1 ⟨g, by
      rw [← hρd, ← Category.assoc D.ψ, ← hg, Category.assoc, ht]⟩)
    (hrgt_m_x''_c := fun ⟨g, hg⟩ ↦ hm1 ⟨D.ψ ≫ g, by
      rw [Category.assoc, ← ht, ← Category.assoc g, hg, hρd]⟩)

end MulBasis

end RayQuiver

end LargeIndecomposable
