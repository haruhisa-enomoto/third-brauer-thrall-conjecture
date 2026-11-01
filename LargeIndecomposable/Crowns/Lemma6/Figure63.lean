module

public import LargeIndecomposable.Crowns.Lemma6.Figure62
public import LargeIndecomposable.Cleaving.Shapes.ShapeF63

/-!
# BO13a Lemma 6, case I.2.b: figure 6.3

* `RayCat.not_parallel`: two nonzero parallel morphisms are comparable from
  one side (comparability and one-sided cyclicity).
* `MulBasis.l6_ρβ`, `l6_σβ'`: `ρ ∤ β`, `σ ∤ β'` (Lemma 4 b)).
* `MulBasis.l6_fig63`: figure 6.3 in `P/μ`, `μ` long with codomain `y₁`.
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

omit [IsRayCategory P] in
/-- **Parallel nonzero morphisms are comparable from one side.** -/
lemma not_parallel (hQ : OneSidedCyclic P) {x y : P} (f g : x ⟶ y) (hf : f ≠ 0) (hg : g ≠ 0)
    (h1 : ¬∃ c, f ≫ c = g) (h2 : ¬∃ c, g ≫ c = f) (h3 : ¬∃ c, c ≫ f = g)
    (h4 : ¬∃ c, c ≫ g = f) : False := by
  rcases IsFiniteRayCategory.factorization_comparable f g with hT | hT
  · rcases hQ x y with h | h
    · obtain ⟨b, hb⟩ := h _ _ hg hT
      exact h1 ⟨b, hb.symm⟩
    · obtain ⟨a, ha⟩ := h _ _ hg hT
      exact h3 ⟨a, ha.symm⟩
  · rcases hQ x y with h | h
    · obtain ⟨b, hb⟩ := h _ _ hf hT
      exact h2 ⟨b, hb.symm⟩
    · obtain ⟨a, ha⟩ := h _ _ hf hT
      exact h4 ⟨a, ha.symm⟩

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- `ρ` does not factor through `β` (Lemma 4 b) for the contour of `σ`). -/
theorem l6_ρβ
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) : ¬∃ g, D.β.1 ≫ g = ρ := by
  rintro hβ
  have hval : pathVal (D.α.toPath.comp (D.χ.comp D.u₂)) = pathVal (D.β.toPath.comp D.w) := by
    rw [← Quiver.Path.comp_assoc, D.hσu, D.hσw]
  have h0 : pathVal (D.α.toPath.comp (D.χ.comp D.u₂)) ≠ 0 := by
    rw [← Quiver.Path.comp_assoc, D.hσu]; exact hσ0
  have e : pathVal (D.α.toPath.comp (D.χ.comp D.u₂)) = σ := by
    rw [← Quiver.Path.comp_assoc, D.hσu]
  refine B.not_factors_both hmin hL hR D.α D.β (D.χ.comp D.u₂) D.w hval h0
    (by rw [← Quiver.Path.comp_assoc]; exact D.hniσ) ⟨y₁, ρ⟩ hρ0 ?_ ?_ ?_ hβ
  · rintro ⟨c, hc⟩
    rw [e] at hc
    exact hv1 ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    change ρ ≫ c = pathVal (D.α.toPath.comp (D.χ.comp D.u₂)) at hc
    rw [e] at hc
    exact hv2 ⟨c, hc⟩
  · refine ⟨pathVal D.χ ≫ D.U', ?_⟩
    change D.α.1 ≫ pathVal D.χ ≫ D.U' = ρ
    have := D.ψU'
    simp only [L6Data.ψ] at this
    rw [pathVal_comp D.α.toPath D.χ, pathVal_toPath, Category.assoc] at this
    exact this

include B in
/-- `σ` does not factor through `β'` (Lemma 4 b) for the contour of `ρ`). -/
theorem l6_σβ'
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) : ¬∃ g, D.β'.1 ≫ g = σ := by
  rintro hβ
  have hval : pathVal (D.α.toPath.comp (D.χ.comp D.u₂')) =
      pathVal (D.β'.toPath.comp D.w') := by
    rw [← Quiver.Path.comp_assoc, D.hρu, D.hρw]
  have h0 : pathVal (D.α.toPath.comp (D.χ.comp D.u₂')) ≠ 0 := by
    rw [← Quiver.Path.comp_assoc, D.hρu]; exact hρ0
  have e : pathVal (D.α.toPath.comp (D.χ.comp D.u₂')) = ρ := by
    rw [← Quiver.Path.comp_assoc, D.hρu]
  refine B.not_factors_both hmin hL hR D.α D.β' (D.χ.comp D.u₂') D.w' hval h0
    (by rw [← Quiver.Path.comp_assoc]; exact D.hniρ) ⟨y₀, σ⟩ hσ0 ?_ ?_ ?_ hβ
  · rintro ⟨c, hc⟩
    rw [e] at hc
    exact hv2 ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    change σ ≫ c = pathVal (D.α.toPath.comp (D.χ.comp D.u₂')) at hc
    rw [e] at hc
    exact hv1 ⟨c, hc⟩
  · refine ⟨pathVal D.χ ≫ D.U, ?_⟩
    change D.α.1 ≫ pathVal D.χ ≫ D.U = σ
    have := D.ψU
    simp only [L6Data.ψ] at this
    rw [pathVal_comp D.α.toPath D.χ, pathVal_toPath, Category.assoc] at this
    exact this

include B in
/-- **BO13a figure 6.3**, in `P/μ` for a long `μ` with codomain `y₁` that is a
crown neighbour of `ρ` (in BO13a, `μ = σ₂`). -/
theorem l6_fig63
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) {x'' : P} (μ : x'' ⟶ y₁) (hμ : IsLong μ)
    (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ) {x' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0)
    (hρnl : ¬IsLong ρn) (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (r : x' ⟶ D.b.out) (hr : r ≫ D.W = ρn) {tf : P} (φ : x' ⟶ tf)
    (h0φ : ¬FactorsThroughMorphism μ φ) (hiφ : ¬IsIso φ) (hrφ : ¬∃ g, r ≫ g = φ)
    (hφr : ¬∃ g, φ ≫ g = r) (hφρn : ¬∃ g, φ ≫ g = ρn) {te : P} (e : te ⟶ y₁)
    (he : IsIrreducible e) (hpk : ¬∃ g, g ≫ e = ρ)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F63.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρβ := B.l6_ρβ hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hσβ' := B.l6_σβ' hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hWU := D.W_U hL hR hσ0 hσ.2.2.1
  have hWU' := D.W'_U' hL hR hρ0 hρ.2.2.1
  have hiW := D.W_not_isIso hσ.2.2.1
  have hiW' := D.W'_not_isIso hρ.2.2.1
  have hμσ : ¬FactorsThroughMorphism μ σ := by
    intro h
    obtain ⟨hx, hy, he'⟩ := hμ.2.2.2 σ hσ0 h
    subst hx hy
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he'
    rw [← he'] at hm1 hm2
    exact not_parallel hQ σ ρ hσ0 hρ0 hv1 hv2 hm1 hm2
  have hμρ : ¬FactorsThroughMorphism μ ρ := not_ftm_long_cod hμ hρ0 hm1
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.β.1 ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.βW]⟩
  refine B.not_f63 hmin hL hR μ hμ.2.1 hμ.1 D.β.1 D.ψ D.β'.1 D.W D.U D.U' D.W' e r φ hD
    (hc0 := by rw [D.ψU, D.βW]) (hc1 := by rw [D.ψU', D.βW'])
    (h0_b_y₀ := fun h ↦ hμσ (by rw [← D.βW]; exact FactorsThroughMorphism.comp_left h _))
    (h0_b'_y₁ := fun h ↦ hμρ (by rw [← D.βW']; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_y₀ := fun h ↦ hμσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _))
    (h0_m_y₁ := fun h ↦ hμρ (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
    (h0_te_y₁ := not_factorsThrough_irr hμ.2.1 hμ.1 hμ.2.2.1 he)
    (h0_x_b := fun h ↦ hμσ (by rw [← D.βW]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_b' := fun h ↦ hμρ (by rw [← D.βW']; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_m := fun h ↦ hμσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_right h _))
    (h0_x_y₀ := by rw [D.βW]; exact hμσ) (h0_x_y₁ := by rw [D.ψU']; exact hμρ)
    (h0_x'_b := fun h ↦ hρnl (hμ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (h0_x'_tf := h0φ)
    (h0_x'_y₀ := by rw [hr]; exact fun h ↦ hρnl (hμ.of_factorsThrough hρn0 h))
    (hi_β := D.β.2.2.1) (hi_ψ := D.ψ_not_isIso) (hi_β' := D.β'.2.2.1) (hi_W := hiW)
    (hi_U := D.U_not_isIso) (hi_U' := D.U'_not_isIso) (hi_W' := hiW') (hi_e := he.2.1)
    (hi_r := hir) (hi_φ := hiφ)
    (hlft_m_y₀_y₁ := D.U_U' hv1) (hlft_m_y₁_y₀ := D.U'_U hv2)
    (hlft_x_b_m := fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩)
    (hlft_x_b_b' := fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.W', by rw [← Category.assoc, hg, D.βW']⟩)
    (hlft_x_b_y₁ := fun ⟨g, hg⟩ ↦ hρβ ⟨g, by rw [hg, D.ψU']⟩)
    (hlft_x_b'_b := fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.W, by rw [← Category.assoc, hg, D.βW]⟩)
    (hlft_x_b'_m := fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩)
    (hlft_x_b'_y₀ := fun ⟨g, hg⟩ ↦ hσβ' ⟨g, by rw [hg, D.βW]⟩)
    (hlft_x_m_b := fun ⟨g, hg⟩ ↦ by
      rcases D.β.2.2.2 _ D.ψ g hg.symm with h | h
      · exact D.ψ_not_isIso h
      · exact hρβ ⟨inv g ≫ D.U', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU']⟩)
    (hlft_x_m_b' := fun ⟨g, hg⟩ ↦ by
      rcases D.β'.2.2.2 _ D.ψ g hg.symm with h | h
      · exact D.ψ_not_isIso h
      · exact hσβ' ⟨inv g ≫ D.U, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU]⟩)
    (hlft_x'_b_tf := hrφ) (hlft_x'_tf_b := hφr) (hlft_x'_tf_y₀ := by rw [hr]; exact hφρn)
    (hrgt_m_b_y₀ := hWU.1) (hrgt_m_b'_y₁ := hWU'.1)
    (hrgt_te_b'_y₁ := fun ⟨g, hg⟩ ↦ by
      rcases he.2.2 _ g D.W' hg.symm with h | h
      · exact hpk ⟨D.β'.1 ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.βW']⟩
      · exact hiW' h)
    (hrgt_b_m_y₀ := hWU.2)
    (hrgt_x'_m_y₀ := by
      rw [hr]
      exact fun hU ↦ B.l6_not_W_and_U hmin hL hR hσ D ρn hρn0 hp1 hp2 ⟨r, hr⟩ hU)
    (hrgt_b'_m_y₁ := hWU'.2)
    (hrgt_te_m_y₁ := fun ⟨g, hg⟩ ↦ by
      rcases he.2.2 _ g D.U' hg.symm with h | h
      · exact hpk ⟨D.ψ ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.ψU']⟩
      · exact D.U'_not_isIso h)
    (hrgt_x_te_y₁ := fun ⟨g, hg⟩ ↦ hpk ⟨g, by rw [hg, D.ψU']⟩)
    (hrgt_m_te_y₁ := fun ⟨g, hg⟩ ↦ hpk ⟨D.ψ ≫ g, by rw [Category.assoc, hg, D.ψU']⟩)
    (hrgt_b'_te_y₁ := fun ⟨g, hg⟩ ↦ hpk ⟨D.β'.1 ≫ g, by rw [Category.assoc, hg, D.βW']⟩)
    (hrgt_x'_x_b := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, D.βW]⟩)
    (hrgt_x_x'_b := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← D.βW, ← hg, Category.assoc, hr]⟩)

end MulBasis

end RayQuiver

end LargeIndecomposable
