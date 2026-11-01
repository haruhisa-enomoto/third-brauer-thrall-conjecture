module

public import LargeIndecomposable.Crowns.Lemma6.CaseI
public import LargeIndecomposable.Cleaving.Shapes.ShapeF62

/-!
# BO13a Lemma 6, case I.2.b: figure 6.2

`ρₙ = ρₙ' ≫ w₂` and `σₙ = ρₙ' ≫ σₙ'` give the `D̃₇` diagram of figure 6.2, in
`P/σ` (or in `P/ρ` when `σₙ` is a multiple of `σ`) (`MulBasis.l6_fig62`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- A nonzero morphism is not divisible by two long morphisms with a common
domain that are not multiples of each other. -/
lemma not_ftm_both {x y₀ y₁ X Y : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) {f : X ⟶ Y} (hf : f ≠ 0) (h1 : FactorsThroughMorphism σ f)
    (h2 : FactorsThroughMorphism ρ f) : False := by
  obtain ⟨hx, hy, rfl⟩ := hσ.2.2.2 f hf h1
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h2
  exact not_ftm_long_dom hρ hσ.1 hv2 h2

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- A morphism incomparable from the left with `σ` does not factor through both
`w₂` and `u₂` (dual Lemma 4 b) for the contour `(ψ u₂, β w₂)`). -/
theorem l6_not_W_and_U
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (D : L6Data σ ρ) {z : P} (t : z ⟶ y₀) (ht : t ≠ 0)
    (h1 : ¬∃ c, c ≫ σ = t) (h2 : ¬∃ c, c ≫ t = σ) (hW : ∃ g, g ≫ D.W = t)
    (hU : ∃ g, g ≫ D.U = t) : False := by
  obtain ⟨c, u'', eu, hu⟩ := exists_last_arrow D.u₂ D.U_not_isIso
  obtain ⟨d, w'', ew, hw⟩ := exists_last_arrow D.w (D.W_not_isIso hσ.2.2.1)
  have hσu : pathVal (((D.α.toPath.comp D.χ).comp u'').cons eu) = σ := by
    have := D.hσu; rw [hu] at this; exact this
  have hσw : pathVal ((D.β.toPath.comp w'').cons ew) = σ := by
    have := D.hσw; rw [hw] at this; exact this
  refine B.not_factors_both_last hmin hL hR eu ew ((D.α.toPath.comp D.χ).comp u'')
    (D.β.toPath.comp w'') (by rw [hσu, hσw]) (by rw [hσu]; exact hσ.1) ?_ t ht
    (by rw [hσu]; exact h1) (by rw [hσu]; exact h2) ?_ ?_
  · intro h
    apply D.hniσ
    rw [hu, hw]
    exact h
  · obtain ⟨g, hg⟩ := hU
    refine ⟨g ≫ pathVal u'', ?_⟩
    rw [← hg, Category.assoc]
    change _ = g ≫ pathVal D.u₂
    rw [hu]
    rfl
  · obtain ⟨g, hg⟩ := hW
    refine ⟨g ≫ pathVal w'', ?_⟩
    rw [← hg, Category.assoc]
    change _ = g ≫ pathVal D.w
    rw [hw]
    rfl

include B in
/-- **BO13a figure 6.2.** -/
theorem l6_fig62
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) {x' zn : P} (ρn : x' ⟶ y₀) (σn : x' ⟶ zn) (hρn0 : ρn ≠ 0) (hσn0 : σn ≠ 0)
    (hρnl : ¬IsLong ρn) (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (hq1 : ¬∃ c, σn ≫ c = ρn) (hq2 : ¬∃ c, ρn ≫ c = σn)
    (r : x' ⟶ D.b.out) (s : D.b.out ⟶ zn) (hr : r ≫ D.W = ρn) (hs : r ≫ s = σn)
    {Te : P} (e : Te ⟶ y₁) (he : IsIrreducible e) (hpk : ¬∃ g, g ≫ e = ρ) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hiW := D.W_not_isIso hσ.2.2.1
  have hiW' := D.W'_not_isIso hρ.2.2.1
  -- the conditions at `y₁`
  have h₁3 : ¬∃ g, g ≫ D.W' = e := by
    rintro ⟨g, hg⟩
    rcases he.2.2 _ g D.W' hg.symm with h | h
    · exact hpk ⟨D.β'.1 ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.βW']⟩
    · exact hiW' h
  have h₁5 : ¬∃ g, g ≫ D.U' = e := by
    rintro ⟨g, hg⟩
    rcases he.2.2 _ g D.U' hg.symm with h | h
    · exact hpk ⟨D.ψ ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.ψU']⟩
    · exact D.U'_not_isIso h
  have h₁1 : ¬∃ g, g ≫ e = D.W' := fun ⟨g, hg⟩ ↦
    hpk ⟨D.β'.1 ≫ g, by rw [Category.assoc, hg, D.βW']⟩
  have h₁2 : ¬∃ g, g ≫ e = D.U' := fun ⟨g, hg⟩ ↦
    hpk ⟨D.ψ ≫ g, by rw [Category.assoc, hg, D.ψU']⟩
  -- the conditions at `b` and `y₀`
  have hsW : ¬∃ g, s ≫ g = D.W := fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hs, Category.assoc, hg, hr]⟩
  have hWs : ¬∃ g, D.W ≫ g = s := fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hr, Category.assoc, hg, hs]⟩
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.β.1 ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.βW]⟩
  have his : ¬IsIso s := fun h ↦ hq1 ⟨inv s ≫ D.W, by
    rw [← hs, Category.assoc, IsIso.hom_inv_id_assoc, hr]⟩
  have hUrW : ¬∃ g, g ≫ D.U = r ≫ D.W := by
    rw [hr]
    exact fun hU ↦ B.l6_not_W_and_U hmin hL hR hσ D ρn hρn0 hp1 hp2 ⟨r, hr⟩ hU
  have hWU := D.W_U hL hR hσ0 hσ.2.2.1
  -- the quotient
  by_cases hσσn : FactorsThroughMorphism σ σn
  · refine B.not_f62 hmin hL hR ρ hρ.2.1 hρ0 r s D.W D.U D.U' D.W' e ?_ ?_
      (fun h ↦ not_ftm_long_dom hρ hσ0 hv2 (by rw [← D.βW]; exact FactorsThroughMorphism.comp_left h _))
      (fun h ↦ not_ftm_long_dom hρ hσ0 hv2 (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _))
      (not_ftm_suffix hρ0 D.ψ_not_isIso D.ψU') (not_ftm_suffix hρ0 D.β'.2.2.1 D.βW')
      (not_factorsThrough_irr hρ.2.1 hρ0 hρ.2.2.1 he) ?_ ?_ hir his hiW D.U_not_isIso
      D.U'_not_isIso hiW' he.2.1 hsW hWs (D.U_U' hv1) (D.U'_U hv2) hWU.2 hUrW hWU.1
      h₁1 h₁2 h₁3 (D.W'_U' hL hR hρ0 hρ.2.2.1).1 h₁5 (D.W'_U' hL hR hρ0 hρ.2.2.1).2
    · exact fun h ↦ hρnl (hρ.of_factorsThrough hρn0 (by rw [← hr]; exact FactorsThroughMorphism.comp_right h _))
    · exact fun h ↦ not_ftm_both hσ hρ hv2 hσn0 hσσn (by rw [← hs]; exact FactorsThroughMorphism.comp_left h _)
    · rw [hs]; exact fun h ↦ not_ftm_both hσ hρ hv2 hσn0 hσσn h
    · rw [hr]; exact fun h ↦ hρnl (hρ.of_factorsThrough hρn0 h)
  · refine B.not_f62 hmin hL hR σ hσ.2.1 hσ0 r s D.W D.U D.U' D.W' e ?_ ?_
      (not_ftm_suffix hσ0 D.β.2.2.1 D.βW) (not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU)
      (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
      (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by rw [← D.βW']; exact FactorsThroughMorphism.comp_left h _))
      (not_factorsThrough_irr hσ.2.1 hσ0 hσ.2.2.1 he) ?_ ?_ hir his hiW D.U_not_isIso
      D.U'_not_isIso hiW' he.2.1 hsW hWs (D.U_U' hv1) (D.U'_U hv2) hWU.2 hUrW hWU.1
      h₁1 h₁2 h₁3 (D.W'_U' hL hR hρ0 hρ.2.2.1).1 h₁5 (D.W'_U' hL hR hρ0 hρ.2.2.1).2
    · exact fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by rw [← hr]; exact FactorsThroughMorphism.comp_right h _))
    · exact fun h ↦ hσσn (by rw [← hs]; exact FactorsThroughMorphism.comp_left h _)
    · rw [hs]; exact hσσn
    · rw [hr]; exact fun h ↦ hρnl (hσ.of_factorsThrough hρn0 h)

end MulBasis

end RayQuiver

end LargeIndecomposable
