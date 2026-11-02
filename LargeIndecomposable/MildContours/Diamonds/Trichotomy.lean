module

public import LargeIndecomposable.MildContours.Contours.Lemma22
public import LargeIndecomposable.Cleaving.Shapes.ShapeDM5
public import LargeIndecomposable.Cleaving.Shapes.ShapeSE6

/-!
# [mild] diamonds: the first trichotomy

For a mild contour `C` with `ρ = ω' ≫ α` and `ω'` not invertible, the `D̃₅`
diagram of [mild] figure 2.5 (first diagram) is not cleaving in `P/τ`. Hence
`γ = ξ ≫ ω'`, or `ω' = g ≫ γ`, or `α ≫ ω' = η ≫ γ`, or `β ≫ ω' = η ≫ γ`
(`MildContour.diamond_cases`).

The star `Ẽ₆` at `y` (arms along `v`, along `w`, and the tail `ω' ≫ α`) shows
that `v` or `w` has length at most two (`MildContour.star_e6`).
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

namespace MildContour

variable {x y : P} (C : MildContour x y)

/-- **[mild] figure 2.5**: the trichotomy of the diamond case. -/
theorem diamond_cases (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω')
    (hρ : C.ρ = ω' ≫ C.α.1) :
    (∃ g, g ≫ ω' = C.γ) ∨ (∃ g, g ≫ C.γ = ω') ∨ (∃ g, g ≫ C.γ = C.α.1 ≫ ω') ∨
      ∃ g, g ≫ C.γ = C.β.1 ≫ ω' := by
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hαn := C.α.2.2.1
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hτv : C.τ = C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ]
  have hτw : C.τ = C.δ ≫ C.β.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_w, hρ]
  refine hM.not_dm5 C.τ C.τ_not_isIso hτ0 C.α.1 C.β.1 ω' C.γ C.α.1
    (not_ftm_mid_right hτ0 hαn (p := C.γ ≫ C.α.1) (by rw [hτv]; simp))
    (by rw [← hρ]; exact C.ftm_ρ) (C.ftm_α hR) (C.ftm_α hR)
    (not_ftm_mid_right hτ0 hαn (p := C.γ) (by rw [hτv]; simp))
    (by rw [Category.assoc, ← hρ]; exact C.ftm_αρ hR) (C.ftm_β hR)
    (not_ftm_mid_right hτ0 hαn (p := C.δ) (by rw [hτw]; simp))
    (by rw [Category.assoc, ← hρ]; exact C.ftm_βρ hR) (C.ftm_γ hR) C.ftm_ω
    hαn C.β.2.2.1 hω' (C.γ_not_isIso hR) hαn hap.2 hap.1 ?_ ?_ ?_ ?_
  · rintro ⟨g, hg⟩; exact h1 g hg
  · rintro ⟨g, hg⟩; exact h2 g hg
  · rintro ⟨g, hg⟩; exact h3 g hg
  · rintro ⟨g, hg⟩; exact h4 g hg

/-- Splitting off the first two arrows of a path of length at least two. -/
lemma path_two_arrows {a b : RayVert P} (p : Quiver.Path a b) (hp : 2 ≤ p.length) :
    ∃ (c d : RayVert P) (e₀ : a ⟶ c) (e₁ : c ⟶ d) (r : Quiver.Path d b),
      p = ((Quiver.Path.nil.cons e₀).cons e₁).comp r := by
  obtain ⟨c, e₀, r₀, h₀⟩ := path_first_arrow p (by omega)
  have hl : r₀.length ≠ 0 := by
    have := congrArg Quiver.Path.length h₀
    rw [Quiver.Path.length_comp] at this
    simp at this; omega
  obtain ⟨d, e₁, r, h₁⟩ := path_first_arrow r₀ hl
  exact ⟨c, d, e₀, e₁, r, by rw [h₀, h₁, ← Quiver.Path.comp_assoc]; rfl⟩

/-- **The star `Ẽ₆` at `y`**: if `ρ = ω' ≫ α` with `ω'` not invertible, then `v` or
`w` has at most two arrows. -/
theorem star_e6 (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    (hv : 2 ≤ C.v'.length) (hw : 2 ≤ C.w'.length) : False := by
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hαn := C.α.2.2.1
  have hβn := C.β.2.2.1
  obtain ⟨c, d, a₀, e₁, r, hr⟩ := path_two_arrows C.v' hv
  obtain ⟨c', d', b₀, f₁, r', hr'⟩ := path_two_arrows C.w' hw
  set u := e₁.1 ≫ pathVal r with hu
  set u' := f₁.1 ≫ pathVal r' with hu'
  have hγ : C.γ = a₀.1 ≫ u := by
    change pathVal C.v' = _; rw [hr, pathVal_comp]; change ((𝟙 _ ≫ a₀.1) ≫ e₁.1) ≫ _ = _
    simp only [Category.id_comp, Category.assoc, hu]
  have hδ : C.δ = b₀.1 ≫ u' := by
    change pathVal C.w' = _; rw [hr', pathVal_comp]; change ((𝟙 _ ≫ b₀.1) ≫ f₁.1) ≫ _ = _
    simp only [Category.id_comp, Category.assoc, hu']
  have hτv : C.τ = a₀.1 ≫ u ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ, hγ]; simp
  have hτw : C.τ = b₀.1 ≫ u' ≫ C.β.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_w, hρ, hδ]; simp
  have ha₀ := a₀.2.2.1
  have hb₀ := b₀.2.2.1
  have hγn := C.γ_not_isIso hR
  have hδn := C.δ_not_isIso hR
  have hun : ¬IsIso u := fun h ↦ e₁.2.2.1 (ray_isIso_factors e₁.1 (pathVal r)).1
  have hu'n : ¬IsIso u' := fun h ↦ f₁.2.2.1 (ray_isIso_factors f₁.1 (pathVal r')).1
  have nf : ∀ {s t : P} (p : x ⟶ s) (g : s ⟶ t) (q : t ⟶ y), ¬IsIso p → p ≫ g ≫ q = C.τ →
      ¬FactorsThroughMorphism C.τ g := fun p g q hp h ↦ not_ftm_mid hτ0 hp h
  -- the interlacing conditions at `y`
  have hv_eq : C.v'.cons C.α = ((Quiver.Path.nil.cons a₀).cons e₁).comp (r.cons C.α) := by
    rw [hr]; rfl
  have hw_eq : C.w'.cons C.β = ((Quiver.Path.nil.cons b₀).cons f₁).comp (r'.cons C.β) := by
    rw [hr']; rfl
  have hS1 : ¬∃ g, g ≫ C.β.1 = u ≫ C.α.1 := by
    rintro ⟨g, hg⟩
    apply C.hni
    rw [hv_eq]
    refine interlaced_of_factor hR _ (by simp) e₁ (r.cons C.α) C.w' C.β
      (by rw [← hv_eq]; exact C.hval) (by rw [← hv_eq]; exact C.h0) g ?_
    rw [hg, hu, Category.assoc]; rfl
  have hS2 : ¬∃ g, g ≫ C.α.1 = u' ≫ C.β.1 := by
    rintro ⟨g, hg⟩
    apply C.hni
    refine Relation.EqvGen.symm _ _ ?_
    rw [hw_eq]
    refine interlaced_of_factor hR _ (by simp) f₁ (r'.cons C.β) C.v' C.α
      (by rw [← hw_eq]; exact C.hval.symm) (by rw [← hw_eq, ← C.hval]; exact C.h0) g ?_
    rw [hg, hu', Category.assoc]; rfl
  refine hM.not_se6 C.τ C.τ_not_isIso hτ0 u C.α.1 u' C.β.1 ω' C.α.1
    (nf (C.γ ≫ C.α.1) ω' C.α.1 (not_isIso_comp_of_right _ _ hαn) (by rw [hτv, hγ]; simp))
    (by rw [← hρ]; exact C.ftm_ρ) (C.ftm_α hR)
    (nf C.γ _ C.α.1 hγn (by rw [hτv, hγ]; simp))
    (by rw [Category.assoc, ← hρ]; exact C.ftm_αρ hR)
    (nf a₀.1 u (C.α.1 ≫ ω' ≫ C.α.1) ha₀ (by rw [hτv]))
    (nf a₀.1 _ (ω' ≫ C.α.1) ha₀ (by rw [hτv]; simp))
    (nf a₀.1 _ C.α.1 ha₀ (by rw [hτv]; simp))
    (nf a₀.1 _ (𝟙 _) ha₀ (by rw [hτv]; simp))
    (C.ftm_β hR)
    (nf C.δ _ C.α.1 hδn (by rw [hτw, hδ]; simp))
    (by rw [Category.assoc, ← hρ]; exact C.ftm_βρ hR)
    (nf b₀.1 u' (C.β.1 ≫ ω' ≫ C.α.1) hb₀ (by rw [hτw]))
    (nf b₀.1 _ (ω' ≫ C.α.1) hb₀ (by rw [hτw]; simp))
    (nf b₀.1 _ C.α.1 hb₀ (by rw [hτw]; simp))
    (nf b₀.1 _ (𝟙 _) hb₀ (by rw [hτw]; simp))
    (C.ftm_α hR) hun hαn hu'n hβn hω' hαn hap.2 hS2 hap.1 hS1

end MildContour

end RayCat

end LargeIndecomposable
