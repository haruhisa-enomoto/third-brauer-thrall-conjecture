module

public import LargeIndecomposable.MildContours.Basic.Contour
public import LargeIndecomposable.Cleaving.Shapes.ShapeE7
public import LargeIndecomposable.Cleaving.Shapes.ShapeE8
public import LargeIndecomposable.Cleaving.Shapes.ShapeD4
public import LargeIndecomposable.Cleaving.Shapes.ShapeE7B
public import LargeIndecomposable.Cleaving.Shapes.ShapeE8B

/-!
# [mild] Lemma 2.1, Case I

With `τ' ≫ α = α ≫ ρ` (Case I), neither `ρ` factoring through `α` or `β` nor
the alternative (2) through `γ` or `δ`, a cleaving diagram exists in `P/τ`:
the crowns of `MildContour.caseIa`, `MildContour.caseIb`, the `Ẽ₇` and `Ẽ₈`
trees of [mild] figure 2.2, and the `D̃₄` of [mild] figure 2.1 (third diagram).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

namespace MildContour

variable {x y : P} (C : MildContour x y)

lemma τ_eq_v : C.τ = C.γ ≫ C.α.1 ≫ C.ρ := by
  change C.ω ≫ C.ρ = _; rw [C.ω_eq_v, Category.assoc]

lemma τ_eq_w : C.τ = C.δ ≫ C.β.1 ≫ C.ρ := by
  change C.ω ≫ C.ρ = _; rw [C.ω_eq_w, Category.assoc]

/-- The contour with `v` and `w` exchanged. -/
def swap : MildContour x y where
  sv := C.sw
  sw := C.sv
  v' := C.w'
  α := C.β
  w' := C.v'
  β := C.α
  hval := C.hval.symm
  h0 := by rw [← C.hval]; exact C.h0
  hni := fun h ↦ C.hni (Relation.EqvGen.symm _ _ h)
  ρ := C.ρ
  hρ := C.hρ
  hωρ := by rw [← C.hval]; exact C.hωρ

lemma swap_ω : C.swap.ω = C.ω := C.hval.symm

lemma swap_τ : C.swap.τ = C.τ := by
  change C.swap.ω ≫ C.ρ = C.ω ≫ C.ρ; rw [swap_ω]

variable [Fintype P] [DecidableEq P] [IsFiniteRayCategory P]

lemma no_ρ_eq_α (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ) : ¬∃ g, g ≫ C.ρ = C.α.1 := by
  rintro ⟨g, hg⟩
  rcases C.α.2.2.2 _ g C.ρ hg.symm with h | h
  · exact hn1 ⟨inv g, by rw [← hg, IsIso.inv_hom_id_assoc]⟩
  · exact C.ρ_not_isIso h

lemma no_ρ_eq_ω (hρρ : C.ρ ≫ C.ρ = 0) : ¬∃ g, g ≫ C.ρ = C.γ ≫ C.α.1 := by
  rintro ⟨g, hg⟩
  apply C.τ_ne_zero
  rw [C.τ_eq_v, ← Category.assoc, ← hg, Category.assoc, hρρ, comp_zero]

section CaseI

variable {τ' : C.sv ⟶ C.sv} (hτ' : τ' ≫ C.α.1 = C.α.1 ≫ C.ρ)
include hτ'

lemma no_τ'_α (hL : LeftCancel P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ) : ¬∃ g, τ' ≫ g = C.α.1 := by
  rintro ⟨c, hc⟩
  rcases C.α.2.2.2 _ τ' c hc.symm with h | h
  · exact C.not_isIso_of_endo_comp τ' C.α hτ' h
  · have hτ'' : τ' = C.α.1 ≫ inv c := by
      rw [← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have e : C.α.1 ≫ inv c ≫ C.α.1 = C.α.1 ≫ C.ρ := by rw [← Category.assoc, ← hτ'', hτ']
    exact hn1 ⟨inv c, hL _ _ _ e (by rw [e]; exact C.αρ_ne_zero)⟩

lemma no_α_τ' (hL : LeftCancel P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ) : ¬∃ g, C.α.1 ≫ g = τ' := by
  rintro ⟨c, hc⟩
  have e : C.α.1 ≫ c ≫ C.α.1 = C.α.1 ≫ C.ρ := by rw [← Category.assoc, hc, hτ']
  exact hn1 ⟨c, hL _ _ _ e (by rw [e]; exact C.αρ_ne_zero)⟩

lemma no_τ'_eq_γ (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) : ¬∃ g, g ≫ C.γ = τ' := by
  rintro ⟨c, hc⟩
  exact hn3γ ⟨c, by rw [C.τ_eq_v, ← hτ', ← hc, C.ω_eq_v]; simp only [Category.assoc]⟩

lemma no_γ_eq_τ' (hρρ : C.ρ ≫ C.ρ = 0) : ¬∃ g, g ≫ τ' = C.γ := by
  rintro ⟨c, hc⟩
  apply C.τ_ne_zero
  rw [C.τ_eq_v, ← hc, Category.assoc, ← Category.assoc τ', hτ', Category.assoc, hρρ, comp_zero,
    comp_zero]

lemma ftm_τ' (hR : RightCancel P) : ¬FactorsThroughMorphism C.τ τ' :=
  not_ftm_mid C.τ_ne_zero (C.γ_not_isIso hR) (by rw [hτ']; exact C.τ_eq_v.symm)

lemma ftm_γτ' : ¬FactorsThroughMorphism C.τ (C.γ ≫ τ') :=
  not_ftm_left C.τ_ne_zero C.α.2.2.1 (by rw [Category.assoc, hτ']; exact C.τ_eq_v.symm)

omit hτ' in
lemma ftm_ω : ¬FactorsThroughMorphism C.τ (C.γ ≫ C.α.1) :=
  not_ftm_left C.τ_ne_zero C.ρ_not_isIso (by rw [Category.assoc]; exact C.τ_eq_v.symm)

variable {k : Type*} [Field k] [Infinite k]

/-- **Cases I and II together** are impossible: the `D̃₄` of [mild] figure 2.1 (third
diagram) with centre `s(α)` is cleaving. -/
theorem caseI_II (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ) (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ) {η : C.sv ⟶ C.sw}
    (hη : η ≫ C.β.1 = C.α.1 ≫ C.ρ) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  refine hM.not_md4 C.τ C.τ_not_isIso C.τ_ne_zero C.γ C.α.1 τ' η (C.ftm_α hR) (C.ftm_τ' hτ' hR)
    (not_ftm_mid C.τ_ne_zero (C.γ_not_isIso hR) (by rw [hη]; exact C.τ_eq_v.symm)) (C.ftm_γ hR)
    C.ftm_ω (C.ftm_γτ' hτ')
    (not_ftm_left C.τ_ne_zero C.β.2.2.1 (by rw [Category.assoc, hη]; exact C.τ_eq_v.symm))
    (C.γ_not_isIso hR) C.α.2.2.1 (C.not_isIso_of_endo_comp τ' C.α hτ') ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro hi
    rcases C.β.2.2.2 _ (inv η ≫ C.α.1) C.ρ (by rw [Category.assoc, ← hη, IsIso.inv_hom_id_assoc])
      with h | h
    · exact C.α.2.2.1 (ray_isIso_factors (inv η) C.α.1).2
    · exact C.ρ_not_isIso h
  · exact C.no_α_τ' hτ' hL hn1
  · rintro ⟨g, hg⟩
    have e : C.α.1 ≫ g ≫ C.β.1 = C.α.1 ≫ C.ρ := by rw [← Category.assoc, hg, hη]
    exact hn2 ⟨g, hL _ _ _ e (by rw [e]; exact C.αρ_ne_zero)⟩
  · exact C.no_τ'_α hτ' hL hn1
  · rintro ⟨g, hg⟩
    have e : τ' ≫ g ≫ C.β.1 = τ' ≫ C.α.1 := by rw [← Category.assoc, hg, hη, hτ']
    exact hap.1 ⟨g, hL _ _ _ e (by rw [e, hτ']; exact C.αρ_ne_zero)⟩
  · rintro ⟨g, hg⟩
    have e : η ≫ g ≫ C.ρ = η ≫ C.β.1 := by rw [← Category.assoc, hg, hη]
    have hgβ := hL _ _ _ e (by rw [e, hη]; exact C.αρ_ne_zero)
    rcases C.β.2.2.2 _ g C.ρ hgβ.symm with h | h
    · exact hn2 ⟨inv g, by rw [← hgβ, IsIso.inv_hom_id_assoc]⟩
    · exact C.ρ_not_isIso h
  · rintro ⟨g, hg⟩
    have e : η ≫ g ≫ C.α.1 = η ≫ C.β.1 := by rw [← Category.assoc, hg, hτ', hη]
    exact hap.2 ⟨g, hL _ _ _ e (by rw [e, hη]; exact C.αρ_ne_zero)⟩

/-- **Case I(c), second diagram**: with `ξ ≫ γ = γ ≫ τ'`, the `Ẽ₈` tree of [mild]
figure 2.2 is cleaving. -/
theorem caseIc_E8 (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ)
    (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ)
    (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) (hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω)
    (hρρ : C.ρ ≫ C.ρ = 0) (hIa : ¬∃ ψ, ψ ≫ C.α.1 = C.β.1 ≫ C.ρ)
    (hIb : ¬∃ ψ, ψ ≫ C.β.1 = C.β.1 ≫ C.ρ) {ξ : x ⟶ x} (hξ : ξ ≫ C.γ = C.γ ≫ τ') : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hγδ := C.γ_δ_apart hR hL
  have hξτ : ξ ≫ C.ω = C.τ := by
    rw [C.ω_eq_v, ← Category.assoc, hξ, Category.assoc, hτ']; exact C.τ_eq_v.symm
  have hτ0 : ξ ≫ C.ω ≠ 0 := by rw [hξτ]; exact C.τ_ne_zero
  refine hM.not_me8 C.τ C.τ_not_isIso C.τ_ne_zero ξ C.δ C.δ C.γ τ' C.α.1 C.ρ C.β.1
    (not_ftm_left C.τ_ne_zero C.ω_not_isIso hξτ)
    (not_ftm_left C.τ_ne_zero C.β.2.2.1 (by rw [Category.assoc, ← C.ω_eq_w, hξτ]))
    (C.ftm_δ hR) (C.ftm_γ hR) (C.ftm_δ hR) (C.ftm_τ' hτ' hR) (C.ftm_α hR) C.ftm_ρ (C.ftm_β hR)
    (C.ftm_βρ hR) ?_ (C.δ_not_isIso hR) (C.δ_not_isIso hR) (C.γ_not_isIso hR)
    (C.not_isIso_of_endo_comp τ' C.α hτ') C.α.2.2.1 C.ρ_not_isIso C.β.2.2.1 ?_ ?_ ?_ ?_
    hγδ.1 (fun ⟨g, hg⟩ ↦ hn3γ ⟨g, by rw [hg, hξτ]⟩) ?_ hγδ.2 (C.no_τ'_α hτ' hL hn1)
    (C.no_α_τ' hτ' hL hn1) (C.no_τ'_eq_γ hτ' hn3γ) (C.no_γ_eq_τ' hτ' hρρ) hn1 hIa
    (C.no_ρ_eq_α hn1)
  · -- `ξ` is not invertible
    intro hi
    obtain ⟨hxx, he⟩ := RayQuiver.eq_id_of_isIso ξ
    have h1 : ξ = 𝟙 x := by rw [he]; rfl
    have e : C.ω = C.ω ≫ C.ρ := by rw [h1, Category.id_comp] at hξτ; exact hξτ
    apply C.τ_ne_zero
    change C.ω ≫ C.ρ = 0
    rw [e, Category.assoc, hρρ, comp_zero]
  · -- `δ = ξ ≫ g`
    rintro ⟨g, hg⟩
    have e : ξ ≫ (g ≫ C.β.1 ≫ C.ρ) = ξ ≫ C.ω := by rw [reassoc_of% hg, hξτ, C.τ_eq_w]
    have e2 := hL _ _ _ e (by rw [e]; exact hτ0)
    apply C.τ_ne_zero
    change C.ω ≫ C.ρ = 0
    rw [← e2]; simp only [Category.assoc, hρρ, comp_zero]
  · -- `γ = ξ ≫ g`
    rintro ⟨g, hg⟩
    have e : ξ ≫ (g ≫ C.α.1 ≫ C.ρ) = ξ ≫ C.ω := by rw [reassoc_of% hg, hξτ, C.τ_eq_v]
    have e2 := hL _ _ _ e (by rw [e]; exact hτ0)
    apply C.τ_ne_zero
    change C.ω ≫ C.ρ = 0
    rw [← e2]; simp only [Category.assoc, hρρ, comp_zero]
  · -- `ξ = δ ≫ g`: alternative (2) through `δ`
    rintro ⟨g, hg⟩
    exact hn3δ ⟨g, by rw [hg, hξτ]⟩
  · -- `ξ ≫ δ = δ ≫ g`: Case I(b)
    rintro ⟨g, hg⟩
    have e : C.δ ≫ (g ≫ C.β.1) = C.δ ≫ (C.β.1 ≫ C.ρ) := by
      rw [reassoc_of% hg, ← C.ω_eq_w, hξτ, C.τ_eq_w]
    exact hIb ⟨g, hL _ _ _ e (by rw [e, ← C.τ_eq_w]; exact C.τ_ne_zero)⟩
  · -- `ξ ≫ δ = γ ≫ g`: Cases I and II together
    rintro ⟨g, hg⟩
    have e : C.γ ≫ (g ≫ C.β.1) = C.γ ≫ (C.α.1 ≫ C.ρ) := by
      rw [reassoc_of% hg, ← C.ω_eq_w, hξτ, C.τ_eq_v]
    exact C.caseI_II hτ' hM hn1 hn2 (hL _ _ _ e (by rw [e, ← C.τ_eq_v]; exact C.τ_ne_zero))

/-- **Case I(c)**: the `Ẽ₇` tree of [mild] figure 2.2 is cleaving unless
`ξ ≫ γ = γ ≫ τ'`, which `caseIc_E8` excludes. -/
theorem caseIc (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ)
    (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ)
    (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) (hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω)
    (hρρ : C.ρ ≫ C.ρ = 0) (hIa : ¬∃ ψ, ψ ≫ C.α.1 = C.β.1 ≫ C.ρ)
    (hIb : ¬∃ ψ, ψ ≫ C.β.1 = C.β.1 ≫ C.ρ) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hγδ := C.γ_δ_apart hR hL
  exact hM.not_me7 C.τ C.τ_not_isIso C.τ_ne_zero C.δ C.γ τ' C.γ C.α.1 C.ρ C.β.1
    (C.ftm_τ' hτ' hR) (C.ftm_α hR) (C.ftm_γ hR) (C.ftm_γτ' hτ') C.ftm_ω (C.ftm_δ hR)
    (C.ftm_γ hR) C.ftm_ρ (C.ftm_β hR) (C.ftm_βρ hR) (C.δ_not_isIso hR) (C.γ_not_isIso hR)
    (C.not_isIso_of_endo_comp τ' C.α hτ') (C.γ_not_isIso hR) C.α.2.2.1 C.ρ_not_isIso C.β.2.2.1
    (C.no_τ'_α hτ' hL hn1) (C.no_α_τ' hτ' hL hn1) hγδ.1 hγδ.2 (C.no_τ'_eq_γ hτ' hn3γ)
    (fun ⟨ξ, hξ⟩ ↦ C.caseIc_E8 hτ' hM hn1 hn2 hn3γ hn3δ hρρ hIa hIb hξ)
    (C.no_γ_eq_τ' hτ' hρρ) hn1 hIa (C.no_ρ_eq_α hn1) (C.no_ρ_eq_ω hρρ)

/-- **[mild] Lemma 2.1, Case I** (`τ' ≫ α = α ≫ ρ`) is impossible when neither `ρ`
factors through `α` or `β` nor the alternative (2) holds. -/
theorem caseI (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ)
    (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ)
    (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) (hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω) : False := by
  have hρρ := C.rho_sq hM hn1 hn2
  by_cases hIa : ∃ ψ, ψ ≫ C.α.1 = C.β.1 ≫ C.ρ
  · obtain ⟨ψ, hψ⟩ := hIa
    exact C.caseIa hM hn1 hτ' hψ
  by_cases hIb : ∃ ψ, ψ ≫ C.β.1 = C.β.1 ≫ C.ρ
  · obtain ⟨ψ, hψ⟩ := hIb
    exact C.caseIb hM hn1 hn2 hn3γ hn3δ hρρ hτ' hψ
  exact C.caseIc hτ' hM hn1 hn2 hn3γ hn3δ hρρ hIa hIb

end CaseI

section CaseII

variable {φ : C.sv ⟶ C.sw} (hφ : φ ≫ C.β.1 = C.α.1 ≫ C.ρ)
include hφ

lemma φ_not_isIso : ¬IsIso φ := by
  intro hi
  rcases C.β.2.2.2 _ (inv φ ≫ C.α.1) C.ρ (by rw [Category.assoc, ← hφ, IsIso.inv_hom_id_assoc])
    with h | h
  · exact C.α.2.2.1 (ray_isIso_factors (inv φ) C.α.1).2
  · exact C.ρ_not_isIso h

lemma no_φ_α (hL : LeftCancel P) (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ) : ¬∃ g, φ ≫ g = C.α.1 := by
  rintro ⟨g, hg⟩
  have e : φ ≫ g ≫ C.ρ = φ ≫ C.β.1 := by rw [← Category.assoc, hg, hφ]
  have hgβ := hL _ _ _ e (by rw [e, hφ]; exact C.αρ_ne_zero)
  rcases C.β.2.2.2 _ g C.ρ hgβ.symm with h | h
  · exact hn2 ⟨inv g, by rw [← hgβ, IsIso.inv_hom_id_assoc]⟩
  · exact C.ρ_not_isIso h

lemma no_α_φ (hL : LeftCancel P) (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ) : ¬∃ g, C.α.1 ≫ g = φ := by
  rintro ⟨g, hg⟩
  have e : C.α.1 ≫ g ≫ C.β.1 = C.α.1 ≫ C.ρ := by rw [← Category.assoc, hg, hφ]
  exact hn2 ⟨g, hL _ _ _ e (by rw [e]; exact C.αρ_ne_zero)⟩

lemma no_φ_eq_δ (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) : ¬∃ g, g ≫ C.δ = φ := by
  rintro ⟨g, hg⟩
  exact hn3γ ⟨g, by rw [C.τ_eq_v, ← hφ, ← hg, C.ω_eq_w]; simp only [Category.assoc]⟩

lemma no_δ_eq_φ (hρρ : C.ρ ≫ C.ρ = 0) : ¬∃ g, g ≫ φ = C.δ := by
  rintro ⟨g, hg⟩
  apply C.τ_ne_zero
  rw [C.τ_eq_w, ← hg, Category.assoc, ← Category.assoc φ, hφ, Category.assoc, hρρ, comp_zero,
    comp_zero]

lemma ftm_φ (hR : RightCancel P) : ¬FactorsThroughMorphism C.τ φ :=
  not_ftm_mid C.τ_ne_zero (C.γ_not_isIso hR) (by rw [hφ]; exact C.τ_eq_v.symm)

lemma ftm_γφ : ¬FactorsThroughMorphism C.τ (C.γ ≫ φ) :=
  not_ftm_left C.τ_ne_zero C.β.2.2.1 (by rw [Category.assoc, hφ]; exact C.τ_eq_v.symm)

variable {k : Type*} [Field k] [Infinite k]

/-- **Cases II and II' together**: `φ ≫ β = α ≫ ρ` and `ψ ≫ α = β ≫ ρ` give the crown
`Ã(γ, ψ, β, α, φ, δ)` in `P/τ`. -/
theorem caseII_II' (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ)
    (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ)
    (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) (hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω)
    (hρρ : C.ρ ≫ C.ρ = 0) {ψ : C.sw ⟶ C.sv} (hψ : ψ ≫ C.α.1 = C.β.1 ≫ C.ρ) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hγδ := C.γ_δ_apart hR hL
  refine hM.not_crown3 C.τ C.τ_not_isIso C.τ_ne_zero C.γ ψ C.β.1 C.α.1 φ C.δ (C.ftm_γ hR)
    (not_ftm_mid C.τ_ne_zero (C.δ_not_isIso hR) (by rw [hψ]; exact C.τ_eq_w.symm))
    (C.ftm_β hR) (C.ftm_α hR) (C.ftm_φ hφ hR) (C.ftm_δ hR) ?_ ?_ hap.2 hap.1
    (C.no_φ_eq_δ hφ hn3γ) (C.no_δ_eq_φ hφ hρρ) ?_ ?_ (C.no_α_φ hφ hL hn2) (C.no_φ_α hφ hL hn2)
    hγδ.1 hγδ.2
  · -- `γ = c ≫ ψ`
    rintro ⟨c, hc⟩
    apply C.τ_ne_zero
    rw [C.τ_eq_v, ← hc, Category.assoc, ← Category.assoc ψ, hψ, Category.assoc, hρρ, comp_zero,
      comp_zero]
  · -- `ψ = c ≫ γ`: alternative (2) through `δ`
    rintro ⟨c, hc⟩
    exact hn3δ ⟨c, by rw [C.τ_eq_w, ← hψ, ← hc, C.ω_eq_v]; simp only [Category.assoc]⟩
  · -- `β = ψ ≫ c`
    rintro ⟨c, hc⟩
    have e : ψ ≫ c ≫ C.ρ = ψ ≫ C.α.1 := by rw [← Category.assoc, hc, hψ]
    exact C.no_ρ_eq_α hn1 ⟨c, hL _ _ _ e (by rw [e, hψ]; exact C.βρ_ne_zero)⟩
  · -- `ψ = β ≫ c`
    rintro ⟨c, hc⟩
    have e : C.β.1 ≫ c ≫ C.α.1 = C.β.1 ≫ C.ρ := by rw [← Category.assoc, hc, hψ]
    exact hn1 ⟨c, hL _ _ _ e (by rw [e]; exact C.βρ_ne_zero)⟩

/-- **Case II(c), second diagram**: with `ξ ≫ δ = γ ≫ φ`, an `Ẽ₈` tree is cleaving. -/
theorem caseIIc_E8 (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ)
    (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ)
    (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) (hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω)
    (hρρ : C.ρ ≫ C.ρ = 0) (hI : ¬∃ t, t ≫ C.α.1 = C.α.1 ≫ C.ρ)
    (hII' : ¬∃ ψ, ψ ≫ C.α.1 = C.β.1 ≫ C.ρ) {ξ : x ⟶ x} (hξ : ξ ≫ C.δ = C.γ ≫ φ) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hγδ := C.γ_δ_apart hR hL
  have hξτ : ξ ≫ C.ω = C.τ := by
    rw [C.ω_eq_w, ← Category.assoc, hξ, Category.assoc, hφ]; exact C.τ_eq_v.symm
  have hτ0 : ξ ≫ C.ω ≠ 0 := by rw [hξτ]; exact C.τ_ne_zero
  refine hM.not_me8b C.τ C.τ_not_isIso C.τ_ne_zero ξ C.γ C.γ C.δ φ C.α.1 C.ρ C.β.1
    (not_ftm_left C.τ_ne_zero C.ω_not_isIso hξτ)
    (not_ftm_left C.τ_ne_zero C.α.2.2.1 (by rw [Category.assoc, ← C.ω_eq_v, hξτ]))
    (C.ftm_γ hR) (C.ftm_δ hR) (C.ftm_γ hR) (C.ftm_φ hφ hR) (C.ftm_α hR) C.ftm_ρ (C.ftm_β hR)
    (C.ftm_βρ hR) ?_ (C.γ_not_isIso hR) (C.γ_not_isIso hR) (C.δ_not_isIso hR)
    (C.φ_not_isIso hφ) C.α.2.2.1 C.ρ_not_isIso C.β.2.2.1 ?_ ?_
    (fun ⟨g, hg⟩ ↦ hn3γ ⟨g, by rw [hg, hξτ]⟩) ?_ hγδ.2
    (fun ⟨g, hg⟩ ↦ hn3δ ⟨g, by rw [hg, hξτ]⟩) ?_ hγδ.1 (C.no_φ_α hφ hL hn2)
    (C.no_α_φ hφ hL hn2) (C.no_φ_eq_δ hφ hn3γ) (C.no_δ_eq_φ hφ hρρ) hn1 hII' (C.no_ρ_eq_α hn1)
  · -- `ξ` is not invertible
    intro hi
    obtain ⟨hxx, he⟩ := RayQuiver.eq_id_of_isIso ξ
    have h1 : ξ = 𝟙 x := by rw [he]; rfl
    have e : C.ω = C.ω ≫ C.ρ := by rw [h1, Category.id_comp] at hξτ; exact hξτ
    apply C.τ_ne_zero
    change C.ω ≫ C.ρ = 0
    rw [e, Category.assoc, hρρ, comp_zero]
  · -- `γ = ξ ≫ g`
    rintro ⟨g, hg⟩
    have e : ξ ≫ (g ≫ C.α.1 ≫ C.ρ) = ξ ≫ C.ω := by rw [reassoc_of% hg, hξτ, C.τ_eq_v]
    have e2 := hL _ _ _ e (by rw [e]; exact hτ0)
    apply C.τ_ne_zero
    change C.ω ≫ C.ρ = 0
    rw [← e2]; simp only [Category.assoc, hρρ, comp_zero]
  · -- `δ = ξ ≫ g`
    rintro ⟨g, hg⟩
    have e : ξ ≫ (g ≫ C.β.1 ≫ C.ρ) = ξ ≫ C.ω := by rw [reassoc_of% hg, hξτ, C.τ_eq_w]
    have e2 := hL _ _ _ e (by rw [e]; exact hτ0)
    apply C.τ_ne_zero
    change C.ω ≫ C.ρ = 0
    rw [← e2]; simp only [Category.assoc, hρρ, comp_zero]
  · -- `ξ ≫ γ = γ ≫ g`: Case I
    rintro ⟨g, hg⟩
    have e : C.γ ≫ (g ≫ C.α.1) = C.γ ≫ (C.α.1 ≫ C.ρ) := by
      rw [reassoc_of% hg, ← C.ω_eq_v, hξτ, C.τ_eq_v]
    exact hI ⟨g, hL _ _ _ e (by rw [e, ← C.τ_eq_v]; exact C.τ_ne_zero)⟩
  · -- `ξ ≫ γ = δ ≫ g`: Case II'
    rintro ⟨g, hg⟩
    have e : C.δ ≫ (g ≫ C.α.1) = C.δ ≫ (C.β.1 ≫ C.ρ) := by
      rw [reassoc_of% hg, ← C.ω_eq_v, hξτ, C.τ_eq_w]
    exact hII' ⟨g, hL _ _ _ e (by rw [e, ← C.τ_eq_w]; exact C.τ_ne_zero)⟩

/-- **Case II(c)**: an `Ẽ₇` tree is cleaving unless `ξ ≫ δ = γ ≫ φ`. -/
theorem caseIIc (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ)
    (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ)
    (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) (hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω)
    (hρρ : C.ρ ≫ C.ρ = 0) (hI : ¬∃ t, t ≫ C.α.1 = C.α.1 ≫ C.ρ)
    (hII' : ¬∃ ψ, ψ ≫ C.α.1 = C.β.1 ≫ C.ρ) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hγδ := C.γ_δ_apart hR hL
  exact hM.not_me7b C.τ C.τ_not_isIso C.τ_ne_zero φ C.δ C.γ C.γ C.α.1 C.ρ C.β.1
    (C.ftm_φ hφ hR) (C.ftm_α hR) (C.ftm_γ hR) (C.ftm_γφ hφ) C.ftm_ω (C.ftm_δ hR) (C.ftm_γ hR)
    C.ftm_ρ (C.ftm_β hR) (C.ftm_βρ hR) (C.φ_not_isIso hφ) (C.δ_not_isIso hR) (C.γ_not_isIso hR)
    (C.γ_not_isIso hR) C.α.2.2.1 C.ρ_not_isIso C.β.2.2.1 (C.no_φ_α hφ hL hn2)
    (C.no_α_φ hφ hL hn2) hγδ.1 hγδ.2 (C.no_δ_eq_φ hφ hρρ) (C.no_φ_eq_δ hφ hn3γ)
    (fun ⟨ξ, hξ⟩ ↦ C.caseIIc_E8 hφ hM hn1 hn2 hn3γ hn3δ hρρ hI hII' hξ) hn1 hII'
    (C.no_ρ_eq_α hn1) (C.no_ρ_eq_ω hρρ)

/-- **[mild] Lemma 2.1, Case II** (`φ ≫ β = α ≫ ρ`) is impossible outside Case I when
neither `ρ` factors through `α` or `β` nor the alternative (2) holds. -/
theorem caseII (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ)
    (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ)
    (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) (hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω)
    (hI : ¬∃ t, t ≫ C.α.1 = C.α.1 ≫ C.ρ) : False := by
  have hρρ := C.rho_sq hM hn1 hn2
  by_cases hII' : ∃ ψ, ψ ≫ C.α.1 = C.β.1 ≫ C.ρ
  · obtain ⟨ψ, hψ⟩ := hII'
    exact C.caseII_II' hφ hM hn1 hn2 hn3γ hn3δ hρρ hψ
  exact C.caseIIc hφ hM hn1 hn2 hn3γ hn3δ hρρ hI hII'

end CaseII

variable {k : Type*} [Field k] [Infinite k]

/-- **[mild] Lemma 2.1**: for a mild contour on the transit side, `ρ = π(y)` factors
through `α` or `β`, or the alternative (2) holds: `τ = (γ ≫ ξ) ≫ ω` or `τ = (δ ≫ ξ) ≫ ω`. -/
theorem lemma21 (hM : MildHyp k P) :
    (∃ ξ, ξ ≫ C.α.1 = C.ρ) ∨ (∃ ξ, ξ ≫ C.β.1 = C.ρ) ∨
      (∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) ∨ (∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ := fun ⟨ξ, hξ⟩ ↦ h1 ξ hξ
  have hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ := fun ⟨ξ, hξ⟩ ↦ h2 ξ hξ
  have hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω := fun ⟨ξ, hξ⟩ ↦ h3 ξ hξ
  have hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω := fun ⟨ξ, hξ⟩ ↦ h4 ξ hξ
  have sn3γ : ¬∃ ξ, C.swap.τ = (C.swap.γ ≫ ξ) ≫ C.swap.ω := by
    rw [swap_τ, swap_ω]; exact hn3δ
  have sn3δ : ¬∃ ξ, C.swap.τ = (C.swap.δ ≫ ξ) ≫ C.swap.ω := by
    rw [swap_τ, swap_ω]; exact hn3γ
  have hI : ¬∃ t, t ≫ C.α.1 = C.α.1 ≫ C.ρ := fun ⟨t, ht⟩ ↦ C.caseI ht hM hn1 hn2 hn3γ hn3δ
  have hI' : ¬∃ t, t ≫ C.β.1 = C.β.1 ≫ C.ρ := fun ⟨t, ht⟩ ↦
    C.swap.caseI (τ' := t) ht hM hn2 hn1 sn3γ sn3δ
  rcases C.step2 hM with ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact hI ⟨t, ht⟩
  · exact hI' ⟨t, ht⟩
  · exact C.caseII hφ hM hn1 hn2 hn3γ hn3δ hI
  · exact C.swap.caseII (φ := φ) hφ hM hn2 hn1 sn3γ sn3δ hI'

end MildContour

end RayCat

end LargeIndecomposable
