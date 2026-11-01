module

public import LargeIndecomposable.MildContours.Diamonds.CaseA
public import LargeIndecomposable.Cleaving.Families.FamMD27

/-!
# [mild] diamonds, case (C): `β ≫ ω' = η ≫ γ`

[mild] Lemma LDII: case (C) leads to case (A) (impossible, `caseA`) or to case (D)
`α ≫ ω' = η ≫ γ`. Otherwise [mild] figure 2.7 is a cleaving thin diagram in `P/τ`; the
one non-obvious condition `αρ = gβ` is excluded by the crown `Ã(γ, αω', g, δ)`.
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

/-- No `g` with `g ≫ β = α ≫ ρ` unless case (A) or (D): the crown `Ã(γ, αω', g, δ)`. -/
theorem no_αρ_β (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    (hD : ¬∃ g, g ≫ C.γ = C.α.1 ≫ ω') (g : C.sv ⟶ C.sw) (hg : g ≫ C.β.1 = C.α.1 ≫ ω' ≫ C.α.1) :
    False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hgd := C.γ_δ_apart hR hL
  have hαn := C.α.2.2.1
  have hβn := C.β.2.2.1
  have hτv : C.τ = C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ]
  have hαρ0 : C.α.1 ≫ ω' ≫ C.α.1 ≠ 0 := by rw [← hρ]; exact C.αρ_ne_zero
  have hvw : C.γ ≫ C.α.1 = C.δ ≫ C.β.1 := C.hval
  refine hM.not_crown2 C.τ C.τ_not_isIso hτ0 C.γ (C.α.1 ≫ ω') g C.δ (C.ftm_γ hR)
    (nfp hτ0 C.γ (C.α.1 ≫ ω') C.α.1 (Or.inr hαn) (by rw [hτv]; simp)) ?_ (C.ftm_δ hR)
    ?_ hD ?_ ?_ ?_ ?_ hgd.1 hgd.2
  · rintro ⟨u, v, huv⟩
    have e : C.α.1 ≫ ω' ≫ C.α.1 = (u ≫ C.γ) ≫ (C.α.1 ≫ ω' ≫ C.α.1) ≫ (v ≫ C.β.1) := by
      conv_lhs => rw [← hg, huv, hτv]
      simp
    obtain ⟨-, h⟩ := IsRayCategory.eq_id_of_two_sided _ hαρ0 _ _ e
    haveI : IsIso (v ≫ C.β.1) := by rw [h]; infer_instance
    exact hβn (ray_isIso_factors v C.β.1).2
  · rintro ⟨c, hc⟩
    exact C.caseA hM hω' hρ (ξ := c ≫ C.α.1) (by rw [Category.assoc, hc])
  · rintro ⟨c, hc⟩
    have e : (c ≫ C.γ) ≫ C.α.1 = (C.α.1 ≫ ω') ≫ C.α.1 := by
      rw [Category.assoc, hvw, ← Category.assoc, hc, hg]; simp
    exact hD ⟨c, hR _ _ _ e (by rw [e]; simpa using hαρ0)⟩
  · rintro ⟨c, hc⟩
    have e : C.γ ≫ C.α.1 = (c ≫ C.α.1 ≫ ω') ≫ C.α.1 := by
      rw [hvw, ← hc, Category.assoc, hg]; simp
    exact C.caseA hM hω' hρ (ξ := c ≫ C.α.1)
      (by rw [Category.assoc]; exact (hR _ _ _ e C.h0).symm)
  · rintro ⟨c, hc⟩
    have e : C.α.1 ≫ (ω' ≫ c ≫ C.β.1) = C.α.1 ≫ (ω' ≫ C.α.1) := by
      rw [← hg, ← hc]; simp
    exact C.not_ρ_factor_both hM hρ (ω'' := ω' ≫ c)
      (by rw [hρ, Category.assoc, hL _ _ _ e (by rw [e]; exact hαρ0)])
  · rintro ⟨c, hc⟩
    have e : g ≫ (c ≫ C.α.1) = g ≫ C.β.1 := by rw [← Category.assoc, hc, hg]; simp
    exact hap.2 ⟨c, hL _ _ _ e (by rw [e, hg]; exact hαρ0)⟩

/-- **Case (C)**: `β ≫ ω' = η ≫ γ` forces case (D). -/
theorem caseC (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    {η : C.sw ⟶ x} (hη : C.β.1 ≫ ω' = η ≫ C.γ) (hD : ¬∃ g, g ≫ C.γ = C.α.1 ≫ ω') : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hgd := C.γ_δ_apart hR hL
  have hαn := C.α.2.2.1
  have hβn := C.β.2.2.1
  have hγn := C.γ_not_isIso hR
  have hδn := C.δ_not_isIso hR
  have hvw : C.γ ≫ C.α.1 = C.δ ≫ C.β.1 := C.hval
  have hτv : C.τ = C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ]
  have hτw : C.τ = C.δ ≫ C.β.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_w, hρ]
  have hτη : C.τ = C.δ ≫ η ≫ C.δ ≫ C.β.1 := by
    rw [hτw, ← Category.assoc C.β.1, hη, ← hvw]; simp
  have hηn : ¬IsIso η := by
    intro h
    exact C.caseA hM hω' hρ (ξ := inv η ≫ C.β.1) (by rw [Category.assoc, hη]; simp)
  have hL2 : ∀ g, g ≫ C.β.1 = ω' ≫ C.α.1 → False := fun g hg ↦
    C.not_ρ_factor_both hM hρ (ω'' := g) (by rw [hρ, hg])
  have hωω0 : C.γ ≫ C.α.1 ≫ ω' ≠ 0 := fun h ↦ hτ0 (by
    rw [hτv, show C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 = (C.γ ≫ C.α.1 ≫ ω') ≫ C.α.1 by simp, h, zero_comp])
  have hβω0 : C.β.1 ≫ ω' ≠ 0 := fun h ↦ hωω0 (by
    rw [← Category.assoc, hvw, Category.assoc, h, comp_zero])
  refine hM.not_md27 C.τ C.τ_not_isIso hτ0 C.γ C.δ C.α.1 C.β.1 η C.δ ω' C.α.1
    MD27.not_isRepresentationFinite hvw.symm (C.ftm_α hR)
    (nfp hτ0 C.γ (C.α.1 ≫ ω') C.α.1 (Or.inr hαn) (by rw [hτv]; simp))
    (by rw [Category.assoc, ← hρ]; exact C.ftm_αρ hR) (C.ftm_α hR)
    (nfp hτ0 C.δ (η ≫ C.δ) C.β.1 (Or.inl hδn) (by rw [hτη]; simp))
    (nfp hτ0 C.δ η (C.δ ≫ C.β.1) (Or.inl hδn) (by rw [hτη]))
    (C.ftm_β hR) (C.ftm_δ hR) (C.ftm_γ hR) (C.ftm_δ hR)
    (nfp hτ0 (𝟙 _) ((C.δ ≫ η) ≫ C.δ) C.β.1 (Or.inr hβn) (by rw [hτη]; simp))
    (nfp hτ0 (𝟙 _) (C.δ ≫ η) (C.δ ≫ C.β.1) (Or.inr (not_isIso_comp_left' _ hδn))
      (by rw [hτη]; simp))
    C.ftm_ω
    (nfp hτ0 (C.γ ≫ C.α.1) ω' C.α.1 (Or.inr hαn) (by rw [hτv]; simp))
    (by rw [← hρ]; exact C.ftm_ρ)
    hγn hδn hαn hβn hηn hδn hω' hαn ?_ ?_ ?_ hgd.2 ?_ ?_ hgd.1 hap.2 hap.1
    (fun ⟨g, hg⟩ ↦ hL2 g hg)
    (fun ⟨g, hg⟩ ↦ C.no_αρ_β hM hω' hρ hD g (by rw [hg]; simp))
    (fun ⟨g, hg⟩ ↦ hD ⟨C.α.1 ≫ g, by rw [Category.assoc, hg]⟩) hD
    (fun ⟨g, hg⟩ ↦ C.caseA hM hω' hρ hg)
  · rintro ⟨g, hg⟩
    have e : η ≫ (g ≫ ω') = η ≫ C.γ := by rw [← Category.assoc, hg, hη]
    exact C.caseA hM hω' hρ (hL _ _ _ e (by rw [e, ← hη]; exact hβω0))
  · rintro ⟨g, hg⟩
    have e : C.β.1 ≫ ω' = C.β.1 ≫ (g ≫ C.γ) := by rw [hη, ← hg, Category.assoc]
    have e2 := hL _ _ _ e hβω0
    exact hD ⟨C.α.1 ≫ g, by rw [Category.assoc, ← e2]⟩
  · rintro ⟨g, hg⟩
    have e : C.β.1 ≫ (g ≫ C.β.1) = C.β.1 ≫ (ω' ≫ C.α.1) := by
      rw [← Category.assoc, hg, Category.assoc, ← hvw, ← Category.assoc, ← hη]; simp
    exact hL2 g (hL _ _ _ e (by rw [e, ← hρ]; exact C.βρ_ne_zero))
  · rintro ⟨g, hg⟩
    have e : C.γ ≫ (g ≫ C.γ) = C.γ ≫ (C.α.1 ≫ ω') := by
      rw [← Category.assoc, hg, Category.assoc, ← hη, ← Category.assoc, ← hvw]; simp
    exact hD ⟨g, hL _ _ _ e (by rw [e]; simpa using hωω0)⟩
  · rintro ⟨g, hg⟩
    have e : C.γ ≫ (g ≫ C.β.1) = C.γ ≫ (C.α.1 ≫ ω' ≫ C.α.1) := by
      rw [← Category.assoc, hg, ← hτv, hτη]; simp
    exact C.no_αρ_β hM hω' hρ hD g (hL _ _ _ e (by rw [e, ← hτv]; exact hτ0))

end MildContour

end RayCat

end LargeIndecomposable
