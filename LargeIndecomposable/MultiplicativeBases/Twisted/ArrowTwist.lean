module

public import LargeIndecomposable.MultiplicativeBases.Twisted.TwistLift
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayPathLift

/-!
# Twisting a chosen ray-arrow lift at one arrow

For a lift `L` of the ray arrows (`BGRSRayArrowLift`), multiply the representative
of one arrow by a unit on its target side (`L.twistTgt`) or source side
(`L.twistSrc`). The result is again a lift (units do not change rays), and it is
zero-detecting when `L` is, under the conditions of `MultiplicativeBases/Twisted/TwistLift.lean`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace LargeIndecomposable.BGRSRayArrowLift

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasWellDefinedBGRSRayProduct C]

open Classical in
/-- The unit `w` at `j₀` and the identity elsewhere. -/
def unitAt (j₀ : RayVertex (BGRSRayCategory C)) (w : j₀.obj.as ⟶ j₀.obj.as) :
    ∀ v : RayVertex (BGRSRayCategory C), v.obj.as ⟶ v.obj.as := fun v ↦
  if h : v = j₀ then eqToHom (by rw [h]) ≫ w ≫ eqToHom (by rw [h]) else 𝟙 _

lemma unitAt_self (j₀ : RayVertex (BGRSRayCategory C)) (w : j₀.obj.as ⟶ j₀.obj.as) :
    unitAt j₀ w j₀ = w := by
  simp [unitAt]

lemma unitAt_isIso (j₀ : RayVertex (BGRSRayCategory C)) (w : j₀.obj.as ⟶ j₀.obj.as)
    [IsIso w] (v : RayVertex (BGRSRayCategory C)) : IsIso (unitAt j₀ w v) := by
  unfold unitAt
  split_ifs with h
  · subst h; simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; infer_instance
  · infer_instance

lemma unitRay_iso_comp {X Y : C} (w : X ⟶ X) [IsIso w] (f : X ⟶ Y) :
    unitRay (w ≫ f) = unitRay f :=
  (unitRay_eq_iff _ _).2 ⟨(asIso w).symm, Iso.refl _, by simp⟩

lemma unitRay_comp_iso {X Y : C} (f : X ⟶ Y) (w : Y ⟶ Y) [IsIso w] :
    unitRay (f ≫ w) = unitRay f :=
  (unitRay_eq_iff _ _).2 ⟨Iso.refl _, (asIso w).symm, by simp⟩

/-- Twist the lift of `a` on its target side by the units `W`. -/
def twistTgt (L : BGRSRayArrowLift (C := C)) {i₀ j₀ : RayVertex (BGRSRayCategory C)}
    (a : i₀ ⟶ j₀) (W : ∀ v : RayVertex (BGRSRayCategory C), v.obj.as ⟶ v.obj.as)
    (hW : ∀ v, IsIso (W v)) : BGRSRayArrowLift (C := C) where
  representative e := LargeIndecomposable.TwistLift.twistTgt (fun v ↦ v.obj.as)
    L.representative a W e
  unitRay_representative e := by
    rcases LargeIndecomposable.TwistLift.twistTgt_eq (fun v ↦ v.obj.as) L.representative a W e
      with h | h
    · rw [h]
      haveI := hW
      rw [unitRay_iso_comp, L.unitRay_representative]
    · rw [h, L.unitRay_representative]

/-- Twist the lift of `a` on its source side by the units `W`. -/
def twistSrc (L : BGRSRayArrowLift (C := C)) {i₀ j₀ : RayVertex (BGRSRayCategory C)}
    (a : i₀ ⟶ j₀) (W : ∀ v : RayVertex (BGRSRayCategory C), v.obj.as ⟶ v.obj.as)
    (hW : ∀ v, IsIso (W v)) : BGRSRayArrowLift (C := C) where
  representative e := LargeIndecomposable.TwistLift.twistSrc (fun v ↦ v.obj.as)
    L.representative a W e
  unitRay_representative e := by
    rcases LargeIndecomposable.TwistLift.twistSrc_eq (fun v ↦ v.obj.as) L.representative a W e
      with h | h
    · rw [h]
      haveI := hW
      rw [unitRay_comp_iso, L.unitRay_representative]
    · rw [h, L.unitRay_representative]

/-- **Zero detection survives a target-side twist.** -/
theorem twistTgt_zero (L : BGRSRayArrowLift (C := C)) {i₀ j₀ : RayVertex (BGRSRayCategory C)}
    (a : i₀ ⟶ j₀) (ℓ : j₀ ⟶ j₀) (w : j₀.obj.as ⟶ j₀.obj.as) [IsIso w]
    (hcomm : w ≫ L.representative ℓ = L.representative ℓ ≫ w)
    (hK : ∀ {m : RayVertex (BGRSRayCategory C)} (e : j₀ ⟶ m), ¬(∃ _ : m = j₀, HEq e ℓ) →
      ∀ u : j₀.obj.as ⟶ j₀.obj.as, L.representative e ≫ u ≫ L.representative a = 0)
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) :
    (L.twistTgt a (unitAt j₀ w) (unitAt_isIso j₀ w)).pathMap p = 0 ↔ L.pathMap p = 0 :=
  LargeIndecomposable.TwistLift.pathMap_twistTgt_eq_zero_iff (fun v ↦ v.obj.as)
    L.representative a (unitAt j₀ w) ℓ (unitAt_isIso j₀ w) (by rw [unitAt_self]; exact hcomm)
    (fun e he u ↦ hK e he u) p

/-- **Zero detection survives a source-side twist.** -/
theorem twistSrc_zero (L : BGRSRayArrowLift (C := C)) {i₀ j₀ : RayVertex (BGRSRayCategory C)}
    (a : i₀ ⟶ j₀) (ℓ : i₀ ⟶ i₀) (w : i₀.obj.as ⟶ i₀.obj.as) [IsIso w]
    (hcomm : w ≫ L.representative ℓ = L.representative ℓ ≫ w)
    (hK : ∀ {m : RayVertex (BGRSRayCategory C)} (e : m ⟶ i₀), ¬(∃ _ : m = i₀, HEq e ℓ) →
      ∀ u : i₀.obj.as ⟶ i₀.obj.as, L.representative a ≫ u ≫ L.representative e = 0)
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) :
    (L.twistSrc a (unitAt i₀ w) (unitAt_isIso i₀ w)).pathMap p = 0 ↔ L.pathMap p = 0 :=
  LargeIndecomposable.TwistLift.pathMap_twistSrc_eq_zero_iff (fun v ↦ v.obj.as)
    L.representative a (unitAt i₀ w) ℓ (unitAt_isIso i₀ w) (by rw [unitAt_self]; exact hcomm)
    (fun e he u ↦ hK e he u) p

/-- The twisted representative of `a`. -/
lemma twistTgt_rep_a (L : BGRSRayArrowLift (C := C)) {i₀ j₀ : RayVertex (BGRSRayCategory C)}
    (a : i₀ ⟶ j₀) (w : j₀.obj.as ⟶ j₀.obj.as) [IsIso w] :
    (L.twistTgt a (unitAt j₀ w) (unitAt_isIso j₀ w)).representative a = w ≫ L.representative a := by
  change LargeIndecomposable.TwistLift.twistTgt _ _ a _ a = _
  rw [LargeIndecomposable.TwistLift.twistTgt_a, unitAt_self]

lemma twistSrc_rep_a (L : BGRSRayArrowLift (C := C)) {i₀ j₀ : RayVertex (BGRSRayCategory C)}
    (a : i₀ ⟶ j₀) (w : i₀.obj.as ⟶ i₀.obj.as) [IsIso w] :
    (L.twistSrc a (unitAt i₀ w) (unitAt_isIso i₀ w)).representative a = L.representative a ≫ w := by
  change LargeIndecomposable.TwistLift.twistSrc _ _ a _ a = _
  rw [LargeIndecomposable.TwistLift.twistSrc_a, unitAt_self]

/-- Other representatives are unchanged. -/
lemma twistTgt_rep_of_not (L : BGRSRayArrowLift (C := C)) {i₀ j₀ : RayVertex (BGRSRayCategory C)}
    (a : i₀ ⟶ j₀) (W : ∀ v : RayVertex (BGRSRayCategory C), v.obj.as ⟶ v.obj.as)
    (hW : ∀ v, IsIso (W v)) {i j : RayVertex (BGRSRayCategory C)} (e : i ⟶ j)
    (he : ¬LargeIndecomposable.TwistLift.IsA a e) :
    (L.twistTgt a W hW).representative e = L.representative e :=
  LargeIndecomposable.TwistLift.twistTgt_of_not _ _ a W e he

lemma twistSrc_rep_of_not (L : BGRSRayArrowLift (C := C)) {i₀ j₀ : RayVertex (BGRSRayCategory C)}
    (a : i₀ ⟶ j₀) (W : ∀ v : RayVertex (BGRSRayCategory C), v.obj.as ⟶ v.obj.as)
    (hW : ∀ v, IsIso (W v)) {i j : RayVertex (BGRSRayCategory C)} (e : i ⟶ j)
    (he : ¬LargeIndecomposable.TwistLift.IsA a e) :
    (L.twistSrc a W hW).representative e = L.representative e :=
  LargeIndecomposable.TwistLift.twistSrc_of_not _ _ a W e he

end LargeIndecomposable.BGRSRayArrowLift
