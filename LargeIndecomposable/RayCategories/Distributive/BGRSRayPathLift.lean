module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import LargeIndecomposable.RayCategories.Basic.FiniteRayCategory

@[expose] public section

/-!
# Source-category lifts of BGRS ray paths

Choose an ordinary source-category representative for every irreducible arrow
of a BGRS ray category and evaluate paths by ordinary composition.  For any
such choice, every nonzero ray path is represented correctly, and equal
nonzero ray paths are exactly those whose ordinary composites differ by
endpoint units.

This file deliberately makes no scalar-normalization claim.  Constructing a
semi-normalized presentation and annihilating singular paths are separate
BGRS inputs.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasWellDefinedBGRSRayProduct C]

/-- A choice of source-category representative for every irreducible arrow of
the BGRS ray category. -/
structure BGRSRayArrowLift where
  representative :
    ∀ {i j : RayVertex (BGRSRayCategory C)} (_a : i ⟶ j),
      j.obj.as ⟶ i.obj.as
  unitRay_representative :
    ∀ {i j : RayVertex (BGRSRayCategory C)} (a : i ⟶ j),
      unitRay (representative a) = a.1

namespace BGRSRayArrowLift

/-- The always-available lift obtained from the quotient's arbitrary
representative choice. -/
def quotientOut : BGRSRayArrowLift (C := C) where
  representative a := a.1.out
  unitRay_representative a := unitRay_out a.1

/-- Ordinary source-category evaluation of a path using chosen ray-arrow
lifts. -/
abbrev pathMap (L : BGRSRayArrowLift (C := C))
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) :
    j.obj.as ⟶ i.obj.as :=
  LinearPathCategory.pathMap (fun x ↦ x.obj.as)
    (fun {i j} (a : i ⟶ j) ↦ L.representative a) p

/-- A nonzero ray-category path is represented by the ordinary composite of
any chosen arrow lifts. -/
theorem unitRay_pathMap_eq_rayPathMap_of_ne_zero
    (L : BGRSRayArrowLift (C := C))
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j)
    (hp : rayPathMap p ≠ 0) :
    unitRay (L.pathMap p) = rayPathMap p := by
  induction p with
  | nil => simp [pathMap, rayPathMap]
  | cons p a ih =>
      simp only [pathMap, LinearPathCategory.pathMap_cons, rayPathMap] at hp ⊢
      have hpTail :
          LinearPathCategory.pathMap RayVertex.obj
            (fun {i j} ↦ rayArrowMorphism) p ≠ 0 := by
        intro hzero
        apply hp
        rw [hzero]
        simp
      have ih' := ih hpTail
      have hcompRay := hp
      change a.1 ≫ rayPathMap p ≠ 0 at hcompRay
      rw [← L.unitRay_representative a, ← ih',
        BGRSRayCategory.comp_unitRay] at hcompRay
      have hprod :
          bgrsRayRepresentativeProduct
              (L.representative a) (L.pathMap p) ≠ 0 :=
        (unitRay_ne_zero_iff _).1 hcompRay
      have hns : ¬ IsBGRSSpecialZero
          (L.representative a) (L.pathMap p) := by
        intro hs
        exact hprod
          (bgrsRayRepresentativeProduct_eq_zero_of_special hs)
      change unitRay (L.representative a ≫ L.pathMap p) =
        a.1 ≫ rayPathMap p
      rw [← L.unitRay_representative a, ← ih',
        BGRSRayCategory.comp_unitRay]
      rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hns]

/-- Every nonzero ray path has nonzero ordinary composite for any chosen
arrow lifts. -/
theorem pathMap_ne_zero_of_rayPathMap_ne_zero
    (L : BGRSRayArrowLift (C := C))
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j)
    (hp : rayPathMap p ≠ 0) : L.pathMap p ≠ 0 := by
  rw [← unitRay_ne_zero_iff]
  rw [L.unitRay_pathMap_eq_rayPathMap_of_ne_zero p hp]
  exact hp

/-- Among nonzero ray paths, equality of ray values is exactly two-sided unit
equivalence of the ordinary composites of chosen arrow lifts. -/
theorem rayPathContourRelation_related_iff_unitRayEquivalent_pathMap
    (L : BGRSRayArrowLift (C := C))
    {i j : RayVertex (BGRSRayCategory C)} (p q : Quiver.Path i j) :
    (rayPathContourRelation (C := BGRSRayCategory C)).related p q ↔
      rayPathMap p ≠ 0 ∧ rayPathMap q ≠ 0 ∧
        UnitRayEquivalent (L.pathMap p) (L.pathMap q) := by
  constructor
  · intro hpq
    have hp : rayPathMap p ≠ 0 := hpq.1
    have hq : rayPathMap q ≠ 0 := by
      rw [← hpq.2]
      exact hp
    refine ⟨hp, hq, ?_⟩
    rw [← unitRay_eq_iff]
    exact
      (L.unitRay_pathMap_eq_rayPathMap_of_ne_zero p hp).trans
        (hpq.2.trans
          (L.unitRay_pathMap_eq_rayPathMap_of_ne_zero q hq).symm)
  · rintro ⟨hp, hq, hpq⟩
    refine ⟨hp, ?_⟩
    exact
      (L.unitRay_pathMap_eq_rayPathMap_of_ne_zero p hp).symm.trans
        (((unitRay_eq_iff _ _).2 hpq).trans
          (L.unitRay_pathMap_eq_rayPathMap_of_ne_zero q hq))

end BGRSRayArrowLift

end LargeIndecomposable
