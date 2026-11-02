module

public import LargeIndecomposable.RayCategories.Distributive.FiniteIdealHomChain
public import LargeIndecomposable.RayCategories.Distributive.KupischCyclicity
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteIdeals
public import LargeIndecomposable.RayCategories.Contours.RayPathInterlacement
public import Mathlib.Tactic
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayPathLift

@[expose] public section

/-!
# Radical representatives of BGRS ray arrows

The chosen representative of an irreducible unit ray is nonzero and belongs
to the ambient Jacobson radical of a finite-dimensional split-basic algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

/-- Membership in any ambient two-sided ideal is invariant under endpoint-unit
equivalence of primitive-projective morphisms. -/
theorem ProjectiveCategory.val_mem_ideal_of_unitRayEquivalent
    {i j : S.ProjectiveCategory} (I : Ideal A) [I.IsTwoSided]
    {f g : i ⟶ j}
    (hf : f.1 ∈ I)
    (hfg : LargeIndecomposable.UnitRayEquivalent f g) :
    g.1 ∈ I := by
  rcases hfg with ⟨a, b, rfl⟩
  have hmul : b.hom.1 * f.1 * a.hom.1 ∈ I :=
    I.mul_mem_right a.hom.1 (I.mul_mem_left b.hom.1 hf)
  simpa only [ProjectiveCategory.comp_val] using hmul

/-- Ambient Jacobson-radical membership is invariant under endpoint-unit
equivalence of primitive-projective morphisms. -/
theorem ProjectiveCategory.val_mem_jacobson_of_unitRayEquivalent
    {i j : S.ProjectiveCategory} {f g : i ⟶ j}
    (hf : f.1 ∈ Ring.jacobson A)
    (hfg : LargeIndecomposable.UnitRayEquivalent f g) :
    g.1 ∈ Ring.jacobson A :=
  ProjectiveCategory.val_mem_ideal_of_unitRayEquivalent S
    (Ring.jacobson A) hf hfg

variable [Module.Finite k A]
variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- A concrete primitive-corner representative of a reversed irreducible
arrow in the ray quiver. -/
def rayQuiverArrowRepresentative
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    y.obj.as ⟶ x.obj.as :=
  a.1.out

@[simp]
theorem unitRay_rayQuiverArrowRepresentative
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    LargeIndecomposable.unitRay (rayQuiverArrowRepresentative S a) = a.1 :=
  LargeIndecomposable.unitRay_out a.1

theorem rayQuiverArrowRepresentative_ne_zero
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    rayQuiverArrowRepresentative S a ≠ 0 := by
  intro h
  apply a.property.1
  rw [← unitRay_rayQuiverArrowRepresentative S a]
  exact (LargeIndecomposable.unitRay_eq_zero_iff _).2 h

/-- Every irreducible ray representative belongs to the ambient Jacobson
radical of the split-basic algebra. -/
theorem rayQuiverArrowRepresentative_mem_jacobson
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    (rayQuiverArrowRepresentative S a).1 ∈ Ring.jacobson A := by
  by_cases hxy : y.obj.as = x.obj.as
  · have hobj : y.obj = x.obj :=
      LargeIndecomposable.BGRSRayCategory.ext hxy
    have hvertex : y = x := LargeIndecomposable.RayVertex.ext hobj
    subst x
    rw [← S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    rw [LargeIndecomposable.mem_ringJacobson_iff_not_isUnit]
    intro hu
    haveI : IsIso (rayQuiverArrowRepresentative S a) :=
      (isUnit_iff_isIso _).1 hu
    apply a.property.2.1
    have hray : a.1 = 𝟙 y.obj := by
      rw [← unitRay_rayQuiverArrowRepresentative S a]
      exact LargeIndecomposable.unitRay_eq_identity_of_isIso
        (rayQuiverArrowRepresentative S a)
    rw [hray]
    infer_instance
  · exact ProjectiveCategory.offDiagonal_val_mem_jacobson S hxy _

/-- Every representative selected by an arbitrary BGRS ray-arrow lift lies
in the ambient Jacobson radical. -/
theorem rayArrowLift_representative_mem_jacobson
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    {i j : LargeIndecomposable.RayVertex S.RayCategory} (a : i ⟶ j) :
    (L.representative a).1 ∈ Ring.jacobson A := by
  apply ProjectiveCategory.val_mem_jacobson_of_unitRayEquivalent S
    (rayQuiverArrowRepresentative_mem_jacobson S a)
  apply (LargeIndecomposable.unitRay_eq_iff _ _).1
  rw [L.unitRay_representative,
    unitRay_rayQuiverArrowRepresentative]

/-- The ordinary composite selected by a ray-arrow lift along every nonempty
ray-quiver path lies in the ambient Jacobson radical. -/
theorem rayArrowLift_pathMap_mem_jacobson
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    (p : Quiver.Path i j) (hp : 1 ≤ p.length) :
    (L.pathMap p).1 ∈ Ring.jacobson A := by
  cases p with
  | nil => simp at hp
  | cons p a =>
      simp only [LargeIndecomposable.BGRSRayArrowLift.pathMap,
        LinearPathCategory.pathMap_cons, ProjectiveCategory.comp_val]
      exact (Ring.jacobson A).mul_mem_left _
        (rayArrowLift_representative_mem_jacobson S L a)

/-- The ordinary composite selected along a ray-quiver path of length `n`
belongs to the `n`th power of the ambient Jacobson radical. -/
theorem rayArrowLift_pathMap_mem_jacobson_pow
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    (p : Quiver.Path i j) :
    (L.pathMap p).1 ∈ (Ring.jacobson A) ^ p.length := by
  induction p with
  | nil =>
      simp only [LargeIndecomposable.BGRSRayArrowLift.pathMap,
        LinearPathCategory.pathMap_nil, ProjectiveCategory.id_val,
        Quiver.Path.length_nil, Submodule.pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | cons p a ih =>
      simp only [LargeIndecomposable.BGRSRayArrowLift.pathMap,
        LinearPathCategory.pathMap_cons, ProjectiveCategory.comp_val,
        Quiver.Path.length_cons]
      rw [Ideal.IsTwoSided.pow_add]
      have ha : (L.representative a).1 ∈ (Ring.jacobson A) ^ 1 := by
        simpa only [Submodule.pow_one] using
          rayArrowLift_representative_mem_jacobson S L a
      exact Ideal.mul_mem_mul ih ha

end LargeIndecomposable.SplitBasicIdempotents
