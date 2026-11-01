module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRadicalSquareFactorization
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayArrowRadicalSquare
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayArrowRadical
public import LargeIndecomposable.RayCategories.Basic.RayQuiverArrowRigidity

@[expose] public section

/-!
# Irreducible ray arrows in the first radical layer

Concrete representatives of irreducible BGRS rays have nonzero classes in
`Jac(A) / Jac(A)^2`.  Distinct arrows incident to one vertex give linearly
independent classes.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [Module.Finite k A]
variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- A concrete representative of an irreducible BGRS ray has nonzero class
in its primitive corner modulo `Jac(A)^2`. -/
theorem rayArrowRepresentative_not_mem_jacobson_sq
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    a.1.out.1 ∉ Ring.jacobson A * Ring.jacobson A := by
  intro ha
  obtain ⟨z, g, h, hgJ, hhJ, hspan⟩ :=
    ProjectiveCategory.exists_radical_composite_span_of_mem_jacobson_sq
      S a.1.out ha
  exact rayArrowRepresentative_mem_radical_composite_span_false
    S a g h hgJ hhJ hspan

/-- Every representative selected by an arbitrary BGRS ray-arrow lift has a
nonzero class in the ambient first radical layer. -/
theorem rayArrowLift_representative_not_mem_jacobson_sq
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    (L.representative a).1 ∉
      Ring.jacobson A * Ring.jacobson A := by
  intro ha
  apply rayArrowRepresentative_not_mem_jacobson_sq S a
  apply ProjectiveCategory.val_mem_ideal_of_unitRayEquivalent S
    (Ring.jacobson A * Ring.jacobson A) ha
  apply (LargeIndecomposable.unitRay_eq_iff _ _).1
  rw [L.unitRay_representative]
  exact (unitRay_rayQuiverArrowRepresentative S a).symm

/-- Distinct outgoing ray arrows determine linearly independent classes in
the ambient first radical layer.  This is stated without introducing a
separate quotient-space API: a linear combination in `Jac(A)^2` has all
coefficients zero. -/
theorem outgoingRayRepresentatives_independent_mod_jacobson_sq
    {T : Type*} [Fintype T]
    {x : LargeIndecomposable.RayVertex S.RayCategory}
    (a : T → LargeIndecomposable.OutgoingQuiverArrow x)
    (ha : Function.Injective a)
    (c : T → k)
    (hsum : (∑ q : T, c q • (a q).2.1.out.1) ∈
      Ring.jacobson A * Ring.jacobson A) :
    ∀ q : T, c q = 0 := by
  classical
  intro q
  let e : A := S.idempotent (S.projectiveVertex (a q).1.obj.as)
  have hproj :
      ((∑ r : T, c r • (a r).2.1.out.1) * e) ∈
        Ring.jacobson A * Ring.jacobson A :=
    (Ring.jacobson A * Ring.jacobson A).mul_mem_right e hsum
  have hprojEq :
      ((∑ r : T, c r • (a r).2.1.out.1) * e) =
        c q • (a q).2.1.out.1 := by
    rw [Finset.sum_mul, Finset.sum_eq_single q]
    · change (c q • (a q).2.1.out.1) * e = c q • (a q).2.1.out.1
      rw [Algebra.smul_mul_assoc]
      exact congrArg (fun t : A ↦ c q • t)
        (ProjectiveCategory.val_mul_idempotent S (a q).2.1.out)
    · intro r _ hrq
      have hsource : (a r).1.obj.as ≠ (a q).1.obj.as := by
        intro hsource
        have htargetObj : (a r).1.obj = (a q).1.obj :=
          LargeIndecomposable.BGRSRayCategory.ext hsource
        have htarget : (a r).1 = (a q).1 :=
          LargeIndecomposable.RayVertex.ext htargetObj
        have harrow : a r = a q :=
          LargeIndecomposable.outgoingQuiverArrow_fst_injective x htarget
        exact hrq (ha harrow)
      change (c r • (a r).2.1.out.1) * e = 0
      rw [Algebra.smul_mul_assoc]
      rw [ProjectiveCategory.val_mul_idempotent_eq_zero_of_ne
        S hsource (a r).2.1.out, smul_zero]
    · intro hq
      exact (hq (Finset.mem_univ q)).elim
  have hscaled : c q • (a q).2.1.out.1 ∈
      Ring.jacobson A * Ring.jacobson A := by
    rw [← hprojEq]
    exact hproj
  by_contra hc
  have hunscale : (a q).2.1.out.1 ∈
      Ring.jacobson A * Ring.jacobson A := by
    have hm := (Ring.jacobson A * Ring.jacobson A).mul_mem_left
      (algebraMap k A (c q)⁻¹) hscaled
    change (algebraMap k A (c q)⁻¹) *
        (c q • (a q).2.1.out.1) ∈
      Ring.jacobson A * Ring.jacobson A at hm
    convert hm using 1
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul]
    simp [hc]
  exact (rayArrowRepresentative_not_mem_jacobson_sq S (a q).2) hunscale

/-- The incoming version: distinct incoming ray arrows determine linearly
independent classes in `Jac(A)/Jac(A)^2`. -/
theorem incomingRayRepresentatives_independent_mod_jacobson_sq
    {T : Type*} [Fintype T]
    {z : LargeIndecomposable.RayVertex S.RayCategory}
    (a : T → LargeIndecomposable.IncomingQuiverArrow z)
    (ha : Function.Injective a)
    (c : T → k)
    (hsum : (∑ q : T, c q • (a q).2.1.out.1) ∈
      Ring.jacobson A * Ring.jacobson A) :
    ∀ q : T, c q = 0 := by
  classical
  intro q
  let e : A := S.idempotent (S.projectiveVertex (a q).1.obj.as)
  have hproj :
      (e * (∑ r : T, c r • (a r).2.1.out.1)) ∈
        Ring.jacobson A * Ring.jacobson A :=
    (Ring.jacobson A * Ring.jacobson A).mul_mem_left e hsum
  have hprojEq :
      (e * (∑ r : T, c r • (a r).2.1.out.1)) =
        c q • (a q).2.1.out.1 := by
    rw [Finset.mul_sum, Finset.sum_eq_single q]
    · change e * (c q • (a q).2.1.out.1) = c q • (a q).2.1.out.1
      rw [Algebra.mul_smul_comm]
      exact congrArg (fun t : A ↦ c q • t)
        (ProjectiveCategory.idempotent_mul_val S (a q).2.1.out)
    · intro r _ hrq
      have htarget : (a q).1.obj.as ≠ (a r).1.obj.as := by
        intro htarget
        have hsourceObj : (a q).1.obj = (a r).1.obj :=
          LargeIndecomposable.BGRSRayCategory.ext htarget
        have hsource : (a q).1 = (a r).1 :=
          LargeIndecomposable.RayVertex.ext hsourceObj
        have harrow : a q = a r :=
          LargeIndecomposable.incomingQuiverArrow_fst_injective z hsource
        exact hrq (ha harrow).symm
      change e * (c r • (a r).2.1.out.1) = 0
      rw [Algebra.mul_smul_comm]
      rw [ProjectiveCategory.idempotent_mul_val_eq_zero_of_ne
        S htarget (a r).2.1.out, smul_zero]
    · intro hq
      exact (hq (Finset.mem_univ q)).elim
  have hscaled : c q • (a q).2.1.out.1 ∈
      Ring.jacobson A * Ring.jacobson A := by
    rw [← hprojEq]
    exact hproj
  by_contra hc
  have hunscale : (a q).2.1.out.1 ∈
      Ring.jacobson A * Ring.jacobson A := by
    have hm := (Ring.jacobson A * Ring.jacobson A).mul_mem_left
      (algebraMap k A (c q)⁻¹) hscaled
    change (algebraMap k A (c q)⁻¹) *
        (c q • (a q).2.1.out.1) ∈
      Ring.jacobson A * Ring.jacobson A at hm
    convert hm using 1
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul]
    simp [hc]
  exact (rayArrowRepresentative_not_mem_jacobson_sq S (a q).2) hunscale

end LargeIndecomposable.SplitBasicIdempotents
