module

public import LargeIndecomposable.RepresentationType.Obstructions.RepresentationFiniteRayValency
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Primitive-corner factorization of the square of the Jacobson radical

Every primitive-corner element of `Jac(A)^2` lies in the two-sided Hom span of
one composite of two radical corner morphisms.  Comparability of BGRS Hom
subbimodules collapses a finite sum of such composites to one principal span.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open Mathlib.Tactic.Module

namespace LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

def cornerProjection (i j : S.ProjectiveCategory) (a : A) : i ⟶ j :=
  ⟨S.idempotent (S.projectiveVertex j) * a *
      S.idempotent (S.projectiveVertex i), ⟨a, rfl⟩⟩

omit [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory] in
@[simp]
private theorem cornerProjection_val (i j : S.ProjectiveCategory) (a : A) :
    (cornerProjection S i j a).1 =
      S.idempotent (S.projectiveVertex j) * a *
        S.idempotent (S.projectiveVertex i) :=
  rfl

omit [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory] in
@[simp]
private theorem cornerProjection_zero (i j : S.ProjectiveCategory) :
    cornerProjection S i j 0 = 0 := by
  apply Subtype.ext
  simp [cornerProjection]

omit [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory] in
@[simp]
private theorem cornerProjection_add (i j : S.ProjectiveCategory) (a b : A) :
    cornerProjection S i j (a + b) =
      cornerProjection S i j a + cornerProjection S i j b := by
  apply Subtype.ext
  simp [cornerProjection, mul_add, add_mul]
  rfl

omit [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory] in
@[simp]
private theorem cornerProjection_hom (i j : S.ProjectiveCategory)
    (f : i ⟶ j) : cornerProjection S i j f.1 = f := by
  apply Subtype.ext
  simp only [cornerProjection_val]
  rw [idempotent_mul_val S f, val_mul_idempotent S f]

omit [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory] in
private theorem cornerProjection_mem_jacobson
    (i j : S.ProjectiveCategory) {a : A} (ha : a ∈ Ring.jacobson A) :
    (cornerProjection S i j a).1 ∈ Ring.jacobson A := by
  change S.idempotent (S.projectiveVertex j) * a *
      S.idempotent (S.projectiveVertex i) ∈ Ring.jacobson A
  exact (Ring.jacobson A).mul_mem_right _
    ((Ring.jacobson A).mul_mem_left _ ha)

private theorem exists_dominating_principal_span_sum_finset
    {i j : S.ProjectiveCategory} {T : Type*}
    (p : T → (i ⟶ j)) (s : Finset T) (hs : s.Nonempty) :
    ∃ q ∈ s,
      (∑ z ∈ s, p z) ∈
        LargeIndecomposable.twoSidedEndomorphismSpan k (p q) ∧
      ∀ r ∈ s,
        LargeIndecomposable.twoSidedEndomorphismSpan k (p r) ≤
          LargeIndecomposable.twoSidedEndomorphismSpan k (p q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · obtain ⟨q, hqs, hsum, hdom⟩ := ih hs'
        rcases
            LargeIndecomposable.HasBGRSDistributiveHomStructure.homSubbimodule_comparable
              (k := k) (C := S.ProjectiveCategory)
              (LargeIndecomposable.twoSidedEndomorphismSpan k (p a))
              (LargeIndecomposable.twoSidedEndomorphismSpan k (p q))
              (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan (p a))
              (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan (p q)) with haq | hqa
        · refine ⟨q, Finset.mem_insert_of_mem hqs, ?_, ?_⟩
          · rw [Finset.sum_insert ha]
            exact (LargeIndecomposable.twoSidedEndomorphismSpan k (p q)).add_mem
              (haq (LargeIndecomposable.mem_twoSidedEndomorphismSpan k (p a))) hsum
          · intro r hr
            rw [Finset.mem_insert] at hr
            rcases hr with rfl | hrs
            · exact haq
            · exact hdom r hrs
        · refine ⟨a, Finset.mem_insert_self a s, ?_, ?_⟩
          · rw [Finset.sum_insert ha]
            exact (LargeIndecomposable.twoSidedEndomorphismSpan k (p a)).add_mem
              (LargeIndecomposable.mem_twoSidedEndomorphismSpan k (p a))
              (hqa hsum)
          · intro r hr
            rw [Finset.mem_insert] at hr
            rcases hr with rfl | hrs
            · exact le_rfl
            · exact (hdom r hrs).trans hqa
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        refine ⟨a, by simp, ?_, ?_⟩
        · simpa using LargeIndecomposable.mem_twoSidedEndomorphismSpan k (p a)
        · intro r hr
          have hra : r = a := by simpa using hr
          subst r
          exact le_rfl

private theorem exists_dominating_principal_span_sum
    {i j : S.ProjectiveCategory} {T : Type*} [Fintype T] [Nonempty T]
    (p : T → (i ⟶ j)) :
    ∃ q : T,
      (∑ z, p z) ∈ LargeIndecomposable.twoSidedEndomorphismSpan k (p q) := by
  classical
  obtain ⟨q, -, hsum, -⟩ :=
    exists_dominating_principal_span_sum_finset S p Finset.univ
      Finset.univ_nonempty
  exact ⟨q, by simpa using hsum⟩

omit [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory] in
private theorem cornerProjection_mul_eq_sum_composites
    (i j : S.ProjectiveCategory) (a b : A) :
    cornerProjection S i j (a * b) =
      ∑ z : S.ProjectiveIndex,
        cornerProjection S i z b ≫ cornerProjection S z j a := by
  apply Subtype.ext
  let valMap : (i ⟶ j) →ₗ[k] A :=
    (LargeIndecomposable.idempotentCorner (k := k) S.idempotent
      (S.projectiveVertex j) (S.projectiveVertex i)).subtype
  change valMap (cornerProjection S i j (a * b)) =
    valMap (∑ z : S.ProjectiveIndex,
      cornerProjection S i z b ≫ cornerProjection S z j a)
  rw [map_sum]
  change S.idempotent (S.projectiveVertex j) * (a * b) *
      S.idempotent (S.projectiveVertex i) =
    ∑ z : S.ProjectiveIndex,
      (cornerProjection S i z b ≫ cornerProjection S z j a).1
  simp only [comp_val, cornerProjection_val]
  have hterm (z : S.ProjectiveIndex) :
      (S.idempotent (S.projectiveVertex j) * a *
          S.idempotent (S.projectiveVertex z)) *
        (S.idempotent (S.projectiveVertex z) * b *
          S.idempotent (S.projectiveVertex i)) =
      S.idempotent (S.projectiveVertex j) *
        (a * (S.idempotent (S.projectiveVertex z) *
          (b * S.idempotent (S.projectiveVertex i)))) := by
    simp only [mul_assoc]
    rw [← mul_assoc (S.idempotent (S.projectiveVertex z))
      (S.idempotent (S.projectiveVertex z))
      (b * S.idempotent (S.projectiveVertex i)),
      S.complete.toOrthogonalIdempotents.idem
        (S.projectiveVertex z) |>.eq]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [S.sum_idempotent_projectiveVertex]
  simp only [one_mul, mul_assoc]

/-- Every primitive corner element of `Jac(A)^2` lies in the principal
two-sided Hom span of one composite of Jacobson-radical corner morphisms. -/
theorem exists_radical_composite_span_of_mem_jacobson_sq
    {i j : S.ProjectiveCategory} (f : i ⟶ j)
    (hf : f.1 ∈ Ring.jacobson A * Ring.jacobson A) :
    ∃ (z : S.ProjectiveCategory) (g : i ⟶ z) (h : z ⟶ j),
      g.1 ∈ Ring.jacobson A ∧ h.1 ∈ Ring.jacobson A ∧
      f ∈ LargeIndecomposable.twoSidedEndomorphismSpan k (g ≫ h) := by
  let Good : A → Prop := fun a ↦
    ∃ (z : S.ProjectiveCategory) (g : i ⟶ z) (h : z ⟶ j),
      g.1 ∈ Ring.jacobson A ∧ h.1 ∈ Ring.jacobson A ∧
      cornerProjection S i j a ∈
        LargeIndecomposable.twoSidedEndomorphismSpan k (g ≫ h)
  have hGood : Good f.1 := by
    refine Submodule.mul_induction_on (C := Good) hf ?_ ?_
    · intro a ha b hb
      let p : S.ProjectiveIndex → (i ⟶ j) := fun z ↦
        cornerProjection S i z b ≫ cornerProjection S z j a
      letI : Nonempty S.ProjectiveIndex := ⟨i⟩
      obtain ⟨z, hz⟩ := exists_dominating_principal_span_sum S p
      refine ⟨z, cornerProjection S i z b, cornerProjection S z j a,
        cornerProjection_mem_jacobson S i z hb,
        cornerProjection_mem_jacobson S z j ha, ?_⟩
      rw [cornerProjection_mul_eq_sum_composites S i j a b]
      exact hz
    · intro a b ha hb
      rcases ha with ⟨z, g, h, hgJ, hhJ, ha⟩
      rcases hb with ⟨w, p, q, hpJ, hqJ, hb⟩
      rcases
          LargeIndecomposable.HasBGRSDistributiveHomStructure.homSubbimodule_comparable
            (k := k) (C := S.ProjectiveCategory)
            (LargeIndecomposable.twoSidedEndomorphismSpan k (g ≫ h))
            (LargeIndecomposable.twoSidedEndomorphismSpan k (p ≫ q))
            (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan (g ≫ h))
            (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan (p ≫ q)) with hghpq | hpqgh
      · refine ⟨w, p, q, hpJ, hqJ, ?_⟩
        rw [cornerProjection_add]
        exact (LargeIndecomposable.twoSidedEndomorphismSpan k (p ≫ q)).add_mem
          (hghpq ha) hb
      · refine ⟨z, g, h, hgJ, hhJ, ?_⟩
        rw [cornerProjection_add]
        exact (LargeIndecomposable.twoSidedEndomorphismSpan k (g ≫ h)).add_mem
          ha (hpqgh hb)
  rcases hGood with ⟨z, g, h, hgJ, hhJ, hspan⟩
  refine ⟨z, g, h, hgJ, hhJ, ?_⟩
  simpa only [cornerProjection_hom] using hspan

end LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory
