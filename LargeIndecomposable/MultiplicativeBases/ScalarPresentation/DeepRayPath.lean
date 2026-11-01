module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.SingularPairDisjointness
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueEfficientLocal
public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRaySocle

@[expose] public section

/-!
# Deep ray paths and endpoint socles

Relate the source's ray-level notion of a deep path to the ordinary endpoint
bimodule socle after singular paths have been normalized.  This supplies the
scalar-proportionality half of the semi-normalized presentation on every deep
ray contour.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSPairDichotomy S.ProjectiveCategory]
variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- A ray path is deep when multiplication by every endpoint-radical ray
vanishes on the appropriate side. -/
def IsBGRSDeepRayPath
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    (p : Quiver.Path i j) : Prop :=
  (∀ a : End j.obj.as, a ∈ Ring.jacobson (End j.obj.as) →
    (show j.obj ⟶ j.obj from LargeIndecomposable.unitRay a.asHom) ≫
      LargeIndecomposable.rayPathMap p = 0) ∧
  (∀ b : End i.obj.as, b ∈ Ring.jacobson (End i.obj.as) →
    LargeIndecomposable.rayPathMap p ≫
      (show i.obj ⟶ i.obj from LargeIndecomposable.unitRay b.asHom) = 0)

theorem BGRSRayArrowLift.isEndpointSocleMorphism_pathMap_of_isBGRSDeepRayPath
    [LargeIndecomposable.IsFiniteRayCategory S.RayCategory]
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    (hzero : ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory}
      (p : Quiver.Path i j),
      L.pathMap p = 0 ↔ LargeIndecomposable.rayPathMap p = 0)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    (p : Quiver.Path i j) (hdeep : S.IsBGRSDeepRayPath p) :
    S.IsEndpointSocleMorphism (L.pathMap p) := by
  constructor
  · intro a ha
    by_cases ha0 : a = 0
    · subst a
      change (0 : j.obj.as ⟶ j.obj.as) ≫ L.pathMap p = 0
      exact CategoryTheory.Limits.zero_comp
    have haHom0 : a.asHom ≠ 0 := by
      change a ≠ 0
      exact ha0
    have haRay0 : LargeIndecomposable.unitRay a.asHom ≠ 0 :=
      (LargeIndecomposable.unitRay_ne_zero_iff a.asHom).2 haHom0
    obtain ⟨q, hq⟩ := LargeIndecomposable.exists_rayPathMap_eq_of_ne_zero
      (C := S.RayCategory) (i := j) (j := j)
      (LargeIndecomposable.unitRay a.asHom) haRay0
    have hq0 : LargeIndecomposable.rayPathMap q ≠ 0 := by
      intro hzero
      apply haRay0
      exact hq ▸ hzero
    have hcompRay :
        LargeIndecomposable.rayPathMap (p.comp q) = 0 := by
      simpa only [LargeIndecomposable.rayPathMap,
        LargeIndecomposable.LinearPathCategory.pathMap_comp, hq] using
          hdeep.1 a ha
    have hcomp : L.pathMap q ≫ L.pathMap p = 0 := by
      have h := (hzero (p.comp q)).2 hcompRay
      simpa only [LargeIndecomposable.BGRSRayArrowLift.pathMap,
        LargeIndecomposable.LinearPathCategory.pathMap_comp] using h
    have hunit : LargeIndecomposable.unitRay (L.pathMap q) =
        LargeIndecomposable.unitRay a.asHom := by
      calc
        LargeIndecomposable.unitRay (L.pathMap q) =
            LargeIndecomposable.rayPathMap q :=
          L.unitRay_pathMap_eq_rayPathMap_of_ne_zero q hq0
        _ = LargeIndecomposable.unitRay a.asHom := hq
    obtain ⟨leftUnit, rightUnit, haEq⟩ :=
      (LargeIndecomposable.unitRay_eq_iff (L.pathMap q) a.asHom).1 hunit
    have hcomm : L.pathMap q ≫ rightUnit.hom =
        rightUnit.hom ≫ L.pathMap q := by
      have h := congrArg End.asHom
        (ProjectiveCategory.end_mul_comm S j.obj.as
          (End.of (L.pathMap q)) (End.of rightUnit.hom))
      simpa only [End.mul_def] using h.symm
    calc
      a.asHom ≫ L.pathMap p =
          (leftUnit.hom ≫ L.pathMap q ≫ rightUnit.hom) ≫
            L.pathMap p := by rw [haEq]
      _ = leftUnit.hom ≫
          ((L.pathMap q ≫ rightUnit.hom) ≫ L.pathMap p) := by
        simp only [Category.assoc]
      _ = leftUnit.hom ≫
          ((rightUnit.hom ≫ L.pathMap q) ≫ L.pathMap p) := by rw [hcomm]
      _ = (leftUnit.hom ≫ rightUnit.hom) ≫
          (L.pathMap q ≫ L.pathMap p) := by simp only [Category.assoc]
      _ = 0 := by rw [hcomp]; simp
  · intro b hb
    by_cases hb0 : b = 0
    · subst b
      change L.pathMap p ≫ (0 : i.obj.as ⟶ i.obj.as) = 0
      exact CategoryTheory.Limits.comp_zero
    have hbHom0 : b.asHom ≠ 0 := by
      change b ≠ 0
      exact hb0
    have hbRay0 : LargeIndecomposable.unitRay b.asHom ≠ 0 :=
      (LargeIndecomposable.unitRay_ne_zero_iff b.asHom).2 hbHom0
    obtain ⟨q, hq⟩ := LargeIndecomposable.exists_rayPathMap_eq_of_ne_zero
      (C := S.RayCategory) (i := i) (j := i)
      (LargeIndecomposable.unitRay b.asHom) hbRay0
    have hq0 : LargeIndecomposable.rayPathMap q ≠ 0 := by
      intro hzero
      apply hbRay0
      exact hq ▸ hzero
    have hcompRay :
        LargeIndecomposable.rayPathMap (q.comp p) = 0 := by
      simpa only [LargeIndecomposable.rayPathMap,
        LargeIndecomposable.LinearPathCategory.pathMap_comp, hq] using
          hdeep.2 b hb
    have hcomp : L.pathMap p ≫ L.pathMap q = 0 := by
      have h := (hzero (q.comp p)).2 hcompRay
      simpa only [LargeIndecomposable.BGRSRayArrowLift.pathMap,
        LargeIndecomposable.LinearPathCategory.pathMap_comp] using h
    have hunit : LargeIndecomposable.unitRay (L.pathMap q) =
        LargeIndecomposable.unitRay b.asHom := by
      calc
        LargeIndecomposable.unitRay (L.pathMap q) =
            LargeIndecomposable.rayPathMap q :=
          L.unitRay_pathMap_eq_rayPathMap_of_ne_zero q hq0
        _ = LargeIndecomposable.unitRay b.asHom := hq
    obtain ⟨leftUnit, rightUnit, hbEq⟩ :=
      (LargeIndecomposable.unitRay_eq_iff (L.pathMap q) b.asHom).1 hunit
    have hcomm : leftUnit.hom ≫ L.pathMap q =
        L.pathMap q ≫ leftUnit.hom := by
      have h := congrArg End.asHom
        (ProjectiveCategory.end_mul_comm S i.obj.as
          (End.of leftUnit.hom) (End.of (L.pathMap q)))
      simpa only [End.mul_def] using h.symm
    calc
      L.pathMap p ≫ b.asHom =
          L.pathMap p ≫
            (leftUnit.hom ≫ L.pathMap q ≫ rightUnit.hom) := by rw [hbEq]
      _ = (L.pathMap p ≫
          (leftUnit.hom ≫ L.pathMap q)) ≫ rightUnit.hom := by
        simp only [Category.assoc]
      _ = (L.pathMap p ≫
          (L.pathMap q ≫ leftUnit.hom)) ≫ rightUnit.hom := by rw [hcomm]
      _ = (L.pathMap p ≫ L.pathMap q) ≫
          (leftUnit.hom ≫ rightUnit.hom) := by simp only [Category.assoc]
      _ = 0 := by rw [hcomp]; simp

omit [IsAlgClosed k] [Module.Finite k A]
  [LargeIndecomposable.HasBGRSDistributiveHomStructure
    k S.ProjectiveCategory] in
/-- Conversely, a nonzero ray path whose lifted ordinary composite lies in
the endpoint bimodule socle is ray-deep.  Ordinary endpoint annihilation
passes to the ray category because a zero ordinary product is a BGRS special
pair, whose ray product is zero. -/
theorem BGRSRayArrowLift.isBGRSDeepRayPath_of_isEndpointSocleMorphism_pathMap
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    (p : Quiver.Path i j) (hp : LargeIndecomposable.rayPathMap p ≠ 0)
    (hsocle : S.IsEndpointSocleMorphism (L.pathMap p)) :
    S.IsBGRSDeepRayPath p := by
  constructor
  · intro a ha
    have hspecial : LargeIndecomposable.IsBGRSSpecialZero
        a.asHom (L.pathMap p) := by
      refine ⟨⟨0, (Ring.jacobson (End j.obj.as)).zero_mem⟩, ?_⟩
      change a.asHom ≫ L.pathMap p =
        (a.asHom ≫ (0 : j.obj.as ⟶ j.obj.as)) ≫ L.pathMap p
      rw [hsocle.1 a ha]
      simp
    rw [← L.unitRay_pathMap_eq_rayPathMap_of_ne_zero p hp,
      LargeIndecomposable.BGRSRayCategory.comp_unitRay,
      LargeIndecomposable.bgrsRayRepresentativeProduct_eq_zero_of_special
        hspecial]
    rfl
  · intro b hb
    have hspecial : LargeIndecomposable.IsBGRSSpecialZero
        (L.pathMap p) b.asHom := by
      refine ⟨⟨0, (Ring.jacobson (End i.obj.as)).zero_mem⟩, ?_⟩
      change L.pathMap p ≫ b.asHom =
        (L.pathMap p ≫ (0 : i.obj.as ⟶ i.obj.as)) ≫ b.asHom
      rw [hsocle.2 b hb]
      simp
    rw [← L.unitRay_pathMap_eq_rayPathMap_of_ne_zero p hp,
      LargeIndecomposable.BGRSRayCategory.comp_unitRay,
      LargeIndecomposable.bgrsRayRepresentativeProduct_eq_zero_of_special
        hspecial]
    rfl

/-- Two related nonzero ray paths are represented by nonzero scalar multiples
as soon as the first path is ray-deep and the lift detects zero paths. -/
theorem BGRSRayArrowLift.rayPathContourRelation_related_implies_scalar_of_deep
    [LargeIndecomposable.IsFiniteRayCategory S.RayCategory]
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    (hzero : ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory}
      (p : Quiver.Path i j),
      L.pathMap p = 0 ↔ LargeIndecomposable.rayPathMap p = 0)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p q : Quiver.Path i j}
    (hpq : (LargeIndecomposable.rayPathContourRelation
      (C := S.RayCategory)).related p q)
    (hdeep : S.IsBGRSDeepRayPath p) :
    (LargeIndecomposable.LinearPathCategory.nonzeroScalarMultiplePathRelation
      (k := k) (fun x : LargeIndecomposable.RayVertex S.RayCategory ↦ x.obj.as)
      (fun {i j} (a : i ⟶ j) ↦ L.representative a)).related p q := by
  apply
    LargeIndecomposable.SplitBasicIdempotents.BGRSRayArrowLift.rayPathContourRelation_related_implies_scalar_of_endpointSocle
      S L hpq
  exact
    LargeIndecomposable.SplitBasicIdempotents.BGRSRayArrowLift.isEndpointSocleMorphism_pathMap_of_isBGRSDeepRayPath
      S L hzero p hdeep

end LargeIndecomposable.SplitBasicIdempotents
