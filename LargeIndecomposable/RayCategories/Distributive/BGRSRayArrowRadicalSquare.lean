module

public import LargeIndecomposable.RepresentationType.Obstructions.RepresentationFiniteRayValency

@[expose] public section

/-!
# Irreducible BGRS rays do not come from radical composites

An irreducible unit ray cannot lie in the principal two-sided span of a
nonzero composite of two ambient-radical corner morphisms.  The proof uses the
special BGRS product and nilpotence of local Jacobson radicals.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
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

variable [Module.Finite k A]
variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

def arrowRepresentative
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    y.obj.as ⟶ x.obj.as :=
  a.1.out

@[simp]
private theorem unitRay_arrowRepresentative
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    LargeIndecomposable.unitRay (arrowRepresentative S a) = a.1 :=
  LargeIndecomposable.unitRay_out a.1

private theorem arrowRepresentative_ne_zero
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y) :
    arrowRepresentative S a ≠ 0 := by
  intro h
  apply a.property.1
  rw [← unitRay_arrowRepresentative S a]
  exact (LargeIndecomposable.unitRay_eq_zero_iff _).2 h

private theorem not_isIso_unitRay_of_val_mem_jacobson
    {i j : S.ProjectiveCategory} (f : i ⟶ j)
    (hf : f.1 ∈ Ring.jacobson A) :
    ¬ IsIso
      (show RayCategory.obj S i ⟶ RayCategory.obj S j from
        LargeIndecomposable.unitRay f) := by
  intro hray
  letI : IsIso
      (show RayCategory.obj S i ⟶ RayCategory.obj S j from
        LargeIndecomposable.unitRay f) := hray
  haveI hfIso : IsIso f :=
    LargeIndecomposable.BGRSRayCategory.representative_isIso_of_isIso
      (ProjectiveCategory.id_ne_zero S) f
  have hij : i = j := ProjectiveCategory.skeletal S ⟨asIso f⟩
  subst j
  let fEnd : End i := End.of f
  letI : IsIso fEnd.asHom := hfIso
  have hunit : IsUnit fEnd := (isUnit_iff_isIso fEnd).2 inferInstance
  have hrad : fEnd ∈ Ring.jacobson (End i) :=
    (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson i fEnd).2 hf
  exact ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit (End i) fEnd).1 hrad)
    hunit

omit [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory] in
private theorem exists_nonSpecial_radical_twist
    {i z j : S.ProjectiveCategory} (g : i ⟶ z) (h : z ⟶ j)
    (hgh : g ≫ h ≠ 0) :
    ∃ q : End z,
      g ≫ h = (g ≫ q.asHom) ≫ h ∧
      ¬ LargeIndecomposable.IsBGRSSpecialZero g (q.asHom ≫ h) := by
  by_contra hex
  push Not at hex
  have hpow : ∀ n : ℕ, ∃ q : End z,
      q ∈ (Ring.jacobson (End z)) ^ n ∧
      g ≫ h = (g ≫ q.asHom) ≫ h := by
    intro n
    induction n with
    | zero =>
        refine ⟨1, ?_, by simp⟩
        rw [Submodule.pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    | succ n ih =>
        rcases ih with ⟨q, hq, heq⟩
        have hspecial : LargeIndecomposable.IsBGRSSpecialZero
            g (q.asHom ≫ h) := by
          apply hex q heq
        obtain ⟨rho, hrhoeq⟩ := hspecial
        refine ⟨q * rho.1, ?_, ?_⟩
        · simpa only [Submodule.pow_succ] using
            (Ideal.mul_mem_mul hq rho.2)
        · calc
            g ≫ h = (g ≫ q.asHom) ≫ h := heq
            _ = g ≫ (q.asHom ≫ h) := by simp only [Category.assoc]
            _ = (g ≫ rho.1.asHom) ≫ (q.asHom ≫ h) := hrhoeq
            _ = (g ≫ (q * rho.1).asHom) ≫ h := by
              rw [End.mul_def]
              simp only [Category.assoc]
  letI : IsArtinianRing (End z) := inferInstance
  obtain ⟨n, hn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End z)
  rw [Ideal.jacobson_bot] at hn
  obtain ⟨q, hq, heq⟩ := hpow n
  have hq0 : q = 0 := by
    rw [hn] at hq
    exact (Submodule.mem_bot (R := End z)).1 hq
  apply hgh
  rw [heq, hq0]
  change (g ≫ (0 : z ⟶ z)) ≫ h = 0
  rw [Limits.comp_zero, Limits.zero_comp]

private theorem unitRay_composite_not_irreducible_of_radical_factors
    {i z j : S.ProjectiveCategory} (g : i ⟶ z) (h : z ⟶ j)
    (hgJ : g.1 ∈ Ring.jacobson A)
    (hhJ : h.1 ∈ Ring.jacobson A)
    (hgh : g ≫ h ≠ 0) :
    ¬ LargeIndecomposable.IsIrreducibleRayMorphism
      (show RayCategory.obj S i ⟶ RayCategory.obj S j from
        LargeIndecomposable.unitRay (g ≫ h)) := by
  obtain ⟨q, heq, hspecial⟩ := exists_nonSpecial_radical_twist S g h hgh
  let hq : z ⟶ j := q.asHom ≫ h
  have hhqJ : hq.1 ∈ Ring.jacobson A := by
    change h.1 * q.1 ∈ Ring.jacobson A
    exact (Ring.jacobson A).mul_mem_right q.1 hhJ
  have hfactor :
      (show RayCategory.obj S i ⟶ RayCategory.obj S z from
          LargeIndecomposable.unitRay g) ≫
        (show RayCategory.obj S z ⟶ RayCategory.obj S j from
          LargeIndecomposable.unitRay hq) =
      (show RayCategory.obj S i ⟶ RayCategory.obj S j from
          LargeIndecomposable.unitRay (g ≫ h)) := by
    change LargeIndecomposable.unitRay
        (LargeIndecomposable.bgrsRayRepresentativeProduct g hq) =
      LargeIndecomposable.unitRay (g ≫ h)
    rw [LargeIndecomposable.bgrsRayRepresentativeProduct_eq_comp_of_not_special
      hspecial]
    rw [← Category.assoc, ← heq]
  intro hirr
  rcases hirr.2.2 (RayCategory.obj S z)
      (LargeIndecomposable.unitRay g)
      (LargeIndecomposable.unitRay hq) hfactor with hgIso | hhIso
  · exact (not_isIso_unitRay_of_val_mem_jacobson S g hgJ) hgIso
  · exact (not_isIso_unitRay_of_val_mem_jacobson S hq hhqJ) hhIso

omit [Module.Finite k A]
  [LargeIndecomposable.HasBGRSDistributiveHomStructure
    k S.ProjectiveCategory] in
private theorem exists_comp_right_of_mem_span_of_allowsTransit
    {i j : S.ProjectiveCategory} {f g : i ⟶ j}
    (ht : LargeIndecomposable.AllowsTransit g)
    (hf : f ∈ LargeIndecomposable.twoSidedEndomorphismSpan k g) :
    ∃ b : End j, f = g ≫ b.asHom := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht a
      refine ⟨b * c, ?_⟩
      change (a.asHom ≫ g) ≫ b.asHom = g ≫ (b * c).asHom
      rw [hc, End.mul_def, Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : i ⟶ j) = g ≫ (0 : j ⟶ j)
      simp
  | add f g _ _ hf hg =>
      rcases hf with ⟨a, rfl⟩
      rcases hg with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (g ≫ a.asHom) + (g ≫ b.asHom) =
        g ≫ (a.asHom + b.asHom)
      rw [Preadditive.comp_add]
  | smul c f _ hf =>
      rcases hf with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (g ≫ a.asHom) = g ≫ (c • a.asHom)
      rw [Linear.comp_smul]

omit [Module.Finite k A]
  [LargeIndecomposable.HasBGRSDistributiveHomStructure
    k S.ProjectiveCategory] in
private theorem exists_comp_left_of_mem_span_of_allowsCotransit
    {i j : S.ProjectiveCategory} {f g : i ⟶ j}
    (ht : LargeIndecomposable.AllowsCotransit g)
    (hf : f ∈ LargeIndecomposable.twoSidedEndomorphismSpan k g) :
    ∃ a : End i, f = a.asHom ≫ g := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht b
      refine ⟨c * a, ?_⟩
      rw [End.mul_def]
      simp only [Category.assoc, hc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : i ⟶ j) = (0 : i ⟶ i) ≫ g
      simp
  | add f g _ _ hf hg =>
      rcases hf with ⟨a, rfl⟩
      rcases hg with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (a.asHom ≫ g) + (b.asHom ≫ g) =
        (a.asHom + b.asHom) ≫ g
      rw [Preadditive.add_comp]
  | smul c f _ hf =>
      rcases hf with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (a.asHom ≫ g) = (c • a.asHom) ≫ g
      rw [Linear.smul_comp]

private theorem arrowRepresentative_mem_composite_span_false
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y)
    {z : S.ProjectiveCategory}
    (g : y.obj.as ⟶ z) (h : z ⟶ x.obj.as)
    (hgJ : g.1 ∈ Ring.jacobson A) (hhJ : h.1 ∈ Ring.jacobson A)
    (hspan : arrowRepresentative S a ∈
      LargeIndecomposable.twoSidedEndomorphismSpan k (g ≫ h)) : False := by
  rcases LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) (g ≫ h) with ht | hc
  · obtain ⟨b, hb⟩ :=
      exists_comp_right_of_mem_span_of_allowsTransit S ht hspan
    let h' : z ⟶ x.obj.as := h ≫ b.asHom
    have hh'J : h'.1 ∈ Ring.jacobson A := by
      change b.1 * h.1 ∈ Ring.jacobson A
      exact (Ring.jacobson A).mul_mem_left b.1 hhJ
    have hgh' : g ≫ h' ≠ 0 := by
      rw [← Category.assoc, ← hb]
      exact arrowRepresentative_ne_zero S a
    apply unitRay_composite_not_irreducible_of_radical_factors
      S g h' hgJ hh'J hgh'
    rw [← Category.assoc, ← hb, unitRay_arrowRepresentative S a]
    exact a.property
  · obtain ⟨b, hb⟩ :=
      exists_comp_left_of_mem_span_of_allowsCotransit S hc hspan
    let g' : y.obj.as ⟶ z := b.asHom ≫ g
    have hg'J : g'.1 ∈ Ring.jacobson A := by
      change g.1 * b.1 ∈ Ring.jacobson A
      exact (Ring.jacobson A).mul_mem_right b.1 hgJ
    have hg'h : g' ≫ h ≠ 0 := by
      rw [Category.assoc, ← hb]
      exact arrowRepresentative_ne_zero S a
    apply unitRay_composite_not_irreducible_of_radical_factors
      S g' h hg'J hhJ hg'h
    rw [Category.assoc, ← hb, unitRay_arrowRepresentative S a]
    exact a.property

/-- An irreducible ray representative cannot lie in the principal
two-sided span of a composite of two ambient-radical corner morphisms. -/
theorem rayArrowRepresentative_mem_radical_composite_span_false
    {x y : LargeIndecomposable.RayVertex S.RayCategory} (a : x ⟶ y)
    {z : S.ProjectiveCategory}
    (g : y.obj.as ⟶ z) (h : z ⟶ x.obj.as)
    (hgJ : g.1 ∈ Ring.jacobson A) (hhJ : h.1 ∈ Ring.jacobson A)
    (hspan : a.1.out ∈
      LargeIndecomposable.twoSidedEndomorphismSpan k (g ≫ h)) : False :=
  arrowRepresentative_mem_composite_span_false S a g h hgJ hhJ hspan

end LargeIndecomposable.SplitBasicIdempotents
