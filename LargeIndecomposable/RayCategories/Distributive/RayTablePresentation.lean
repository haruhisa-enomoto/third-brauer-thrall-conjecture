module

public import LargeIndecomposable.RayCategories.Distributive.ProjectiveCategoryRays
public import LargeIndecomposable.RayCategories.Distributive.InsertionSpan
public import LargeIndecomposable.RayCategories.Distributive.LinearizationTable
public import LargeIndecomposable.RayCategories.Distributive.FromDistributive
public import LargeIndecomposable.RayCategories.Basic.Small
public import LargeIndecomposable.RayCategories.RayTables.RayPres

/-!
# The ray table of the small ray category presents the algebra

For split basic data `S` of a distributive algebra, the ray table
`linTable k P` of `P = RaySmall S.toIdempotents.RayCategory` is a ray presentation of
`B` in the sense of the multiplicative-bases library: representatives of the
rays are the chosen representatives of the unit orbits
(`SplitBasicData.isRayPres_linTable`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayQuiver RayCat RayCat.RaySmall
  LargeIndecomposable

universe u

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]
  [LocallySmall.{0} S.toIdempotents.RayCategory]

/-- A representative of a morphism of the small ray category. -/
def repP {X Y : RaySmall.{0} S.toIdempotents.RayCategory} (f : X ⟶ Y) : X.as.as ⟶ Y.as.as :=
  Quotient.out ((sh.{0}).symm f)

lemma unitRay_repP {X Y : RaySmall.{0} S.toIdempotents.RayCategory} (f : X ⟶ Y) :
    (unitRay (S.repP f) : X.as ⟶ Y.as) = (sh.{0}).symm f :=
  unitRay_out _

lemma repP_eq_zero_iff {X Y : RaySmall.{0} S.toIdempotents.RayCategory} (f : X ⟶ Y) :
    S.repP f = 0 ↔ f = 0 := by
  rw [← unitRay_eq_zero_iff, S.unitRay_repP]
  constructor
  · intro h
    rw [← (sh.{0}).apply_symm_apply f, h]
    rfl
  · intro h
    rw [h]
    exact (sh.{0}).symm_apply_apply _

/-- Composition in the small ray category through representatives. -/
lemma sh_symm_comp_repP {X Y Z : RaySmall.{0} S.toIdempotents.RayCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sh.{0}).symm (f ≫ g) = unitRay (bgrsRayRepresentativeProduct (S.repP f) (S.repP g)) := by
  rw [sh_symm_comp, ← S.unitRay_repP f, ← S.unitRay_repP g]
  rfl

/-- The label of an object of the small ray category. -/
def labelP (X : RaySmall.{0} S.toIdempotents.RayCategory) : Fin S.primitiveIdempotents.m := S.pidx X.as.as

lemma labelP_bijective : Function.Bijective S.labelP := by
  refine ⟨fun X Y h ↦ ?_, fun i ↦ ?_⟩
  · have := S.pidx_injective h
    rcases X with ⟨⟨X⟩⟩
    rcases Y with ⟨⟨Y⟩⟩
    cases this
    rfl
  · obtain ⟨X, hX⟩ := S.pidx_surjective i
    exact ⟨⟨⟨X⟩⟩, hX⟩

/-- The labels as an equivalence. -/
def labelEquiv : RaySmall.{0} S.toIdempotents.RayCategory ≃ Fin S.primitiveIdempotents.m :=
  Equiv.ofBijective _ S.labelP_bijective

/-- The representative in `B` of a nonzero morphism of the small ray category. -/
def betaP [IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory)]
    (r : NZ (RaySmall.{0} S.toIdempotents.RayCategory)) : B :=
  (S.repP r.2.2.1).1

lemma eq_of_mem_corner {x y x' y' : Fin S.primitiveIdempotents.m} {a : B} (ha : a ∈ S.primitiveIdempotents.corner (k := k) x y)
    (ha' : a ∈ S.primitiveIdempotents.corner (k := k) x' y') (h0 : a ≠ 0) : x = x' ∧ y = y' := by
  have e1 := S.primitiveIdempotents.e_mul_of_mem ha
  have e2 := S.primitiveIdempotents.e_mul_of_mem ha'
  have e3 := S.primitiveIdempotents.mul_e_of_mem ha
  have e4 := S.primitiveIdempotents.mul_e_of_mem ha'
  constructor
  · by_contra hxx
    apply h0
    rw [← e1, ← e2, ← mul_assoc, S.primitiveIdempotents.complete.ortho hxx, zero_mul]
  · by_contra hyy
    apply h0
    rw [← e3, ← e4, mul_assoc, S.primitiveIdempotents.complete.ortho (Ne.symm hyy), mul_zero]

section Pres

variable [IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory)]
  [Fintype (RaySmall.{0} S.toIdempotents.RayCategory)] [DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory)]

lemma betaP_mem_corner (r : NZ (RaySmall.{0} S.toIdempotents.RayCategory)) :
    S.betaP r ∈ S.primitiveIdempotents.corner (k := k) (S.labelP r.2.1) (S.labelP r.1) :=
  S.val_mem_corner _

lemma betaP_ne_zero (r : NZ (RaySmall.{0} S.toIdempotents.RayCategory)) : S.betaP r ≠ 0 := by
  intro h
  apply r.2.2.2
  rw [← S.repP_eq_zero_iff]
  exact Subtype.ext h

lemma betaP_inj (r s : NZ (RaySmall.{0} S.toIdempotents.RayCategory))
    (h : S.betaP r ∈ S.primitiveIdempotents.ray (k := k) (S.labelP s.2.1) (S.labelP s.1) (S.betaP s)) : r = s := by
  obtain ⟨Xr, Yr, fr, hr⟩ := r
  obtain ⟨Xs, Ys, fs, hs⟩ := s
  have hc := S.primitiveIdempotents.ray_subset_corner (S.betaP_mem_corner ⟨Xs, Ys, fs, hs⟩) h
  obtain ⟨h1, h2⟩ := S.eq_of_mem_corner (S.betaP_mem_corner ⟨Xr, Yr, fr, hr⟩) hc
    (S.betaP_ne_zero ⟨Xr, Yr, fr, hr⟩)
  have hY := S.labelP_bijective.1 h1
  have hX := S.labelP_bijective.1 h2
  subst hY hX
  have hu : UnitRayEquivalent (S.repP fs) (S.repP fr) := (S.unitRayEquivalent_iff _ _).2 h
  have : fr = fs := by
    rw [← (sh.{0}).apply_symm_apply fr, ← (sh.{0}).apply_symm_apply fs, ← S.unitRay_repP fr,
      ← S.unitRay_repP fs, (unitRay_eq_iff _ _).2 hu]
  subst this
  rfl

lemma betaP_surj (x y : Fin S.primitiveIdempotents.m) (f : B) (hf : f ∈ S.primitiveIdempotents.corner (k := k) x y) (hf0 : f ≠ 0) :
    ∃ r : NZ (RaySmall.{0} S.toIdempotents.RayCategory), S.labelP r.2.1 = x ∧ S.labelP r.1 = y ∧
      f ∈ S.primitiveIdempotents.ray (k := k) x y (S.betaP r) := by
  obtain ⟨Y, rfl⟩ := S.pidx_surjective x
  obtain ⟨X, rfl⟩ := S.pidx_surjective y
  let φ : X ⟶ Y := S.ofCorner f hf
  let g : (⟨⟨X⟩⟩ : RaySmall.{0} S.toIdempotents.RayCategory) ⟶ ⟨⟨Y⟩⟩ := sh.{0} (unitRay φ)
  have hg : g ≠ 0 := by
    intro h
    apply hf0
    have h1 := (sh_eq_zero_iff (X := (⟨⟨X⟩⟩ : RaySmall.{0} S.toIdempotents.RayCategory)) (Y := ⟨⟨Y⟩⟩)
      (unitRay φ : (⟨X⟩ : S.toIdempotents.RayCategory) ⟶ ⟨Y⟩)).1 h
    have h2 : φ = 0 := (unitRay_eq_zero_iff φ).1 h1
    exact congrArg Subtype.val h2
  refine ⟨⟨⟨⟨X⟩⟩, ⟨⟨Y⟩⟩, g, hg⟩, rfl, rfl, ?_⟩
  have hu : UnitRayEquivalent (S.repP g) φ := by
    rw [← unitRay_eq_iff, S.unitRay_repP]
    exact (sh.{0}).symm_apply_apply _
  exact (S.unitRayEquivalent_iff _ _).1 hu

lemma morElt_ne_zero_nz (t : NZ (RaySmall.{0} S.toIdempotents.RayCategory)) :
    morElt k t.2.2.1 ≠ 0 := by
  rw [← linBasisR_apply]
  exact (linBasisR k _).ne_zero t

lemma sh_symm_ne_zero {X Y : RaySmall.{0} S.toIdempotents.RayCategory} {f : X ⟶ Y} (hf : f ≠ 0) :
    (sh.{0}).symm f ≠ 0 := fun h ↦ hf (by rw [← (sh.{0}).apply_symm_apply f, h]; rfl)

/-- **The dichotomy as a statement about values**: for a non-special pair, inserting
`e + t ρ` with `ρ` radical keeps the product in its ray. -/
lemma hray_of_not_special {X Y Z : S.toIdempotents.ProjectiveCategory} (μ : X ⟶ Y) (ν : Y ⟶ Z)
    (hns : ¬IsBGRSSpecialZero μ ν) (t' : k) (ρ : B)
    (hρ : ρ ∈ S.primitiveIdempotents.cornerRadical (k := k) (S.pidx Y)) :
    ∃ u w, S.primitiveIdempotents.IsCornerUnit (k := k) (S.pidx Z) u ∧ S.primitiveIdempotents.IsCornerUnit (k := k) (S.pidx X) w ∧
      ν.1 * (S.primitiveIdempotents.e (S.pidx Y) + t' • ρ) * μ.1 = u * (ν.1 * μ.1) * w := by
  have hu0 : S.primitiveIdempotents.e (S.pidx Y) + t' • ρ ∈ S.primitiveIdempotents.corner (k := k) (S.pidx Y) (S.pidx Y) :=
    Submodule.add_mem _ (S.primitiveIdempotents.e_mem_corner _) (Submodule.smul_mem _ _ hρ.1)
  have hu1 : S.primitiveIdempotents.e (S.pidx Y) + t' • ρ ∉ S.primitiveIdempotents.cornerRadical (k := k) (S.pidx Y) := by
    intro hrad
    apply S.primitiveIdempotents.e_not_mem_radical (k := k) (S.pidx Y)
    have := Submodule.sub_mem _ hrad.2 (Submodule.smul_mem _ t' hρ.2)
    rwa [add_sub_cancel_right] at this
  let a := S.isoOfCornerUnit (S.primitiveIdempotents.isCornerUnit_of_not_mem hu0 hu1)
  obtain ⟨-, hray'⟩ := (HasBGRSPairDichotomy.pair μ ν).nonzero_common_ray_of_not_special hns
    (μ ≫ a.hom) ν ⟨Iso.refl _, a, by simp⟩ ⟨Iso.refl _, Iso.refl _, by simp⟩
  obtain ⟨u, w, hu, hw, hval'⟩ := (S.unitRayEquivalent_iff _ _).1 hray'
  refine ⟨u, w, hu, hw, ?_⟩
  have hval : (μ ≫ ν).1 = ν.1 * μ.1 :=
    LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val _ _ _
  rw [← hval, ← hval']
  simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val, mul_assoc]
  rfl

lemma betaP_mul_some (r s t : NZ (RaySmall.{0} S.toIdempotents.RayCategory))
    (h : (linTable k (RaySmall.{0} S.toIdempotents.RayCategory)).mul r s = some t) :
    S.betaP r * S.betaP s ∉ S.primitiveIdempotents.insertionSpan (k := k) (S.labelP r.2.1) (S.labelP r.1)
        (S.labelP s.1) (S.betaP r) (S.betaP s) ∧
      S.betaP r * S.betaP s ∈ S.primitiveIdempotents.ray (k := k) (S.labelP t.2.1) (S.labelP t.1) (S.betaP t) := by
  obtain ⟨Xr, Yr, fr, hr⟩ := r
  obtain ⟨Xs, Ys, fs, hs⟩ := s
  rw [linTable_mul_eq_some] at h
  by_cases hY : Ys = Xr
  swap
  · exact absurd (h.symm.trans (morElt_mul_ne k fs fr hY)) (S.morElt_ne_zero_nz t)
  subst hY
  rw [morElt_mul] at h
  have hne : fs ≫ fr ≠ 0 := fun h0 ↦ S.morElt_ne_zero_nz t (by rw [← h, h0, morElt_zero])
  have ht : (⟨Xs, Yr, fs ≫ fr, hne⟩ : NZ (RaySmall.{0} S.toIdempotents.RayCategory)) = t :=
    morElt_injective_nz k h
  subst ht
  simp only [betaP]
  set μ := S.repP fs
  set ν := S.repP fr
  have hcomp := S.sh_symm_comp_repP fs fr
  have hprod : bgrsRayRepresentativeProduct μ ν ≠ 0 := by
    intro h0
    apply S.sh_symm_ne_zero hne
    rw [hcomp, h0]
    rfl
  have hns : ¬IsBGRSSpecialZero μ ν := fun hsp ↦
    hprod (bgrsRayRepresentativeProduct_eq_zero_of_special hsp)
  have heq : bgrsRayRepresentativeProduct μ ν = μ ≫ ν :=
    bgrsRayRepresentativeProduct_eq_comp_of_not_special hns
  have hμν : μ ≫ ν ≠ 0 := heq ▸ hprod
  have hval : (μ ≫ ν).1 = ν.1 * μ.1 :=
    LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val _ _ _
  refine ⟨?_, ?_⟩
  · refine mul_not_mem_insertionSpan S.primitiveIdempotents (S.val_mem_corner ν) (S.val_mem_corner μ)
      (fun h0 ↦ hμν (Subtype.ext (by rw [hval]; exact h0))) ?_
    intro t' ρ hρ
    exact S.hray_of_not_special μ ν hns t' ρ hρ
  · have hu : UnitRayEquivalent (S.repP (fs ≫ fr)) (μ ≫ ν) := by
      rw [← unitRay_eq_iff, S.unitRay_repP, hcomp, heq]
    have := (S.unitRayEquivalent_iff _ _).1 hu
    rwa [hval] at this

lemma betaP_mul_none (r s : NZ (RaySmall.{0} S.toIdempotents.RayCategory))
    (h : (linTable k (RaySmall.{0} S.toIdempotents.RayCategory)).mul r s = none)
    (hmid : (linTable k (RaySmall.{0} S.toIdempotents.RayCategory)).tgt r =
      (linTable k (RaySmall.{0} S.toIdempotents.RayCategory)).src s) :
    S.betaP r * S.betaP s ∈ S.primitiveIdempotents.insertionSpan (k := k) (S.labelP r.2.1) (S.labelP r.1)
      (S.labelP s.1) (S.betaP r) (S.betaP s) := by
  obtain ⟨Xr, Yr, fr, hr⟩ := r
  obtain ⟨Xs, Ys, fs, hs⟩ := s
  change Xr = Ys at hmid
  subst hmid
  by_cases h0 : fs ≫ fr = 0
  swap
  · have : (linTable k (RaySmall.{0} S.toIdempotents.RayCategory)).mul ⟨Xr, Yr, fr, hr⟩ ⟨Xs, Xr, fs, hs⟩ =
        some ⟨Xs, Yr, fs ≫ fr, h0⟩ := by
      rw [linTable_mul_eq_some]
      exact morElt_mul k fs fr
    rw [h] at this
    exact absurd this (by simp)
  simp only [betaP]
  set μ := S.repP fs
  set ν := S.repP fr
  have hval : (μ ≫ ν).1 = ν.1 * μ.1 :=
    LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val _ _ _
  have hprod : bgrsRayRepresentativeProduct μ ν = 0 := by
    rw [← unitRay_eq_zero_iff, ← S.sh_symm_comp_repP fs fr, h0]
    exact (sh.{0}).symm_apply_apply _
  change ν.1 * μ.1 ∈ _
  by_cases hsp : IsBGRSSpecialZero μ ν
  · obtain ⟨ρ, hρ⟩ := hsp
    have hρv : (ρ.1.asHom : Xr.as.as ⟶ Xr.as.as).1 ∈ S.primitiveIdempotents.cornerRadical (k := k) (S.pidx Xr.as.as) :=
      (S.mem_jacobson_iff ρ.1).1 ρ.2
    have h2 := congrArg Subtype.val hρ
    simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val] at h2
    refine Submodule.subset_span ⟨S.primitiveIdempotents.e (S.pidx Yr.as.as), S.primitiveIdempotents.e_mem_corner _, _, hρv,
      S.primitiveIdempotents.e (S.pidx Xs.as.as), S.primitiveIdempotents.e_mem_corner _, ?_⟩
    rw [S.primitiveIdempotents.e_mul_of_mem (S.val_mem_corner ν), mul_assoc, mul_assoc,
      S.primitiveIdempotents.mul_e_of_mem (S.val_mem_corner μ), h2]
  · have : μ ≫ ν = 0 := by rw [← bgrsRayRepresentativeProduct_eq_comp_of_not_special hsp, hprod]
    rw [← hval, this]
    exact Submodule.zero_mem _

/-- **The ray table of the small ray category presents the algebra.** -/
theorem isRayPres_linTable :
    S.primitiveIdempotents.IsRayPres (k := k) (linTable k (RaySmall.{0} S.toIdempotents.RayCategory)) S.labelEquiv
      S.betaP where
  corner r := S.betaP_mem_corner r
  ne r := S.betaP_ne_zero r
  inj r s h := S.betaP_inj r s h
  surj x y f hf hf0 := S.betaP_surj x y f hf hf0
  mul_some r s t h := S.betaP_mul_some r s t h
  mul_none r s h hmid := S.betaP_mul_none r s h hmid

end Pres

end SplitBasicData

end LargeIndecomposable
