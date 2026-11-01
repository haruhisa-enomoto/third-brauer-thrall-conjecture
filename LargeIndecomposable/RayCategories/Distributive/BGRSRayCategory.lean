module

public import LargeIndecomposable.RayCategories.Basic.UnitRayOrbit
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.RingTheory.Jacobson.Ideal

@[expose] public section

/-!
# The special product underlying the BGRS ray category

For morphisms `μ : X ⟶ Y` and `ν : Y ⟶ Z`, BGRS does not always
compose their unit rays by taking the ray of `μ ≫ ν`.  The product is the
zero ray when the composite is already obtained by inserting an element of the
Jacobson radical of the middle endomorphism ring.  This file records that test,
the representative-level product, and the exact laws needed for it to descend
to a category of rays.

The laws are proved later from distributivity of the concrete primitive-
projective category.  Keeping them explicit here prevents the unit-orbit
projection from being mistaken for a functor or an ordinary categorical
quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The BGRS exceptional-zero test for a pair of composable representatives.
The radical is that of the intermediate endomorphism ring. -/
def IsBGRSSpecialZero {X Y Z : C} (μ : X ⟶ Y) (ν : Y ⟶ Z) : Prop :=
  ∃ ρ : Ring.jacobson (End Y),
    μ ≫ ν = (μ ≫ ρ.1.asHom) ≫ ν

/-- The representative-level BGRS product.  It is not ordinary composition:
an ordinary nonzero composite can be sent to zero. -/
def bgrsRayRepresentativeProduct {X Y Z : C}
    (μ : X ⟶ Y) (ν : Y ⟶ Z) : X ⟶ Z := by
  classical
  exact if IsBGRSSpecialZero μ ν then 0 else μ ≫ ν

@[simp]
theorem bgrsRayRepresentativeProduct_eq_zero_of_special
    {X Y Z : C} {μ : X ⟶ Y} {ν : Y ⟶ Z}
    (h : IsBGRSSpecialZero μ ν) :
    bgrsRayRepresentativeProduct μ ν = 0 := by
  simp [bgrsRayRepresentativeProduct, h]

@[simp]
theorem bgrsRayRepresentativeProduct_eq_comp_of_not_special
    {X Y Z : C} {μ : X ⟶ Y} {ν : Y ⟶ Z}
    (h : ¬IsBGRSSpecialZero μ ν) :
    bgrsRayRepresentativeProduct μ ν = μ ≫ ν := by
  simp [bgrsRayRepresentativeProduct, h]

theorem isBGRSSpecialZero_zero_left {X Y Z : C} (ν : Y ⟶ Z) :
    IsBGRSSpecialZero (0 : X ⟶ Y) ν := by
  refine ⟨⟨0, (Ring.jacobson (End Y)).zero_mem⟩, ?_⟩
  simp

theorem isBGRSSpecialZero_zero_right {X Y Z : C} (μ : X ⟶ Y) :
    IsBGRSSpecialZero μ (0 : Y ⟶ Z) := by
  refine ⟨⟨0, (Ring.jacobson (End Y)).zero_mem⟩, ?_⟩
  simp

@[simp]
theorem bgrsRayRepresentativeProduct_zero_left
    {X Y Z : C} (ν : Y ⟶ Z) :
    bgrsRayRepresentativeProduct (0 : X ⟶ Y) ν = 0 :=
  bgrsRayRepresentativeProduct_eq_zero_of_special
    (isBGRSSpecialZero_zero_left ν)

@[simp]
theorem bgrsRayRepresentativeProduct_zero_right
    {X Y Z : C} (μ : X ⟶ Y) :
    bgrsRayRepresentativeProduct μ (0 : Y ⟶ Z) = 0 :=
  bgrsRayRepresentativeProduct_eq_zero_of_special
    (isBGRSSpecialZero_zero_right μ)

/-- In a possibly noncommutative ring, one minus an element of the Jacobson
radical is a unit. -/
private theorem isUnit_one_sub_of_mem_ringJacobson
    {R : Type u} [Ring R] {r : R} (hr : r ∈ Ring.jacobson R) :
    IsUnit (1 - r) := by
  have hneg : (1 - r) - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
    rw [Ideal.jacobson_bot]
    simpa using (Ring.jacobson R).neg_mem hr
  rcases Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson (1 - r) hneg with
    ⟨s, hs⟩
  have hs_left : s * (1 - r) = 1 :=
    sub_eq_zero.mp ((Submodule.mem_bot R).1 hs)
  have hsr : s - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
    rw [Ideal.jacobson_bot]
    have hmul : s * r ∈ Ring.jacobson R :=
      (Ring.jacobson R).mul_mem_left s hr
    have heq : s - 1 = s * r := by
      calc
        s - 1 = s - s * (1 - r) := by rw [hs_left]
        _ = s * r := by rw [mul_sub, mul_one, sub_sub_cancel]
    rw [heq]
    exact hmul
  rcases Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson s hsr with
    ⟨t, ht⟩
  have ht_left : t * s = 1 :=
    sub_eq_zero.mp ((Submodule.mem_bot R).1 ht)
  have ht_eq : t = 1 - r := by
    calc
      t = t * 1 := by rw [mul_one]
      _ = t * (s * (1 - r)) := by rw [hs_left]
      _ = (t * s) * (1 - r) := by rw [mul_assoc]
      _ = 1 - r := by rw [ht_left, one_mul]
  refine isUnit_iff_exists.2 ⟨s, ?_, hs_left⟩
  rw [← ht_eq]
  exact ht_left

@[simp]
theorem bgrsRayRepresentativeProduct_id_comp {X Y : C} (f : X ⟶ Y) :
    bgrsRayRepresentativeProduct (𝟙 X) f = f := by
  by_cases h : IsBGRSSpecialZero (𝟙 X) f
  · rcases h with ⟨ρ, hρ⟩
    have hρ' : f = ρ.1.asHom ≫ f := by simpa using hρ
    haveI : IsIso ((𝟙 X) - ρ.1.asHom) :=
      (isUnit_iff_isIso _).1
        (isUnit_one_sub_of_mem_ringJacobson ρ.2)
    have hzero : ((𝟙 X) - ρ.1.asHom) ≫ f = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp]
      exact sub_eq_zero.mpr hρ'
    have hf : f = 0 := by
      apply (cancel_epi ((𝟙 X) - ρ.1.asHom)).1
      simpa using hzero
    rw [bgrsRayRepresentativeProduct_eq_zero_of_special ⟨ρ, hρ⟩, hf]
  · rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special h,
      Category.id_comp]

@[simp]
theorem bgrsRayRepresentativeProduct_comp_id {X Y : C} (f : X ⟶ Y) :
    bgrsRayRepresentativeProduct f (𝟙 Y) = f := by
  by_cases h : IsBGRSSpecialZero f (𝟙 Y)
  · rcases h with ⟨ρ, hρ⟩
    have hρ' : f = f ≫ ρ.1.asHom := by
      simpa [Category.assoc] using hρ
    haveI : IsIso ((𝟙 Y) - ρ.1.asHom) :=
      (isUnit_iff_isIso _).1
        (isUnit_one_sub_of_mem_ringJacobson ρ.2)
    have hzero : f ≫ ((𝟙 Y) - ρ.1.asHom) = 0 := by
      rw [Preadditive.comp_sub, Category.comp_id]
      exact sub_eq_zero.mpr hρ'
    have hf : f = 0 := by
      apply (cancel_mono ((𝟙 Y) - ρ.1.asHom)).1
      simpa using hzero
    rw [bgrsRayRepresentativeProduct_eq_zero_of_special ⟨ρ, hρ⟩, hf]
  · rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special h,
      Category.comp_id]

/-- The BGRS dichotomy for one composable pair.  In the exceptional case,
some representatives have zero ordinary composite; otherwise every pair of
representatives has nonzero composite in one common unit ray. -/
structure BGRSPairDichotomy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop where
  zero_representatives_of_special : IsBGRSSpecialZero f g →
    ∃ f' : X ⟶ Y, ∃ g' : Y ⟶ Z,
      UnitRayEquivalent f f' ∧ UnitRayEquivalent g g' ∧ f' ≫ g' = 0
  nonzero_common_ray_of_not_special : ¬IsBGRSSpecialZero f g →
    ∀ (f' : X ⟶ Y) (g' : Y ⟶ Z),
      UnitRayEquivalent f f' → UnitRayEquivalent g g' →
        f' ≫ g' ≠ 0 ∧ UnitRayEquivalent (f ≫ g) (f' ≫ g')

/-- Every composable pair satisfies the BGRS zero/common-ray dichotomy. -/
class HasBGRSPairDichotomy
    (C : Type u) [Category.{v} C] [Preadditive C] : Prop where
  pair : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    BGRSPairDichotomy f g

/-- The exact operational laws needed for the representative-level BGRS
product to define a category on two-sided unit rays.

For the concrete primitive-projective category these laws are consequences of
distributivity.  They are kept as a named boundary rather than silently
assuming that ordinary composition descends to unit orbits. -/
class HasWellDefinedBGRSRayProduct
    (C : Type u) [Category.{v} C] [Preadditive C] : Prop where
  congr : ∀ {W X Y : C} {f f' : W ⟶ X} {g g' : X ⟶ Y},
    UnitRayEquivalent f f' → UnitRayEquivalent g g' →
      UnitRayEquivalent
        (bgrsRayRepresentativeProduct f g)
        (bgrsRayRepresentativeProduct f' g')
  assoc : ∀ {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    UnitRayEquivalent
      (bgrsRayRepresentativeProduct
        (bgrsRayRepresentativeProduct f g) h)
      (bgrsRayRepresentativeProduct f
        (bgrsRayRepresentativeProduct g h))

section PairDichotomy

variable [HasBGRSPairDichotomy C]

omit [Preadditive C] [HasBGRSPairDichotomy C] in
private theorem unitRayEquivalent_refl {X Y : C} (f : X ⟶ Y) :
    UnitRayEquivalent f f := by
  apply (unitRay_eq_iff f f).mp
  rfl

omit [Preadditive C] [HasBGRSPairDichotomy C] in
private theorem unitRayEquivalent_symm {X Y : C} {f g : X ⟶ Y}
    (h : UnitRayEquivalent f g) : UnitRayEquivalent g f := by
  apply (unitRay_eq_iff g f).mp
  exact ((unitRay_eq_iff f g).mpr h).symm

omit [Preadditive C] [HasBGRSPairDichotomy C] in
private theorem unitRayEquivalent_trans {X Y : C} {f g h : X ⟶ Y}
    (hfg : UnitRayEquivalent f g) (hgh : UnitRayEquivalent g h) :
    UnitRayEquivalent f h := by
  apply (unitRay_eq_iff f h).mp
  exact ((unitRay_eq_iff f g).mpr hfg).trans
    ((unitRay_eq_iff g h).mpr hgh)

omit [Preadditive C] [HasBGRSPairDichotomy C] in
private theorem factor_representative_of_composite {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) {k : W ⟶ Y}
    (hk : UnitRayEquivalent (f ≫ g) k) :
    ∃ f' : W ⟶ X, ∃ g' : X ⟶ Y,
      UnitRayEquivalent f f' ∧ UnitRayEquivalent g g' ∧ f' ≫ g' = k := by
  rcases hk with ⟨a, b, rfl⟩
  refine ⟨a.hom ≫ f, g ≫ b.hom, ?_, ?_, ?_⟩
  · exact ⟨a, Iso.refl X, by simp⟩
  · exact ⟨Iso.refl X, b, by simp⟩
  · simp [Category.assoc]

/-- The exceptional-zero test is invariant under changing either morphism
within its two-sided unit ray. -/
theorem isBGRSSpecialZero_iff_of_unitRayEquivalent
    {W X Y : C} {f f' : W ⟶ X} {g g' : X ⟶ Y}
    (hf : UnitRayEquivalent f f') (hg : UnitRayEquivalent g g') :
    IsBGRSSpecialZero f g ↔ IsBGRSSpecialZero f' g' := by
  constructor
  · intro hs
    by_contra hs'
    rcases
        (HasBGRSPairDichotomy.pair f g).zero_representatives_of_special hs with
      ⟨u, v, hu, hv, huv⟩
    have hf'u := unitRayEquivalent_trans (unitRayEquivalent_symm hf) hu
    have hg'v := unitRayEquivalent_trans (unitRayEquivalent_symm hg) hv
    exact ((HasBGRSPairDichotomy.pair f' g').nonzero_common_ray_of_not_special
      hs' u v hf'u hg'v).1 huv
  · intro hs'
    by_contra hs
    rcases
        (HasBGRSPairDichotomy.pair f' g').zero_representatives_of_special hs' with
      ⟨u, v, hu, hv, huv⟩
    have hfu := unitRayEquivalent_trans hf hu
    have hgv := unitRayEquivalent_trans hg hv
    exact ((HasBGRSPairDichotomy.pair f g).nonzero_common_ray_of_not_special
      hs u v hfu hgv).1 huv

/-- The BGRS representative product is invariant up to two-sided units under
changing either representative. -/
theorem bgrsRayRepresentativeProduct_unitRayEquivalent
    {W X Y : C} {f f' : W ⟶ X} {g g' : X ⟶ Y}
    (hf : UnitRayEquivalent f f') (hg : UnitRayEquivalent g g') :
    UnitRayEquivalent (bgrsRayRepresentativeProduct f g)
      (bgrsRayRepresentativeProduct f' g') := by
  by_cases hs : IsBGRSSpecialZero f g
  · have hs' := (isBGRSSpecialZero_iff_of_unitRayEquivalent hf hg).mp hs
    rw [bgrsRayRepresentativeProduct_eq_zero_of_special hs,
      bgrsRayRepresentativeProduct_eq_zero_of_special hs']
    exact unitRayEquivalent_refl 0
  · have hs' : ¬IsBGRSSpecialZero f' g' :=
      fun h ↦ hs ((isBGRSSpecialZero_iff_of_unitRayEquivalent hf hg).mpr h)
    rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs,
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hs']
    exact ((HasBGRSPairDichotomy.pair f g).nonzero_common_ray_of_not_special
      hs f' g' hf hg).2

private def AllBGRSTripleRepresentativeProductsNonzero {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : Prop :=
  ∀ (f' : W ⟶ X) (g' : X ⟶ Y) (h' : Y ⟶ Z),
    UnitRayEquivalent f f' → UnitRayEquivalent g g' →
      UnitRayEquivalent h h' → (f' ≫ g') ≫ h' ≠ 0

private theorem bgrsRayRepresentativeProduct_left_ne_zero_iff
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    bgrsRayRepresentativeProduct (bgrsRayRepresentativeProduct f g) h ≠ 0 ↔
      AllBGRSTripleRepresentativeProductsNonzero f g h := by
  constructor
  · intro hleft
    have hfg : ¬IsBGRSSpecialZero f g := by
      intro hs
      rw [bgrsRayRepresentativeProduct_eq_zero_of_special hs,
        bgrsRayRepresentativeProduct_zero_left] at hleft
      exact hleft rfl
    have hout : ¬IsBGRSSpecialZero (f ≫ g) h := by
      intro hs
      rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hfg,
        bgrsRayRepresentativeProduct_eq_zero_of_special hs] at hleft
      exact hleft rfl
    intro f' g' h' hf hg hh
    have hfg' : UnitRayEquivalent (f ≫ g) (f' ≫ g') :=
      ((HasBGRSPairDichotomy.pair f g).nonzero_common_ray_of_not_special
        hfg f' g' hf hg).2
    exact
      ((HasBGRSPairDichotomy.pair (f ≫ g) h).nonzero_common_ray_of_not_special
        hout (f' ≫ g') h' hfg' hh).1
  · intro hall
    have hfg : ¬IsBGRSSpecialZero f g := by
      intro hs
      rcases
          (HasBGRSPairDichotomy.pair f g).zero_representatives_of_special hs with
        ⟨f', g', hf, hg, hzero⟩
      apply hall f' g' h hf hg (unitRayEquivalent_refl h)
      rw [hzero, zero_comp]
    have hout : ¬IsBGRSSpecialZero (f ≫ g) h := by
      intro hs
      rcases
          (HasBGRSPairDichotomy.pair (f ≫ g) h).zero_representatives_of_special
            hs with
        ⟨k, h', hk, hh, hzero⟩
      rcases factor_representative_of_composite f g hk with
        ⟨f', g', hf, hg, hfgk⟩
      apply hall f' g' h' hf hg hh
      rw [hfgk]
      exact hzero
    rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hfg,
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hout]
    exact hall f g h (unitRayEquivalent_refl f) (unitRayEquivalent_refl g)
      (unitRayEquivalent_refl h)

private theorem bgrsRayRepresentativeProduct_right_ne_zero_iff
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    bgrsRayRepresentativeProduct f (bgrsRayRepresentativeProduct g h) ≠ 0 ↔
      AllBGRSTripleRepresentativeProductsNonzero f g h := by
  constructor
  · intro hright
    have hgh : ¬IsBGRSSpecialZero g h := by
      intro hs
      rw [bgrsRayRepresentativeProduct_eq_zero_of_special hs,
        bgrsRayRepresentativeProduct_zero_right] at hright
      exact hright rfl
    have hout : ¬IsBGRSSpecialZero f (g ≫ h) := by
      intro hs
      rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hgh,
        bgrsRayRepresentativeProduct_eq_zero_of_special hs] at hright
      exact hright rfl
    intro f' g' h' hf hg hh
    have hgh' : UnitRayEquivalent (g ≫ h) (g' ≫ h') :=
      ((HasBGRSPairDichotomy.pair g h).nonzero_common_ray_of_not_special
        hgh g' h' hg hh).2
    have hn :=
      ((HasBGRSPairDichotomy.pair f (g ≫ h)).nonzero_common_ray_of_not_special
        hout f' (g' ≫ h') hf hgh').1
    simpa only [Category.assoc] using hn
  · intro hall
    have hgh : ¬IsBGRSSpecialZero g h := by
      intro hs
      rcases
          (HasBGRSPairDichotomy.pair g h).zero_representatives_of_special hs with
        ⟨g', h', hg, hh, hzero⟩
      apply hall f g' h' (unitRayEquivalent_refl f) hg hh
      rw [Category.assoc, hzero, comp_zero]
    have hout : ¬IsBGRSSpecialZero f (g ≫ h) := by
      intro hs
      rcases
          (HasBGRSPairDichotomy.pair f (g ≫ h)).zero_representatives_of_special
            hs with
        ⟨f', k, hf, hk, hzero⟩
      rcases factor_representative_of_composite g h hk with
        ⟨g', h', hg, hh, hghk⟩
      apply hall f' g' h' hf hg hh
      rw [Category.assoc, hghk]
      exact hzero
    rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hgh,
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hout]
    simpa only [Category.assoc] using
      (hall f g h (unitRayEquivalent_refl f) (unitRayEquivalent_refl g)
        (unitRayEquivalent_refl h))

/-- Under the BGRS pair dichotomy, the representative product is strictly
associative, not merely associative up to unit rays. -/
theorem bgrsRayRepresentativeProduct_assoc_of_pairDichotomy
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    bgrsRayRepresentativeProduct (bgrsRayRepresentativeProduct f g) h =
      bgrsRayRepresentativeProduct f (bgrsRayRepresentativeProduct g h) := by
  classical
  by_cases hall : AllBGRSTripleRepresentativeProductsNonzero f g h
  · have hleft :
        bgrsRayRepresentativeProduct (bgrsRayRepresentativeProduct f g) h ≠
          0 :=
      (bgrsRayRepresentativeProduct_left_ne_zero_iff f g h).mpr hall
    have hright :
        bgrsRayRepresentativeProduct f (bgrsRayRepresentativeProduct g h) ≠
          0 :=
      (bgrsRayRepresentativeProduct_right_ne_zero_iff f g h).mpr hall
    have hfg : ¬IsBGRSSpecialZero f g := by
      intro hs
      rw [bgrsRayRepresentativeProduct_eq_zero_of_special hs,
        bgrsRayRepresentativeProduct_zero_left] at hleft
      exact hleft rfl
    have hleftOuter : ¬IsBGRSSpecialZero (f ≫ g) h := by
      intro hs
      rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hfg,
        bgrsRayRepresentativeProduct_eq_zero_of_special hs] at hleft
      exact hleft rfl
    have hgh : ¬IsBGRSSpecialZero g h := by
      intro hs
      rw [bgrsRayRepresentativeProduct_eq_zero_of_special hs,
        bgrsRayRepresentativeProduct_zero_right] at hright
      exact hright rfl
    have hrightOuter : ¬IsBGRSSpecialZero f (g ≫ h) := by
      intro hs
      rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hgh,
        bgrsRayRepresentativeProduct_eq_zero_of_special hs] at hright
      exact hright rfl
    rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hfg,
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hleftOuter,
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hgh,
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hrightOuter,
      Category.assoc]
  · have hleft :
        bgrsRayRepresentativeProduct (bgrsRayRepresentativeProduct f g) h =
          0 := by
      by_contra hn
      exact hall
        ((bgrsRayRepresentativeProduct_left_ne_zero_iff f g h).mp hn)
    have hright :
        bgrsRayRepresentativeProduct f (bgrsRayRepresentativeProduct g h) =
          0 := by
      by_contra hn
      exact hall
        ((bgrsRayRepresentativeProduct_right_ne_zero_iff f g h).mp hn)
    rw [hleft, hright]

/-- The BGRS pair dichotomy supplies all operational laws required by the
two-sided unit-ray quotient. -/
instance hasWellDefinedBGRSRayProduct_of_hasBGRSPairDichotomy :
    HasWellDefinedBGRSRayProduct C where
  congr := bgrsRayRepresentativeProduct_unitRayEquivalent
  assoc := by
    intro W X Y Z f g h
    rw [bgrsRayRepresentativeProduct_assoc_of_pairDichotomy f g h]
    exact unitRayEquivalent_refl _

end PairDichotomy

variable [HasWellDefinedBGRSRayProduct C]

/-- The BGRS product descended to two-sided unit rays. -/
def bgrsRayComp {X Y Z : C} :
    UnitRayOrbit X Y → UnitRayOrbit Y Z → UnitRayOrbit X Z :=
  fun f g ↦ Quotient.liftOn₂ f g
    (fun f g ↦ unitRay (bgrsRayRepresentativeProduct f g))
    (fun _ _ _ _ hf hg ↦ Quotient.sound
      (HasWellDefinedBGRSRayProduct.congr hf hg))

@[simp]
theorem bgrsRayComp_unitRay {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    bgrsRayComp (unitRay f) (unitRay g) =
      unitRay (bgrsRayRepresentativeProduct f g) :=
  rfl

@[simp]
theorem bgrsRayComp_zero_left {X Y Z : C}
    (g : UnitRayOrbit Y Z) :
    bgrsRayComp (0 : UnitRayOrbit X Y) g = 0 := by
  induction g using Quotient.inductionOn with
  | _ g =>
      change unitRay (bgrsRayRepresentativeProduct (0 : X ⟶ Y) g) =
        unitRay (0 : X ⟶ Z)
      rw [bgrsRayRepresentativeProduct_zero_left]

@[simp]
theorem bgrsRayComp_zero_right {X Y Z : C}
    (f : UnitRayOrbit X Y) :
    bgrsRayComp f (0 : UnitRayOrbit Y Z) = 0 := by
  induction f using Quotient.inductionOn with
  | _ f =>
      change unitRay (bgrsRayRepresentativeProduct f (0 : Y ⟶ Z)) =
        unitRay (0 : X ⟶ Z)
      rw [bgrsRayRepresentativeProduct_zero_right]

/-- Object wrapper for the BGRS ray category. -/
@[ext]
structure BGRSRayCategory (C : Type u) where
  as : C

namespace BGRSRayCategory

/-- The object type is equivalent to that of the source category. -/
def equiv : BGRSRayCategory C ≃ C where
  toFun := as
  invFun := BGRSRayCategory.mk
  left_inv X := by cases X; rfl
  right_inv _ := rfl

instance [Finite C] : Finite (BGRSRayCategory C) :=
  Finite.of_injective as (by
    intro X Y h
    exact BGRSRayCategory.ext h)

instance category : Category.{v} (BGRSRayCategory C) where
  Hom X Y := UnitRayOrbit X.as Y.as
  id X := unitRay (𝟙 X.as)
  comp f g := bgrsRayComp f g
  comp_id := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ f =>
        change unitRay (bgrsRayRepresentativeProduct f (𝟙 Y.as)) =
          unitRay f
        rw [bgrsRayRepresentativeProduct_comp_id]
  id_comp := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ f =>
        change unitRay (bgrsRayRepresentativeProduct (𝟙 X.as) f) =
          unitRay f
        rw [bgrsRayRepresentativeProduct_id_comp]
  assoc := by
    intro W X Y Z f g h
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        induction h using Quotient.inductionOn with
        | _ h =>
            change unitRay (bgrsRayRepresentativeProduct
                (bgrsRayRepresentativeProduct f g) h) =
              unitRay (bgrsRayRepresentativeProduct f
                (bgrsRayRepresentativeProduct g h))
            exact (unitRay_eq_iff _ _).2
              (HasWellDefinedBGRSRayProduct.assoc f g h)

instance hasZeroMorphisms : HasZeroMorphisms (BGRSRayCategory C) where
  zero X Y := ⟨unitRay (0 : X.as ⟶ Y.as)⟩
  comp_zero := by
    intro X Y f Z
    exact bgrsRayComp_zero_right f
  zero_comp := by
    intro X Y Z f
    exact bgrsRayComp_zero_left f

omit [Preadditive C] [HasWellDefinedBGRSRayProduct C] in
private theorem isIso_of_unitRay_composites_eq_identity
    {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X}
    (hfg : unitRay (f ≫ g) = unitRay (𝟙 X))
    (hgf : unitRay (g ≫ f) = unitRay (𝟙 Y)) : IsIso f := by
  rcases (unitRay_eq_iff _ _).1 hfg with ⟨a, b, hab⟩
  have hfg' : f ≫ g = a.inv ≫ (𝟙 X) ≫ b.inv := by
    have h := congrArg (fun q ↦ a.inv ≫ q ≫ b.inv) hab
    simpa [Category.assoc] using h.symm
  haveI hfgIso : IsIso (f ≫ g) := by
    rw [hfg']
    infer_instance
  rcases (unitRay_eq_iff _ _).1 hgf with ⟨c, d, hcd⟩
  have hgf' : g ≫ f = c.inv ≫ (𝟙 Y) ≫ d.inv := by
    have h := congrArg (fun q ↦ c.inv ≫ q ≫ d.inv) hcd
    simpa [Category.assoc] using h.symm
  haveI hgfIso : IsIso (g ≫ f) := by
    rw [hgf']
    infer_instance
  let r : Y ⟶ X := g ≫ inv (f ≫ g)
  let l : Y ⟶ X := inv (g ≫ f) ≫ g
  have hfr : f ≫ r = 𝟙 X := by
    dsimp [r]
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hlf : l ≫ f = 𝟙 Y := by
    dsimp [l]
    rw [Category.assoc, IsIso.inv_hom_id]
  have hrl : r = l := by
    rw [← Category.id_comp r, ← hlf, Category.assoc, hfr,
      Category.comp_id]
  have hrf : r ≫ f = 𝟙 Y := by
    rw [hrl]
    exact hlf
  exact ⟨⟨r, hfr, hrf⟩⟩

/-- If the unit ray of a representative is invertible in the BGRS category,
then the original representative is an isomorphism. -/
theorem representative_isIso_of_isIso
    (hid : ∀ X : C, (𝟙 X : X ⟶ X) ≠ 0)
    {X Y : C} (f : X ⟶ Y)
    [IsIso (show BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Y from
      unitRay f)] :
    IsIso f := by
  let rf : BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Y := unitRay f
  obtain ⟨g, hg⟩ := (unitRay_surjective Y X) (inv rf)
  have hfgRay : rf ≫ unitRay g = 𝟙 (BGRSRayCategory.mk X) := by
    rw [hg]
    exact IsIso.hom_inv_id _
  have hgfRay :
      (unitRay g : BGRSRayCategory.mk Y ⟶ BGRSRayCategory.mk X) ≫ rf =
        𝟙 (BGRSRayCategory.mk Y) := by
    rw [hg]
    exact IsIso.inv_hom_id _
  change unitRay (bgrsRayRepresentativeProduct f g) =
    unitRay (𝟙 X) at hfgRay
  change unitRay (bgrsRayRepresentativeProduct g f) =
    unitRay (𝟙 Y) at hgfRay
  have hpfg : bgrsRayRepresentativeProduct f g ≠ 0 := by
    rw [← unitRay_ne_zero_iff]
    rw [hfgRay]
    exact (unitRay_ne_zero_iff (𝟙 X)).2 (hid X)
  have hpgf : bgrsRayRepresentativeProduct g f ≠ 0 := by
    rw [← unitRay_ne_zero_iff]
    rw [hgfRay]
    exact (unitRay_ne_zero_iff (𝟙 Y)).2 (hid Y)
  have hnsfg : ¬IsBGRSSpecialZero f g := by
    intro hs
    exact hpfg (bgrsRayRepresentativeProduct_eq_zero_of_special hs)
  have hnsgf : ¬IsBGRSSpecialZero g f := by
    intro hs
    exact hpgf (bgrsRayRepresentativeProduct_eq_zero_of_special hs)
  have hfg : unitRay (f ≫ g) = unitRay (𝟙 X) := by
    rw [← bgrsRayRepresentativeProduct_eq_comp_of_not_special hnsfg]
    exact hfgRay
  have hgf : unitRay (g ≫ f) = unitRay (𝟙 Y) := by
    rw [← bgrsRayRepresentativeProduct_eq_comp_of_not_special hnsgf]
    exact hgfRay
  exact isIso_of_unitRay_composites_eq_identity hfg hgf

/-- Every automorphism endoray is the identity ray. -/
theorem end_eq_id_of_isIso
    (hid : ∀ X : C, (𝟙 X : X ⟶ X) ≠ 0)
    {X : C} (r : End (BGRSRayCategory.mk X)) [IsIso r] :
    r = 𝟙 (BGRSRayCategory.mk X) := by
  let r' : UnitRayOrbit X X := r
  let f : X ⟶ X := r'.out
  have hfRay : unitRay f = r' := unitRay_out r'
  let rf : End (BGRSRayCategory.mk X) := unitRay f
  have hrf : rf = r := hfRay
  letI hrfIso : IsIso rf := hrf ▸ inferInstance
  letI : IsIso f := representative_isIso_of_isIso hid f
  change r' = unitRay (𝟙 X)
  rw [← hfRay]
  exact unitRay_eq_identity_of_isIso f

/-- Skeletality of the source category descends to its BGRS ray category. -/
theorem skeletal
    (hid : ∀ X : C, (𝟙 X : X ⟶ X) ≠ 0)
    (hskel : Skeletal C) : Skeletal (BGRSRayCategory C) := by
  intro X Y hXY
  rcases hXY with ⟨e⟩
  obtain ⟨f, hf⟩ := (unitRay_surjective X.as Y.as) e.hom
  let rf : X ⟶ Y := unitRay f
  have hrf : rf = e.hom := hf
  letI : IsIso rf := by
    rw [hrf]
    infer_instance
  letI : IsIso f := representative_isIso_of_isIso hid f
  exact BGRSRayCategory.ext (hskel ⟨asIso f⟩)

@[simp]
theorem id_eq (X : BGRSRayCategory C) :
    (𝟙 X : X ⟶ X) = unitRay (𝟙 X.as) :=
  rfl

@[simp]
theorem zero_eq {X Y : C} :
    (0 : BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Y) =
      (unitRay (0 : X ⟶ Y) : UnitRayOrbit X Y) :=
  rfl

@[simp]
theorem comp_unitRay {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (unitRay f : BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Y) ≫
      (unitRay g : BGRSRayCategory.mk Y ⟶ BGRSRayCategory.mk Z) =
    (show BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Z from
      unitRay (bgrsRayRepresentativeProduct f g)) :=
  bgrsRayComp_unitRay f g

end BGRSRayCategory

end LargeIndecomposable
