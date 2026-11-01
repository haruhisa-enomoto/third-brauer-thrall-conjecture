module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import LargeIndecomposable.Foundations.Ring.LocalRingJacobson
public import Mathlib.RingTheory.Artinian.Ring

@[expose] public section

/-!
# Reducing the BGRS pair dichotomy to the middle-unit common-ray law

The exceptional branch of the BGRS pair dichotomy follows from local
Artinian endomorphism rings.  For the nonexceptional branch, nonvanishing of
middle-unit twists follows from a split residue map detecting the Jacobson
radical.  The remaining source-specific datum is exactly that such twists
belong to the common unit ray.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem BGRSPairDichotomy.zero_representatives_of_special_of_artinianLocal
    {X Y Z : C} [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsBGRSSpecialZero f g →
      ∃ f' : X ⟶ Y, ∃ g' : Y ⟶ Z,
        UnitRayEquivalent f f' ∧ UnitRayEquivalent g g' ∧ f' ≫ g' = 0 := by
  rintro ⟨ρ, hρ⟩
  have hρ_nonunit : ¬ IsUnit ρ.1 :=
    (mem_ringJacobson_iff_not_isUnit (End Y) ρ.1).1 ρ.2
  have hu : IsUnit (1 - ρ.1) := by
    simpa [sub_eq_add_neg] using
      isUnit_one_add_of_not_isUnit (End Y) (-ρ.1)
        (fun hneg ↦ hρ_nonunit (by simpa using hneg.neg))
  haveI : IsIso (1 - ρ.1).asHom := (isUnit_iff_isIso _).1 hu
  let u : Y ≅ Y := asIso (1 - ρ.1).asHom
  refine ⟨f ≫ u.hom, g, ?_, ?_, ?_⟩
  · exact ⟨Iso.refl X, u, by simp⟩
  · exact ⟨Iso.refl Y, Iso.refl Z, by simp⟩
  · dsimp [u]
    change (f ≫ ((𝟙 Y) - ρ.1.asHom)) ≫ g = 0
    rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp]
    exact sub_eq_zero.mpr hρ

section Linear

variable {k : Type w} [Field k]
variable [Linear k C]

theorem middleUnitComposite_ne_zero_of_not_bgrsSpecial
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (res : End Y →ₐ[k] k)
    (hres : ∀ q : End Y,
      res q = 0 ↔ q ∈ Ring.jacobson (End Y))
    (m : End Y) (hm : IsUnit m)
    (hns : ¬IsBGRSSpecialZero f g) :
    (f ≫ m.asHom) ≫ g ≠ 0 := by
  intro hzero
  have hcm : res m ≠ 0 := by
    exact (hm.map res.toRingHom).ne_zero
  let c : k := res m
  let n : End Y := c⁻¹ • m
  have hnres : res n = 1 := by
    dsimp [n, c]
    rw [map_smul]
    exact inv_mul_cancel₀ hcm
  let ρ : End Y := 1 - n
  have hρres : res ρ = 0 := by
    dsimp [ρ]
    rw [map_sub]
    change res (1 : End Y) - res n = 0
    rw [map_one, hnres, sub_self]
  have hρmem : ρ ∈ Ring.jacobson (End Y) :=
    (hres ρ).1 hρres
  have hnzero : (f ≫ n.asHom) ≫ g = 0 := by
    dsimp [n, c]
    change (f ≫ ((res m)⁻¹ • m.asHom)) ≫ g = 0
    rw [Linear.comp_smul, Linear.smul_comp, hzero, smul_zero]
  apply hns
  refine ⟨⟨ρ, hρmem⟩, ?_⟩
  dsimp [ρ]
  change f ≫ g = (f ≫ ((𝟙 Y) - n.asHom)) ≫ g
  rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
    hnzero, sub_zero]

end Linear

variable (C)

/-- The remaining source-specific half of the BGRS pair theorem: a
nonexceptional composite has the same unit ray after insertion of any unit at
the intermediate object. -/
class HasBGRSMiddleUnitCommonRay : Prop where
  common_ray_of_not_special : ∀ {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : End Y),
    ¬IsBGRSSpecialZero f g → IsUnit m →
      UnitRayEquivalent (f ≫ g) ((f ≫ m.asHom) ≫ g)

variable {C}

private theorem comp_ne_zero_of_not_bgrsSpecial
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hns : ¬IsBGRSSpecialZero f g) :
    f ≫ g ≠ 0 := by
  intro hzero
  apply hns
  refine ⟨⟨0, (Ring.jacobson (End Y)).zero_mem⟩, ?_⟩
  change f ≫ g = (f ≫ (0 : Y ⟶ Y)) ≫ g
  simp [hzero]

instance hasBGRSPairDichotomy_of_middleUnitCommonRay
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSMiddleUnitCommonRay C] :
    HasBGRSPairDichotomy C where
  pair f g := by
    constructor
    · exact
        BGRSPairDichotomy.zero_representatives_of_special_of_artinianLocal f g
    · intro hns f' g' hff' hgg'
      rcases hff' with ⟨a, b, rfl⟩
      rcases hgg' with ⟨c, d, rfl⟩
      let m : End _ := b.hom ≫ c.hom
      haveI : IsIso m := by
        dsimp [m]
        infer_instance
      have hm : IsUnit m := (isUnit_iff_isIso m).2 inferInstance
      have hmiddle :
          UnitRayEquivalent (f ≫ g) ((f ≫ m.asHom) ≫ g) :=
        HasBGRSMiddleUnitCommonRay.common_ray_of_not_special
          f g m hns hm
      rcases hmiddle with ⟨p, q, hpq⟩
      have hcommon :
          UnitRayEquivalent (f ≫ g)
            ((a.hom ≫ f ≫ b.hom) ≫ (c.hom ≫ g ≫ d.hom)) := by
        refine ⟨a.trans p, q.trans d, ?_⟩
        dsimp [m] at hpq
        calc
          (a.hom ≫ f ≫ b.hom) ≫ (c.hom ≫ g ≫ d.hom) =
              a.hom ≫ ((f ≫ (b.hom ≫ c.hom)) ≫ g) ≫ d.hom := by
                simp only [Category.assoc]
          _ = a.hom ≫ (p.hom ≫ (f ≫ g) ≫ q.hom) ≫ d.hom := by
                rw [hpq]
          _ = (a.trans p).hom ≫ (f ≫ g) ≫ (q.trans d).hom := by
                simp only [Iso.trans_hom, Category.assoc]
      refine ⟨?_, hcommon⟩
      have hfg0 : f ≫ g ≠ 0 :=
        comp_ne_zero_of_not_bgrsSpecial hns
      intro hzero
      have hray :
          unitRay (f ≫ g) =
            unitRay ((a.hom ≫ f ≫ b.hom) ≫
              (c.hom ≫ g ≫ d.hom)) :=
        (unitRay_eq_iff _ _).2 hcommon
      rw [hzero] at hray
      exact hfg0 ((unitRay_eq_zero_iff (f ≫ g)).1 hray)

end LargeIndecomposable
