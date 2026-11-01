module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackle

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An element congruent to one modulo the ring Jacobson radical is a unit. -/
theorem isUnit_one_sub_of_mem_jacobson
    {R : Type*} [Ring R] {r : R} (hr : r ∈ Ring.jacobson R) :
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

/-- A nonzero morphism followed by an isomorphism cannot be a BGRS special
pair.  Cancellation reduces a hypothetical special equation to multiplication
by `1-rho`, which is invertible for `rho` in the Jacobson radical. -/
theorem not_isBGRSSpecialZero_of_right_isIso
    {X Y Z : C} (f : X ⟶ Y) (hf : f ≠ 0) (e : Y ⟶ Z) [IsIso e] :
    ¬IsBGRSSpecialZero f e := by
  rintro ⟨rho, hrho⟩
  have hfix : f = f ≫ rho.1.asHom := by
    apply (cancel_mono e).1
    simpa [Category.assoc] using hrho
  have hu : IsUnit (1 - rho.1) :=
    isUnit_one_sub_of_mem_jacobson rho.2
  letI : IsIso (1 - rho.1).asHom := (isUnit_iff_isIso _).1 hu
  have hz : f ≫ (1 - rho.1).asHom = 0 := by
    change f ≫ ((𝟙 Y) - rho.1.asHom) = 0
    rw [Preadditive.comp_sub, Category.comp_id]
    exact sub_eq_zero.mpr hfix
  apply hf
  apply (cancel_mono (1 - rho.1).asHom).1
  simpa using hz

/-- An isomorphism followed by a nonzero morphism cannot be a BGRS special
pair. -/
theorem not_isBGRSSpecialZero_of_left_isIso
    {X Y Z : C} (e : X ⟶ Y) [IsIso e] (f : Y ⟶ Z) (hf : f ≠ 0) :
    ¬IsBGRSSpecialZero e f := by
  rintro ⟨rho, hrho⟩
  have hfix : f = rho.1.asHom ≫ f := by
    apply (cancel_epi e).1
    simpa [Category.assoc] using hrho
  have hu : IsUnit (1 - rho.1) :=
    isUnit_one_sub_of_mem_jacobson rho.2
  letI : IsIso (1 - rho.1).asHom := (isUnit_iff_isIso _).1 hu
  have hz : (1 - rho.1).asHom ≫ f = 0 := by
    change ((𝟙 Y) - rho.1.asHom) ≫ f = 0
    rw [Preadditive.sub_comp, Category.id_comp]
    exact sub_eq_zero.mpr hfix
  apply hf
  apply (cancel_epi (1 - rho.1).asHom).1
  simpa using hz

variable [HasWellDefinedBGRSRayProduct C]

/-- Regard a nonzero ordinary morphism as its nonzero morphism in the BGRS
ray category. -/
def unitRayNonzeroHom {X Y : C} (f : X ⟶ Y) (hf : f ≠ 0) :
    NonzeroHom (BGRSRayCategory.mk X) (BGRSRayCategory.mk Y) :=
  ⟨unitRay f, by
    change unitRay f ≠ (0 : UnitRayOrbit X Y)
    intro h
    exact hf ((unitRay_eq_zero_iff f).1 h)⟩

/-- Source incomparability of two irreducible rays lifts to source
incomparability of any nonzero ordinary representatives.  In a hypothetical
factorization, irreducibility makes the remaining factor invertible, so the
BGRS product agrees with ordinary composition. -/
theorem raySourceIncomparable_representatives_of_irreducible
    {X Y Z : C} (a : X ⟶ Y) (ha0 : a ≠ 0) (f : X ⟶ Z) (hf0 : f ≠ 0)
    (ha : IsIrreducibleRayMorphism a) (hf : IsIrreducibleRayMorphism f)
    (hinc : RaySourceIncomparable
      (unitRayNonzeroHom a ha0) (unitRayNonzeroHom f hf0)) :
    RaySourceIncomparable
      (⟨a, ha0⟩ : NonzeroHom X Y) (⟨f, hf0⟩ : NonzeroHom X Z) := by
  constructor
  · rintro ⟨g, hag⟩
    rcases hf.2.2 Y a g hag with hai | hgi
    · exact ha.2.1 hai
    · letI : IsIso g := hgi
      apply hinc.1
      refine ⟨unitRay g, ?_⟩
      dsimp only [unitRayNonzeroHom]
      rw [BGRSRayCategory.comp_unitRay,
        bgrsRayRepresentativeProduct_eq_comp_of_not_special
          (not_isBGRSSpecialZero_of_right_isIso a ha0 g)]
      exact congrArg (unitRay : (X ⟶ Z) → UnitRayOrbit X Z) hag
  · rintro ⟨g, hfg⟩
    rcases ha.2.2 Z f g hfg with hfi | hgi
    · exact hf.2.1 hfi
    · letI : IsIso g := hgi
      apply hinc.2
      refine ⟨unitRay g, ?_⟩
      dsimp only [unitRayNonzeroHom]
      rw [BGRSRayCategory.comp_unitRay,
        bgrsRayRepresentativeProduct_eq_comp_of_not_special
          (not_isBGRSSpecialZero_of_right_isIso f hf0 g)]
      exact congrArg (unitRay : (X ⟶ Y) → UnitRayOrbit X Y) hfg

/-- Target-incomparability version of
`raySourceIncomparable_representatives_of_irreducible`. -/
theorem rayTargetIncomparable_representatives_of_irreducible
    {X Y Z : C} (f : X ⟶ Z) (hf0 : f ≠ 0) (q : Y ⟶ Z) (hq0 : q ≠ 0)
    (hf : IsIrreducibleRayMorphism f) (hq : IsIrreducibleRayMorphism q)
    (hinc : RayTargetIncomparable
      (unitRayNonzeroHom f hf0) (unitRayNonzeroHom q hq0)) :
    RayTargetIncomparable
      (⟨f, hf0⟩ : NonzeroHom X Z) (⟨q, hq0⟩ : NonzeroHom Y Z) := by
  constructor
  · rintro ⟨g, hgq⟩
    rcases hf.2.2 Y g q hgq with hgi | hqi
    · letI : IsIso g := hgi
      apply hinc.1
      refine ⟨unitRay g, ?_⟩
      dsimp only [unitRayNonzeroHom]
      rw [BGRSRayCategory.comp_unitRay,
        bgrsRayRepresentativeProduct_eq_comp_of_not_special
          (not_isBGRSSpecialZero_of_left_isIso g q hq0)]
      exact congrArg (unitRay : (X ⟶ Z) → UnitRayOrbit X Z) hgq
    · exact hq.2.1 hqi
  · rintro ⟨g, hgf⟩
    rcases hq.2.2 X g f hgf with hgi | hfi
    · letI : IsIso g := hgi
      apply hinc.2
      refine ⟨unitRay g, ?_⟩
      dsimp only [unitRayNonzeroHom]
      rw [BGRSRayCategory.comp_unitRay,
        bgrsRayRepresentativeProduct_eq_comp_of_not_special
          (not_isBGRSSpecialZero_of_left_isIso g f hf0)]
      exact congrArg (unitRay : (Y ⟶ Z) → UnitRayOrbit Y Z) hgf
    · exact hf.2.1 hfi

end LargeIndecomposable.ClosedZigzagTransfer
