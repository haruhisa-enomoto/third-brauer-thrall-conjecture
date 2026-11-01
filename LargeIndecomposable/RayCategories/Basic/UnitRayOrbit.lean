module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

/-!
# Two-sided unit orbits of morphisms

This file constructs the underlying sets of rays used in the BGRS ray
category.  Two morphisms with the same endpoints define the same unit ray when
they differ by invertible endomorphisms at the source and target.

Only the Hom-set quotient is constructed here.  In particular, it is not a
categorical quotient: composition in the BGRS ray category has a special zero
case and is not induced by ordinary composition of representatives.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v w

variable {C : Type u} [Category.{v} C]

/-- Two morphisms lie in the same two-sided orbit under invertible endpoint
endomorphisms.  This is the underlying equivalence relation defining a ray. -/
def UnitRayEquivalent {X Y : C} (f g : X ⟶ Y) : Prop :=
  ∃ (a : X ≅ X) (b : Y ≅ Y), g = a.hom ≫ f ≫ b.hom

/-- The equivalence relation of two-sided unit orbits on a Hom set. -/
def unitRaySetoid (X Y : C) : Setoid (X ⟶ Y) where
  r := UnitRayEquivalent
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro f
      exact ⟨Iso.refl X, Iso.refl Y, by simp⟩
    · intro f g h
      rcases h with ⟨a, b, rfl⟩
      refine ⟨a.symm, b.symm, ?_⟩
      simp [Category.assoc]
    · intro f g h hfg hgh
      rcases hfg with ⟨a, b, rfl⟩
      rcases hgh with ⟨c, d, rfl⟩
      refine ⟨c.trans a, b.trans d, ?_⟩
      simp [Category.assoc]

/-- The set of two-sided unit orbits in `X ⟶ Y`.

This is deliberately only a quotient type.  Its eventual BGRS composition is
not the quotient of ordinary categorical composition. -/
abbrev UnitRayOrbit (X Y : C) := Quotient (unitRaySetoid X Y)

/-- The two-sided unit orbit represented by a morphism. -/
def unitRay {X Y : C} (f : X ⟶ Y) : UnitRayOrbit X Y :=
  Quotient.mk'' f

/-- The orbit of the zero morphism. -/
def zeroUnitRay [HasZeroMorphisms C] (X Y : C) : UnitRayOrbit X Y :=
  unitRay (0 : X ⟶ Y)

instance unitRayOrbitZero [HasZeroMorphisms C] (X Y : C) :
    Zero (UnitRayOrbit X Y) :=
  ⟨zeroUnitRay X Y⟩

/-- Equality of unit rays is exactly two-sided unit equivalence. -/
theorem unitRay_eq_iff {X Y : C} (f g : X ⟶ Y) :
    unitRay f = unitRay g ↔ UnitRayEquivalent f g :=
  Quotient.eq''

/-- Every unit ray has a representative. -/
theorem unitRay_surjective (X Y : C) :
    Function.Surjective (unitRay : (X ⟶ Y) → UnitRayOrbit X Y) :=
  Quotient.mk_surjective

@[simp]
theorem unitRay_out {X Y : C} (r : UnitRayOrbit X Y) :
    unitRay r.out = r :=
  Quotient.out_eq' r

/-- A morphism represents the zero ray exactly when it is zero. -/
@[simp]
theorem unitRay_eq_zero_iff [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) :
    unitRay f = (0 : UnitRayOrbit X Y) ↔ f = 0 := by
  change unitRay f = unitRay (0 : X ⟶ Y) ↔ f = 0
  rw [unitRay_eq_iff]
  constructor
  · rintro ⟨a, b, h⟩
    have h' := congrArg (fun q ↦ a.inv ≫ q ≫ b.inv) h
    simpa [Category.assoc] using h'.symm
  · rintro rfl
    exact ⟨Iso.refl X, Iso.refl Y, by simp⟩

@[simp]
theorem zero_eq_unitRay_iff [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) :
    (0 : UnitRayOrbit X Y) = unitRay f ↔ f = 0 := by
  rw [eq_comm, unitRay_eq_zero_iff]

@[simp]
theorem unitRay_ne_zero_iff [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) :
    unitRay f ≠ (0 : UnitRayOrbit X Y) ↔ f ≠ 0 :=
  not_congr (unitRay_eq_zero_iff f)

/-- Every isomorphism endomorphism represents the identity ray. -/
theorem unitRay_eq_identity_of_isIso {X : C} (f : End X) [IsIso f] :
    unitRay f = unitRay (𝟙 X) := by
  rw [unitRay_eq_iff]
  refine ⟨Iso.refl X, (asIso f).symm, ?_⟩
  simp

/-- A functor preserves two-sided unit equivalence. -/
theorem unitRayEquivalent_map
    {D : Type w} [Category D] (F : C ⥤ D)
    {X Y : C} {f g : X ⟶ Y} (hfg : UnitRayEquivalent f g) :
    UnitRayEquivalent (F.map f) (F.map g) := by
  rcases hfg with ⟨a, b, rfl⟩
  refine ⟨F.mapIso a, F.mapIso b, ?_⟩
  simp only [Functor.map_comp]
  rfl

/-- A full faithful functor reflects two-sided unit equivalence. -/
theorem unitRayEquivalent_of_map_of_fullyFaithful
    {D : Type w} [Category D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f g : X ⟶ Y}
    (hfg : UnitRayEquivalent (F.map f) (F.map g)) :
    UnitRayEquivalent f g := by
  rcases hfg with ⟨a, b, hab⟩
  let aPre := F.preimageIso a
  let bPre := F.preimageIso b
  refine ⟨aPre, bPre, ?_⟩
  apply F.map_injective
  simpa [aPre, bPre, Functor.map_comp, Category.assoc] using hab

/-- A full faithful functor preserves and reflects two-sided unit
equivalence. -/
theorem unitRayEquivalent_map_iff_of_fullyFaithful
    {D : Type w} [Category D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f g : X ⟶ Y} :
    UnitRayEquivalent (F.map f) (F.map g) ↔ UnitRayEquivalent f g := by
  constructor
  · exact unitRayEquivalent_of_map_of_fullyFaithful F
  · exact unitRayEquivalent_map F

/-- Transporting both endpoints along isomorphisms preserves two-sided unit
equivalence. -/
theorem unitRayEquivalent_homCongr
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    {f g : X ⟶ Y} (hfg : UnitRayEquivalent f g) :
    UnitRayEquivalent (eX.inv ≫ f ≫ eY.hom)
      (eX.inv ≫ g ≫ eY.hom) := by
  rcases hfg with ⟨a, b, rfl⟩
  refine ⟨eX.symm ≪≫ a ≪≫ eX, eY.symm ≪≫ b ≪≫ eY, ?_⟩
  simp [Category.assoc]

/-- Endpoint transport preserves and reflects two-sided unit equivalence. -/
theorem unitRayEquivalent_homCongr_iff
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    {f g : X ⟶ Y} :
    UnitRayEquivalent (eX.inv ≫ f ≫ eY.hom)
        (eX.inv ≫ g ≫ eY.hom) ↔
      UnitRayEquivalent f g := by
  constructor
  · intro hfg
    have hback := unitRayEquivalent_homCongr eX.symm eY.symm hfg
    simpa using hback
  · exact unitRayEquivalent_homCongr eX eY

section Linear

variable (k : Type w) [Field k]
variable [Preadditive C] [Linear k C]

/-- The two-sided endomorphism multiples of a morphism. -/
def twoSidedEndomorphismMultiples {X Y : C} (f : X ⟶ Y) :
    Set (X ⟶ Y) :=
  {g | ∃ (a : End X) (b : End Y), g = (a ≫ f) ≫ b}

/-- The `k`-submodule generated by the two-sided endomorphism multiples of a
morphism.  This is the source's principal subbimodule `A_f`. -/
def twoSidedEndomorphismSpan {X Y : C} (f : X ⟶ Y) :
    Submodule k (X ⟶ Y) :=
  Submodule.span k (twoSidedEndomorphismMultiples f)

/-- A morphism belongs to its principal subbimodule. -/
theorem mem_twoSidedEndomorphismSpan {X Y : C} (f : X ⟶ Y) :
    f ∈ twoSidedEndomorphismSpan k f := by
  apply Submodule.subset_span
  exact ⟨𝟙 X, 𝟙 Y, by simp⟩

/-- The zero morphism generates the bottom principal subbimodule. -/
@[simp]
theorem twoSidedEndomorphismSpan_zero (X Y : C) :
    twoSidedEndomorphismSpan k (0 : X ⟶ Y) = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨a, b, rfl⟩
    simp
  · exact bot_le

/-- A principal subbimodule is bottom exactly for the zero generator. -/
@[simp]
theorem twoSidedEndomorphismSpan_eq_bot_iff {X Y : C} (f : X ⟶ Y) :
    twoSidedEndomorphismSpan k f = ⊥ ↔ f = 0 := by
  constructor
  · intro h
    have hf := mem_twoSidedEndomorphismSpan k f
    rw [h] at hf
    simpa using hf
  · rintro rfl
    exact twoSidedEndomorphismSpan_zero k X Y

/-- Unit-equivalent morphisms generate the same principal subbimodule. -/
theorem twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
    {X Y : C} {f g : X ⟶ Y} (h : UnitRayEquivalent f g) :
    twoSidedEndomorphismSpan k f = twoSidedEndomorphismSpan k g := by
  rcases h with ⟨u, v, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.2
    intro x hx
    rcases hx with ⟨a, b, rfl⟩
    apply Submodule.subset_span
    refine ⟨a ≫ u.inv, v.inv ≫ b, ?_⟩
    simp [Category.assoc]
  · apply Submodule.span_le.2
    intro x hx
    rcases hx with ⟨a, b, rfl⟩
    apply Submodule.subset_span
    refine ⟨a ≫ u.hom, v.hom ≫ b, ?_⟩
    simp [Category.assoc]

namespace UnitRayOrbit

/-- The principal subbimodule generated by a unit ray. -/
def twoSidedEndomorphismSpan {X Y : C} (r : UnitRayOrbit X Y) :
    Submodule k (X ⟶ Y) :=
  Quotient.liftOn' r (LargeIndecomposable.twoSidedEndomorphismSpan k)
    (fun _ _ h ↦ twoSidedEndomorphismSpan_eq_of_unitRayEquivalent k h)

@[simp]
theorem twoSidedEndomorphismSpan_unitRay {X Y : C} (f : X ⟶ Y) :
    (unitRay f).twoSidedEndomorphismSpan k =
      LargeIndecomposable.twoSidedEndomorphismSpan k f :=
  rfl

/-- The principal subbimodule of a unit ray is bottom exactly for the zero
ray. -/
@[simp]
theorem twoSidedEndomorphismSpan_eq_bot_iff {X Y : C}
    (r : UnitRayOrbit X Y) :
    r.twoSidedEndomorphismSpan k = ⊥ ↔ r = 0 := by
  induction r using Quotient.inductionOn' with
  | _ f =>
      change LargeIndecomposable.twoSidedEndomorphismSpan k f = ⊥ ↔
        unitRay f = 0
      rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_bot_iff,
        unitRay_eq_zero_iff]

end UnitRayOrbit

/-- The two source properties of a distributive category used to make the set
of rays finite: principal subbimodules classify unit rays, and those principal
subbimodules form a chain in every Hom space. -/
class HasClassifyingComparableUnitRaySpans
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] : Prop where
  span_injective : ∀ X Y : C, Function.Injective
    (UnitRayOrbit.twoSidedEndomorphismSpan (C := C) k :
      UnitRayOrbit X Y → Submodule k (X ⟶ Y))
  span_comparable : ∀ {X Y : C} (r s : UnitRayOrbit X Y),
    r.twoSidedEndomorphismSpan k ≤ s.twoSidedEndomorphismSpan k ∨
      s.twoSidedEndomorphismSpan k ≤ r.twoSidedEndomorphismSpan k

/-- A finite-dimensional Hom space has finitely many unit rays whenever
principal two-sided spans classify rays and form a chain. -/
theorem finite_unitRayOrbit_of_twoSidedEndomorphismSpan_injective_of_comparable
    {X Y : C} [Module.Finite k (X ⟶ Y)]
    (hinjective : Function.Injective
      (UnitRayOrbit.twoSidedEndomorphismSpan (C := C) k :
        UnitRayOrbit X Y → Submodule k (X ⟶ Y)))
    (hcomparable : ∀ r s : UnitRayOrbit X Y,
      r.twoSidedEndomorphismSpan k ≤ s.twoSidedEndomorphismSpan k ∨
        s.twoSidedEndomorphismSpan k ≤ r.twoSidedEndomorphismSpan k) :
    Finite (UnitRayOrbit X Y) := by
  let rankCode : UnitRayOrbit X Y →
      Fin (Module.finrank k (X ⟶ Y) + 1) :=
    fun r ↦ ⟨Module.finrank k (r.twoSidedEndomorphismSpan k),
      Nat.lt_succ_of_le (Submodule.finrank_le _)⟩
  apply Finite.of_injective rankCode
  intro r s hrs
  apply hinjective
  have hfinrank :
      Module.finrank k (r.twoSidedEndomorphismSpan k) =
        Module.finrank k (s.twoSidedEndomorphismSpan k) := by
    exact congrArg Fin.val hrs
  rcases hcomparable r s with hrs_le | hsr_le
  · exact Submodule.eq_of_le_of_finrank_eq hrs_le hfinrank
  · exact (Submodule.eq_of_le_of_finrank_eq hsr_le hfinrank.symm).symm

/-- Under the distributive source properties, a finite-dimensional Hom space
has a finite unit-ray orbit set. -/
theorem finite_unitRayOrbit_of_classifyingComparableSpans
    [HasClassifyingComparableUnitRaySpans k C]
    (X Y : C) [Module.Finite k (X ⟶ Y)] :
    Finite (UnitRayOrbit X Y) :=
  finite_unitRayOrbit_of_twoSidedEndomorphismSpan_injective_of_comparable k
    (HasClassifyingComparableUnitRaySpans.span_injective X Y)
    HasClassifyingComparableUnitRaySpans.span_comparable

end Linear

end LargeIndecomposable
