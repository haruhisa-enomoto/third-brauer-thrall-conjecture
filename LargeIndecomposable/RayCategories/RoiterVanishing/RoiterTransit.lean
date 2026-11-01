module

public import LargeIndecomposable.RayCategories.Distributive.DistributiveHomStructure
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-!
# Roiter's transit lemma

This file records the exact algebraic output of BGRS Section 1.5.  For a
composable pair `f : X ⟶ Y`, `g : Y ⟶ Z` with `f` prohibiting cotransit and
`g` prohibiting transit, Roiter's lemma says that one side kills the square of
the middle Jacobson radical.  Its stated consequence is that the space of
middle-endomorphism sandwiches has dimension at most one.

The class below isolates that source theorem while its mildness/cleaving proof
is constructed.  The remaining results in this file are unconditional linear
algebra consequences of its two literal conclusions.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- A nonzero composite obtained by inserting a Jacobson-radical
endomorphism between two fixed morphisms. -/
def HasNonzeroJacobsonSandwich
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∃ ρ : Ring.jacobson (End Y), (f ≫ ρ.1.asHom) ≫ g ≠ 0

/-- Nonvanishing of a radical sandwich depends only on the two endpoint unit
rays. -/
theorem hasNonzeroJacobsonSandwich_of_unitRayEquivalent
    {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : UnitRayEquivalent f f') (hg : UnitRayEquivalent g g')
    (h : HasNonzeroJacobsonSandwich f g) :
    HasNonzeroJacobsonSandwich f' g' := by
  rcases hf with ⟨a, b, rfl⟩
  rcases hg with ⟨c, d, rfl⟩
  rcases h with ⟨ρ, hρ⟩
  let bInv : End Y := End.of b.inv
  let cInv : End Y := End.of c.inv
  let ρ' : End Y := (cInv * ρ.1) * bInv
  have hρ' : ρ' ∈ Ring.jacobson (End Y) := by
    exact (Ring.jacobson (End Y)).mul_mem_right bInv
      ((Ring.jacobson (End Y)).mul_mem_left cInv ρ.2)
  refine ⟨⟨ρ', hρ'⟩, ?_⟩
  intro hzero
  have houter :
      (a.hom ≫ ((f ≫ ρ.1.asHom) ≫ g)) ≫ d.hom = 0 := by
    simpa only [ρ', bInv, cInv, End.mul_def, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] using hzero
  have hleft : a.hom ≫ ((f ≫ ρ.1.asHom) ≫ g) = 0 := by
    apply (cancel_mono d.hom).1
    simpa using houter
  apply hρ
  apply (cancel_epi a.hom).1
  simpa using hleft

/-- A zero pair in the same two rays as a pair carrying a nonzero radical
sandwich. -/
structure BGRSZeroPairRadicalSandwich
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) where
  left : X ⟶ Y
  right : Y ⟶ Z
  left_unitRayEquivalent : UnitRayEquivalent f left
  right_unitRayEquivalent : UnitRayEquivalent g right
  comp_eq_zero : left ≫ right = 0
  nonzero_sandwich : HasNonzeroJacobsonSandwich left right

namespace BGRSZeroPairRadicalSandwich

/-- The left morphism of such a zero pair cannot allow cotransit. -/
theorem left_not_allowsCotransit
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (D : BGRSZeroPairRadicalSandwich f g) :
    ¬AllowsCotransit D.left := by
  intro htransit
  rcases D.nonzero_sandwich with ⟨ρ, hρ⟩
  obtain ⟨a, ha⟩ := htransit ρ.1
  apply hρ
  rw [ha, Category.assoc, D.comp_eq_zero]
  simp

/-- The right morphism of such a zero pair cannot allow transit. -/
theorem right_not_allowsTransit
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (D : BGRSZeroPairRadicalSandwich f g) :
    ¬AllowsTransit D.right := by
  intro htransit
  rcases D.nonzero_sandwich with ⟨ρ, hρ⟩
  obtain ⟨b, hb⟩ := htransit ρ.1
  apply hρ
  rw [Category.assoc, hb, ← Category.assoc, D.comp_eq_zero]
  simp

end BGRSZeroPairRadicalSandwich

/-- The linear map whose range is the source's space `f A(Y,Y) g`. -/
def middleEndomorphismSandwich
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    End Y →ₗ[k] (X ⟶ Z) where
  toFun a := (f ≫ a.asHom) ≫ g
  map_add' a b := by
    change (f ≫ (a.asHom + b.asHom)) ≫ g =
      (f ≫ a.asHom) ≫ g + (f ≫ b.asHom) ≫ g
    rw [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c a := by
    change (f ≫ (c • a.asHom)) ≫ g =
      c • ((f ≫ a.asHom) ≫ g)
    rw [Linear.comp_smul, Linear.smul_comp]

@[simp]
theorem middleEndomorphismSandwich_apply
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (a : End Y) :
    middleEndomorphismSandwich (k := k) f g a =
      (f ≫ a.asHom) ≫ g :=
  rfl

/-- The left morphism kills the square of the middle Jacobson radical. -/
def LeftJacobsonSquareAnnihilates
    {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ a : End Y, a ∈ (Ring.jacobson (End Y)) ^ 2 → f ≫ a.asHom = 0

/-- The square of the middle Jacobson radical kills the right morphism. -/
def RightJacobsonSquareAnnihilates
    {Y Z : C} (g : Y ⟶ Z) : Prop :=
  ∀ a : End Y, a ∈ (Ring.jacobson (End Y)) ^ 2 → a.asHom ≫ g = 0

/-- The one-dimensional middle-sandwich consequence of Roiter's transit
lemma, isolated because this is the only part used by the critical-path
propagation in BGRS 4.2. -/
class HasRoiterTransitRankBound
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] : Prop where
  middle_finrank_le_one : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    ¬AllowsCotransit f → ¬AllowsTransit g →
      Module.finrank k (LinearMap.range
        (middleEndomorphismSandwich (k := k) f g)) ≤ 1

/-- The literal square-annihilation alternative in Roiter's transit lemma,
separated from its rank-one consequence so that the latter can be derived
from split-basic distributivity. -/
class HasRoiterTransitSquareAlternative
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] : Prop where
  square_alternative : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    ¬AllowsCotransit f → ¬AllowsTransit g →
      LeftJacobsonSquareAnnihilates f ∨
        RightJacobsonSquareAnnihilates g

/-- Roiter's transit lemma packaged with both its literal square alternative
and its stated rank consequence. -/
class HasRoiterTransitLemma
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] : Prop
    extends HasRoiterTransitRankBound k C,
      HasRoiterTransitSquareAlternative k C

/-- In a middle-sandwich space of dimension at most one, any fixed nonzero
sandwich spans every other middle-endomorphism composite. -/
theorem middleEndomorphismSandwich_eq_smul_of_finrank_le_one
    {X Y Z : C} [Module.Finite k (End Y)]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hrank : Module.finrank k (LinearMap.range
      (middleEndomorphismSandwich (k := k) f g)) ≤ 1)
    (a₀ : End Y)
    (ha₀ : middleEndomorphismSandwich (k := k) f g a₀ ≠ 0)
    (a : End Y) :
    ∃ c : k,
      middleEndomorphismSandwich (k := k) f g a =
        c • middleEndomorphismSandwich (k := k) f g a₀ := by
  let L := middleEndomorphismSandwich (k := k) f g
  let V := LinearMap.range L
  let x : V := ⟨L a₀, ⟨a₀, rfl⟩⟩
  let y : V := ⟨L a, ⟨a, rfl⟩⟩
  have hx : x ≠ 0 := by
    intro hzero
    apply ha₀
    exact congrArg Subtype.val hzero
  letI : Nontrivial V := nontrivial_iff.mpr ⟨x, 0, hx⟩
  have hpositive : 0 < Module.finrank k V := Module.finrank_pos
  have hrankV : Module.finrank k V ≤ 1 := by
    simpa [V, L] using hrank
  have hone : Module.finrank k V = 1 := by
    omega
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one hone hx y
  refine ⟨c, ?_⟩
  exact (congrArg Subtype.val hc).symm

/-- Cotransit moves a target-radical coefficient to a source-radical
coefficient across a nonzero morphism. -/
theorem exists_jacobson_left_of_allowsCotransit
    {X Y : C}
    [IsLocalRing (End X)] [IsDedekindFiniteMonoid (End X)]
    [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    {f : X ⟶ Y} (hf : f ≠ 0) (hC : AllowsCotransit f)
    (b : Ring.jacobson (End Y)) :
    ∃ a : Ring.jacobson (End X),
      f ≫ b.1.asHom = a.1.asHom ≫ f := by
  obtain ⟨a, ha⟩ := hC b.1
  have hbnu : ¬IsUnit b.1 :=
    (mem_ringJacobson_iff_not_isUnit (End Y) b.1).1 b.2
  have hanu : ¬IsUnit a :=
    not_isUnit_left_of_transfer hf a b.1 hbnu ha.symm
  exact ⟨⟨a,
    (mem_ringJacobson_iff_not_isUnit (End X) a).2 hanu⟩, ha⟩

/-- Transit moves a source-radical coefficient to a target-radical
coefficient across a nonzero morphism. -/
theorem exists_jacobson_right_of_allowsTransit
    {X Y : C}
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    [IsLocalRing (End Y)] [IsDedekindFiniteMonoid (End Y)]
    {f : X ⟶ Y} (hf : f ≠ 0) (hT : AllowsTransit f)
    (a : Ring.jacobson (End X)) :
    ∃ b : Ring.jacobson (End Y),
      a.1.asHom ≫ f = f ≫ b.1.asHom := by
  obtain ⟨b, hb⟩ := hT a.1
  have hanu : ¬IsUnit a.1 :=
    (mem_ringJacobson_iff_not_isUnit (End X) a.1).1 a.2
  have hbnu : ¬IsUnit b :=
    not_isUnit_right_of_transfer hf a.1 b hanu hb
  exact ⟨⟨b,
    (mem_ringJacobson_iff_not_isUnit (End Y) b).2 hbnu⟩, hb⟩

/-- Roiter's one-dimensional middle-sandwich conclusion, together with a
nonzero radical sandwich and nonvanishing of every invertible middle twist,
forces one of the two permissible transit behaviours. -/
theorem allowsCotransit_or_allowsTransit_of_roiter
    [HasRoiterTransitRankBound k C]
    {X Y Z : C} [Module.Finite k (End Y)]
    [IsLocalRing (End Y)] [IsDedekindFiniteMonoid (End Y)]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hsandwich : HasNonzeroJacobsonSandwich f g)
    (hunit : ∀ u : End Y, IsUnit u → (f ≫ u.asHom) ≫ g ≠ 0) :
    AllowsCotransit f ∨ AllowsTransit g := by
  by_cases hf : AllowsCotransit f
  · exact Or.inl hf
  right
  by_contra hg
  obtain ⟨ρ, hρ⟩ := hsandwich
  have hrank := HasRoiterTransitRankBound.middle_finrank_le_one
    (k := k) (C := C) f g hf hg
  obtain ⟨c, hc⟩ :=
    middleEndomorphismSandwich_eq_smul_of_finrank_le_one
      (k := k) f g hrank ρ.1 hρ (1 : End Y)
  let r : End Y := c • ρ.1
  have hr : r ∈ Ring.jacobson (End Y) := by
    dsimp [r]
    rw [Algebra.smul_def]
    exact (Ring.jacobson (End Y)).mul_mem_left _ ρ.2
  have hu : IsUnit (1 - r) := by
    have hrnu : ¬IsUnit r :=
      (mem_ringJacobson_iff_not_isUnit (End Y) r).1 hr
    have hneg : ¬IsUnit (-r) := by
      intro h
      exact hrnu (by simpa using h.neg)
    simpa [sub_eq_add_neg] using
      isUnit_one_add_of_not_isUnit (End Y) (-r) hneg
  apply hunit (1 - r) hu
  change (f ≫ ((𝟙 Y) - r.asHom)) ≫ g = 0
  rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp]
  apply sub_eq_zero.mpr
  calc
    f ≫ g = middleEndomorphismSandwich (k := k) f g (1 : End Y) := by
      simp [middleEndomorphismSandwich]
    _ = c • middleEndomorphismSandwich (k := k) f g ρ.1 := hc
    _ = (f ≫ r.asHom) ≫ g := by
      change c • ((f ≫ ρ.1.asHom) ≫ g) =
        (f ≫ (c • ρ.1.asHom)) ≫ g
      rw [Linear.comp_smul, Linear.smul_comp]

end LargeIndecomposable
