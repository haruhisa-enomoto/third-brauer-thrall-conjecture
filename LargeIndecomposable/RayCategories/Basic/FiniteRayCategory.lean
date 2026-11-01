module

public import LargeIndecomposable.RayCategories.Contours.ContourFunction
public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift

@[expose] public section

/-!
# Finite ray categories and their irreducible path relation

Record the source-level axioms of a finite ray category and construct the
quiver whose reversed arrows are irreducible morphisms.  Parallel paths are
related when they evaluate to the same nonzero ray morphism.  This relation is
the combinatorial contour relation used in the BGRS tackle argument; it is not
identified here with scalar proportionality in a linear realization.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The distinguished zero endomorphism supplied by zero morphisms. -/
instance categoryEndZero {X : C} : Zero (End X) :=
  ⟨(0 : X ⟶ X)⟩

/-- Endomorphism composition is absorbing at the categorical zero. -/
instance categoryEndMonoidWithZero {X : C} : MonoidWithZero (End X) where
  toMonoid := inferInstance
  zero := (0 : X ⟶ X)
  zero_mul a := by
    change a ≫ 0 = 0
    simp
  mul_zero a := by
    change 0 ≫ a = 0
    simp

/-- A morphism is irreducible when it is nonzero, noninvertible, and every
two-step factorization has an invertible factor. -/
def IsIrreducibleRayMorphism {X Y : C} (f : X ⟶ Y) : Prop :=
  f ≠ 0 ∧ ¬IsIso f ∧
    ∀ (Z : C) (g : X ⟶ Z) (h : Z ⟶ Y),
      g ≫ h = f → IsIso g ∨ IsIso h

/-- Postcomposition by an isomorphism preserves irreducibility. -/
theorem IsIrreducibleRayMorphism.comp_isIso
    {X Y Z : C} {f : X ⟶ Y} (hf : IsIrreducibleRayMorphism f)
    (e : Y ⟶ Z) [IsIso e] :
    IsIrreducibleRayMorphism (f ≫ e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hf.1
    have hcomp := congrArg (fun q ↦ q ≫ inv e) hzero
    simpa [Category.assoc] using hcomp
  · intro hIso
    letI : IsIso (f ≫ e) := hIso
    exact hf.2.1 ((isIso_comp_right_iff f e).1 inferInstance)
  · intro W a b hab
    have hab' : a ≫ (b ≫ inv e) = f := by
      rw [← Category.assoc, hab, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    rcases hf.2.2 W a (b ≫ inv e) hab' with ha | hb
    · exact Or.inl ha
    · letI : IsIso (b ≫ inv e) := hb
      exact Or.inr ((isIso_comp_right_iff b (inv e)).1 inferInstance)

/-- `g` lies above `f` in the two-sided endomorphism factorization order. -/
def TwoSidedEndomorphismFactors {X Y : C} (f g : X ⟶ Y) : Prop :=
  ∃ (a : End X) (b : End Y), g = (a ≫ f) ≫ b

/-- Source-faithful finite form of the ray-category axioms in BGRS 1.7.

Finiteness of the object type is kept as a separate `Finite C` assumption,
since several abstract lemmas only need the local axioms below. -/
class IsFiniteRayCategory (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  id_ne_zero : ∀ X : C, 𝟙 X ≠ 0
  hom_finite : ∀ X Y : C, Finite (X ⟶ Y)
  endomorphism_nilpotent : ∀ {X : C} (f : End X),
    f ≠ 𝟙 X → ∃ n : ℕ, (0 : ℕ) < n ∧ f ^ n = (0 : End X)
  skeletal : ∀ {X Y : C}, Nonempty (X ≅ Y) → X = Y
  factorization_comparable : ∀ {X Y : C} (f g : X ⟶ Y),
    TwoSidedEndomorphismFactors f g ∨
      TwoSidedEndomorphismFactors g f
  source_stabilizer_trivial : ∀ {X Y Z : C}
      (f : X ⟶ Y) (g : Y ⟶ Z) (a : End X),
    f ≫ g ≠ 0 → (a ≫ f) ≫ g = f ≫ g → a = 𝟙 X

/-- The basic ray axioms, without comparability of factorizations. The reduction machinery
(Fischbacher's Lemmas 2.1 and 2.2) needs only these. -/
class IsFiniteRayCategory0 (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  id_ne_zero : ∀ X : C, 𝟙 X ≠ 0
  hom_finite : ∀ X Y : C, Finite (X ⟶ Y)
  endomorphism_nilpotent : ∀ {X : C} (f : End X),
    f ≠ 𝟙 X → ∃ n : ℕ, (0 : ℕ) < n ∧ f ^ n = (0 : End X)
  skeletal : ∀ {X Y : C}, Nonempty (X ≅ Y) → X = Y

instance (priority := 100) IsFiniteRayCategory.toIsFiniteRayCategory0 [IsFiniteRayCategory C] :
    IsFiniteRayCategory0 C where
  id_ne_zero := IsFiniteRayCategory.id_ne_zero
  hom_finite := IsFiniteRayCategory.hom_finite
  endomorphism_nilpotent := IsFiniteRayCategory.endomorphism_nilpotent
  skeletal := IsFiniteRayCategory.skeletal

/-- An invertible endomorphism in a ray category is the identity. -/
theorem ray_endomorphism_eq_id_of_isIso [IsFiniteRayCategory C]
    {X : C} (a : End X) [IsIso a] : a = 𝟙 X := by
  by_contra ha
  obtain ⟨n, -, han⟩ :=
    IsFiniteRayCategory.endomorphism_nilpotent a ha
  letI : Nontrivial (End X) :=
    ⟨⟨(𝟙 X : End X), 0, IsFiniteRayCategory.id_ne_zero X⟩⟩
  have ha_unit : IsUnit a := (isUnit_iff_isIso a).2 inferInstance
  have hpow_unit : IsUnit (a ^ n) := ha_unit.pow n
  rw [han] at hpow_unit
  exact not_isUnit_zero hpow_unit

/-- Every isomorphism in a skeletal ray category is the equality isomorphism
for some equality of its endpoints. -/
theorem ray_isIso_eq_eqToHom [IsFiniteRayCategory C]
    {X Y : C} (f : X ⟶ Y) [IsIso f] :
    ∃ h : X = Y, f = eqToHom h := by
  have hXY : X = Y :=
    IsFiniteRayCategory.skeletal ⟨asIso f⟩
  subst Y
  refine ⟨rfl, ?_⟩
  change (End.of f : End X) = (𝟙 X : End X)
  exact ray_endomorphism_eq_id_of_isIso f

/-- A nonzero ray morphism cannot be fixed by a nonidentity endomorphism at
its target.  This is the right-hand cancellation consequence used in BGRS
1.13(d). -/
theorem ray_right_stabilizer_trivial [IsFiniteRayCategory0 C]
    {X Y : C} (f : X ⟶ Y) (a : End Y)
    (hf : f ≠ 0) (hfa : f ≫ a = f) : a = 𝟙 Y := by
  by_contra ha
  obtain ⟨n, -, han⟩ :=
    IsFiniteRayCategory0.endomorphism_nilpotent a ha
  have hpow : ∀ m : ℕ, f ≫ a ^ m = f := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        simp only [pow_succ, End.mul_def, ← Category.assoc, hfa, ih]
  have hf_zero : f = 0 := by
    have hanHom : End.asHom (a ^ n) = (0 : Y ⟶ Y) := han
    have hcomp : f ≫ End.asHom (a ^ n) = 0 := by
      rw [hanHom, comp_zero]
    exact (hpow n).symm.trans hcomp
  exact hf hf_zero

/-- The left-hand stabilizer axiom in the form needed for cancellation. -/
theorem ray_left_stabilizer_trivial [IsFiniteRayCategory C]
    {X Y : C} (f : X ⟶ Y) (a : End X)
    (hf : f ≠ 0) (haf : a ≫ f = f) : a = 𝟙 X := by
  apply IsFiniteRayCategory.source_stabilizer_trivial f (𝟙 Y) a
  · simpa using hf
  · simpa using haf

/-- An isomorphism in a ray category is nonzero. -/
theorem ray_isIso_ne_zero [IsFiniteRayCategory0 C]
    {X Y : C} (f : X ⟶ Y) [IsIso f] : f ≠ 0 := by
  intro hf
  haveI : IsIso (0 : X ⟶ Y) := hf ▸ inferInstance
  have hzero_id : (0 : X ⟶ X) = 𝟙 X := by
    have hzero_comp :
        (0 : X ⟶ Y) ≫ inv (0 : X ⟶ Y) = (0 : X ⟶ X) := by
      exact Limits.zero_comp
    exact hzero_comp.symm.trans (IsIso.hom_inv_id (0 : X ⟶ Y))
  exact IsFiniteRayCategory0.id_ne_zero X hzero_id.symm

/-- In a ray category, both factors of an isomorphism are isomorphisms. -/
theorem ray_isIso_factors [IsFiniteRayCategory0 C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso (f ≫ g)] :
    IsIso f ∧ IsIso g := by
  let r : Y ⟶ X := g ≫ inv (f ≫ g)
  let a : End Y := r ≫ f
  have hf : f ≠ 0 := by
    intro hf
    apply ray_isIso_ne_zero (f ≫ g)
    rw [hf, zero_comp]
  have hfa : f ≫ a = f := by
    dsimp [a, r]
    rw [← Category.assoc, ← Category.assoc, IsIso.hom_inv_id,
      Category.id_comp]
  have ha : a = 𝟙 Y :=
    ray_right_stabilizer_trivial f a hf hfa
  have hfr : f ≫ r = 𝟙 X := by
    dsimp [r]
    rw [← Category.assoc, IsIso.hom_inv_id]
  let l : Z ⟶ Y := inv (f ≫ g) ≫ f
  have haHom : (g ≫ inv (f ≫ g)) ≫ f = 𝟙 Y := by
    change (End.of ((g ≫ inv (f ≫ g)) ≫ f) : End Y) =
      (𝟙 Y : End Y)
    exact ha
  have hgl : g ≫ l = 𝟙 Y := by
    dsimp [l]
    rw [← Category.assoc]
    exact haHom
  have hlg : l ≫ g = 𝟙 Z := by
    dsimp [l]
    rw [Category.assoc, IsIso.inv_hom_id]
  exact ⟨⟨⟨r, hfr, ha⟩⟩, ⟨⟨l, hgl, hlg⟩⟩⟩

/-- A wrapper for the objects of a category, used to install the reversed
irreducible-morphism quiver without conflicting with the category's own
underlying quiver. -/
@[ext]
structure RayVertex (C : Type u) where
  obj : C

/-- Ray vertices are equivalent to the original category objects. -/
def rayVertexEquiv : RayVertex C ≃ C where
  toFun := RayVertex.obj
  invFun := RayVertex.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- The reversed irreducible quiver of a category with zero morphisms.  An
arrow `i ⟶ j` represents an irreducible category morphism `j.obj ⟶ i.obj`,
matching the reversed path convention used by the Auslander realization. -/
instance rayVertexQuiver : Quiver.{v} (RayVertex C) where
  Hom i j := {f : j.obj ⟶ i.obj // IsIrreducibleRayMorphism f}

/-- The category morphism represented by a reversed ray-quiver arrow. -/
def rayArrowMorphism {i j : RayVertex C} (a : i ⟶ j) :
    j.obj ⟶ i.obj :=
  a.1

/-- Evaluate a reversed irreducible path in the underlying category. -/
abbrev rayPathMap {i j : RayVertex C} (p : Quiver.Path i j) :
    j.obj ⟶ i.obj :=
  LinearPathCategory.pathMap RayVertex.obj rayArrowMorphism p

/-- A one-arrow ray path evaluates to its represented irreducible morphism. -/
@[simp]
theorem rayPathMap_toPath {i j : RayVertex C} (a : i ⟶ j) :
    rayPathMap (Quiver.Hom.toPath a) = rayArrowMorphism a := by
  simp [rayPathMap, Quiver.Hom.toPath]

/-- Two parallel irreducible paths form a ray contour when they evaluate to
the same nonzero morphism of the ray category. -/
def rayPathContourRelation : PathContourRelation (RayVertex C) where
  related := fun p q ↦ rayPathMap p ≠ 0 ∧ rayPathMap p = rayPathMap q
  symm' := by
    intro i j p q hpq
    refine ⟨?_, hpq.2.symm⟩
    rw [← hpq.2]
    exact hpq.1
  trans' := by
    intro i j p q r hpq hqr
    exact ⟨hpq.1, hpq.2.trans hqr.2⟩

/-- Self-related ray paths are exactly the paths with nonzero evaluation. -/
theorem rayPathContourRelation_related_self_iff
    {i j : RayVertex C} (p : Quiver.Path i j) :
    (rayPathContourRelation (C := C)).related p p ↔ rayPathMap p ≠ 0 := by
  simp [rayPathContourRelation]

/-- Unpack the concrete equal-nonzero definition of a ray contour. -/
theorem rayPathContourRelation_related_iff
    {i j : RayVertex C} (p q : Quiver.Path i j) :
    (rayPathContourRelation (C := C)).related p q ↔
      rayPathMap p ≠ 0 ∧ rayPathMap p = rayPathMap q := by
  rfl

/-- Equality of nonzero path evaluations is stable under a common context
whenever the resulting outer evaluation remains nonzero. -/
theorem rayPathContourRelation_whisker
    {a i j b : RayVertex C} (s : Quiver.Path a i)
    (p q : Quiver.Path i j) (t : Quiver.Path j b)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (houter : rayPathMap ((s.comp p).comp t) ≠ 0) :
    (rayPathContourRelation (C := C)).related
      ((s.comp p).comp t) ((s.comp q).comp t) := by
  refine ⟨houter, ?_⟩
  simp only [rayPathMap, LinearPathCategory.pathMap_comp]
  have heq := hpq.2
  change LinearPathCategory.pathMap RayVertex.obj rayArrowMorphism p =
    LinearPathCategory.pathMap RayVertex.obj rayArrowMorphism q at heq
  rw [heq]

end LargeIndecomposable
