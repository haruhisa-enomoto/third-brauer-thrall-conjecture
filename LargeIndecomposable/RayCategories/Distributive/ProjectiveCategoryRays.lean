module

public import LargeIndecomposable.RayCategories.Distributive.SplitBasicPrimitiveIdempotents
public import LargeIndecomposable.RayCategories.Quotients.Residue
public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayCategory
public import LargeIndecomposable.RayCategories.RayTables.EndpointChains

/-!
# The projective category of split basic data in the multiplicative-bases language

`SplitBasicData.primitiveIdempotents` is the basic set of primitive idempotents of `S`;
`SplitBasicData.pidx` labels the objects of the projective category
`S.toIdempotents.ProjectiveCategory` (a morphism `X ⟶ Y` is an element of
`e_Y B e_X`). Morphism values lie in corners, automorphisms are corner units,
two-sided unit orbits are rays, and the radical of an endomorphism ring is the
corner radical.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory LargeIndecomposable

universe u

namespace SplitBasicData

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B] {ι : Type} [Fintype ι]
  [DecidableEq ι] (S : SplitBasicData k B ι)

/-- The idempotents of `S` as a basic set of primitive idempotents. -/
def primitiveIdempotents : PrimitiveIdempotents B where
  m := Fintype.card ι
  e i := S.e ((Fintype.equivFin ι).symm i)
  complete := (CompleteOrthogonalIdempotents.equiv (Fintype.equivFin ι).symm).2 S.complete
  primitive _ := S.isPrimitive _

/-- The label of an object of the projective category. -/
def pidx (X : S.toIdempotents.ProjectiveCategory) : Fin S.primitiveIdempotents.m :=
  Fintype.equivFin ι (S.toIdempotents.projectiveVertex X)

lemma primitiveIdempotents_e_pidx (X : S.toIdempotents.ProjectiveCategory) :
    S.primitiveIdempotents.e (S.pidx X) = S.e (S.toIdempotents.projectiveVertex X) := by
  simp [primitiveIdempotents, pidx]

lemma pidx_injective : Function.Injective S.pidx := fun _ _ h ↦
  S.toIdempotents.projectiveVertex_injective ((Fintype.equivFin ι).injective h)

/-- Every label is the label of an object. -/
lemma pidx_surjective : Function.Surjective S.pidx := fun i ↦
  ⟨S.toIdempotents.projectiveVertexEquiv.symm ((Fintype.equivFin ι).symm i), by
    simp only [pidx]
    rw [show ∀ v, S.toIdempotents.projectiveVertex (S.toIdempotents.projectiveVertexEquiv.symm v) = v from
      fun v ↦ S.toIdempotents.projectiveVertexEquiv.apply_symm_apply v]
    exact Equiv.apply_symm_apply _ _⟩

lemma val_eq {X Y : S.toIdempotents.ProjectiveCategory} (f : X ⟶ Y) :
    S.e (S.toIdempotents.projectiveVertex Y) * f.1 * S.e (S.toIdempotents.projectiveVertex X) = f.1 := by
  obtain ⟨a, ha⟩ := f.2
  change S.e (S.toIdempotents.projectiveVertex Y) * a * S.e (S.toIdempotents.projectiveVertex X) = f.1 at ha
  rw [← ha]
  simp only [← mul_assoc, S.e_mul_e]
  rw [mul_assoc _ (S.e _) (S.e _), S.e_mul_e]

variable [IsAlgClosed k] [FiniteDimensional k B]

lemma val_mem_corner {X Y : S.toIdempotents.ProjectiveCategory} (f : X ⟶ Y) :
    f.1 ∈ S.primitiveIdempotents.corner (k := k) (S.pidx Y) (S.pidx X) := by
  rw [PrimitiveIdempotents.mem_corner_iff', S.primitiveIdempotents_e_pidx, S.primitiveIdempotents_e_pidx]
  exact S.val_eq f

/-- An element of a corner as a morphism. -/
def ofCorner {X Y : S.toIdempotents.ProjectiveCategory} (a : B)
    (ha : a ∈ S.primitiveIdempotents.corner (k := k) (S.pidx Y) (S.pidx X)) : X ⟶ Y :=
  ⟨a, ⟨a, by
    have := (PrimitiveIdempotents.mem_corner_iff' (F := S.primitiveIdempotents)).1 ha
    rwa [S.primitiveIdempotents_e_pidx, S.primitiveIdempotents_e_pidx] at this⟩⟩

@[simp] lemma ofCorner_val {X Y : S.toIdempotents.ProjectiveCategory} (a : B)
    (ha : a ∈ S.primitiveIdempotents.corner (k := k) (S.pidx Y) (S.pidx X)) : (S.ofCorner a ha).1 = a := rfl

omit [IsAlgClosed k] [FiniteDimensional k B] in
lemma id_val' (X : S.toIdempotents.ProjectiveCategory) : (𝟙 X : X ⟶ X).1 = S.primitiveIdempotents.e (S.pidx X) := by
  rw [S.primitiveIdempotents_e_pidx]
  exact LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.id_val S.toIdempotents X

/-- **Automorphisms are corner units.** -/
lemma isCornerUnit_hom {X : S.toIdempotents.ProjectiveCategory} (a : X ≅ X) :
    S.primitiveIdempotents.IsCornerUnit (k := k) (S.pidx X) a.hom.1 := by
  refine ⟨S.val_mem_corner a.hom, a.inv.1, S.val_mem_corner a.inv, ?_, ?_⟩
  · have := congrArg Subtype.val a.inv_hom_id
    rwa [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val, S.id_val'] at this
  · have := congrArg Subtype.val a.hom_inv_id
    rwa [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val, S.id_val'] at this

/-- **Corner units are automorphisms.** -/
def isoOfCornerUnit {X : S.toIdempotents.ProjectiveCategory} {u : B}
    (hu : S.primitiveIdempotents.IsCornerUnit (k := k) (S.pidx X) u) : X ≅ X where
  hom := S.ofCorner u hu.1
  inv := S.ofCorner hu.2.choose hu.2.choose_spec.1
  hom_inv_id := by
    apply Subtype.ext
    rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val, S.id_val']
    exact hu.2.choose_spec.2.2
  inv_hom_id := by
    apply Subtype.ext
    rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val, S.id_val']
    exact hu.2.choose_spec.2.1

/-- **Two-sided unit orbits are rays.** -/
lemma unitRayEquivalent_iff {X Y : S.toIdempotents.ProjectiveCategory} (f g : X ⟶ Y) :
    LargeIndecomposable.UnitRayEquivalent f g ↔
      g.1 ∈ S.primitiveIdempotents.ray (k := k) (S.pidx Y) (S.pidx X) f.1 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨b.hom.1, a.hom.1, S.isCornerUnit_hom b, S.isCornerUnit_hom a, ?_⟩
    rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val,
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val, mul_assoc]
  · rintro ⟨u, w, hu, hw, hg⟩
    refine ⟨S.isoOfCornerUnit hw, S.isoOfCornerUnit hu, Subtype.ext ?_⟩
    rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val,
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val, hg]
    rfl

/-- **The radical of an endomorphism ring is the corner radical.** -/
lemma mem_jacobson_iff {X : S.toIdempotents.ProjectiveCategory} (ρ : End X) :
    ρ ∈ Ring.jacobson (End X) ↔ ρ.1 ∈ S.primitiveIdempotents.cornerRadical (k := k) (S.pidx X) := by
  rw [LargeIndecomposable.SplitBasicIdempotents.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  exact ⟨fun h ↦ ⟨S.val_mem_corner ρ, h⟩, fun h ↦ h.2⟩

end SplitBasicData

end LargeIndecomposable
