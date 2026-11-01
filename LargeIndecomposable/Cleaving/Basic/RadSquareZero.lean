module

public import LargeIndecomposable.Coverings.UniversalCover.Cover
public import LargeIndecomposable.Foundations.Group.FreeGroupoidFree
public import Mathlib.CategoryTheory.IsConnected

/-!
# Ray categories without long morphisms

If composites of two irreducible morphisms vanish (no long morphism; the
algebra has zero relations of length two), two paths with the same nonzero
value are equal, so the homotopy relation is trivial and the fundamental group
is the vertex group of the free groupoid on the quiver, a free group when the
quiver is connected (`RayCat.isFreeGroup_pi1_of_radSq`). This is the first case
of the proof of Theorem 2 of Bongartz, *Indecomposables live in all smaller
lengths*.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe u

namespace RayCat

variable {P : Type (u + 1)} [Category.{u + 1} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- Composites of two irreducible morphisms vanish. -/
def RadSq (P : Type (u + 1)) [Category.{u + 1} P] [HasZeroMorphisms P] : Prop :=
  ∀ {x y z : P} (f : x ⟶ y) (g : y ⟶ z), IsIrreducible f → IsIrreducible g → f ≫ g = 0

omit [IsRayCategory P] in
lemma pathVal_cons_cons (hr : RadSq P) {x w z y : RayVert P} (q : Quiver.Path x w) (e₁ : w ⟶ z)
    (e₂ : z ⟶ y) : pathVal ((q.cons e₁).cons e₂) = 0 := by
  change (pathVal q ≫ e₁.1) ≫ e₂.1 = 0
  rw [Category.assoc, hr e₁.1 e₂.1 e₁.2 e₂.2, comp_zero]

omit [IsRayCategory P] in
lemma pathVal_single {x y : RayVert P} (e : x ⟶ y) :
    pathVal ((Quiver.Path.nil : Quiver.Path x x).cons e) = e.1 :=
  Category.id_comp _

omit [IsRayCategory P] in
lemma not_id_eq {x : RayVert P} (e : x ⟶ x) : e.1 ≠ 𝟙 _ := by
  intro h
  apply e.2.2.1
  rw [h]; infer_instance

omit [IsRayCategory P] in
/-- Under `RadSq`, two paths with the same nonzero value are equal. -/
lemma path_eq_of_radSq (hr : RadSq P) {x : RayVert P} : ∀ {y : RayVert P} (p q : Quiver.Path x y),
    pathVal p = pathVal q → pathVal p ≠ 0 → p = q
  | _, .nil, .nil, _, _ => rfl
  | _, .nil, .cons .nil e, h, _ => absurd ((pathVal_single e).symm.trans h.symm) (not_id_eq e)
  | _, .nil, .cons (.cons q e₁) e₂, h, h0 => absurd (h.trans (pathVal_cons_cons hr q e₁ e₂)) h0
  | _, .cons .nil e, .nil, h, _ => absurd ((pathVal_single e).symm.trans h) (not_id_eq e)
  | _, .cons .nil e, .cons .nil e', h, _ => by
    rw [pathVal_single, pathVal_single] at h
    rw [Subtype.ext h]
  | _, .cons .nil e, .cons (.cons q e₁) e₂, h, h0 =>
    absurd (h.trans (pathVal_cons_cons hr q e₁ e₂)) h0
  | _, .cons (.cons p e₁) e₂, _, _, h0 => absurd (pathVal_cons_cons hr p e₁ e₂) h0

omit [IsRayCategory P] in
/-- Under `RadSq` the homotopy relation is equality. -/
lemma homotopy_eq (hr : RadSq P) {X Y : Quiver.FreeGroupoid (RayVert P)} {f g : X ⟶ Y}
    (h : homotopy f g) : f = g := by
  cases h with
  | path p q hpq h0 => rw [path_eq_of_radSq hr p q hpq h0]

omit [IsRayCategory P] in
lemma functor_map_injective (hr : RadSq P) {X Y : Quiver.FreeGroupoid (RayVert P)} :
    Function.Injective ((CategoryTheory.Quotient.functor (homotopy (P := P))).map (X := X) (Y := Y)) := by
  intro f g hfg
  have H : ∀ (X Y : Quiver.FreeGroupoid (RayVert P)) (f g : X ⟶ Y), homotopy f g →
      (𝟭 _).map f = (𝟭 _).map g := fun _ _ _ _ h ↦ homotopy_eq hr h
  have := congrArg (CategoryTheory.Quotient.lift homotopy (𝟭 _) H).map hfg
  rwa [CategoryTheory.Quotient.lift_map_functor_map, CategoryTheory.Quotient.lift_map_functor_map]
    at this

omit [IsRayCategory P] in
/-- Under `RadSq`, the vertex groups of the fundamental groupoid are those of
the free groupoid. -/
def endEquiv (hr : RadSq P) (X : Quiver.FreeGroupoid (RayVert P)) :
    End X ≃* End ((CategoryTheory.Quotient.functor (homotopy (P := P))).obj X) :=
  MulEquiv.ofBijective ((CategoryTheory.Quotient.functor homotopy).mapEnd X)
    ⟨functor_map_injective hr, fun g ↦
      (CategoryTheory.Quotient.functor homotopy).map_surjective g⟩

omit [IsRayCategory P] in
/-- Bongartz, Theorem 2, case of no long morphism: the fundamental group is
free when the quiver is connected. -/
theorem isFreeGroup_pi1_of_radSq (hr : RadSq P) [IsConnected (Quiver.FreeGroupoid (RayVert P))]
    (x₀ : P) : IsFreeGroup (Cover.Pi1 x₀) := by
  let X := (Quiver.FreeGroupoid.of (RayVert P)).obj (RayVert.mk x₀)
  have : IsFreeGroupoid (Quiver.FreeGroupoid (RayVert P)) := isFreeGroupoid_freeGroupoid
  have : IsFreeGroup (End X) := IsFreeGroupoid.endIsFreeOfConnectedFree X
  exact IsFreeGroup.ofMulEquiv ((endEquiv hr X).trans
    ((toUnits (G := End (vtx x₀))).trans (Aut.unitsEndEquivAut (vtx x₀))))

/-- `P` is connected: objects are linked by zigzags of nonzero morphisms. -/
def RayConnected (P : Type (u + 1)) [Category.{u + 1} P] [HasZeroMorphisms P] : Prop :=
  ∀ x y : P, Relation.EqvGen (fun a b : P ↦ ∃ f : a ⟶ b, f ≠ 0) x y

/-- A connected ray category has a connected free groupoid on its quiver. -/
lemma isConnected_freeGroupoid [Nonempty P] (hc : RayConnected P) :
    IsConnected (Quiver.FreeGroupoid (RayVert P)) := by
  have : Nonempty (Quiver.FreeGroupoid (RayVert P)) :=
    ⟨(Quiver.FreeGroupoid.of (RayVert P)).obj (RayVert.mk (Classical.arbitrary P))⟩
  refine zigzag_isConnected fun X Y ↦ ?_
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  have key : ∀ a b : P, Relation.EqvGen (fun a b : P ↦ ∃ f : a ⟶ b, f ≠ 0) a b →
      Nonempty (((Quiver.FreeGroupoid.of (RayVert P)).obj (RayVert.mk a)) ⟶
        ((Quiver.FreeGroupoid.of (RayVert P)).obj (RayVert.mk b))) := by
    intro a b h
    induction h with
    | rel a b h =>
      obtain ⟨f, hf⟩ := h
      obtain ⟨p, -⟩ := exists_path f hf
      exact ⟨pathFG p⟩
    | refl => exact ⟨𝟙 _⟩
    | symm a b _ ih => exact ⟨Groupoid.inv ih.some⟩
    | trans a b c _ _ ih ih' => exact ⟨ih.some ≫ ih'.some⟩
  exact Relation.ReflTransGen.single (Or.inl (key x y (hc x y)))

/-- Bongartz, Theorem 2, case of no long morphism, for a connected ray category. -/
theorem isFreeGroup_pi1_of_radSq_connected [Nonempty P] (hr : RadSq P) (hc : RayConnected P)
    (x₀ : P) : IsFreeGroup (Cover.Pi1 x₀) := by
  have := isConnected_freeGroupoid hc
  exact isFreeGroup_pi1_of_radSq hr x₀

end RayCat

end LargeIndecomposable
