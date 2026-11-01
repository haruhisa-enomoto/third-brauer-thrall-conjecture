module

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid

/-!
# The free groupoid on a quiver is free

`Quiver.FreeGroupoid V` with generating arrows the arrows of `V` satisfies
`IsFreeGroupoid` (Mathlib's universal property against groups), by the
universal property of the free groupoid (`Quiver.FreeGroupoid.lift`). So its
vertex groups are free when it is connected (`IsFreeGroupoid.endIsFreeOfConnectedFree`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe u

variable {V : Type (u + 1)} [Quiver.{u + 1} V]

/-- The vertex of `V` underlying a generator. -/
def vert (a : IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) : V :=
  (show Quiver.FreeGroupoid V from a).as

/-- The generating quiver: the arrows of `V`. -/
abbrev genQuiver : Quiver.{u + 1} (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) where
  Hom a b := @Quiver.Hom V _ (vert a) (vert b)

/-- A generating arrow as an arrow of `V`. -/
def genArr {a b : IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)}
    (e : @Quiver.Hom _ genQuiver a b) : @Quiver.Hom V _ (vert a) (vert b) := e

/-- An arrow of `V` as a generating arrow. -/
def toGen {x y : V} (e : x ⟶ y) :
    @Quiver.Hom (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) genQuiver ⟨x⟩ ⟨y⟩ := e

instance isFreeGroupoid_freeGroupoid : IsFreeGroupoid (Quiver.FreeGroupoid V) where
  quiverGenerators := genQuiver
  of e := (Quiver.FreeGroupoid.of V).map (genArr e)
  unique_lift {X} _ f := by
    let φ : V ⥤q SingleObj X :=
      { obj := fun _ ↦ SingleObj.star X, map := fun e ↦ f (toGen e) }
    refine ⟨Quiver.FreeGroupoid.lift φ, fun a b e ↦ ?_, fun F hF ↦ ?_⟩
    · have := Quiver.FreeGroupoid.lift_spec φ
      exact congrArg (fun ψ : V ⥤q SingleObj X ↦ ψ.map (genArr e)) this
    · refine Quiver.FreeGroupoid.lift_unique φ F ?_
      refine Prefunctor.ext (fun _ ↦ rfl) fun x y e ↦ ?_
      exact hF ⟨x⟩ ⟨y⟩ (toGen e)

/-! ### Vertices and arrows in a universe of the form `u`, through `ULift` -/

section AnyUniverse

variable {V : Type u} [Quiver.{u} V]

/-- The quiver `V` with vertices and arrows lifted one universe. -/
def Up (V : Type u) : Type (u + 1) := ULift.{u + 1} V

instance : Quiver.{u + 1} (Up V) where
  Hom a b := ULift.{u + 1} ((a.down : V) ⟶ b.down)

/-- `V ⥤q Up V`. -/
def upQ : V ⥤q Up V where
  obj x := ULift.up x
  map e := ULift.up e

/-- `Up V ⥤q V`. -/
def downQ : Up V ⥤q V where
  obj x := x.down
  map e := e.down

lemma upQ_downQ : upQ (V := V) ⋙q downQ = 𝟭q V := rfl

lemma downQ_upQ : downQ (V := V) ⋙q upQ = 𝟭q (Up V) := rfl

/-- The free groupoids on `V` and `Up V` are equivalent. -/
def upEquiv : Quiver.FreeGroupoid V ≌ Quiver.FreeGroupoid (Up V) :=
  CategoryTheory.Equivalence.mk (Quiver.freeGroupoidFunctor upQ) (Quiver.freeGroupoidFunctor downQ)
    (eqToIso (by rw [← Quiver.freeGroupoidFunctor_comp, upQ_downQ,
      Quiver.freeGroupoidFunctor_id]))
    (eqToIso (by rw [← Quiver.freeGroupoidFunctor_comp, downQ_upQ,
      Quiver.freeGroupoidFunctor_id]))

/-- Vertex groups of a connected free groupoid are free (Nielsen–Schreier). -/
theorem isFreeGroup_end_freeGroupoid [IsConnected (Quiver.FreeGroupoid V)]
    (X : Quiver.FreeGroupoid V) : IsFreeGroup (End X) := by
  have : IsConnected (Quiver.FreeGroupoid (Up V)) := isConnected_of_equivalent upEquiv
  have : IsFreeGroup (End (upEquiv.functor.obj X)) := IsFreeGroupoid.endIsFreeOfConnectedFree _
  exact IsFreeGroup.ofMulEquiv (upEquiv.fullyFaithfulFunctor.mulEquivEnd X).symm

end AnyUniverse

/-! ### Vertices and arrows in two universes -/

section TwoUniverses

universe w

variable {V : Type u} [Quiver.{w} V]

/-- The quiver `V` with vertices and arrows lifted to `Type (max u w)`. -/
def Up₂ (V : Type u) : Type (max u w) := ULift.{w} V

instance : Quiver.{max u w} (Up₂.{u, w} V) where
  Hom a b := ULift.{u} ((a.down : V) ⟶ b.down)

/-- `V ⥤q Up₂ V`. -/
def upQ₂ : V ⥤q Up₂.{u, w} V where
  obj x := ULift.up x
  map e := ULift.up e

/-- `Up₂ V ⥤q V`. -/
def downQ₂ : Up₂.{u, w} V ⥤q V where
  obj x := x.down
  map e := e.down

lemma upQ₂_downQ₂ : upQ₂.{u, w} (V := V) ⋙q downQ₂ = 𝟭q V := rfl

lemma downQ₂_upQ₂ : downQ₂.{u, w} (V := V) ⋙q upQ₂ = 𝟭q (Up₂.{u, w} V) := rfl

/-- The free groupoids on `V` and `Up₂ V` are equivalent. -/
def upEquiv₂ : Quiver.FreeGroupoid V ≌ Quiver.FreeGroupoid (Up₂.{u, w} V) :=
  CategoryTheory.Equivalence.mk (Quiver.freeGroupoidFunctor upQ₂)
    (Quiver.freeGroupoidFunctor downQ₂)
    (eqToIso (by rw [← Quiver.freeGroupoidFunctor_comp, upQ₂_downQ₂,
      Quiver.freeGroupoidFunctor_id]))
    (eqToIso (by rw [← Quiver.freeGroupoidFunctor_comp, downQ₂_upQ₂,
      Quiver.freeGroupoidFunctor_id]))

/-- Vertex groups of a connected free groupoid are free (Nielsen–Schreier),
for vertices and arrows in any universes. -/
theorem isFreeGroup_end_freeGroupoid₂ [IsConnected (Quiver.FreeGroupoid V)]
    (X : Quiver.FreeGroupoid V) : IsFreeGroup (End X) := by
  have : IsConnected (Quiver.FreeGroupoid (Up₂.{u, w} V)) := isConnected_of_equivalent upEquiv₂
  have : IsFreeGroup (End (upEquiv₂.{u, w}.functor.obj X)) := isFreeGroup_end_freeGroupoid _
  exact IsFreeGroup.ofMulEquiv (upEquiv₂.fullyFaithfulFunctor.mulEquivEnd X).symm

end TwoUniverses

end LargeIndecomposable
