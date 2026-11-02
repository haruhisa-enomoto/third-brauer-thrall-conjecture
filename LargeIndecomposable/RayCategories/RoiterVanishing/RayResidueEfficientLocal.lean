module

public import LargeIndecomposable.RayCategories.Contours.ProperPathInterlacement
public import LargeIndecomposable.RayCategories.Contours.ContourClinging
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueCategory
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackle
public import LargeIndecomposable.RayCategories.Contours.RayPathInterlacement
public import Mathlib.Data.Fintype.Card
public import LargeIndecomposable.RayCategories.Basic.RayMorphismDepth
public import Mathlib.Data.Fin.Tuple.Take
@[expose] public section

/-!
# Efficient-tackle local corrections in a ray residue

Specialize the residue-ready sparse corrections to the last arrow of an
efficient hook or cohook tackle.  BGRS 8.4 supplies suffix or prefix
triviality, respectively; the easy `N = 2` branch additionally assumes that
this selected arrow belongs to no essential contour surviving the residue.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {k : Type*} [Field k]
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Every nonzero morphism between the objects represented by two ray vertices
has an irreducible-path presentation with exactly those vertices as its path
endpoints. -/
theorem exists_rayPathMap_eq_of_ne_zero
    [Finite C] [IsFiniteRayCategory C]
    {i j : RayVertex C} (f : j.obj ⟶ i.obj) (hf : f ≠ 0) :
    ∃ p : Quiver.Path i j, rayPathMap p = f := by
  let fNonzero : NonzeroHom j.obj i.obj := ⟨f, hf⟩
  obtain ⟨p⟩ := rayPathPresentation_nonempty_of_finite fNonzero
  cases i
  cases j
  exact ⟨p.path, p.map_eq⟩

def quiverArrowCast {Q : Type u} [Quiver.{v} Q]
    {i j i' j' : Q} (hi : i = i') (hj : j = j') (a : i ⟶ j) :
    i' ⟶ j' := by
  subst i'
  subst j'
  exact a

namespace BundledArrowOccurrence

end BundledArrowOccurrence

namespace RayHookTackle

end RayHookTackle

namespace RayCohookTackle

end RayCohookTackle

end LargeIndecomposable
