module

public import LargeIndecomposable.RayCategories.Contours.ContourFunction
@[expose] public section

/-!
# Interlacement classes and Roiter clinging

Package the source-faithful global interface in BGRS, Section 8.3.  A contour
function clings at a source when every pair of related paths admits
representatives in the same respective interlacement classes on which the
contour value is one.  If clinging at every source detects the identity and a
local exact correction adds one source while preserving previous ones, finite
source induction gives contour-cohomology vanishing.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- An equivalence relation on parallel paths representing the
interlacement classes inside every nonzero ray.  Compatibility with a
particular ray-category realization is intentionally kept separate. -/
structure PathInterlacementRelation
    (R : PathContourRelation Q) where
  interlaced : ∀ {i j : Q},
    Quiver.Path i j → Quiver.Path i j → Prop
  refl' : ∀ {i j : Q} (p : Quiver.Path i j), interlaced p p
  symm' : ∀ {i j : Q} {p q : Quiver.Path i j},
    interlaced p q → interlaced q p
  trans' : ∀ {i j : Q} {p q r : Quiver.Path i j},
    interlaced p q → interlaced q r → interlaced p r

namespace PathInterlacementRelation

variable {R : PathContourRelation Q}

theorem refl (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) : I.interlaced p p :=
  I.refl' p

theorem symm (I : PathInterlacementRelation R)
    {i j : Q} {p q : Quiver.Path i j}
    (h : I.interlaced p q) : I.interlaced q p :=
  I.symm' h

theorem trans (I : PathInterlacementRelation R)
    {i j : Q} {p q r : Quiver.Path i j}
    (hpq : I.interlaced p q) (hqr : I.interlaced q r) :
    I.interlaced p r :=
  I.trans' hpq hqr

end PathInterlacementRelation

end LargeIndecomposable
