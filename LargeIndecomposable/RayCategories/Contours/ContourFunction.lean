module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Tactic.Group
@[expose] public section

/-!
# Contour functions and their cohomological vanishing target

Restrict raw scalar assignments on parallel path pairs to the subgroup
satisfying the contour-function laws: transitivity through parallel paths and
invariance under common path whiskers.  The arrow-weight coboundary lands in
this subgroup.  Surjectivity onto it is the precise formal target of Roiter's
contour-cohomology vanishing theorem.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- A symmetric, transitive relation on parallel quiver paths.  It is allowed
to be non-reflexive: in ray-category applications `related p p` expresses
that `p` has nonzero image. -/
structure PathContourRelation (Q : Type v) [Quiver.{w} Q] where
  related : ∀ {i j : Q}, Quiver.Path i j → Quiver.Path i j → Prop
  symm' : ∀ {i j : Q} {p q : Quiver.Path i j}, related p q → related q p
  trans' : ∀ {i j : Q} {p q r : Quiver.Path i j},
    related p q → related q r → related p r

namespace PathContourRelation

variable (R : PathContourRelation Q)

theorem symm {i j : Q} {p q : Quiver.Path i j}
    (h : R.related p q) : R.related q p :=
  R.symm' h

theorem trans {i j : Q} {p q r : Quiver.Path i j}
    (hpq : R.related p q) (hqr : R.related q r) : R.related p r :=
  R.trans' hpq hqr

end PathContourRelation

variable {D : Type z} [CategoryTheory.Category D] [CategoryTheory.Preadditive D]
  [CategoryTheory.Linear k D]

end LargeIndecomposable
