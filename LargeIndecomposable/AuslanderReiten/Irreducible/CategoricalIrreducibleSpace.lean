module

public import LargeIndecomposable.Foundations.CategoryTheory.HomIdealComap
public import LargeIndecomposable.Foundations.CategoryTheory.CategoricalRadicalIdeal
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option backward.isDefEq.respectTransparency.types false

/-! # The intrinsic linear space of irreducible morphisms -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory

open LargeIndecomposable.CategoricalRadical
namespace LargeIndecomposable.CategoricalIrreducible
universe u v w
variable (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- The intrinsic categorical radical as a linear subspace. -/
def radical (X Y : C) : Submodule k (X ⟶ Y) := MorphismIdeal.homSubmodule homIdeal X Y

/-- The square of the intrinsic radical as a linear subspace. -/
def radicalSquare (X Y : C) : Submodule k (X ⟶ Y) :=
  MorphismIdeal.homSubmodule (homIdeal ⋆ᵢ homIdeal) X Y

/-- The radical-square denominator inside the radical numerator. -/
def denominator (X Y : C) : Submodule k (radical k X Y) :=
  (radicalSquare k X Y).comap (radical k X Y).subtype

/-- The standard quotient `rad(X,Y) / rad²(X,Y)` in a linear category. -/
abbrev Space (X Y : C) := (radical k X Y) ⧸ denominator k X Y

/-- The irreducible quotient cannot have dimension larger than its Hom space. -/
theorem finrank_le_hom (X Y : C) [FiniteDimensional k (X ⟶ Y)] :
    Module.finrank k (Space k X Y) ≤ Module.finrank k (X ⟶ Y) :=
  (Submodule.finrank_quotient_le (denominator k X Y)).trans (Submodule.finrank_le _)

end LargeIndecomposable.CategoricalIrreducible
