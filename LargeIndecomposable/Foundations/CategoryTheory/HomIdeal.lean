module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.CategoryTheory.Preadditive.Basic

set_option backward.isDefEq.respectTransparency.types false

/-!
# Additive ideals in preadditive categories

This file contains the lightweight two-sided Hom-ideal structure shared by
categorical quotients and radical-power arguments.
-/

@[expose] public section

open CategoryTheory

namespace LargeIndecomposable.CategoricalIdeal

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- A two-sided additive ideal in a preadditive category. -/
structure HomIdeal where
  hom : ∀ X Y : C, AddSubgroup (X ⟶ Y)
  precomp :
    ∀ {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z},
      g ∈ hom Y Z → f ≫ g ∈ hom X Z
  postcomp :
    ∀ {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z),
      f ∈ hom X Y → f ≫ g ∈ hom X Z

end LargeIndecomposable.CategoricalIdeal
