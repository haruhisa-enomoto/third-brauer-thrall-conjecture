module

public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Compatibility for ported LargeIndecomposable.Foundations files

LargeIndecomposable.Foundations's Mathlib has `End.linearEquiv : End X ≃ₗ[R] (X ⟶ X)`; the Mathlib
pinned here does not, and `End X` is definitionally `X ⟶ X`.
-/

@[expose] public section

namespace CategoryTheory.End

universe v u

variable {C : Type u} [CategoryStruct.{v} C] {X : C}

/-- `End X` and `X ⟶ X` as modules. -/
def linearEquiv {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Semiring R]
    [Linear R C] {X : C} : End X ≃ₗ[R] (X ⟶ X) := LinearEquiv.refl R (X ⟶ X)

end CategoryTheory.End
