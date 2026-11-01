module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Mat

@[expose] public section

/-!
# Linear structure on additive matrix categories

The additive envelope `CategoryTheory.Mat_ C` has pointwise scalar
multiplication on its Hom matrices.  This file records that composition is
linear in both variables when `C` is a linear category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace CategoryTheory.Mat_

universe u v w

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The additive matrix category of an `R`-linear category is `R`-linear,
with pointwise scalar multiplication on Hom matrices. -/
instance linear : Linear R (Mat_ C) where
  homModule M N :=
    Pi.module M.ι (fun i ↦ ∀ j : N.ι, M.X i ⟶ N.X j) R
  smul_comp _ _ _ r f g := by
    ext i j
    change (∑ a, (r • f i a) ≫ g a j) = r • ∑ a, f i a ≫ g a j
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact Linear.smul_comp _ _ _ r (f i a) (g a j)
  comp_smul _ _ _ f r g := by
    ext i j
    change (∑ a, f i a ≫ (r • g a j)) = r • ∑ a, f i a ≫ g a j
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact Linear.comp_smul _ _ _ (f i a) r (g a j)

end CategoryTheory.Mat_
