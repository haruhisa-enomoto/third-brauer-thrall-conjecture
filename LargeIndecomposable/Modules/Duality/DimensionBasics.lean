module

public import LargeIndecomposable.Statement
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Dimensions of modules over a finite-dimensional algebra

Helpers for `Statement.dim`: `A`-linear isomorphisms preserve the
`k`-dimension, and over a finite-dimensional algebra a module is finitely
generated exactly when it is finite-dimensional.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement

universe u

namespace Reduction

variable (k : Type u) [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- An `A`-linear map as a `k`-linear map of the restricted modules. -/
def restrictScalarsMap {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) : RestrictScalars k A M →ₗ[k] RestrictScalars k A N where
  toFun x := f x
  map_add' x y := f.map_add x y
  map_smul' c x := f.map_smul (algebraMap k A c) x

/-- An `A`-linear equivalence as a `k`-linear equivalence of the restricted modules. -/
def restrictScalarsEquiv {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (f : M ≃ₗ[A] N) : RestrictScalars k A M ≃ₗ[k] RestrictScalars k A N where
  __ := restrictScalarsMap k f.toLinearMap
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv

theorem dim_eq_of_iso {M N : ModuleCat.{u} A} (i : M ≅ N) : dim k A M = dim k A N :=
  (restrictScalarsEquiv k i.toLinearEquiv).rank_eq

theorem finite_of_iso {M N : ModuleCat.{u} A} (i : M ≅ N)
    [Module.Finite k (RestrictScalars k A M)] : Module.Finite k (RestrictScalars k A N) :=
  Module.Finite.equiv (restrictScalarsEquiv k i.toLinearEquiv)

attribute [local instance] RestrictScalars.moduleOrig in
/-- Finitely generated modules over a finite-dimensional algebra are finite-dimensional. -/
theorem finite_restrictScalars [FiniteDimensional k A] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] : Module.Finite k (RestrictScalars k A M) := by
  have : Module.Finite A (RestrictScalars k A M) := ‹Module.Finite A M›
  exact Module.Finite.trans A (RestrictScalars k A M)

attribute [local instance] RestrictScalars.moduleOrig in
/-- Finite-dimensional modules are finitely generated. -/
theorem finite_of_finite_restrictScalars (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite k (RestrictScalars k A M)] : Module.Finite A M :=
  Module.Finite.of_restrictScalars_finite k A (RestrictScalars k A M)

end Reduction

end LargeIndecomposable
