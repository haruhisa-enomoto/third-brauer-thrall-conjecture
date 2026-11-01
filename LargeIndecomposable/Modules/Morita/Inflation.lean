module

public import LargeIndecomposable.Modules.Corners.Corner
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import LargeIndecomposable.Modules.Duality.DimensionBasics
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Inflation along quotient maps and central idempotents

For a surjective ring homomorphism `π : B → C`, inflation
`ModuleCat.restrictScalars π : Mod C ⥤ Mod B` is fully faithful
(`restrictScalars_full`); for a `k`-algebra map it is `k`-linear and keeps the
underlying `k`-vector space (`dim_restrictScalars`).

-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

namespace Reduction

variable {B C : Type u} [Ring B] [Ring C]

/-- Inflation along a surjective ring homomorphism is full. -/
theorem restrictScalars_full {π : B →+* C} (hπ : Function.Surjective π) :
    (ModuleCat.restrictScalars.{u} π).Full where
  map_surjective {X Y} g := ⟨ModuleCat.ofHom
    { toFun := g.hom
      map_add' := g.hom.map_add
      map_smul' := fun c x ↦ by
        obtain ⟨b, rfl⟩ := hπ c
        exact g.hom.map_smul b x }, rfl⟩

variable (k : Type u) [Field k] [Algebra k B] [Algebra k C]

/-- Inflation along a `k`-algebra map is `k`-linear. -/
theorem restrictScalars_linear (π : B →ₐ[k] C) :
    (ModuleCat.restrictScalars.{u} π.toRingHom).Linear k where
  map_smul {M N} g c := by
    ext m
    exact congr_arg (· • g.hom m) (π.commutes c).symm

/-- The underlying `k`-space does not change under inflation. -/
def restrictScalarsLinearEquiv (π : B →ₐ[k] C) (M : ModuleCat.{u} C) :
    RestrictScalars k B ((ModuleCat.restrictScalars.{u} π.toRingHom).obj M) ≃ₗ[k]
      RestrictScalars k C M where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' c m := by
    change π (algebraMap k B c) • (show M from m) = algebraMap k C c • (show M from m)
    rw [π.commutes]
  left_inv _ := rfl
  right_inv _ := rfl

theorem dim_restrictScalars (π : B →ₐ[k] C) (M : ModuleCat.{u} C) :
    dim k B ((ModuleCat.restrictScalars.{u} π.toRingHom).obj M) = dim k C M :=
  (restrictScalarsLinearEquiv k π M).rank_eq

end Reduction

end LargeIndecomposable
