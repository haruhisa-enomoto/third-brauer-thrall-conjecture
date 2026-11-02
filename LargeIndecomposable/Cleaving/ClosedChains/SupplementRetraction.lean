module

public import LargeIndecomposable.Cleaving.ClosedChains.ThinPathRetraction
public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueCategory
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackle
public import Mathlib.Data.Fintype.Card
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import LargeIndecomposable.Cleaving.ClosedChains.ArrowCoefficient
@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C] [Preadditive C] [Linear k C]

/-- A vector outside a subspace admits a normalized linear coefficient whose
kernel contains that subspace. -/
theorem exists_normalized_coefficient_killing
    {V : Type*} [AddCommGroup V] [Module k V]
    (S : Submodule k V) (f : V) (hf : f ∉ S) :
    ∃ ell : V →ₗ[k] k, ell f = 1 ∧ S ≤ LinearMap.ker ell := by
  obtain ⟨φ, hφf, hφ⟩ := S.exists_le_ker_of_notMem hf
  let ell : V →ₗ[k] k := (φ f)⁻¹ • φ
  refine ⟨ell, ?_, ?_⟩
  · dsimp [ell]
    simp [hφf]
  · intro g hg
    change (φ f)⁻¹ * φ g = 0
    rw [show φ g = 0 from hφ hg]
    simp

end LargeIndecomposable.ClosedZigzagTransfer
