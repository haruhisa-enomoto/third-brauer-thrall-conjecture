module

public import LargeIndecomposable.KroneckerBricks.Extension
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Morphisms with vector-space coefficients

Let `u : X ⟶ Y` be a morphism of Kronecker modules such that every morphism
`X ⟶ Y` is a scalar multiple of `u`, and `u` is nonzero on some vector of `V`.
For a vector space `N`, a pair of linear maps `V_X → N ⊗ V_Y`,
`W_X → N ⊗ W_Y` commuting with `a` and `b` (a morphism `X ⟶ N ⊗ Y`) has the
form `ν ⊗ u` for a vector `ν ∈ N` (`Bricks.coeff_eq`). Coordinates in a basis
of `N` are morphisms `X ⟶ Y`, hence scalar multiples of `u`, and only finitely
many are nonzero. This is the coefficient condition (S3) of Göbel–Simson for
the rigid gluing families.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct

universe u

variable {k : Type u} [Field k]

namespace Bricks

variable {X Y : Kron k} {N : Type u} [AddCommGroup N] [Module k N]

/-- The `i`-th coordinate of `N ⊗ M` in a basis of `N`. -/
def coordL {ι : Type u} (ℬ : Module.Basis ι k N) (i : ι) (M : Type u) [AddCommGroup M] [Module k M] :
    N ⊗[k] M →ₗ[k] M :=
  TensorProduct.lid k M ∘ₗ (ℬ.coord i).rTensor M

lemma coordL_apply {ι : Type u} [DecidableEq ι] (ℬ : Module.Basis ι k N) (i : ι) {M : Type u} [AddCommGroup M]
    [Module k M] (x : N ⊗[k] M) : coordL ℬ i M x = TensorProduct.equivFinsuppOfBasisLeft ℬ x i :=
  (TensorProduct.equivFinsuppOfBasisLeft_apply ℬ x i).symm

lemma coordL_lTensor {ι : Type u} (ℬ : Module.Basis ι k N) (i : ι) {M M' : Type u}
    [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M') :
    coordL ℬ i M' ∘ₗ g.lTensor N = g ∘ₗ coordL ℬ i M := by
  ext n m
  simp [coordL]

/-- Morphisms `X ⟶ N ⊗ Y` are `ν ⊗ u` when `Hom(X, Y) = k · u`. -/
theorem coeff_eq (u : X ⟶ Y) (hu : ∀ f : X ⟶ Y, ∃ c : k, f = c • u) (x0 : X.V)
    (hx0 : (u.app zero).hom x0 ≠ 0) (φ : X.V →ₗ[k] N ⊗[k] Y.V) (ψ : X.W →ₗ[k] N ⊗[k] Y.W)
    (ha : (Y.a.hom).lTensor N ∘ₗ φ = ψ ∘ₗ X.a.hom) (hb : (Y.b.hom).lTensor N ∘ₗ φ = ψ ∘ₗ X.b.hom) :
    ∃ ν : N, (∀ x, φ x = ν ⊗ₜ (u.app zero).hom x) ∧ ∀ w, ψ w = ν ⊗ₜ (u.app one).hom w := by
  classical
  let ℬ := Module.Free.chooseBasis k N
  let m : ∀ i, X ⟶ Y := fun i ↦ Kron.homMk (ModuleCat.ofHom (coordL ℬ i _ ∘ₗ φ))
    (ModuleCat.ofHom (coordL ℬ i _ ∘ₗ ψ))
    (ModuleCat.hom_ext (by
      change coordL ℬ i _ ∘ₗ ψ ∘ₗ X.a.hom = Y.a.hom ∘ₗ coordL ℬ i _ ∘ₗ φ
      rw [← ha, ← LinearMap.comp_assoc, coordL_lTensor, LinearMap.comp_assoc]))
    (ModuleCat.hom_ext (by
      change coordL ℬ i _ ∘ₗ ψ ∘ₗ X.b.hom = Y.b.hom ∘ₗ coordL ℬ i _ ∘ₗ φ
      rw [← hb, ← LinearMap.comp_assoc, coordL_lTensor, LinearMap.comp_assoc]))
  choose c hc using fun i ↦ hu (m i)
  have hφ : ∀ i x, coordL ℬ i _ (φ x) = c i • (u.app zero).hom x := fun i x ↦
    congrArg (fun f : X ⟶ Y ↦ (f.app zero).hom x) (hc i)
  have hψ : ∀ i w, coordL ℬ i _ (ψ w) = c i • (u.app one).hom w := fun i w ↦
    congrArg (fun f : X ⟶ Y ↦ (f.app one).hom w) (hc i)
  let S := (TensorProduct.equivFinsuppOfBasisLeft ℬ (φ x0)).support
  have hcS : ∀ i, i ∉ S → c i = 0 := by
    intro i hi
    rw [Finsupp.notMem_support_iff, ← coordL_apply, hφ] at hi
    exact (smul_eq_zero.1 hi).resolve_right hx0
  let ν : N := ∑ i ∈ S, c i • ℬ i
  have hrepr : ∀ i, ℬ.repr ν i = c i := by
    intro i
    simp only [ν, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', ite_eq_left_iff]
    intro hi
    exact (hcS i hi).symm
  refine ⟨ν, fun x ↦ ?_, fun w ↦ ?_⟩
  · apply (TensorProduct.equivFinsuppOfBasisLeft ℬ).injective
    ext i
    rw [← coordL_apply, hφ, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, hrepr]
  · apply (TensorProduct.equivFinsuppOfBasisLeft ℬ).injective
    ext i
    rw [← coordL_apply, hψ, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, hrepr]

end Bricks

end LargeIndecomposable
