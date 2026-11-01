module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Cartan matrices from finite idempotent families

For a finite family `e` in a finite-dimensional algebra, the `(i,j)` corner
is `e i * A * e j`.  Its dimension is the usual split-basic left-module
Cartan entry.  This file packages that matrix and proves that it is preserved
when an algebra equivalence transports the idempotent family.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {B : Type w} [Ring B] [Algebra k B]

/-- The vector subspace `e i * A * e j`, presented as the range of the
corresponding two-sided multiplication map. -/
def idempotentCorner {ι : Type*} (e : ι → A) (i j : ι) : Submodule k A :=
  LinearMap.range
    ((LinearMap.mulRight k (e j)).comp (LinearMap.mulLeft k (e i)))

theorem mem_idempotentCorner_iff {ι : Type*} (e : ι → A) (i j : ι) (x : A) :
    x ∈ idempotentCorner (k := k) e i j ↔
      ∃ a : A, e i * a * e j = x :=
  Iff.rfl

/-- The integral Cartan matrix attached to a finite family of split-basic
idempotents.  Rows index simples and columns index left projectives. -/
def idempotentCartanMatrix {ι : Type*} [Fintype ι]
    (e : ι → A) : Matrix ι ι ℤ :=
  fun i j ↦ (Module.finrank k (idempotentCorner (k := k) e i j) : ℤ)

/-- An algebra equivalence restricts to the corresponding two-sided
idempotent corners. -/
def idempotentCornerLinearEquiv {ι : Type*}
    (f : A ≃ₐ[k] B) (e : ι → A) (i j : ι) :
    idempotentCorner (k := k) e i j ≃ₗ[k]
      idempotentCorner (k := k) (fun r ↦ f (e r)) i j where
  toFun x := by
    refine ⟨f x.1, ?_⟩
    obtain ⟨a, ha⟩ := x.2
    refine ⟨f a, ?_⟩
    simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, map_mul] using congrArg f ha
  invFun x := by
    refine ⟨f.symm x.1, ?_⟩
    obtain ⟨b, hb⟩ := x.2
    refine ⟨f.symm b, ?_⟩
    simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, map_mul, AlgEquiv.symm_apply_apply] using
        congrArg f.symm hb
  left_inv x := by
    apply Subtype.ext
    exact f.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact f.apply_symm_apply x.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add f x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact f.toLinearMap.map_smul c x.1

/-- Transporting a finite idempotent family through an algebra equivalence
does not change its Cartan matrix. -/
theorem idempotentCartanMatrix_map {ι : Type*} [Fintype ι]
  (f : A ≃ₐ[k] B) (e : ι → A) :
    idempotentCartanMatrix (k := k) (fun r ↦ f (e r)) =
      idempotentCartanMatrix (k := k) e := by
  ext i j
  change (Module.finrank k
      (idempotentCorner (k := k) (fun r ↦ f (e r)) i j) : ℤ) =
    (Module.finrank k (idempotentCorner (k := k) e i j) : ℤ)
  exact_mod_cast (idempotentCornerLinearEquiv (k := k) f e i j).finrank_eq.symm

/-- In particular, the determinant of an idempotent Cartan matrix is
unchanged by algebra equivalence. -/
theorem det_idempotentCartanMatrix_map {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : A ≃ₐ[k] B) (e : ι → A) :
    (idempotentCartanMatrix (k := k) (fun r ↦ f (e r))).det =
      (idempotentCartanMatrix (k := k) e).det := by
  rw [idempotentCartanMatrix_map]

end LargeIndecomposable
