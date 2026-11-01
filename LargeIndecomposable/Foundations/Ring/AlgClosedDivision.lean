module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import LargeIndecomposable.Foundations.Ring.LocalRingJacobson

@[expose] public section

/-!
# Finite-dimensional division algebras over algebraically closed fields

A finite-dimensional central division algebra over an algebraically closed
field consists only of scalars.  The proof uses an eigenvector of left
multiplication and works without first proving that the division algebra is
commutative.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v

variable (k : Type u) [Field k] [IsAlgClosed k]
variable (D : Type v) [DivisionRing D] [Algebra k D] [Module.Finite k D]

/-- The scalar embedding into a finite-dimensional division algebra over an
algebraically closed field is surjective. -/
theorem algebraMap_surjective_of_finiteDimensional_divisionRing :
    Function.Surjective (algebraMap k D) := by
  intro x
  let L : Module.End k D := Algebra.lmul k D x
  obtain ⟨c, hc⟩ := L.exists_eigenvalue
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  have hxy : x * y = c • y := by
    simpa [L, Algebra.coe_lmul_eq_mul] using hy.apply_eq_smul
  have hmul : (x - algebraMap k D c) * y = 0 := by
    rw [sub_mul, hxy, Algebra.smul_def, sub_self]
  have hx : x - algebraMap k D c = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hy.2
  exact ⟨c, (sub_eq_zero.mp hx).symm⟩

variable (R : Type v) [Ring R] [Algebra k R] [Module.Finite k R]
  [IsDedekindFiniteMonoid R] [IsLocalRing R]

/-- Every element of a finite-dimensional local algebra over an algebraically
closed field is congruent to a scalar modulo its Jacobson radical. -/
theorem exists_sub_algebraMap_mem_ringJacobson (x : R) :
    ∃ c : k, x - algebraMap k R c ∈ Ring.jacobson R := by
  letI : (Ring.jacobson R).IsMaximal := by
    rw [ringJacobson_eq_nonunitsIdeal]
    infer_instance
  letI : DivisionRing (R ⧸ Ring.jacobson R) :=
    Ideal.Quotient.divisionRing (Ring.jacobson R)
  obtain ⟨c, hc⟩ :=
    algebraMap_surjective_of_finiteDimensional_divisionRing
      k (R ⧸ Ring.jacobson R) (Ideal.Quotient.mk (Ring.jacobson R) x)
  refine ⟨c, (Submodule.Quotient.mk_eq_zero _).mp ?_⟩
  change (Ideal.Quotient.mk (Ring.jacobson R))
    (x - algebraMap k R c) = 0
  rw [map_sub, Ideal.Quotient.mk_algebraMap, hc]
  simp

end LargeIndecomposable
