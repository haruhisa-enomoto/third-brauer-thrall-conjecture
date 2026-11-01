module

public import LargeIndecomposable.Modules.Idempotents.IdempotentCartan
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Jacobson.Ideal

@[expose] public section

/-!
# Chosen split-basic presentations

A split-basic finite-dimensional algebra has semisimple quotient a finite
product of copies of its coefficient field.  This file packages a compatible
complete family of primitive idempotent lifts and defines the ordinary Cartan
matrix in that ordering.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {B : Type w} [Ring B] [Algebra k B]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

/-- Chosen split-basic idempotents: a complete orthogonal family whose
images identify the semisimple quotient with the coordinate idempotents of
`k^ι`.  This is the presentation on which the ordinary Cartan matrix is
computed. -/
structure SplitBasicIdempotents where
  /-- Chosen primitive idempotent lifts. -/
  idempotent : ι → A
  complete : CompleteOrthogonalIdempotents idempotent
  quotientEquiv : (A ⧸ Ring.jacobson A) ≃ₐ[k] (ι → k)
  quotientEquiv_mk_idempotent : ∀ i j,
    quotientEquiv (Ideal.Quotient.mk (Ring.jacobson A) (idempotent i)) j =
      if i = j then 1 else 0

namespace SplitBasicIdempotents

/-- The standard Cartan matrix of a split-basic algebra in a chosen complete
primitive-idempotent ordering. -/
def cartanMatrix (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι)) :
    Matrix ι ι ℤ :=
  idempotentCartanMatrix (k := k) S.idempotent

@[simp]
theorem cartanMatrix_apply
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι)) (i j : ι) :
    S.cartanMatrix i j =
      (Module.finrank k
        (idempotentCorner (k := k) S.idempotent i j) : ℤ) :=
  rfl

/-- An idempotent-preserving algebra equivalence identifies the chosen
split-basic Cartan matrix with the transported corner matrix. -/
theorem cartanMatrix_eq_idempotentCartanMatrix_map
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (f : A ≃ₐ[k] B) :
    S.cartanMatrix =
      idempotentCartanMatrix (k := k) (fun i ↦ f (S.idempotent i)) := by
  change idempotentCartanMatrix (k := k) S.idempotent = _
  exact (idempotentCartanMatrix_map (k := k) f S.idempotent).symm

/-- Consequently an algebra equivalence carrying the chosen primitive
idempotents preserves the determinant of the standard Cartan matrix. -/
theorem det_cartanMatrix_eq_det_idempotentCartanMatrix_map
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (f : A ≃ₐ[k] B) :
    S.cartanMatrix.det =
      (idempotentCartanMatrix (k := k)
        (fun i ↦ f (S.idempotent i))).det := by
  rw [S.cartanMatrix_eq_idempotentCartanMatrix_map f]

end SplitBasicIdempotents

/-- A split-basic algebra admits some finite chosen coordinate-idempotent
presentation. -/
def IsSplitBasic (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : Prop :=
  ∃ n : ℕ, Nonempty (SplitBasicIdempotents (k := k) (A := A) (ι := Fin n))

end LargeIndecomposable
