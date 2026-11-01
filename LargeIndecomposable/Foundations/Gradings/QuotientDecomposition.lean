module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

@[expose] public section

/-!
# Internal gradings transported through homogeneous quotients

A surjective linear map carries an internal direct-sum decomposition to the
images of its pieces when its kernel is closed under homogeneous projection.
This is the linear-algebra bridge used for Hom spaces of a mesh quotient.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LargeIndecomposable.Graded

universe u v w z

variable {k : Type u} [Field k]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module k M]
variable [AddCommGroup N] [Module k N]
variable {d : Type z} [DecidableEq d]

/-- The span of a set of homogeneous vectors is a homogeneous submodule. -/
theorem span_isHomogeneous_of_forall_mem_component
    (A : d → Submodule k M) [DirectSum.Decomposition A]
    (S : Set M) (hS : ∀ m ∈ S, ∃ i, m ∈ A i) :
    DirectSum.SetLike.IsHomogeneous A (Submodule.span k S) := by
  intro i m hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
      obtain ⟨j, hj⟩ := hS m hm
      by_cases hji : j = i
      · subst i
        rw [DirectSum.decompose_of_mem_same A hj]
        exact Submodule.subset_span hm
      · rw [DirectSum.decompose_of_mem_ne A hj hji]
        exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
      rw [DirectSum.decompose_add]
      exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      rw [DirectSum.decompose_smul]
      exact Submodule.smul_mem _ c hx

/-- A surjective linear map whose kernel is homogeneous transports an
internal decomposition to the images of its homogeneous pieces. -/
theorem image_isInternal_of_surjective_of_ker_isHomogeneous
    (A : d → Submodule k M) [DirectSum.Decomposition A]
    (f : M →ₗ[k] N) (hf : Function.Surjective f)
    (hker : DirectSum.SetLike.IsHomogeneous A (LinearMap.ker f)) :
    DirectSum.IsInternal (fun i ↦ (A i).map f) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hv0
    let y : d → M := fun i ↦
      if hi : i ∈ s then (hv i hi).choose else 0
    have hyA {i : d} (hi : i ∈ s) : y i ∈ A i := by
      simp only [y, dif_pos hi]
      exact (hv i hi).choose_spec.1
    have hyf {i : d} (hi : i ∈ s) : f (y i) = v i := by
      simp only [y, dif_pos hi]
      exact (hv i hi).choose_spec.2
    have hsum : ∑ i ∈ s, y i ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      calc
        f (∑ i ∈ s, y i) = ∑ i ∈ s, f (y i) := map_sum f _ _
        _ = ∑ i ∈ s, v i := Finset.sum_congr rfl fun i hi ↦ hyf hi
        _ = 0 := hv0
    intro i hi
    have hcomponent := hker i hsum
    have hcomponent_eq :
        ((DirectSum.decompose A (∑ j ∈ s, y j)) i : A i) = y i := by
      calc
        ((DirectSum.decompose A (∑ j ∈ s, y j)) i : M) =
            ∑ j ∈ s, ((DirectSum.decompose A (y j)) i : M) := by
          rw [DirectSum.decompose_sum]
          simp
        _ = y i := by
          rw [Finset.sum_eq_single i]
          · exact DirectSum.decompose_of_mem_same A (hyA hi)
          · intro j hj hji
            exact DirectSum.decompose_of_mem_ne A (hyA hj) hji
          · exact fun h ↦ False.elim (h hi)
    have hyker : y i ∈ LinearMap.ker f := by
      rw [← hcomponent_eq]
      exact hcomponent
    calc
      v i = f (y i) := (hyf hi).symm
      _ = 0 := LinearMap.mem_ker.mp hyker
  · rw [← Submodule.map_iSup,
      (DirectSum.Decomposition.isInternal (ℳ := A)).submodule_iSup_eq_top,
      Submodule.map_top]
    exact LinearMap.range_eq_top.2 hf

end LargeIndecomposable.Graded
