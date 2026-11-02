module

public import LargeIndecomposable.RayCategories.Quotients.Residue
public import LargeIndecomposable.MultiplicativeBases.Normed.NormedBasis
public import LargeIndecomposable.RayCategories.RayTables.Rays

/-!
# From split basic data to the primitive idempotents of the multiplicative-bases library

The idempotents of `SplitBasicData` are primitive and pairwise non-isomorphic,
so they form a basic set of primitive idempotents in the sense of the
multiplicative-bases library (`LargeIndecomposable/MBD`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

namespace SplitBasicData

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B] {ι : Type*} [Fintype ι]
  (S : SplitBasicData k B ι)

/-- **The idempotents of split basic data are primitive.** -/
lemma isPrimitive (x : ι) : LargeIndecomposable.IsPrimitiveIdempotent (S.e x) := by
  refine ⟨S.idem x, S.ne_zero x, fun f hf hef hfe ↦ ?_⟩
  obtain ⟨c, hc⟩ := S.corner_diag x f
  have hfc : S.e x * f * S.e x = f := by rw [hef, hfe]
  rw [hfc] at hc
  -- the residue `c` of the idempotent `f` is `0` or `1`
  have hsq : (c * c - c) • S.e x ∈ Ring.jacobson B := by
    have h1 : f * f - (c • S.e x) * (c • S.e x) ∈ Ring.jacobson B := by
      have : f * f - (c • S.e x) * (c • S.e x) =
          (f - c • S.e x) * f + (c • S.e x) * (f - c • S.e x) := by
        rw [sub_mul, mul_sub]; abel
      rw [this]
      exact add_mem ((Ring.jacobson B).mul_mem_right _ hc) ((Ring.jacobson B).mul_mem_left _ hc)
    have h2 : (c * c - c) • S.e x = (f - c • S.e x) - (f * f - (c • S.e x) * (c • S.e x)) := by
      rw [hf.eq, smul_mul_smul_comm, S.e_mul_e, sub_smul]; abel
    rw [h2]
    exact sub_mem hc h1
  have hc01 : c * c - c = 0 := by
    by_contra h0
    apply S.e_not_mem_jacobson x
    have := (Ring.jacobson B).smul_mem (algebraMap k B (c * c - c)⁻¹) hsq
    rwa [smul_eq_mul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ h0, one_smul] at this
  have hc' : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact hc01
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases hc' with rfl | rfl
  · left
    rw [zero_smul, sub_zero] at hc
    exact hf.eq_zero_of_mem_jacobson hc
  · right
    have hidem : IsIdempotentElem (S.e x - f) := by
      unfold IsIdempotentElem
      rw [sub_mul, mul_sub, mul_sub, S.e_mul_e, hef, hfe, hf.eq]; abel
    have hJ : S.e x - f ∈ Ring.jacobson B := by
      rw [one_smul] at hc
      have := (Ring.jacobson B).neg_mem hc
      rwa [neg_sub] at this
    exact (sub_eq_zero.1 (hidem.eq_zero_of_mem_jacobson hJ)).symm

include S in
/-- **Split basic data give a basic algebra.** -/
lemma isBasicAlgebra [DecidableEq ι] : LargeIndecomposable.IsBasicAlgebra B := by
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i ↦ S.e (σ.symm i), ?_, fun i ↦ S.isPrimitive _, ?_⟩
  · exact (CompleteOrthogonalIdempotents.equiv σ.symm).2 S.complete
  · intro i j ⟨a, b, ha, hb, hab, hba⟩
    by_contra hij
    have hne : σ.symm i ≠ σ.symm j := fun h ↦ hij (σ.symm.injective h)
    have haJ : a ∈ Ring.jacobson B := by
      rw [← ha]; exact S.corner_offdiag _ _ hne a
    apply S.e_not_mem_jacobson (σ.symm i)
    have hab' : a * b = S.e (σ.symm i) := hab
    rw [← hab']
    exact (Ring.jacobson B).mul_mem_right _ haJ

end SplitBasicData

end LargeIndecomposable
