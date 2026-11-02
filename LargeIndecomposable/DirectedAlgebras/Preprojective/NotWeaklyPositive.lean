module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerDirecting2
public import LargeIndecomposable.DirectedAlgebras.Preprojective.Preproj
public import LargeIndecomposable.UnitForms.Drozd

/-!
# Unbounded preprojective components make the Euler form not weakly positive

Over an algebraically closed field a directing module has `End M = k` (`Directing.finrank_end`),
so `χ(dim M) = 1` (`euler_directing`). If a preprojective component has members of every
dimension, their dimension vectors are infinitely many positive roots of the Euler form, which is
therefore not weakly positive by Drozd's finiteness (`not_weaklyPositive_of_unbounded`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **A directing module over an algebraically closed field has `End M = k`.** -/
theorem Directing.finrank_end [IsAlgClosed k] {M : FDMod k A} (hM : Directing M) :
    finrank k (M →ₗ[A] M) = 1 := by
  haveI := hM.1.2
  have hall : ∀ f : M →ₗ[A] M, ∃ c : k, f = c • LinearMap.id := by
    intro f
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrictScalars k)
    refine ⟨c, ?_⟩
    have h := hM.endo (FDMod.ofLin (f - c • LinearMap.id))
    rcases h with h0 | hb
    · exact sub_eq_zero.1 (congrArg FDMod.lin h0)
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      apply hv.2
      apply hb.1
      rw [map_zero]
      change f v - c • v = 0
      rw [sub_eq_zero]
      exact hv.apply_eq_smul
  have hid : (LinearMap.id : M →ₗ[A] M) ≠ 0 := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    intro h
    exact hm (LinearMap.congr_fun h m)
  exact (finrank_eq_one_iff_of_nonzero' _ hid).2 fun f ↦ by
    obtain ⟨c, hc⟩ := hall f
    exact ⟨c, hc.symm⟩

variable (D : DirData k A)

/-- **Unbounded preprojective components make the Euler form not weakly positive.** -/
theorem not_weaklyPositive_of_unbounded [IsAlgClosed k] (hT : ∀ x, x ∈ D.T)
    {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞)
    (hunb : ∀ b, ∃ X, 𝒞 X ∧ b < finrank k X) : ¬(eulerForm D hT).WeaklyPositive := by
  intro hwp
  have hfin := Forms.UnitForm.finite_roots (eulerForm D hT) hwp
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ x ∈ {x : D.ι → ℤ | Forms.UnitForm.Pos x ∧
      (eulerForm D hT).val x = 1}, (∑ i, x i) ≤ B := by
    obtain ⟨B, hB⟩ := hfin.bddAbove.imp fun B hB ↦ hB
    refine ⟨(hfin.toFinset.sup fun x ↦ (∑ i, x i).toNat), fun x hx ↦ ?_⟩
    have := Finset.le_sup (f := fun x : D.ι → ℤ ↦ (∑ i, x i).toNat) (hfin.mem_toFinset.2 hx)
    omega
  obtain ⟨X, hX, hXb⟩ := hunb B
  have hdir := h𝒞.directing hX
  have hroot : dimZ D X ∈ {x : D.ι → ℤ | Forms.UnitForm.Pos x ∧ (eulerForm D hT).val x = 1} := by
    refine ⟨⟨fun i ↦ by simp [dimZ], fun h0 ↦ ?_⟩, ?_⟩
    · haveI := hdir.1.2
      have hpos : 0 < finrank k X := Module.finrank_pos
      have hall : ∀ i, dimv D.e X i = 0 := fun i ↦ by
        have := congrFun h0 i
        simp only [dimZ, Pi.zero_apply, Nat.cast_eq_zero] at this
        exact this
      rw [finrank_eq_sum_dimv D.e D.idem D.orth D.sum X, Finset.sum_eq_zero fun i _ ↦ hall i]
        at hpos
      exact lt_irrefl 0 hpos
    · rw [eulerForm_val, euler_directing D hT hdir, hdir.finrank_end]
      rfl
  have h1 := hB _ hroot
  have h2 : (finrank k X : ℤ) = ∑ i, dimZ D X i := by
    rw [finrank_eq_sum_dimv D.e D.idem D.orth D.sum X]
    push_cast
    rfl
  omega

end LargeIndecomposable.AR
