module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerUnit

/-!
# The Euler form on an interval with two points

The inverse Cartan matrix is supported on the path order (`cartan_inv_support`). If `b` is
reached from `a` with `dim e_b A e_a = 1` and no third point lies on a path from `a` to `b`,
then `⟨e_a, e_b⟩ + ⟨e_b, e_a⟩ = -1`, a full edge of the Euler form (`eulerForm_c_interval`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module Matrix

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

/-- **The inverse Cartan matrix is supported on the path order.** -/
theorem cartan_inv_support (hT : ∀ x, x ∈ D.T) (i : D.ι) :
    ∀ j, (cartan D)⁻¹ j i ≠ 0 → Relation.ReflTransGen D.Arr i j := by
  classical
  obtain ⟨lo, hmono⟩ := exists_linOrder D
  letI := lo
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  intro hj
  by_cases hji : j = i
  · subst hji; exact Relation.ReflTransGen.refl
  have h1 := congrFun (congrFun (mul_nonsing_inv _ hu) j) i
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), cartan_diag D (hT j), one_mul,
    one_apply_ne hji] at h1
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ Finset.univ.erase j, cartan D j y * (cartan D)⁻¹ y i ≠ 0 := by
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero hall, add_zero] at h1
    exact hj h1
  have hyj : y ≠ j := Finset.ne_of_mem_erase hy
  have hc : cartan D j y ≠ 0 := fun h0 ↦ hyne (by rw [h0, zero_mul])
  have hci : (cartan D)⁻¹ y i ≠ 0 := fun h0 ↦ hyne (by rw [h0, mul_zero])
  have hpath : Relation.ReflTransGen D.Arr y j := by
    by_contra hn
    exact hc (cartan_eq_zero D hn)
  have hlt : y < j := lt_of_le_of_ne (hmono _ _ hpath) hyj
  exact (ih y hlt hci).trans hpath

/-- **A two-point interval gives a full edge.** -/
theorem eulerForm_c_interval (hT : ∀ x, x ∈ D.T) {a b : D.ι} (hab : a ≠ b)
    (hba : cartan D b a = 1)
    (hint : ∀ y, y ≠ a → y ≠ b → Relation.ReflTransGen D.Arr a y →
      Relation.ReflTransGen D.Arr y b → False) :
    (eulerForm D hT).c a b = -1 := by
  classical
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  have hab' : Relation.ReflTransGen D.Arr a b := by
    by_contra hn
    rw [cartan_eq_zero D hn] at hba
    exact absurd hba (by norm_num)
  -- no path back
  have h1 : (cartan D)⁻¹ a b = 0 := by
    by_contra h
    have hba' := cartan_inv_support D hT b a h
    have := D.acyc a b (D.transGen_of_ne hab' hab) hba'
    exact this
  -- the entry `(b, a)`
  have h2 : (cartan D)⁻¹ b a = -1 := by
    have e := congrFun (congrFun (mul_nonsing_inv _ hu) b) a
    rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), cartan_diag D (hT b), one_mul,
      one_apply_ne (Ne.symm hab), ← Finset.add_sum_erase _ _
        (Finset.mem_erase.2 ⟨hab, Finset.mem_univ a⟩), hba, cartan_inv_diag D hT a] at e
    have hrest : ∑ y ∈ (Finset.univ.erase b).erase a, cartan D b y * (cartan D)⁻¹ y a = 0 := by
      refine Finset.sum_eq_zero fun y hy ↦ ?_
      have hya : y ≠ a := Finset.ne_of_mem_erase hy
      have hyb : y ≠ b := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
      by_cases hc : cartan D b y = 0
      · rw [hc, zero_mul]
      · have hpath : Relation.ReflTransGen D.Arr y b := by
          by_contra hn
          exact hc (cartan_eq_zero D hn)
        by_cases hi : (cartan D)⁻¹ y a = 0
        · rw [hi, mul_zero]
        · exact (hint y hya hyb (cartan_inv_support D hT a y hi) hpath).elim
    rw [hrest, add_zero] at e
    linarith
  change (cartan D)⁻¹ b a + (cartan D)⁻¹ a b = -1
  rw [h1, h2, add_zero]

end LargeIndecomposable.AR
