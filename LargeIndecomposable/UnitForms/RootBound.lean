module

public import LargeIndecomposable.UnitForms.Restrict
public import LargeIndecomposable.UnitForms.Critical

/-!
# Roots off a coordinate are bounded

If `q ≥ 0` and `q(x) = 0` forces `x = x_c • z` with `z_c = 1`, then the form is positive definite on
`x_c = 0`, so the vectors there with `q = 1` have bounded coordinates (`bounded_off`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (q : UnitForm ι)

/-- The quadratic expansion. -/
lemma two_val_add_smul (s t : ℤ) (x y : ι → ℤ) :
    2 * q.val (s • x + t • y) = 2 * s ^ 2 * q.val x + 2 * s * t * q.B x y + 2 * t ^ 2 * q.val y := by
  rw [two_mul_val]
  simp only [B_add_left, B_add_right, B_smul_left, B_smul_right]
  rw [B_symm q y x]
  have h1 := q.two_mul_val x
  have h2 := q.two_mul_val y
  rw [← h1, ← h2]
  ring

/-- **Cauchy–Schwarz.** -/
theorem B_sq_le (hnn : ∀ x, 0 ≤ q.val x) (x y : ι → ℤ) :
    q.B x y ^ 2 ≤ 4 * q.val x * q.val y := by
  have hy := hnn y
  have hx := hnn x
  rcases hy.lt_or_eq with hpos | hzero
  · have h := hnn ((2 * q.val y) • x + (-q.B x y) • y)
    have h2 := q.two_val_add_smul (2 * q.val y) (-q.B x y) x y
    have h3 : 0 ≤ q.val y * (4 * q.val x * q.val y - q.B x y ^ 2) := by nlinarith
    by_contra hn
    push Not at hn
    have h4 : 4 * q.val x * q.val y - q.B x y ^ 2 < 0 := by linarith
    nlinarith [mul_pos hpos (neg_pos.2 h4)]
  · have hb : q.B x y = 0 := by
      by_contra hne
      have h := hnn ((1 : ℤ) • x + (-(q.val x + 1) * q.B x y) • y)
      have h2 := q.two_val_add_smul 1 (-(q.val x + 1) * q.B x y) x y
      rw [← hzero] at h2
      have h3 : 1 ≤ q.B x y ^ 2 := by
        have : q.B x y ^ 2 ≠ 0 := pow_ne_zero 2 hne
        have h4 : 0 ≤ q.B x y ^ 2 := sq_nonneg _
        omega
      nlinarith
    rw [hb, ← hzero]
    simp

/-- **Vectors of value one off a coordinate are bounded.** -/
theorem bounded_off (hnn : ∀ x, 0 ≤ q.val x) (c : ι) (z : ι → ℤ) (hz : ∀ x, q.val x = 0 → x = x c • z)
    : ∃ R : ℤ, 0 ≤ R ∧ ∀ r : ι → ℤ, r c = 0 → q.val r = 1 → ∀ a, r a ^ 2 ≤ R := by
  classical
  let s : Finset ι := Finset.univ.erase c
  let M : Matrix s s ℤ := fun a b ↦ q.c a b
  have hc : ∀ h : c ∈ s, False := fun h ↦ (Finset.mem_erase.1 h).1 rfl
  have hBM : ∀ x y : s → ℤ, q.B (extZ s x) (extZ s y) = x ⬝ᵥ (M.mulVec y) := by
    intro x y
    rw [← B_restrict]
    simp only [B, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    change q.c a b * x a * y b = x a * (q.c a b * y b)
    ring
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : q.val (extZ s v) = 0 := by
      have h2 := q.two_mul_val (extZ s v)
      rw [hBM, hMv] at h2
      simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h2
      omega
    have h3 := hz _ h1
    rw [extZ_out v (fun h ↦ hc h), zero_smul] at h3
    apply hv
    funext a
    have := congrFun h3 a
    rwa [extZ_mem] at this
  let y : s → (s → ℤ) := fun a ↦ M.adjugate.mulVec (Pi.single a 1)
  have hy : ∀ a, M.mulVec (y a) = M.det • (Pi.single a 1 : s → ℤ) := fun a ↦ by
    simp only [y, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨∑ a, 4 * q.val (extZ s (y a)), Finset.sum_nonneg fun a _ ↦ by
    have := hnn (extZ s (y a)); omega, fun r hr hr1 a ↦ ?_⟩
  by_cases ha : a = c
  · subst ha
    rw [hr]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact Finset.sum_nonneg fun a _ ↦ by have := hnn (extZ s (y a)); omega
  have has : a ∈ s := Finset.mem_erase.2 ⟨ha, Finset.mem_univ a⟩
  let a' : s := ⟨a, has⟩
  let r' : s → ℤ := fun b ↦ r b
  have hrr : extZ s r' = r := by
    funext i
    by_cases hi : i ∈ s
    · exact extZ_mem r' ⟨i, hi⟩
    · have : i = c := by
        by_contra hne
        exact hi (Finset.mem_erase.2 ⟨hne, Finset.mem_univ i⟩)
      subst this
      rw [extZ_out r' hi, hr]
  have h1 : q.B r (extZ s (y a')) = M.det * r a := by
    rw [← hrr, hBM, hy, hrr]
    simp [dotProduct, Pi.single_apply, r', a', mul_comm]
  have h2 := q.B_sq_le hnn r (extZ s (y a'))
  rw [h1, hr1, mul_one] at h2
  have h3 : 1 ≤ M.det ^ 2 := by
    have : M.det ^ 2 ≠ 0 := pow_ne_zero 2 hdet
    have h4 : 0 ≤ M.det ^ 2 := sq_nonneg _
    omega
  have h5 : r a ^ 2 ≤ 4 * q.val (extZ s (y a')) := by
    have h6 : 0 ≤ r a ^ 2 := sq_nonneg _
    nlinarith
  refine h5.trans ?_
  exact Finset.single_le_sum (f := fun a ↦ 4 * q.val (extZ s (y a)))
    (fun a _ ↦ by have := hnn (extZ s (y a)); omega) (Finset.mem_univ a')

end UnitForm

end LargeIndecomposable.Forms
