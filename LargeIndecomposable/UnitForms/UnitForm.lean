module

public import Mathlib

/-!
# Integral unit forms

A unit form on `ℤ^ι` is `q(x) = Σ_a x_a² + Σ_{a<b} q_ab x_a x_b`. We encode it by the
symmetric matrix `c` of its polar form `B(x, y) = Σ_{a,b} c_ab x_a y_b` with `c_aa = 2`,
so that `B(x, x) = 2 q(x)`. Weak positivity, restrictions and critical forms (Ovsienko)
are as in von Höhne, *On weakly positive unit forms* (1988), §1.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

open Finset

/-- A unit form on `ℤ^ι`, by the symmetric coefficient matrix of its polar form. -/
structure UnitForm (ι : Type) [Fintype ι] where
  /-- The coefficients of the polar form. -/
  c : ι → ι → ℤ
  symm : ∀ a b, c a b = c b a
  diag : ∀ a, c a a = 2

namespace UnitForm

variable {ι : Type} [Fintype ι] (q : UnitForm ι)

/-- The polar form `B(x, y) = Σ c_ab x_a y_b`. -/
def B (x y : ι → ℤ) : ℤ := ∑ a, ∑ b, q.c a b * x a * y b

lemma B_symm (x y : ι → ℤ) : q.B x y = q.B y x := by
  unfold B
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [q.symm]; ring

lemma B_add_left (x x' y : ι → ℤ) : q.B (x + x') y = q.B x y + q.B x' y := by
  unfold B; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [Pi.add_apply]; ring

lemma B_add_right (x y y' : ι → ℤ) : q.B x (y + y') = q.B x y + q.B x y' := by
  rw [B_symm, B_add_left, B_symm q y x, B_symm q y' x]

lemma B_smul_left (t : ℤ) (x y : ι → ℤ) : q.B (t • x) y = t * q.B x y := by
  unfold B; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma B_smul_right (t : ℤ) (x y : ι → ℤ) : q.B x (t • y) = t * q.B x y := by
  rw [B_symm, B_smul_left, B_symm]

lemma B_neg_left (x y : ι → ℤ) : q.B (-x) y = -q.B x y := by
  have := q.B_smul_left (-1) x y; simpa using this

lemma B_sub_left (x x' y : ι → ℤ) : q.B (x - x') y = q.B x y - q.B x' y := by
  rw [sub_eq_add_neg, B_add_left, B_neg_left, ← sub_eq_add_neg]

lemma B_zero_left (y : ι → ℤ) : q.B 0 y = 0 := by simp [B]

/-- `B(x, x)` is even. -/
lemma two_dvd_B (x : ι → ℤ) : (2 : ℤ) ∣ q.B x x := by
  classical
  -- `B(x,x) = Σ_a 2 x_a² + Σ_{a ≠ b} c_ab x_a x_b`, and the second sum pairs `(a,b)`, `(b,a)`
  have h : q.B x x = ∑ a, 2 * x a * x a + ∑ a, ∑ b ∈ univ.erase a, q.c a b * x a * x b := by
    unfold B
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), q.diag]
  rw [h]
  refine dvd_add (Finset.dvd_sum fun a _ ↦ ⟨x a * x a, by ring⟩) ?_
  -- the off-diagonal sum is twice the sum over `a < b` for an arbitrary linear order
  let e := Fintype.equivFin ι
  have hsplit : ∑ a, ∑ b ∈ univ.erase a, q.c a b * x a * x b =
      2 * ∑ a, ∑ b ∈ univ.filter (fun b ↦ e a < e b), q.c a b * x a * x b := by
    have h1 : ∀ a, ∑ b ∈ univ.erase a, q.c a b * x a * x b =
        ∑ b ∈ univ.filter (fun b ↦ e a < e b), q.c a b * x a * x b +
          ∑ b ∈ univ.filter (fun b ↦ e b < e a), q.c a b * x a * x b := by
      intro a
      rw [← Finset.sum_union]
      · apply Finset.sum_congr _ (fun _ _ ↦ rfl)
        ext b
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
          Finset.mem_filter, true_and]
        constructor
        · intro hb
          rcases lt_or_gt_of_ne (fun h ↦ hb (e.injective h).symm) with h | h
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h) rfl <;> exact lt_irrefl _ h
      · rw [Finset.disjoint_filter]; intro b _ h h'; exact lt_asymm h h'
    simp only [h1, Finset.sum_add_distrib]
    rw [two_mul]
    congr 1
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij' (fun p _ ↦ ⟨p.2, p.1⟩) (fun p _ ↦ ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp ⊢
      exact hp
    · intro p hp; simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp ⊢
      exact hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; simp only; rw [q.symm]; ring
  rw [hsplit]; exact dvd_mul_right _ _

/-- The unit form `q(x) = B(x, x) / 2`. -/
def val (x : ι → ℤ) : ℤ := q.B x x / 2

lemma two_mul_val (x : ι → ℤ) : 2 * q.val x = q.B x x :=
  Int.mul_ediv_cancel' (q.two_dvd_B x)

/-- `q(e_a) = 1`. -/
lemma val_single [DecidableEq ι] (a : ι) : q.val (Pi.single a 1) = 1 := by
  have : q.B (Pi.single a 1) (Pi.single a 1) = 2 := by
    unfold B
    rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
    · simp [q.diag]
    · intro b _ hb; simp [hb]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have h := q.two_mul_val (Pi.single a 1)
  omega

/-- `x ≥ 0`, `x ≠ 0`. -/
def Pos (x : ι → ℤ) : Prop := (∀ a, 0 ≤ x a) ∧ x ≠ 0

/-- **Weakly positive**: `q(x) > 0` for every nonzero `x ≥ 0`. -/
def WeaklyPositive : Prop := ∀ x, Pos x → 0 < q.val x

/-- `q` is weakly positive on vectors vanishing at `a`. -/
def WeaklyPositiveOff (a : ι) : Prop := ∀ x, Pos x → x a = 0 → 0 < q.val x

/-- **Critical form** (Ovsienko): not weakly positive, but every restriction to the
complement of one index is. -/
def Critical : Prop := ¬q.WeaklyPositive ∧ ∀ a, q.WeaklyPositiveOff a

end UnitForm

end LargeIndecomposable.Forms
