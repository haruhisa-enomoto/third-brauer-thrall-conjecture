module

public import LargeIndecomposable.UnitForms.UnitForm

/-!
# Critical unit forms are nonnegative with a sincere radical

For a critical unit form `q` in at least three variables:

* a sincere `z ≫ 0` with `q(z) ≤ 0` and `Σ z` minimal is a radical vector:
  `q(z - e_a) ≥ 1` gives `B(z, e_a) ≤ q(z)`, and summing gives `q(z) = 0` and
  `B(z, e_a) = 0` (`exists_sincere_radical`);
* `q` is nonnegative, and `q(x) = 0` only for rational multiples of `z`: compare `x`
  with `z_{a₀} x - x_{a₀} z`, which is `≥ 0` and vanishes at `a₀` for `a₀` minimizing
  `x_a / z_a` (`nonneg_of_radical`).

This is the elementary part of Ovsienko's theorem (von Höhne 1988, §1).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

open Finset

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (q : UnitForm ι)

lemma B_sub_right (x y y' : ι → ℤ) : q.B x (y - y') = q.B x y - q.B x y' := by
  rw [B_symm, B_sub_left, B_symm q y x, B_symm q y' x]

lemma B_single_right (x : ι → ℤ) (a : ι) : q.B x (Pi.single a 1) = ∑ b, q.c b a * x b := by
  unfold B
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

/-- `B(z, x) = Σ_a x_a B(z, e_a)`. -/
lemma B_eq_sum_single (z x : ι → ℤ) : q.B z x = ∑ a, x a * q.B z (Pi.single a 1) := by
  unfold B
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_eq_single a]
  · simp; ring
  · intro c _ hc; simp [hc]
  · simp

/-- `2 q(z - e_a) = 2 q(z) - 2 B(z, e_a) + 2`. -/
lemma val_sub_single (z : ι → ℤ) (a : ι) :
    q.val (z - Pi.single a 1) = q.val z - q.B z (Pi.single a 1) + 1 := by
  have h1 := q.two_mul_val (z - Pi.single a 1)
  have h2 := q.two_mul_val z
  have h3 := q.two_mul_val (Pi.single a 1)
  rw [q.val_single] at h3
  rw [B_sub_left, B_sub_right, B_sub_right, B_symm q (Pi.single a 1) z] at h1
  omega

/-- A critical form has a sincere vector with nonpositive value. -/
lemma Critical.exists_sincere (hq : q.Critical) : ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ q.val z ≤ 0 := by
  obtain ⟨hnw, hoff⟩ := hq
  simp only [WeaklyPositive, not_forall, not_lt] at hnw
  obtain ⟨z, hz, hz0⟩ := hnw
  refine ⟨z, fun a ↦ ?_, hz0⟩
  rcases (hz.1 a).lt_or_eq with h | h
  · exact h
  · exact absurd (hoff a z hz h.symm) (not_lt.2 hz0)

/-- **A critical form in at least three variables has a sincere radical vector.** -/
theorem Critical.exists_sincere_radical (hq : q.Critical) (hn : 3 ≤ Fintype.card ι) :
    ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ ∀ x, q.B z x = 0 := by
  classical
  have hex : ∃ s : ℕ, ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ q.val z ≤ 0 ∧ (∑ a, z a) = s := by
    obtain ⟨z, hz, hz0⟩ := hq.exists_sincere
    exact ⟨(∑ a, z a).toNat, z, hz, hz0, by
      rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun a _ ↦ (hz a).le)]⟩
  obtain ⟨z, hz, hz0, hzs⟩ := Nat.find_spec hex
  have hmin : ∀ z' : ι → ℤ, (∀ a, 0 < z' a) → (∑ a, z' a) < ∑ a, z a → 0 < q.val z' := by
    intro z' hz' hlt
    by_contra h
    push Not at h
    have hle : (∑ a, z' a).toNat < Nat.find hex := by
      have h0 : 0 ≤ ∑ a, z' a := Finset.sum_nonneg fun a _ ↦ (hz' a).le
      have h1 : (((∑ a, z' a).toNat : ℕ) : ℤ) = ∑ a, z' a := Int.toNat_of_nonneg h0
      omega
    exact Nat.find_min hex hle ⟨z', hz', h, by
      rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun a _ ↦ (hz' a).le)]⟩
  -- `q(z - e_a) ≥ 1`
  have hstep : ∀ a, q.B z (Pi.single a 1) ≤ q.val z := by
    intro a
    have hpos : 0 < q.val (z - Pi.single a 1) := by
      rcases (show 1 < z a ∨ z a = 1 by have := hz a; omega) with h | h
      · -- `z_a ≥ 2`: still sincere, smaller sum
        refine hmin _ (fun b ↦ ?_) ?_
        · by_cases hb : b = a
          · subst hb; simp; omega
          · simp [hb, hz b]
        · have hs : ∑ b, (z - (Pi.single a 1 : ι → ℤ)) b = (∑ b, z b) - 1 := by
            simp [Finset.sum_sub_distrib]
          rw [hs]; omega
      · -- `z_a = 1`: vanishes at `a`
        refine hq.2 a _ ⟨fun b ↦ ?_, fun h0 ↦ ?_⟩ ?_
        · by_cases hb : b = a
          · subst hb; simp; omega
          · simp [hb, (hz b).le]
        · obtain ⟨b, hb⟩ : ∃ b, b ≠ a := by
            by_contra hall
            push Not at hall
            have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.2 fun x y ↦ by
              rw [hall x, hall y]
            omega
          have := congrFun h0 b
          simp [hb] at this
          exact absurd this (hz b).ne'
        · simp; omega
    have := q.val_sub_single z a
    omega
  -- summing: `2 q(z) = Σ z_a B(z, e_a) ≤ q(z) Σ z_a`
  have hsum : 2 * q.val z = ∑ a, z a * q.B z (Pi.single a 1) := by
    rw [q.two_mul_val, q.B_eq_sum_single]
  have hS : (Fintype.card ι : ℤ) ≤ ∑ a, z a := by
    have : ∑ _a : ι, (1 : ℤ) ≤ ∑ a, z a := Finset.sum_le_sum fun a _ ↦ hz a
    simpa using this
  have hle : ∑ a, z a * q.B z (Pi.single a 1) ≤ ∑ a, z a * q.val z :=
    Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hstep a) (hz a).le
  rw [← Finset.sum_mul] at hle
  have hv : q.val z = 0 := by
    by_contra hne
    have hlt : q.val z < 0 := lt_of_le_of_ne hz0 hne
    have hS3 : (3 : ℤ) ≤ ∑ a, z a := le_trans (by exact_mod_cast hn) hS
    have h3 : (∑ a, z a) * q.val z ≤ 3 * q.val z := by nlinarith
    linarith
  -- all terms vanish
  have hterm : ∀ a, q.B z (Pi.single a 1) = 0 := by
    have hnonpos : ∀ a, z a * q.B z (Pi.single a 1) ≤ 0 := fun a ↦
      mul_nonpos_of_nonneg_of_nonpos (hz a).le (by have := hstep a; omega)
    have hzero : ∑ a, z a * q.B z (Pi.single a 1) = 0 := by rw [← hsum, hv]; ring
    intro a
    have := (Finset.sum_eq_zero_iff_of_nonpos fun b _ ↦ hnonpos b).1 hzero a (Finset.mem_univ a)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hz a).ne'
    · exact h
  exact ⟨z, hz, fun x ↦ by rw [q.B_eq_sum_single]; simp [hterm]⟩

/-- `q(s x + t z) = s² q(x)` for a radical vector `z`. -/
lemma val_smul_add_radical (z : ι → ℤ) (hz : ∀ x, q.B z x = 0) (s t : ℤ) (x : ι → ℤ) :
    q.val (s • x + t • z) = s ^ 2 * q.val x := by
  have key : q.B (s • x + t • z) (s • x + t • z) = s ^ 2 * q.B x x := by
    simp only [B_add_left, B_add_right, B_smul_left, B_smul_right]
    rw [B_symm q x z]
    simp only [hz]
    ring
  have h1 := q.two_mul_val (s • x + t • z)
  have h2 := q.two_mul_val x
  rw [key, ← h2] at h1
  linarith

/-- **Nonnegativity**: a form with a sincere positive radical vector, weakly positive
off each index, is nonnegative, and vanishes only on rational multiples of the radical
vector. -/
theorem nonneg_of_radical [Nonempty ι] (z : ι → ℤ) (hz : ∀ a, 0 < z a)
    (hrad : ∀ x, q.B z x = 0) (hoff : ∀ a, q.WeaklyPositiveOff a) (x : ι → ℤ) :
    0 ≤ q.val x ∧ (q.val x = 0 → ∃ a, z a • x = x a • z) := by
  classical
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_min_image Finset.univ
    (fun a ↦ (x a : ℚ) / (z a : ℚ)) Finset.univ_nonempty
  have hcross : ∀ b, x a₀ * z b ≤ x b * z a₀ := by
    intro b
    have h := ha₀ b (Finset.mem_univ b)
    have hza : (0 : ℚ) < z a₀ := by exact_mod_cast hz a₀
    have hzb : (0 : ℚ) < z b := by exact_mod_cast hz b
    rw [div_le_div_iff₀ hza hzb] at h
    exact_mod_cast h
  set w : ι → ℤ := z a₀ • x + (-x a₀) • z with hw
  have hwv : q.val w = z a₀ ^ 2 * q.val x := q.val_smul_add_radical z hrad _ _ x
  have hwnn : ∀ b, 0 ≤ w b := fun b ↦ by
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hcross b; linarith
  have hwa : w a₀ = 0 := by simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hz2 : 0 < z a₀ ^ 2 := by have := hz a₀; positivity
  by_cases hw0 : w = 0
  · have hval : q.val x = 0 := by
      have : q.val w = 0 := by rw [hw0]; simp [val, B]
      rw [hwv] at this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hz2.ne'
      · exact h
    refine ⟨hval.ge, fun _ ↦ ⟨a₀, ?_⟩⟩
    funext b
    have := congrFun hw0 b
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linarith
  · have hpos : 0 < q.val w := hoff a₀ w ⟨hwnn, hw0⟩ hwa
    rw [hwv] at hpos
    have hx : 0 < q.val x := pos_of_mul_pos_right hpos hz2.le
    exact ⟨hx.le, fun h ↦ absurd h hx.ne'⟩

/-- **Critical forms are nonnegative** (in at least three variables), with a sincere
positive radical vector `z` spanning the rational radical. -/
theorem Critical.nonneg (hq : q.Critical) (hn : 3 ≤ Fintype.card ι) :
    ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ (∀ x, q.B z x = 0) ∧
      ∀ x, 0 ≤ q.val x ∧ (q.val x = 0 → ∃ a, z a • x = x a • z) := by
  obtain ⟨z, hz, hrad⟩ := Critical.exists_sincere_radical q hq hn
  haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  exact ⟨z, hz, hrad, q.nonneg_of_radical z hz hrad hq.2⟩

end UnitForm

end LargeIndecomposable.Forms
