module

public import LargeIndecomposable.UnitForms.Critical

/-!
# Pulling back unit forms; inflations

For a `ℤ`-linear map `T` with `B(T e_a, T e_a) = 2`, the form `x ↦ q(T x)` is again a
unit form (`UnitForm.pullback`). An *inflation* (von Höhne 1988, 1.2) is the pullback
along `T_ab : x ↦ x - x_b e_a` when `q_ab = 1`. Nonnegativity is preserved, and the
radical vector `y` of `q` becomes `y + y_b e_a`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

open Finset

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (q : UnitForm ι)

lemma B_sum_left {κ : Type} (s : Finset κ) (f : κ → ι → ℤ) (y : ι → ℤ) :
    q.B (∑ i ∈ s, f i) y = ∑ i ∈ s, q.B (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [B_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, B_add_left, ih]

lemma B_sum_right {κ : Type} (s : Finset κ) (x : ι → ℤ) (f : κ → ι → ℤ) :
    q.B x (∑ i ∈ s, f i) = ∑ i ∈ s, q.B x (f i) := by
  rw [B_symm, B_sum_left]
  exact Finset.sum_congr rfl fun i _ ↦ B_symm _ _ _

lemma B_single_single (a b : ι) : q.B (Pi.single a 1) (Pi.single b 1) = q.c a b := by
  unfold B
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro u _ hu; simp [hu]
  · simp
  · intro u _ hu; simp [hu]
  · simp

lemma eq_sum_single (x : ι → ℤ) : x = ∑ a, x a • (Pi.single a 1 : ι → ℤ) := by
  funext u
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Pullback** of a unit form along a linear map preserving the unit vectors' values. -/
def pullback (T : (ι → ℤ) →ₗ[ℤ] (ι → ℤ))
    (hT : ∀ a, q.B (T (Pi.single a 1)) (T (Pi.single a 1)) = 2) : UnitForm ι where
  c u v := q.B (T (Pi.single u 1)) (T (Pi.single v 1))
  symm u v := q.B_symm _ _
  diag a := hT a

lemma pullback_B (T : (ι → ℤ) →ₗ[ℤ] (ι → ℤ))
    (hT : ∀ a, q.B (T (Pi.single a 1)) (T (Pi.single a 1)) = 2) (x y : ι → ℤ) :
    (q.pullback T hT).B x y = q.B (T x) (T y) := by
  change ∑ u, ∑ v, q.B (T (Pi.single u 1)) (T (Pi.single v 1)) * x u * y v = _
  conv_rhs => rw [eq_sum_single x, eq_sum_single y]
  simp only [map_sum, map_zsmul, B_sum_left, B_sum_right, B_smul_left, B_smul_right,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
  ring

lemma pullback_val (T : (ι → ℤ) →ₗ[ℤ] (ι → ℤ))
    (hT : ∀ a, q.B (T (Pi.single a 1)) (T (Pi.single a 1)) = 2) (x : ι → ℤ) :
    (q.pullback T hT).val x = q.val (T x) := by
  unfold val; rw [pullback_B]

/-- The inflation map `x ↦ x - x_b e_a`. -/
def inflMap (a b : ι) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) where
  toFun x := x - x b • Pi.single a 1
  map_add' x y := by funext u; simp only [Pi.add_apply, Pi.sub_apply, smul_eq_mul, Pi.smul_apply,
    Pi.single_apply]; split_ifs <;> ring
  map_smul' t x := by funext u; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Pi.single_apply, RingHom.id_apply]; split_ifs <;> ring

/-- Its inverse `x ↦ x + x_b e_a` (for `a ≠ b`). -/
def deflMap (a b : ι) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) where
  toFun x := x + x b • Pi.single a 1
  map_add' x y := by funext u; simp only [Pi.add_apply, smul_eq_mul, Pi.smul_apply,
    Pi.single_apply]; split_ifs <;> ring
  map_smul' t x := by funext u; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Pi.single_apply, RingHom.id_apply]; split_ifs <;> ring

lemma inflMap_deflMap {a b : ι} (hab : a ≠ b) (x : ι → ℤ) : inflMap a b (deflMap a b x) = x := by
  funext u; simp [inflMap, deflMap, Pi.single_apply, Ne.symm hab]

lemma deflMap_inflMap {a b : ι} (hab : a ≠ b) (x : ι → ℤ) : deflMap a b (inflMap a b x) = x := by
  funext u; simp [inflMap, deflMap, Pi.single_apply, Ne.symm hab]

lemma inflMap_unit {a b : ι} (hab : a ≠ b) (h : q.c a b = 1) (u : ι) :
    q.B (inflMap a b (Pi.single u 1)) (inflMap a b (Pi.single u 1)) = 2 := by
  by_cases hu : u = b
  · subst hu
    have : inflMap a u (Pi.single u 1) = Pi.single u 1 - Pi.single a 1 := by
      funext v; simp [inflMap]
    rw [this, B_sub_left, B_sub_right, B_sub_right, B_single_single, B_single_single,
      B_single_single, B_single_single, q.diag, q.diag, q.symm u a, h]
    norm_num
  · have : inflMap a b (Pi.single u 1) = Pi.single u 1 := by
      funext v; simp [inflMap, Pi.single_apply, hu]
    rw [this, B_single_single, q.diag]

/-- **Inflation** of `q` at `(a, b)` with `q_ab = 1`. -/
def inflate {a b : ι} (hab : a ≠ b) (h : q.c a b = 1) : UnitForm ι :=
  q.pullback (inflMap a b) (q.inflMap_unit hab h)

/-- Nonnegativity, the radical and the vanishing locus move along an inflation. -/
lemma inflate_val {a b : ι} (hab : a ≠ b) (h : q.c a b = 1) (x : ι → ℤ) :
    (q.inflate hab h).val x = q.val (inflMap a b x) := q.pullback_val _ _ x

lemma inflate_radical {a b : ι} (hab : a ≠ b) (h : q.c a b = 1) (y : ι → ℤ)
    (hy : ∀ x, q.B y x = 0) (x : ι → ℤ) :
    (q.inflate hab h).B (deflMap a b y) x = 0 := by
  unfold inflate
  rw [pullback_B, inflMap_deflMap hab, hy]

/-- Off-diagonal coefficients of a nonnegative form lie in `[-2, 2]`. -/
lemma coeff_bound (hnn : ∀ x, 0 ≤ q.val x) {a b : ι} (hab : a ≠ b) :
    -2 ≤ q.c a b ∧ q.c a b ≤ 2 := by
  have h1 := hnn (Pi.single a 1 + Pi.single b 1)
  have h2 := hnn (Pi.single a 1 - Pi.single b 1)
  have e1 := q.two_mul_val (Pi.single a 1 + Pi.single b 1)
  have e2 := q.two_mul_val (Pi.single a 1 - Pi.single b 1)
  rw [B_add_left, B_add_right, B_add_right, B_single_single, B_single_single,
    B_single_single, B_single_single, q.diag, q.diag, q.symm b a] at e1
  rw [B_sub_left, B_sub_right, B_sub_right, B_single_single, B_single_single,
    B_single_single, B_single_single, q.diag, q.diag, q.symm b a] at e2
  constructor <;> omega

end UnitForm

end LargeIndecomposable.Forms
