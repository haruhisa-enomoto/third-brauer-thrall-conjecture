module

public import LargeIndecomposable.DirectedAlgebras.Directing.Cartan
public import LargeIndecomposable.UnitForms.Drozd

/-!
# The Euler form of a directed algebra is a unit form

The inverse of the Cartan matrix is again unitriangular (`cartan_inv_diag`), so the symmetrized
Euler form `c_ab = ⟨e_a, e_b⟩ + ⟨e_b, e_a⟩` has `c_aa = 2` and defines a unit form `eulerForm`
whose value is the Euler quadratic form `⟨x, x⟩` (`eulerForm_val`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module Matrix

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

lemma exists_linOrder : ∃ lo : LinearOrder D.ι,
    ∀ x y : D.ι, Relation.ReflTransGen D.Arr x y → lo.le x y := by
  letI : PartialOrder D.ι := pathOrder D
  exact ⟨(inferInstance : LinearOrder (LinearExtension D.ι)), fun x y h ↦
    (toLinearExtension (α := D.ι)).monotone h⟩

/-- **The diagonal of the inverse Cartan matrix is one.** -/
theorem cartan_inv_diag (hT : ∀ x, x ∈ D.T) (a : D.ι) : (cartan D)⁻¹ a a = 1 := by
  obtain ⟨lo, hmono⟩ := exists_linOrder D
  letI := lo
  have hM : (cartan D).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    apply cartan_eq_zero D
    intro h
    exact absurd (hmono _ _ h) (not_le_of_gt hij')
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  letI := invertibleOfIsUnitDet _ hu
  have hMi : ((cartan D)⁻¹).IsLowerTriangular := blockTriangular_inv_of_blockTriangular hM
  have h1 := congrFun (congrFun (nonsing_inv_mul _ hu) a) a
  rw [mul_apply, Finset.sum_eq_single a] at h1
  · rw [cartan_diag D (hT a), mul_one] at h1
    simpa using h1
  · intro j _ hja
    rcases lt_or_gt_of_ne hja with h | h
    · rw [cartan_eq_zero D, mul_zero]
      intro hr
      exact absurd (hmono _ _ hr) (not_le_of_gt h)
    · rw [hMi (OrderDual.toDual_lt_toDual.2 h), zero_mul]
  · simp

/-- **The Euler form as a unit form.** -/
def eulerForm (hT : ∀ x, x ∈ D.T) : Forms.UnitForm D.ι where
  c a b := (cartan D)⁻¹ b a + (cartan D)⁻¹ a b
  symm a b := add_comm _ _
  diag a := by rw [cartan_inv_diag D hT]; norm_num

lemma euler_apply (u v : D.ι → ℤ) :
    euler D u v = ∑ a, ∑ b, (cartan D)⁻¹ b a * u a * v b := by
  unfold euler
  simp only [dotProduct, mulVec, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The unit form is the Euler quadratic form.** -/
theorem eulerForm_val (hT : ∀ x, x ∈ D.T) (x : D.ι → ℤ) :
    (eulerForm D hT).val x = euler D x x := by
  have h := (eulerForm D hT).two_mul_val x
  have hB : (eulerForm D hT).B x x = 2 * euler D x x := by
    simp only [Forms.UnitForm.B, eulerForm, euler_apply, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    have e : ∑ a, ∑ b, (cartan D)⁻¹ a b * x a * x b = ∑ a, ∑ b, (cartan D)⁻¹ b a * x a * x b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
      ring
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    ring
  omega

end LargeIndecomposable.AR
