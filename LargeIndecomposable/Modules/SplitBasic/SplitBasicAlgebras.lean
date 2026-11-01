module

public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.NoncommRing

/-!
# Split basic algebras

A finite-dimensional algebra `B` over a field `k` is *split basic* if it has a
complete family `e : ι → B` of orthogonal idempotents with
`e_x B e_x = k e_x ⊕ e_x J e_x` and `e_x B e_y ⊆ J` for `x ≠ y`, where
`J = rad B` (manuscript, Section 3; note v2, Section 4).

`SplitBasicData` records this as plain data. Quotients by two-sided ideals
inside `J` are again split basic with the images of the idempotents
(`SplitBasicData.quotient`), and their radical is the image of `J`
(`SplitBasicData.mem_jacobson_quotient_iff`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u v w

/-- A split basic algebra: a complete family `e : ι → B` of nonzero orthogonal
idempotents with `e_x B e_x ⊆ k e_x + J` and `e_x B e_y ⊆ J` for `x ≠ y`,
where `J = Ring.jacobson B`. -/
structure SplitBasicData (k : Type u) [Field k] (B : Type v) [Ring B] [Algebra k B]
    (ι : Type w) [Fintype ι] where
  /-- The idempotents `e_x`. -/
  e : ι → B
  complete : CompleteOrthogonalIdempotents e
  ne_zero : ∀ x, e x ≠ 0
  /-- `e_x B e_x = k e_x + e_x J e_x`. -/
  corner_diag : ∀ x (b : B), ∃ c : k, e x * b * e x - c • e x ∈ Ring.jacobson B
  /-- `e_x B e_y ⊆ J` for `x ≠ y`. -/
  corner_offdiag : ∀ x y, x ≠ y → ∀ b : B, e x * b * e y ∈ Ring.jacobson B

namespace SplitBasicData

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B] {ι : Type w} [Fintype ι]
  (S : SplitBasicData k B ι)

lemma idem (x : ι) : IsIdempotentElem (S.e x) := S.complete.idem x

lemma sum_eq_one : ∑ x, S.e x = 1 := S.complete.complete

lemma e_mul_e (x : ι) : S.e x * S.e x = S.e x := (S.idem x).eq

/-- Every element is the sum of its corners: `b = ∑ e_x b e_y`. -/
lemma sum_corners (b : B) : ∑ x, ∑ y, S.e x * b * S.e y = b := by
  calc ∑ x, ∑ y, S.e x * b * S.e y = (∑ x, S.e x) * b * (∑ y, S.e y) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_comm
    _ = b := by rw [S.sum_eq_one, one_mul, mul_one]

lemma sandwich_sandwich (x y : ι) (b : B) :
    S.e x * (S.e x * b * S.e y) * S.e y = S.e x * b * S.e y := by
  rw [← mul_assoc, ← mul_assoc, S.e_mul_e, mul_assoc, S.e_mul_e]

/-- An idempotent in the Jacobson radical is zero. -/
lemma _root_.IsIdempotentElem.eq_zero_of_mem_jacobson {R : Type*} [Ring R] {a : R}
    (ha : IsIdempotentElem a) (hJ : a ∈ Ring.jacobson R) : a = 0 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hJ
  obtain ⟨z, hz⟩ := hJ (-1)
  rw [Ideal.mem_bot] at hz
  have h1 : z * (1 - a) = 1 := by
    rw [← sub_eq_zero, ← hz]; noncomm_ring
  calc a = z * (1 - a) * a := by rw [h1, one_mul]
    _ = z * (a - a * a) := by noncomm_ring
    _ = 0 := by rw [ha.eq, sub_self, mul_zero]

section Quotient

variable (K : TwoSidedIdeal B)

/-- The quotient map is `k`-linear. -/
lemma mk_smul (c : k) (b : B) :
    Ideal.Quotient.mk K.asIdeal (c • b) = c • Ideal.Quotient.mk K.asIdeal b := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

/-- If `K ⊆ J`, the radical of `B/K` is the image of `J`. -/
lemma mem_jacobson_quotient_iff (hK : K.asIdeal ≤ Ring.jacobson B) (z : B ⧸ K.asIdeal) :
    z ∈ Ring.jacobson (B ⧸ K.asIdeal) ↔
      ∃ j ∈ Ring.jacobson B, Ideal.Quotient.mk K.asIdeal j = z := by
  rw [Ring.jacobson_quotient_of_le hK, Submodule.mem_map]
  rfl

lemma mk_mem_jacobson (hK : K.asIdeal ≤ Ring.jacobson B) {j : B} (hj : j ∈ Ring.jacobson B) :
    Ideal.Quotient.mk K.asIdeal j ∈ Ring.jacobson (B ⧸ K.asIdeal) :=
  (mem_jacobson_quotient_iff K hK _).2 ⟨j, hj, rfl⟩

/-- A quotient `B/K` with `K ⊆ J` is split basic, with the images of the `e_x`. -/
def quotient (hK : K.asIdeal ≤ Ring.jacobson B) : SplitBasicData k (B ⧸ K.asIdeal) ι where
  e x := Ideal.Quotient.mk K.asIdeal (S.e x)
  complete := S.complete.map (Ideal.Quotient.mk K.asIdeal)
  ne_zero x h := S.ne_zero x <| (S.idem x).eq_zero_of_mem_jacobson
    (hK ((Ideal.Quotient.eq_zero_iff_mem).1 h))
  corner_diag x z := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨c, hc⟩ := S.corner_diag x b
    refine ⟨c, ?_⟩
    have := mk_mem_jacobson K hK hc
    rwa [map_sub, map_mul, map_mul, mk_smul] at this
  corner_offdiag x y hxy z := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have := mk_mem_jacobson K hK (S.corner_offdiag x y hxy b)
    rwa [map_mul, map_mul] at this

@[simp] lemma quotient_e (hK : K.asIdeal ≤ Ring.jacobson B) (x : ι) :
    (S.quotient K hK).e x = Ideal.Quotient.mk K.asIdeal (S.e x) := rfl

end Quotient

end SplitBasicData

end LargeIndecomposable
