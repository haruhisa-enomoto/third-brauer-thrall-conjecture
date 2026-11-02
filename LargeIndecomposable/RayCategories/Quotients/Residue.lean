module

public import LargeIndecomposable.Modules.SplitBasic.SplitBasicAlgebras
public import LargeIndecomposable.Modules.SplitBasic.SplitBasic

/-!
# The residue algebra of split basic data

For split basic data `(e_x)` of `B`, the scalar `c_x(b)` with
`e_x b e_x ≡ c_x(b) e_x` modulo the radical defines an algebra map
`B → k^ι` with kernel the radical (`SplitBasicData.residue`). Its quotient
isomorphism turns our split basic data into the split-basic idempotents of
the ported BGRS theory (`SplitBasicData.toIdempotents`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

namespace SplitBasicData

universe u v w

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B] {ι : Type w} [Fintype ι]
  (S : SplitBasicData k B ι)

omit [Fintype ι] in
lemma smul_mem_jac (r : k) {b : B} (hb : b ∈ Ring.jacobson B) : r • b ∈ Ring.jacobson B := by
  rw [Algebra.smul_def]
  exact (Ring.jacobson B).mul_mem_left _ hb

lemma e_not_mem_jacobson (x : ι) : S.e x ∉ Ring.jacobson B :=
  fun h ↦ S.ne_zero x ((S.idem x).eq_zero_of_mem_jacobson h)

lemma scalar_unique (x : ι) (b : B) {c c' : k} (h : S.e x * b * S.e x - c • S.e x ∈ Ring.jacobson B)
    (h' : S.e x * b * S.e x - c' • S.e x ∈ Ring.jacobson B) : c = c' := by
  by_contra hne
  have hd : (c' - c) • S.e x ∈ Ring.jacobson B := by
    have := (Ring.jacobson B).sub_mem h h'
    rwa [sub_sub_sub_cancel_left, ← sub_smul] at this
  apply S.e_not_mem_jacobson x
  have hu : (c' - c)⁻¹ • ((c' - c) • S.e x) ∈ Ring.jacobson B := smul_mem_jac _ hd
  rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hne)), one_smul] at hu

/-- The residue scalar `c_x(b)`: `e_x b e_x ≡ c_x(b) e_x` modulo the radical. -/
def res (x : ι) (b : B) : k := (S.corner_diag x b).choose

lemma res_spec (x : ι) (b : B) : S.e x * b * S.e x - S.res x b • S.e x ∈ Ring.jacobson B :=
  (S.corner_diag x b).choose_spec

lemma res_eq (x : ι) (b : B) {c : k} (h : S.e x * b * S.e x - c • S.e x ∈ Ring.jacobson B) :
    S.res x b = c :=
  S.scalar_unique x b (S.res_spec x b) h

lemma res_add (x : ι) (a b : B) : S.res x (a + b) = S.res x a + S.res x b := by
  refine S.res_eq x _ ?_
  have := (Ring.jacobson B).add_mem (S.res_spec x a) (S.res_spec x b)
  convert this using 1
  rw [mul_add, add_mul, add_smul]; abel

lemma res_smul (x : ι) (r : k) (b : B) : S.res x (r • b) = r * S.res x b := by
  refine S.res_eq x _ ?_
  have := smul_mem_jac r (S.res_spec x b)
  convert this using 1
  rw [smul_sub, smul_smul, mul_smul_comm, smul_mul_assoc]

lemma res_algebraMap (x : ι) (r : k) : S.res x (algebraMap k B r) = r := by
  refine S.res_eq x _ ?_
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, S.e_mul_e, sub_self]
  exact (Ring.jacobson B).zero_mem

lemma res_mul (x : ι) (a b : B) : S.res x (a * b) = S.res x a * S.res x b := by
  refine S.res_eq x _ ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  let q := Ideal.Quotient.mkₐ k (Ring.jacobson B)
  change q _ = 0
  have hd : ∀ c : B, q (S.e x * c * S.e x) = S.res x c • q (S.e x) := by
    intro c
    have := (Ideal.Quotient.eq_zero_iff_mem).2 (S.res_spec x c)
    change q _ = 0 at this
    rwa [map_sub, map_smul, sub_eq_zero] at this
  have ho : ∀ y, y ≠ x → q (S.e x * a * S.e y) = 0 := fun y hy ↦
    (Ideal.Quotient.eq_zero_iff_mem).2 (S.corner_offdiag x y (Ne.symm hy) a)
  have hsplit : S.e x * (a * b) * S.e x = ∑ y, (S.e x * a * S.e y) * (S.e y * b * S.e x) := by
    have : ∀ y, (S.e x * a * S.e y) * (S.e y * b * S.e x) = S.e x * a * S.e y * b * S.e x := by
      intro y
      rw [show S.e x * a * S.e y * (S.e y * b * S.e x) = S.e x * a * (S.e y * S.e y) * b * S.e x by
        noncomm_ring, S.e_mul_e]
    simp_rw [this, ← Finset.sum_mul, ← Finset.mul_sum, S.sum_eq_one, mul_one, mul_assoc]
  rw [map_sub, hsplit, map_sum, Finset.sum_eq_single x, map_mul, hd, hd, smul_mul_smul_comm,
    ← map_mul, S.e_mul_e, map_smul, sub_self]
  · intro y _ hy
    rw [map_mul, ho y hy, zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- The residue algebra map `B → k^ι`. -/
def residue : B →ₐ[k] (ι → k) where
  toFun b x := S.res x b
  map_one' := funext fun x ↦ by simpa using S.res_algebraMap x 1
  map_mul' a b := funext fun x ↦ S.res_mul x a b
  map_zero' := funext fun x ↦ by simpa using S.res_smul x 0 0
  map_add' a b := funext fun x ↦ S.res_add x a b
  commutes' r := funext fun x ↦ S.res_algebraMap x r

lemma residue_apply (b : B) (x : ι) : S.residue b x = S.res x b := rfl

lemma res_e [DecidableEq ι] (x y : ι) : S.res x (S.e y) = if y = x then 1 else 0 := by
  refine S.res_eq x _ ?_
  split_ifs with h
  · subst h; rw [S.e_mul_e, S.e_mul_e, one_smul, sub_self]; exact (Ring.jacobson B).zero_mem
  · rw [(S.complete.ortho (Ne.symm h)), zero_mul, zero_smul, sub_zero]
    exact (Ring.jacobson B).zero_mem

lemma ker_residue : RingHom.ker S.residue = Ring.jacobson B := by
  ext b
  rw [RingHom.mem_ker]
  constructor
  · intro hb
    rw [← S.sum_corners b]
    refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
    by_cases hxy : x = y
    · subst hxy
      have := S.res_spec x b
      rwa [show S.res x b = 0 from congrFun hb x, zero_smul, sub_zero] at this
    · exact S.corner_offdiag x y hxy b
  · intro hb
    funext x
    refine S.res_eq x b ?_
    rw [Pi.zero_apply, zero_smul, sub_zero]
    exact (Ring.jacobson B).mul_mem_right _ ((Ring.jacobson B).mul_mem_left _ hb)

lemma residue_surjective [DecidableEq ι] : Function.Surjective S.residue := by
  intro v
  refine ⟨∑ y, v y • S.e y, funext fun x ↦ ?_⟩
  rw [residue_apply]
  simp_rw [show ∀ c, S.res x c = S.residue c x from fun _ ↦ rfl, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, residue_apply, res_e, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Our split basic data as split-basic idempotents of the ported theory. -/
def toIdempotents [DecidableEq ι] : LargeIndecomposable.SplitBasicIdempotents (k := k) (A := B) (ι := ι) where
  idempotent := S.e
  complete := S.complete
  quotientEquiv := (Ideal.quotientEquivAlgOfEq k S.ker_residue.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective S.residue_surjective)
  quotientEquiv_mk_idempotent i j := by
    change S.res j (S.e i) = _
    rw [res_e]

end SplitBasicData

end LargeIndecomposable
