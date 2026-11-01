module

public import LargeIndecomposable.UnitForms.UnitForm

/-!
# Drozd's lemma: weakly positive forms have finitely many positive roots

A weakly positive unit form is positive on all nonzero real vectors `v ≥ 0` (`pos_real`): on a
face of the simplex where the minimum is not positive, a minimizer in the relative interior
satisfies a square rational linear system with no nonzero solution of the homogeneous system
(moving along a solution would reach a smaller face), so it is rational, and clearing
denominators contradicts weak positivity. Comparing with the minimum on the simplex bounds the
positive roots (`finite_roots`; Drozd, see Ringel, *Tame algebras*, 1.0).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

open Finset Matrix

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (q : UnitForm ι)

/-- The real polar form. -/
def Br (v w : ι → ℝ) : ℝ := ∑ a, ∑ b, (q.c a b : ℝ) * v a * w b

/-- The real form. -/
def Qr (v : ι → ℝ) : ℝ := q.Br v v / 2

/-- The linear forms `B(v, e_b)`. -/
def Lr (v : ι → ℝ) (b : ι) : ℝ := ∑ a, (q.c a b : ℝ) * v a

lemma Br_eq_sum (v w : ι → ℝ) : q.Br v w = ∑ b, w b * q.Lr v b := by
  unfold Br Lr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

lemma Br_symm (v w : ι → ℝ) : q.Br v w = q.Br w v := by
  unfold Br
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [q.symm]; ring

lemma Qr_add_smul (v w : ι → ℝ) (t : ℝ) :
    q.Qr (v + t • w) = q.Qr v + t * q.Br v w + t ^ 2 * q.Qr w := by
  have h : q.Br (v + t • w) (v + t • w) = q.Br v v + 2 * t * q.Br v w + t ^ 2 * q.Br w w := by
    have hs := q.Br_symm w v
    unfold Br at hs ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∀ a b, (q.c a b : ℝ) * (v a + t * w a) * (v b + t * w b) =
        (q.c a b : ℝ) * v a * v b + t * ((q.c a b : ℝ) * v a * w b) +
          t * ((q.c a b : ℝ) * w a * v b) + t ^ 2 * ((q.c a b : ℝ) * w a * w b) := by
      intro a b; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hs]; ring
  unfold Qr; rw [h]; ring

lemma Qr_smul (v : ι → ℝ) (t : ℝ) : q.Qr (t • v) = t ^ 2 * q.Qr v := by
  have := q.Qr_add_smul 0 v t
  simp only [zero_add] at this
  rw [this]
  simp [Qr, Br]

lemma Qr_cast (x : ι → ℤ) : q.Qr (fun i ↦ (x i : ℝ)) = q.val x := by
  have h := q.two_mul_val x
  have h2 : q.Br (fun i ↦ (x i : ℝ)) (fun i ↦ (x i : ℝ)) = (q.B x x : ℝ) := by
    unfold Br B; push_cast; rfl
  unfold Qr
  rw [h2, ← h]
  push_cast; ring

lemma continuous_Qr : Continuous q.Qr := by
  unfold Qr Br; fun_prop

lemma Qr_eq_of_kernel {w : ι → ℝ} {s : Finset ι} {ν : ℝ} (hws : ∀ i ∉ s, w i = 0)
    (hL : ∀ i ∈ s, q.Lr w i = ν) (hsum : ∑ i, w i = 0) : q.Qr w = 0 := by
  have : q.Br w w = 0 := by
    rw [Br_eq_sum]
    have : ∀ b, w b * q.Lr w b = w b * ν := fun b ↦ by
      by_cases hb : b ∈ s
      · rw [hL b hb]
      · rw [hws b hb, zero_mul, zero_mul]
    simp only [this, ← Finset.sum_mul, hsum, zero_mul]
  unfold Qr; rw [this, zero_div]

lemma Br_eq_zero_of_const {v w : ι → ℝ} {s : Finset ι} {lam : ℝ} (hws : ∀ i ∉ s, w i = 0)
    (hL : ∀ i ∈ s, q.Lr v i = lam) (hsum : ∑ i, w i = 0) : q.Br v w = 0 := by
  rw [Br_eq_sum]
  have : ∀ b, w b * q.Lr v b = w b * lam := fun b ↦ by
    by_cases hb : b ∈ s
    · rw [hL b hb]
    · rw [hws b hb, zero_mul, zero_mul]
  simp only [this, ← Finset.sum_mul, hsum, zero_mul]

/-- The square linear system of a face: `B(w, e_i) = ν` on `s`, `w = 0` off `s`, `Σ w = 0`. -/
def faceMat (s : Finset ι) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℚ := fun r col ↦
  Sum.elim (fun i ↦ Sum.elim (fun j ↦ if i ∈ s then (q.c j i : ℚ) else if j = i then 1 else 0)
    (fun _ ↦ if i ∈ s then -1 else 0) col) (fun _ ↦ Sum.elim (fun _ ↦ 1) (fun _ ↦ 0) col) r

lemma faceMat_mulVec_inl (s : Finset ι) (z : ι ⊕ Unit → ℝ) (i : ι) :
    ((q.faceMat s).map (Rat.cast : ℚ → ℝ) *ᵥ z) (Sum.inl i) =
      if i ∈ s then q.Lr (fun j ↦ z (Sum.inl j)) i - z (Sum.inr ()) else z (Sum.inl i) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply, faceMat,
    Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton]
  by_cases hi : i ∈ s
  · simp only [hi, if_true, Lr]; push_cast; ring
  · simp only [hi, if_false]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp

lemma faceMat_mulVec_inr (s : Finset ι) (z : ι ⊕ Unit → ℝ) :
    ((q.faceMat s).map (Rat.cast : ℚ → ℝ) *ᵥ z) (Sum.inr ()) = ∑ i, z (Sum.inl i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, faceMat]

/-- A rational vector `v ≥ 0` with `q(v) ≤ 0` contradicts weak positivity. -/
lemma not_rat (hq : q.WeaklyPositive) (r : ι → ℚ) (hr : ∀ i, 0 ≤ r i) (hr0 : r ≠ 0)
    (hQ : q.Qr (fun i ↦ (r i : ℝ)) ≤ 0) : False := by
  set D : ℕ := ∏ i, (r i).den
  have hdvd : ∀ i, (r i).den ∣ D := fun i ↦ Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hDpos : 0 < D := Finset.prod_pos fun i _ ↦ (r i).den_pos
  set x : ι → ℤ := fun i ↦ (r i).num * ((D / (r i).den : ℕ) : ℤ)
  have hx : ∀ i, (x i : ℚ) = D * r i := by
    intro i
    have h0 : (x i : ℚ) = ((r i).num : ℚ) * (((D / (r i).den : ℕ)) : ℚ) := by
      simp only [x, Int.cast_mul, Int.cast_natCast]
    have h1 : ((D / (r i).den : ℕ) : ℚ) = (D : ℚ) / (r i).den :=
      Nat.cast_div (hdvd i) (by exact_mod_cast (r i).den_ne_zero)
    rw [h0, h1]
    calc ((r i).num : ℚ) * ((D : ℚ) / (r i).den) = D * (((r i).num : ℚ) / (r i).den) := by ring
      _ = D * r i := by rw [Rat.num_div_den]
  have hxr : (fun i ↦ (x i : ℝ)) = (D : ℝ) • (fun i ↦ (r i : ℝ)) := by
    funext i
    have := congrArg (Rat.cast : ℚ → ℝ) (hx i)
    push_cast at this
    simpa using this
  have hpos : Pos x := by
    refine ⟨fun i ↦ ?_, fun h ↦ hr0 (funext fun i ↦ ?_)⟩
    · have := hx i
      have h2 : (0 : ℚ) ≤ D * r i := mul_nonneg (by positivity) (hr i)
      rw [← this] at h2
      exact_mod_cast h2
    · have := hx i
      rw [h] at this
      simp only [Pi.zero_apply, Int.cast_zero] at this
      rcases mul_eq_zero.1 this.symm with h3 | h3
      · exact absurd h3 (by positivity)
      · exact h3
  have hval0 := hq x hpos
  have hval : (0 : ℝ) < (q.val x : ℝ) := by exact_mod_cast hval0
  rw [← q.Qr_cast, hxr, q.Qr_smul] at hval
  have : (0 : ℝ) ≤ (D : ℝ) ^ 2 := by positivity
  nlinarith

/-- **Weakly positive forms are positive on the real nonnegative cone.** -/
theorem pos_real (hq : q.WeaklyPositive) (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (hv0 : v ≠ 0) :
    0 < q.Qr v := by
  suffices key : ∀ s : Finset ι, ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∀ i ∉ s, v i = 0) → v ≠ 0 →
      0 < q.Qr v from
    key univ v hv (fun i hi ↦ absurd (Finset.mem_univ i) hi) hv0
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro v₀ hv₀ hs₀ hne₀
  by_contra hle
  push_neg at hle
  have sum_pos : ∀ u : ι → ℝ, (∀ i, 0 ≤ u i) → u ≠ 0 → 0 < ∑ i, u i := by
    intro u hu hu0
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h; push_neg at h; exact hu0 (funext h)
    exact lt_of_lt_of_le ((hu i).lt_of_ne' hi)
      (Finset.single_le_sum (fun j _ ↦ hu j) (Finset.mem_univ i))
  -- the face of the simplex
  set K : Set (ι → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ (∀ i ∉ s, u i = 0) ∧ ∑ i, u i = 1}
  have hK : IsCompact K := by
    refine (isCompact_univ_pi (fun _ ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset
      ?_ ?_
    · have h1 : IsClosed {u : ι → ℝ | ∀ i, 0 ≤ u i} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
      have h2 : IsClosed {u : ι → ℝ | ∀ i ∉ s, u i = 0} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
          isClosed_eq (continuous_apply i) continuous_const
      have h3 : IsClosed {u : ι → ℝ | ∑ i, u i = 1} :=
        isClosed_eq (continuous_finset_sum _ fun i _ ↦ continuous_apply i) continuous_const
      exact h1.inter (h2.inter h3)
    · intro u hu
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
      intro i
      refine ⟨hu.1 i, ?_⟩
      rw [← hu.2.2]
      exact Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i)
  have hS0 := sum_pos v₀ hv₀ hne₀
  have hKne : (∑ i, v₀ i)⁻¹ • v₀ ∈ K := by
    refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, ?_⟩
    · exact mul_nonneg (inv_nonneg.2 hS0.le) (hv₀ i)
    · simp [hs₀ i hi]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hS0.ne'
  obtain ⟨v, hvK, hmin⟩ := hK.exists_isMinOn ⟨_, hKne⟩ q.continuous_Qr.continuousOn
  have hQv : q.Qr v ≤ 0 := by
    have h1 : q.Qr v ≤ q.Qr ((∑ i, v₀ i)⁻¹ • v₀) := hmin hKne
    rw [q.Qr_smul] at h1
    have : 0 ≤ ((∑ i, v₀ i)⁻¹) ^ 2 := by positivity
    nlinarith
  have hv0 : v ≠ 0 := by
    intro h
    have := hvK.2.2
    rw [h] at this
    simp at this
  -- the minimizer is in the relative interior
  have hpos : ∀ i ∈ s, 0 < v i := by
    intro i hi
    by_contra h
    have hvi : v i = 0 := le_antisymm (not_lt.1 h) (hvK.1 i)
    have := ih (s.erase i) (Finset.erase_ssubset hi) v hvK.1 (fun j hj ↦ by
      by_cases hji : j = i
      · rw [hji]; exact hvi
      · exact hvK.2.1 j fun h ↦ hj (Finset.mem_erase.2 ⟨hji, h⟩)) hv0
    linarith
  -- first-order condition
  have hfo : ∀ w : ι → ℝ, (∀ i ∉ s, w i = 0) → ∑ i, w i = 0 → q.Br v w = 0 := by
    intro w hws hw
    let f : ℝ → ℝ := fun t ↦ q.Qr (v + t • w)
    have hf : f = fun t ↦ q.Qr v + t * q.Br v w + t ^ 2 * q.Qr w :=
      funext fun t ↦ q.Qr_add_smul v w t
    have hderiv : HasDerivAt f (q.Br v w) 0 := by
      rw [hf]
      have h1 := ((hasDerivAt_id' (0 : ℝ)).mul_const (q.Br v w)).const_add (q.Qr v)
      have h2 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (q.Qr w)
      convert h1.add h2 using 1 <;> first | simp | (funext t; simp)
    have hloc : IsLocalMin f 0 := by
      have hev : ∀ᶠ t in nhds (0 : ℝ), v + t • w ∈ K := by
        have hi : ∀ i ∈ s, ∀ᶠ t in nhds (0 : ℝ), 0 < v i + t * w i := fun i hi ↦ by
          have hc : Continuous fun t : ℝ ↦ v i + t * w i := by fun_prop
          have : 0 < v i + 0 * w i := by simpa using hpos i hi
          exact hc.continuousAt.eventually (lt_mem_nhds this)
        filter_upwards [(Filter.eventually_all_finset s).2 hi] with t ht
        refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, ?_⟩
        · by_cases his : i ∈ s
          · exact (ht i his).le
          · simp [hvK.2.1 i his, hws i his]
        · simp [hvK.2.1 i hi, hws i hi]
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum, hvK.2.2, hw, mul_zero, add_zero]
      filter_upwards [hev] with t ht
      have h1 := hmin ht
      simp only [f, zero_smul, add_zero]
      exact h1
    exact hloc.hasDerivAt_eq_zero hderiv
  -- `B(v, e_i)` is constant on `s`
  obtain ⟨i₀, hi₀⟩ : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hv0
    funext i
    exact hvK.2.1 i (by simp [h])
  set lam := q.Lr v i₀
  have hL : ∀ i ∈ s, q.Lr v i = lam := by
    intro i hi
    have h := hfo (Pi.single i 1 - Pi.single i₀ 1) (fun j hj ↦ by
      have hji : j ≠ i := fun h ↦ hj (h ▸ hi)
      have hji₀ : j ≠ i₀ := fun h ↦ hj (h ▸ hi₀)
      simp [hji, hji₀]) (by simp)
    rw [Br_eq_sum] at h
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at h
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp),
      Finset.sum_eq_single i₀ (fun j _ hj ↦ by simp [hj]) (by simp)] at h
    simp only [Pi.single_eq_same, one_mul] at h
    linarith
  -- the homogeneous system has only the trivial solution
  have hker : ∀ (w : ι → ℝ) (ν : ℝ), (∀ i ∉ s, w i = 0) → (∀ i ∈ s, q.Lr w i = ν) →
      ∑ i, w i = 0 → w = 0 := by
    intro w ν hws hwL hw
    by_contra hw0
    have hneg : ∃ i, w i < 0 := by
      by_contra h
      push_neg at h
      apply hw0
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ h j).1 hw i (Finset.mem_univ i)
      exact this
    obtain ⟨j, hj⟩ := hneg
    have hjs : j ∈ s := by
      by_contra h; rw [hws j h] at hj; exact lt_irrefl _ hj
    set N := s.filter fun i ↦ w i < 0
    have hN : N.Nonempty := ⟨j, Finset.mem_filter.2 ⟨hjs, hj⟩⟩
    obtain ⟨i₁, hi₁N, hi₁min⟩ := N.exists_min_image (fun i ↦ v i / (-w i)) hN
    obtain ⟨hi₁s, hi₁neg⟩ := Finset.mem_filter.1 hi₁N
    set t₀ := v i₁ / (-w i₁)
    have ht₀ : 0 ≤ t₀ := div_nonneg (hvK.1 i₁) (by linarith)
    set u := v + t₀ • w
    have hQ : q.Qr u = q.Qr v := by
      rw [Qr_add_smul, q.Br_eq_zero_of_const hws hL hw, q.Qr_eq_of_kernel hws hwL hw]
      ring
    have hu : ∀ i, 0 ≤ u i := by
      intro i
      simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hwi : w i < 0
      · have his : i ∈ s := by
          by_contra h; rw [hws i h] at hwi; exact lt_irrefl _ hwi
        have h1 := hi₁min i (Finset.mem_filter.2 ⟨his, hwi⟩)
        have h2 : t₀ * (-w i) ≤ v i := by
          rw [le_div_iff₀ (by linarith)] at h1
          linarith
        linarith
      · push_neg at hwi
        have := hvK.1 i
        nlinarith
    have hu1 : u i₁ = 0 := by
      have hw1 : w i₁ ≠ 0 := hi₁neg.ne
      simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul, t₀]
      field_simp
      ring
    have hu0 : u ≠ 0 := by
      intro h
      have h1 : ∑ i, u i = 1 := by
        simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hvK.2.2, hw, mul_zero, add_zero]
      rw [h] at h1
      simp at h1
    have := ih (s.erase i₁) (Finset.erase_ssubset hi₁s) u hu (fun i hi ↦ by
      by_cases hii : i = i₁
      · rw [hii]; exact hu1
      · have his : i ∉ s := fun h ↦ hi (Finset.mem_erase.2 ⟨hii, h⟩)
        simp [u, hvK.2.1 i his, hws i his]) hu0
    linarith
  -- the minimizer is rational
  set M := q.faceMat s
  set Mr := M.map (Rat.cast : ℚ → ℝ)
  have hkerM : ∀ z : ι ⊕ Unit → ℝ, Mr *ᵥ z = 0 → z = 0 := by
    intro z hz
    have hw := hker (fun j ↦ z (Sum.inl j)) (z (Sum.inr ()))
      (fun i hi ↦ by
        have := congrFun hz (Sum.inl i)
        rw [q.faceMat_mulVec_inl, if_neg hi] at this
        exact this)
      (fun i hi ↦ by
        have := congrFun hz (Sum.inl i)
        rw [q.faceMat_mulVec_inl, if_pos hi] at this
        simpa [sub_eq_zero] using this)
      (by have := congrFun hz (Sum.inr ()); rwa [q.faceMat_mulVec_inr] at this)
    have hν : z (Sum.inr ()) = 0 := by
      have := congrFun hz (Sum.inl i₀)
      rw [q.faceMat_mulVec_inl, if_pos hi₀] at this
      have h0 : (fun j ↦ z (Sum.inl j)) = 0 := hw
      rw [h0] at this
      simpa [Lr] using this
    funext r
    rcases r with j | ⟨⟩
    · exact congrFun hw j
    · exact hν
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 : Mr.det = 0 := by
      have := RingHom.map_det (Rat.castHom ℝ) M
      rw [h0, map_zero] at this
      exact this.symm
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
    exact hz0 (hkerM z hz)
  set bq : ι ⊕ Unit → ℚ := Sum.elim 0 (fun _ ↦ 1)
  set zq := M⁻¹ *ᵥ bq
  have hzq : M *ᵥ zq = bq := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have hzr : Mr *ᵥ (fun r ↦ (zq r : ℝ)) = fun r ↦ (bq r : ℝ) := by
    funext r
    have := RingHom.map_mulVec (Rat.castHom ℝ) M zq r
    rw [hzq] at this
    exact this.symm
  set zs : ι ⊕ Unit → ℝ := Sum.elim v (fun _ ↦ lam)
  have hzs : Mr *ᵥ zs = fun r ↦ (bq r : ℝ) := by
    funext r
    rcases r with i | ⟨⟩
    · rw [q.faceMat_mulVec_inl]
      by_cases hi : i ∈ s
      · rw [if_pos hi]; simp [zs, bq, hL i hi]
      · rw [if_neg hi]; simp [zs, bq, hvK.2.1 i hi]
    · rw [q.faceMat_mulVec_inr]; simp [zs, bq, hvK.2.2]
  have heq : zs = fun r ↦ (zq r : ℝ) := by
    have := hkerM (zs - fun r ↦ (zq r : ℝ)) (by rw [Matrix.mulVec_sub, hzs, hzr, sub_self])
    exact sub_eq_zero.1 this
  have hvr : (fun i ↦ ((zq (Sum.inl i) : ℚ) : ℝ)) = v := by
    funext i
    have := congrFun heq (Sum.inl i)
    simp only [zs, Sum.elim_inl] at this
    exact this.symm
  refine q.not_rat hq (fun i ↦ zq (Sum.inl i)) (fun i ↦ ?_) (fun h ↦ hv0 ?_) ?_
  · have := hvK.1 i
    rw [← hvr] at this
    have h2 : (0 : ℝ) ≤ (zq (Sum.inl i) : ℝ) := by simpa using this
    exact_mod_cast h2
  · rw [← hvr]
    funext i
    have := congrFun h i
    simp only [Pi.zero_apply] at this
    simp [this]
  · rw [hvr]; exact hQv

/-- **Drozd's lemma**: a weakly positive unit form has only finitely many positive roots. -/
theorem finite_roots (hq : q.WeaklyPositive) : {x : ι → ℤ | Pos x ∧ q.val x = 1}.Finite := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · refine Set.Finite.subset (Set.finite_empty) fun x hx ↦ ?_
    exact absurd (funext fun i ↦ (IsEmpty.false i).elim) hx.1.2
  set K : Set (ι → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1}
  have hK : IsCompact K := by
    refine (isCompact_univ_pi (fun _ ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset
      ?_ ?_
    · have h1 : IsClosed {u : ι → ℝ | ∀ i, 0 ≤ u i} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
      have h3 : IsClosed {u : ι → ℝ | ∑ i, u i = 1} :=
        isClosed_eq (continuous_finset_sum _ fun i _ ↦ continuous_apply i) continuous_const
      exact h1.inter h3
    · intro u hu
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
      intro i
      refine ⟨hu.1 i, ?_⟩
      rw [← hu.2]
      exact Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i)
  have hKne : (Pi.single i₀ 1 : ι → ℝ) ∈ K := by
    refine ⟨fun i ↦ ?_, by simp⟩
    by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  obtain ⟨u₀, hu₀K, hmin⟩ := hK.exists_isMinOn ⟨_, hKne⟩ q.continuous_Qr.continuousOn
  have hu₀0 : u₀ ≠ 0 := by
    intro h; have := hu₀K.2; rw [h] at this; simp at this
  have hc : 0 < q.Qr u₀ := q.pos_real hq u₀ hu₀K.1 hu₀0
  set N : ℕ := ⌈(q.Qr u₀)⁻¹⌉₊
  refine (Set.finite_Icc (0 : ι → ℤ) (fun _ ↦ (N : ℤ))).subset fun x hx ↦ ?_
  obtain ⟨⟨hx0, hxne⟩, hx1⟩ := hx
  set xr : ι → ℝ := fun i ↦ (x i : ℝ)
  set S := ∑ i, xr i
  have hS1 : 1 ≤ S := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h; push_neg at h; exact hxne (funext h)
    have h1 : (1 : ℝ) ≤ xr i := by
      have : 1 ≤ x i := by have := hx0 i; omega
      show (1 : ℝ) ≤ (x i : ℝ)
      exact_mod_cast this
    exact h1.trans (Finset.single_le_sum (fun j _ ↦ by
      have := hx0 j; simp only [xr]; exact_mod_cast this) (Finset.mem_univ i))
  have hQx : q.Qr xr = 1 := by rw [q.Qr_cast, hx1]; norm_num
  have huK : S⁻¹ • xr ∈ K := by
    refine ⟨fun i ↦ mul_nonneg (inv_nonneg.2 (by linarith)) (by
      have := hx0 i; simp only [xr]; exact_mod_cast this), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ (by linarith)
  have h1 : q.Qr u₀ ≤ q.Qr (S⁻¹ • xr) := hmin huK
  rw [q.Qr_smul, hQx, mul_one] at h1
  have hS2 : S ^ 2 * q.Qr u₀ ≤ 1 := by
    have e : S ^ 2 * (S⁻¹) ^ 2 = 1 := by field_simp
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg S)
    linarith
  have hSN : S ≤ N := by
    have h6 : S * q.Qr u₀ ≤ 1 := by
      have : S * q.Qr u₀ ≤ S ^ 2 * q.Qr u₀ := by
        have : S ≤ S ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hc.le
      linarith
    have h3 : S ≤ (q.Qr u₀)⁻¹ := by
      calc S = S * q.Qr u₀ * (q.Qr u₀)⁻¹ := by field_simp
        _ ≤ 1 * (q.Qr u₀)⁻¹ := by gcongr
        _ = (q.Qr u₀)⁻¹ := one_mul _
    exact h3.trans (Nat.le_ceil _)
  refine ⟨fun i ↦ hx0 i, fun i ↦ ?_⟩
  have h4 : xr i ≤ S := Finset.single_le_sum (fun j _ ↦ by
    have := hx0 j; simp only [xr]; exact_mod_cast this) (Finset.mem_univ i)
  have h5 : (x i : ℝ) ≤ (N : ℝ) := h4.trans hSN
  exact_mod_cast h5

end UnitForm

end LargeIndecomposable.Forms
