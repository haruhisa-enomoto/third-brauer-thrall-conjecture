module

public import LargeIndecomposable.UnitForms.Reduction

/-!
# Graph forms and patterns

For a graph form (off-diagonal coefficients `0` or `-1`),
`B(u, u) = 2 Σ u_v² - Σ_v u_v Σ_{w ~ v} u_w` (`B_self_graph`). For `u ≥ 0` the
neighbour sums can be replaced by sums over any subsets of the neighbours
(`B_self_le_pattern`). A nonempty set in which every point has two neighbours gives
`q(1_S) ≤ 0` (`val_indicator_le`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

open Finset

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (q : UnitForm ι)

/-- The neighbours of `v` in the graph of `q`. -/
def nbrs (v : ι) : Finset ι := univ.filter fun w ↦ w ≠ v ∧ q.c v w = -1

/-- **The graph formula** for `B(u, u)`. -/
lemma B_self_graph (hg : ∀ a b, a ≠ b → q.c a b = 0 ∨ q.c a b = -1) (u : ι → ℤ) :
    q.B u u = 2 * ∑ v, u v ^ 2 - ∑ v, u v * ∑ w ∈ q.nbrs v, u w := by
  unfold B
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), q.diag, Finset.mul_sum]
  have : ∑ w ∈ univ.erase v, q.c v w * u v * u w = -∑ w ∈ q.nbrs v, u v * u w := by
    rw [← Finset.sum_neg_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not (univ.erase v) (fun w ↦ q.c v w = -1)]
    have h0 : ∑ w ∈ (univ.erase v).filter (fun w ↦ ¬q.c v w = -1), q.c v w * u v * u w = 0 := by
      refine Finset.sum_eq_zero fun w hw ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_erase] at hw
      rcases hg v w (Ne.symm hw.1.1) with h | h
      · rw [h]; ring
      · exact absurd h hw.2
    rw [h0, add_zero]
    have hset : (univ.erase v).filter (fun w ↦ q.c v w = -1) = q.nbrs v := by
      ext w; simp [nbrs, and_comm]
    rw [hset]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    simp only [nbrs, Finset.mem_filter] at hw
    rw [hw.2.2]; ring
  rw [this]; ring

/-- **Pattern bound**: for `u ≥ 0` and subsets `P v` of the neighbours. -/
lemma B_self_le_pattern (hg : ∀ a b, a ≠ b → q.c a b = 0 ∨ q.c a b = -1) {u : ι → ℤ}
    (hu : ∀ v, 0 ≤ u v) (P : ι → Finset ι) (hP : ∀ v, P v ⊆ q.nbrs v) :
    q.B u u ≤ 2 * ∑ v, u v ^ 2 - ∑ v, u v * ∑ w ∈ P v, u w := by
  rw [q.B_self_graph hg]
  have : ∑ v, u v * ∑ w ∈ P v, u w ≤ ∑ v, u v * ∑ w ∈ q.nbrs v, u w :=
    Finset.sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (hP v) fun w _ _ ↦ hu w) (hu v)
  linarith

/-- **Two-core pattern**: if every point of a nonempty `S` has two neighbours in `S`,
then `q(1_S) ≤ 0`. -/
lemma val_indicator_le (hg : ∀ a b, a ≠ b → q.c a b = 0 ∨ q.c a b = -1) (S : Finset ι)
    (hS : ∀ v ∈ S, 2 ≤ (q.nbrs v ∩ S).card) :
    q.val (fun v ↦ if v ∈ S then 1 else 0) ≤ 0 := by
  set u : ι → ℤ := fun v ↦ if v ∈ S then 1 else 0 with hu
  have hu0 : ∀ v, 0 ≤ u v := fun v ↦ by simp only [hu]; split_ifs <;> norm_num
  have h := q.B_self_le_pattern hg hu0 (fun v ↦ q.nbrs v ∩ S) fun v ↦ Finset.inter_subset_left
  have e1 : ∑ v, u v ^ 2 = (S.card : ℤ) := by
    simp only [hu]
    rw [show (fun v ↦ (if v ∈ S then (1 : ℤ) else 0) ^ 2) = fun v ↦ if v ∈ S then 1 else 0 by
      funext v; split_ifs <;> norm_num]
    rw [Finset.sum_ite_mem, Finset.univ_inter]; simp
  have e2 : ∑ v, u v * ∑ w ∈ q.nbrs v ∩ S, u w = ∑ v ∈ S, ((q.nbrs v ∩ S).card : ℤ) := by
    simp only [hu]
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ S)]
    have h0 : ∑ v ∈ univ.filter (fun v ↦ v ∉ S),
        (if v ∈ S then (1 : ℤ) else 0) * ∑ w ∈ q.nbrs v ∩ S, (if w ∈ S then (1 : ℤ) else 0) = 0 :=
      Finset.sum_eq_zero fun v hv ↦ by simp only [Finset.mem_filter] at hv; simp [hv.2]
    rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun v hv ↦ ?_
    rw [if_pos hv, one_mul]
    rw [Finset.sum_congr rfl fun w hw ↦ if_pos (Finset.mem_inter.1 hw).2]
    simp
  have e3 : ∑ v ∈ S, (2 : ℤ) ≤ ∑ v ∈ S, ((q.nbrs v ∩ S).card : ℤ) :=
    Finset.sum_le_sum fun v hv ↦ by exact_mod_cast hS v hv
  rw [Finset.sum_const, nsmul_eq_mul] at e3
  have := q.two_mul_val u
  rw [e1, e2] at h
  linarith

/-- Graph forms: off-diagonal coefficients `0` or `-1`. -/
def IsGraph : Prop := ∀ a b, a ≠ b → q.c a b = 0 ∨ q.c a b = -1

/-- A positive radical vector with a coordinate `1` and all coordinates at most `6`. -/
def Good : Prop :=
  ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ (∀ x, q.B z x = 0) ∧ (∃ c, z c = 1) ∧ ∀ a, z a ≤ 6

variable {q}

lemma not_mem_nbrs (v : ι) : v ∉ q.nbrs v := by simp [nbrs]

lemma mem_nbrs_comm {v w : ι} : w ∈ q.nbrs v ↔ v ∈ q.nbrs w := by
  simp only [nbrs, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [q.symm v w]
  exact ⟨fun h ↦ ⟨Ne.symm h.1, h.2⟩, fun h ↦ ⟨Ne.symm h.1, h.2⟩⟩

lemma ne_of_mem_nbrs {v w : ι} (h : w ∈ q.nbrs v) : w ≠ v := by
  simp only [nbrs, Finset.mem_filter] at h; exact h.2.1

/-- The value of `B(x, e_v)` for a graph form. -/
lemma B_single_graph (hg : q.IsGraph) (x : ι → ℤ) (v : ι) :
    q.B x (Pi.single v 1) = 2 * x v - ∑ w ∈ q.nbrs v, x w := by
  rw [B_single_right, ← Finset.add_sum_erase _ _ (Finset.mem_univ v), q.diag]
  rw [← Finset.sum_filter_add_sum_filter_not (univ.erase v) (fun w ↦ q.c v w = -1)]
  have h0 : ∑ w ∈ (univ.erase v).filter (fun w ↦ ¬q.c v w = -1), q.c w v * x w = 0 := by
    refine Finset.sum_eq_zero fun w hw ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_erase] at hw
    rcases hg v w (Ne.symm hw.1.1) with h | h
    · rw [q.symm, h]; ring
    · exact absurd h hw.2
  have hset : (univ.erase v).filter (fun w ↦ q.c v w = -1) = q.nbrs v := by
    ext w; simp [nbrs, and_comm]
  rw [h0, add_zero, hset, Finset.sum_congr rfl fun w hw ↦ by
    simp only [nbrs, Finset.mem_filter] at hw; rw [q.symm, hw.2.2]]
  simp [Finset.sum_neg_distrib]; ring

/-- **Local pattern lemma**: if `u ≥ 0` and every `v` in the support has neighbour sum at
least `2 u_v`, then `q(u) ≤ 0`. -/
lemma val_le_of_local (hg : q.IsGraph) {u : ι → ℤ} (hu : ∀ v, 0 ≤ u v)
    (hloc : ∀ v, 0 < u v → 2 * u v ≤ ∑ w ∈ q.nbrs v, u w) : q.val u ≤ 0 := by
  have e := q.two_mul_val u
  rw [B_eq_sum_single] at e
  have : ∑ a, u a * q.B u (Pi.single a 1) ≤ 0 := by
    refine Finset.sum_nonpos fun a _ ↦ ?_
    rw [B_single_graph hg]
    rcases (hu a).lt_or_eq with h | h
    · exact mul_nonpos_of_nonneg_of_nonpos (hu a) (by linarith [hloc a h])
    · rw [← h]; simp
  linarith

/-- Radical vectors are additive. -/
lemma additive (hg : q.IsGraph) {y : ι → ℤ} (hrad : ∀ x, q.B y x = 0) (v : ι) :
    2 * y v = ∑ w ∈ q.nbrs v, y w := by
  have := hrad (Pi.single v 1); rw [B_single_graph hg] at this; linarith

/-- A positive radical vector whose least coordinate divides the others gives `Good`. -/
lemma good_of_dvd {y : ι → ℤ} (hy : ∀ a, 0 < y a) (hrad : ∀ x, q.B y x = 0) {a : ι}
    (hdvd : ∀ c, y a ∣ y c) (hbd : ∀ c, y c ≤ 6 * y a) : q.Good := by
  refine ⟨fun c ↦ y c / y a, fun c ↦ ?_, fun x ↦ ?_, ⟨a, Int.ediv_self (hy a).ne'⟩, fun c ↦ ?_⟩
  · obtain ⟨t, ht⟩ := hdvd c
    show 0 < y c / y a
    rw [ht, Int.mul_ediv_cancel_left _ (hy a).ne']
    have := hy c; rw [ht] at this
    exact pos_of_mul_pos_right this (hy a).le
  · have hy' : y = y a • fun c ↦ y c / y a := by
      funext c; obtain ⟨t, ht⟩ := hdvd c
      simp [ht, Int.mul_ediv_cancel_left _ (hy a).ne']
    have h := hrad x
    rw [hy', B_smul_left] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (hy a).ne'
    · exact h
  · obtain ⟨t, ht⟩ := hdvd c
    show y c / y a ≤ 6
    rw [ht, Int.mul_ediv_cancel_left _ (hy a).ne']
    have h1 := hbd c
    rw [ht] at h1
    have := hy a
    nlinarith

/-- A pattern with a coordinate `1` gives `Good`. -/
lemma Rad1.good_of_pattern {y : ι → ℤ} (h : q.Rad1 y) {u : ι → ℤ} (hu : q.val u ≤ 0)
    {a : ι} (ha : u a = 1) (hub : ∀ c, u c ≤ 6) : q.Good := by
  have e := h.eq_smul_of_nonpos hu ha
  refine good_of_dvd h.2.1 h.2.2.1 (a := a) (fun c ↦ ⟨u c, ?_⟩) fun c ↦ ?_
  · conv_lhs => rw [e]
    rfl
  · have hc : y c = y a * u c := by
      conv_lhs => rw [e]
      rfl
    rw [hc]
    have := h.2.1 a
    nlinarith [hub c]

/-- **Connectivity**: a nonempty neighbour-closed set is everything. -/
lemma Rad1.closed_eq_univ (hg : q.IsGraph) {y : ι → ℤ} (h : q.Rad1 y) (S : Finset ι)
    (hS : S.Nonempty) (hcl : ∀ v ∈ S, q.nbrs v ⊆ S) (c : ι) : c ∈ S := by
  by_contra hc
  set u : ι → ℤ := fun v ↦ if v ∈ S then y v else 0 with hu
  have hB : ∀ v, u v * q.B u (Pi.single v 1) = 0 := by
    intro v
    by_cases hv : v ∈ S
    · rw [B_single_graph hg]
      have : ∑ w ∈ q.nbrs v, u w = ∑ w ∈ q.nbrs v, y w :=
        Finset.sum_congr rfl fun w hw ↦ by simp [hu, hcl v hv hw]
      rw [this, ← additive hg h.2.2.1 v]
      simp [hu, hv]
    · simp [hu, hv]
  have hv0 : q.val u = 0 := by
    have e := q.two_mul_val u
    rw [B_eq_sum_single, Finset.sum_eq_zero fun v _ ↦ hB v] at e
    omega
  obtain ⟨d, hd⟩ := hS
  have := h.2.2.2 u hv0 d c
  simp only [hu, if_pos hd, if_neg hc, mul_zero] at this
  have := mul_pos (h.2.1 d) (h.2.1 c)
  linarith

/-- **Case 2-core.** -/
lemma Rad1.good_of_core (hg : q.IsGraph) {y : ι → ℤ} (h : q.Rad1 y) (S : Finset ι)
    (hS : S.Nonempty) (hcore : ∀ v ∈ S, 2 ≤ (q.nbrs v ∩ S).card) : q.Good := by
  obtain ⟨a, ha⟩ := hS
  refine h.good_of_pattern (u := fun v ↦ if v ∈ S then 1 else 0) ?_ (a := a) (by simp [ha])
    (fun c ↦ by split_ifs <;> norm_num)
  refine val_le_of_local hg (fun v ↦ by split_ifs <;> norm_num) fun v hv ↦ ?_
  have hvS : v ∈ S := by by_contra h'; simp [h'] at hv
  rw [if_pos hvS, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ S)]
  have h1 : ∑ w ∈ (q.nbrs v).filter (· ∈ S), (if w ∈ S then (1 : ℤ) else 0) =
      ((q.nbrs v ∩ S).card : ℤ) := by
    rw [Finset.sum_congr rfl fun w hw ↦ if_pos (Finset.mem_filter.1 hw).2,
      Finset.filter_mem_eq_inter]
    simp
  have h2 : 0 ≤ ∑ w ∈ (q.nbrs v).filter (· ∉ S), (if w ∈ S then (1 : ℤ) else 0) :=
    Finset.sum_nonneg fun w _ ↦ by split_ifs <;> norm_num
  have := hcore v hvS
  rw [h1]; omega

/-- **Case degree `≥ 4`** (`D̃₄`). -/
lemma Rad1.good_of_deg4 (hg : q.IsGraph) {y : ι → ℤ} (h : q.Rad1 y) (v : ι)
    (hv : 4 ≤ (q.nbrs v).card) : q.Good := by
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hv
  obtain ⟨a, ha⟩ : T.Nonempty := by rw [← Finset.card_pos]; omega
  have hvT : v ∉ T := fun h' ↦ not_mem_nbrs v (hT h')
  set u : ι → ℤ := fun w ↦ if w = v then 2 else if w ∈ T then 1 else 0 with hu
  have hav : a ≠ v := fun h' ↦ hvT (h' ▸ ha)
  refine h.good_of_pattern (u := u) ?_ (a := a) (by simp [hu, hav, ha])
    (fun c ↦ by simp only [hu]; split_ifs <;> norm_num)
  refine val_le_of_local hg (fun w ↦ by simp only [hu]; split_ifs <;> norm_num) fun w hw ↦ ?_
  have hnn : ∀ s : Finset ι, 0 ≤ ∑ x ∈ s, u x :=
    fun s ↦ Finset.sum_nonneg fun x _ ↦ by simp only [hu]; split_ifs <;> norm_num
  by_cases hwv : w = v
  · subst hwv
    rw [← Finset.sum_sdiff hT]
    have : ∑ x ∈ T, u x = 4 := by
      rw [Finset.sum_congr rfl fun x hx ↦ show u x = 1 by
        simp [hu, hx, show x ≠ w from fun h' ↦ hvT (h' ▸ hx)]]
      simp [hTc]
    have := hnn (q.nbrs w \ T)
    have hw2 : u w = 2 := by simp [hu]
    rw [hw2]; omega
  · have hwT : w ∈ T := by by_contra h'; simp [hu, hwv, h'] at hw
    have hvw : v ∈ q.nbrs w := mem_nbrs_comm.1 (hT hwT)
    rw [← Finset.add_sum_erase _ _ hvw]
    have := hnn ((q.nbrs w).erase v)
    simp only [hu, if_pos rfl, if_neg hwv, if_pos hwT] at this ⊢
    omega

end UnitForm

end LargeIndecomposable.Forms
