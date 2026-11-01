module

public import LargeIndecomposable.UnitForms.Graph

/-!
# Walks in graph forms without cycles

`NoCore q`: every nonempty set has a point with at most one neighbour inside it (the
graph of `q` is a forest). Then non-backtracking walks have distinct points
(`nb_inj`). `walk b n` starts at `b`, steps to `n`, then keeps going away from where
it came; `IsStop b n k` says it passes through points of degree two until step `k`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

open Finset

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (q : UnitForm ι)

/-- The graph of `q` has no cycle. -/
def NoCore : Prop := ∀ S : Finset ι, S.Nonempty → ∃ v ∈ S, (q.nbrs v ∩ S).card ≤ 1

/-- A neighbour of `c` other than `p` (if any). -/
def other (p c : ι) : ι := if h : ((q.nbrs c).erase p).Nonempty then h.choose else c

/-- Pairs (previous, current) of the walk. -/
def walkPair (b n : ι) : ℕ → ι × ι
  | 0 => (b, n)
  | i + 1 => ((walkPair b n i).2, q.other (walkPair b n i).1 (walkPair b n i).2)

/-- The walk from `b` through `n`. -/
def walk (b n : ι) (i : ℕ) : ι := (q.walkPair b n i).1

/-- The walk passes through degree-two points strictly between steps `0` and `k`, and
stops at step `k`. -/
def IsStop (b n : ι) (k : ℕ) : Prop :=
  1 ≤ k ∧ (∀ i, 1 ≤ i → i < k → (q.nbrs (q.walk b n i)).card = 2) ∧
    (q.nbrs (q.walk b n k)).card ≠ 2

variable {q}

lemma walk_zero (b n : ι) : q.walk b n 0 = b := rfl

lemma walk_one (b n : ι) : q.walk b n 1 = n := rfl

lemma walk_succ_succ (b n : ι) (i : ℕ) :
    q.walk b n (i + 2) = q.other (q.walk b n i) (q.walk b n (i + 1)) := rfl

lemma other_spec {p c : ι} (h : 2 ≤ (q.nbrs c).card) :
    q.other p c ∈ q.nbrs c ∧ q.other p c ≠ p := by
  have hne : ((q.nbrs c).erase p).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.pred_card_le_card_erase (s := q.nbrs c) (a := p)
    omega
  unfold other
  rw [dif_pos hne]
  exact ⟨Finset.mem_of_mem_erase hne.choose_spec, Finset.ne_of_mem_erase hne.choose_spec⟩

/-- **Non-backtracking walks in a forest have distinct points.** -/
lemma nb_inj (hc : q.NoCore) (w : ℕ → ι) (K : ℕ)
    (hstep : ∀ i < K, w (i + 1) ∈ q.nbrs (w i))
    (hnb : ∀ i, i + 2 ≤ K → w (i + 2) ≠ w i) {i j : ℕ} (hij : i < j) (hjK : j ≤ K) :
    w i ≠ w j := by
  classical
  intro heq
  have hex : ∃ g, ∃ i, 0 < g ∧ i + g ≤ K ∧ w i = w (i + g) :=
    ⟨j - i, i, by omega, by omega, by rw [heq]; congr 1; omega⟩
  obtain ⟨i0, hg0, hgK, hw⟩ := Nat.find_spec hex
  set g := Nat.find hex with hgdef
  have hmin : ∀ g' < g, ∀ i', 0 < g' → i' + g' ≤ K → w i' ≠ w (i' + g') :=
    fun g' hg' i' h1 h2 h3 ↦ Nat.find_min hex hg' ⟨i', h1, h2, h3⟩
  have hg1 : g ≠ 1 := by
    intro h1
    have := ne_of_mem_nbrs (hstep i0 (by omega))
    rw [h1] at hw
    exact this hw.symm
  have hg2 : g ≠ 2 := by
    intro h2
    rw [h2] at hw
    exact hnb i0 (by omega) hw.symm
  set S := (Finset.range g).image fun l ↦ w (i0 + l) with hS
  have memS : ∀ l < g, w (i0 + l) ∈ S := fun l hl ↦ Finset.mem_image_of_mem _
    (Finset.mem_range.2 hl)
  obtain ⟨v, hv, hcard⟩ := hc S ⟨_, memS 0 hg0⟩
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
  rw [Finset.mem_range] at hl
  have hsucc : w (i0 + l + 1) ∈ q.nbrs (w (i0 + l)) ∩ S := by
    refine Finset.mem_inter.2 ⟨hstep _ (by omega), ?_⟩
    by_cases hl1 : l + 1 < g
    · exact memS (l + 1) hl1
    · have : i0 + l + 1 = i0 + g := by omega
      rw [this, ← hw]
      simpa using memS 0 hg0
  obtain ⟨p, hp, hpne⟩ : ∃ p ∈ q.nbrs (w (i0 + l)) ∩ S, p ≠ w (i0 + l + 1) := by
    by_cases hl0 : l = 0
    · subst hl0
      refine ⟨w (i0 + (g - 1)), Finset.mem_inter.2 ⟨?_, memS _ (by omega)⟩, ?_⟩
      · have := hstep (i0 + (g - 1)) (by omega)
        rw [show i0 + (g - 1) + 1 = i0 + g by omega, ← hw] at this
        simpa using mem_nbrs_comm.1 this
      · intro h
        have := hmin (g - 2) (by omega) (i0 + 1) (by omega) (by omega)
        apply this
        rw [show i0 + 1 + (g - 2) = i0 + (g - 1) by omega, h]
    · refine ⟨w (i0 + (l - 1)), Finset.mem_inter.2 ⟨?_, memS _ (by omega)⟩, ?_⟩
      · have := hstep (i0 + (l - 1)) (by omega)
        rw [show i0 + (l - 1) + 1 = i0 + l by omega] at this
        exact mem_nbrs_comm.1 this
      · intro h
        have := hnb (i0 + (l - 1)) (by omega)
        rw [show i0 + (l - 1) + 2 = i0 + l + 1 by omega] at this
        exact this h.symm
  have : 1 < (q.nbrs (w (i0 + l)) ∩ S).card :=
    Finset.one_lt_card.2 ⟨_, hp, _, hsucc, hpne⟩
  omega

section Stop

variable {b n : ι} {k : ℕ}

lemma IsStop.step (hn : n ∈ q.nbrs b) (hk : q.IsStop b n k) {i : ℕ} (hi : i < k) :
    q.walk b n (i + 1) ∈ q.nbrs (q.walk b n i) := by
  rcases i with _ | i
  · exact hn
  · rw [walk_succ_succ]
    exact (other_spec (by rw [hk.2.1 (i + 1) (by omega) hi])).1

lemma IsStop.nb (hk : q.IsStop b n k) {i : ℕ} (hi : i + 2 ≤ k) :
    q.walk b n (i + 2) ≠ q.walk b n i := by
  rw [walk_succ_succ]
  exact (other_spec (by rw [hk.2.1 (i + 1) (by omega) (by omega)])).2

lemma IsStop.inj (hc : q.NoCore) (hn : n ∈ q.nbrs b) (hk : q.IsStop b n k) {i j : ℕ}
    (hij : i < j) (hjk : j ≤ k) : q.walk b n i ≠ q.walk b n j :=
  nb_inj hc (q.walk b n) k (fun l hl ↦ hk.step hn (i := l) hl) (fun l hl ↦ hk.nb (i := l) hl)
    hij hjk

/-- At a degree-two point the neighbours are the previous and next points. -/
lemma IsStop.nbrs_eq (hn : n ∈ q.nbrs b) (hk : q.IsStop b n k) {i : ℕ} (hi : i + 1 < k) :
    q.nbrs (q.walk b n (i + 1)) = {q.walk b n i, q.walk b n (i + 2)} := by
  have h1 := mem_nbrs_comm.1 (hk.step hn (i := i) (by omega))
  have h2 := hk.step hn (i := i + 1) hi
  have hne := hk.nb (i := i) (by omega)
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  · rw [hk.2.1 (i + 1) (by omega) hi, Finset.card_pair (Ne.symm hne)]

/-- The last neighbour: a point of degree one at the stop is a leaf of the walk. -/
lemma IsStop.nbrs_end (hn : n ∈ q.nbrs b) (hk : q.IsStop b n k)
    (h1 : (q.nbrs (q.walk b n k)).card = 1) :
    q.nbrs (q.walk b n k) = {q.walk b n (k - 1)} := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
  have := mem_nbrs_comm.1 (hk.step hn (i := k - 1) (by have := hk.1; omega))
  rw [show k - 1 + 1 = k by have := hk.1; omega] at this
  rw [hx] at this ⊢
  rw [Finset.mem_singleton.1 this]

/-- Values along the walk form an arithmetic progression. -/
lemma IsStop.val (hg : q.IsGraph) {y : ι → ℤ} (hrad : ∀ x, q.B y x = 0)
    (hn : n ∈ q.nbrs b) (hk : q.IsStop b n k) {i : ℕ} (hi : i ≤ k) :
    y (q.walk b n i) = y b + i * (y n - y b) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  rcases i with _ | _ | i
  · simp [walk_zero]
  · simp [walk_one]
  · have e := additive hg hrad (q.walk b n (i + 1))
    rw [hk.nbrs_eq hn (by omega), Finset.sum_pair (hk.nb (by omega)).symm] at e
    have e1 := ih i (by omega) (by omega)
    have e2 := ih (i + 1) (by omega) (by omega)
    push_cast at e1 e2 ⊢
    linarith

/-- **Every walk from a neighbour stops** (in a forest). -/
lemma exists_stop (hc : q.NoCore) (hn : n ∈ q.nbrs b) : ∃ k, q.IsStop b n k := by
  classical
  by_contra hno
  push Not at hno
  have hall : ∀ i, 1 ≤ i → (q.nbrs (q.walk b n i)).card = 2 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    intro hi
    by_contra hne
    exact hno i ⟨hi, fun j hj1 hji ↦ ih j hji hj1, hne⟩
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (q.walk b n)
  wlog h : i < j generalizing i j
  · exact this j i (Ne.symm hij) heq.symm (by omega)
  refine nb_inj hc (q.walk b n) j (fun l hl ↦ ?_) (fun l hl ↦ ?_) h le_rfl heq
  · rcases l with _ | l
    · exact hn
    · rw [walk_succ_succ]
      exact (other_spec (by rw [hall (l + 1) (by omega)])).1
  · rw [walk_succ_succ]
    exact (other_spec (by rw [hall (l + 1) (by omega)])).2

end Stop

/-- `1/a + 1/b + 1/c = 1` with `a, b, c ≥ 2` forces `a, b, c ≤ 6`. -/
lemma tri_le_six (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (E : a * b * c = b * c + a * c + a * b) :
    a ≤ 6 ∧ b ≤ 6 ∧ c ≤ 6 := by
  have bound : ∀ a b c : ℕ, 2 ≤ a → a ≤ 3 → 2 ≤ b → 2 ≤ c →
      a * b * c = b * c + a * c + a * b → b ≤ 6 := by
    intro a b c ha ha3 hb hc E
    by_contra hb6
    rcases Nat.eq_or_lt_of_le hc with hc2 | hc3
    · subst hc2; interval_cases a <;> omega
    have key : (0 : ℤ) ≤ ((b : ℤ) - 7) * ((c : ℤ) - 3) :=
      mul_nonneg (by push_cast; omega) (by push_cast; omega)
    have E' : (a : ℤ) * b * c = b * c + a * c + a * b := by exact_mod_cast E
    interval_cases a <;> push_cast at E' <;> nlinarith
  have small : a ≤ 3 ∨ b ≤ 3 ∨ c ≤ 3 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : 4 * (b * c) ≤ a * (b * c) := Nat.mul_le_mul_right _ h1
    have e2 : 4 * (a * c) ≤ b * (a * c) := Nat.mul_le_mul_right _ h2
    have e3 : 4 * (a * b) ≤ c * (a * b) := Nat.mul_le_mul_right _ h3
    have : 0 < a * b * c := by positivity
    nlinarith
  have hall : a ≤ 6 ∧ b ≤ 6 ∧ c ≤ 6 := by
    rcases small with h | h | h
    · exact ⟨by omega, bound a b c ha h hb hc E,
        bound a c b ha h hc hb (by linarith [E, show a * c * b = a * b * c by ring])⟩
    · exact ⟨bound b a c hb h ha hc (by linarith [E, show b * a * c = a * b * c by ring]),
        by omega, bound b c a hb h hc ha (by linarith [E, show b * c * a = a * b * c by ring])⟩
    · exact ⟨bound c a b hc h ha hb (by linarith [E, show c * a * b = a * b * c by ring]),
        bound c b a hc h hb ha (by linarith [E, show c * b * a = a * b * c by ring]), by omega⟩
  exact hall

/-- `1/a + 1/b + 1/c = 1` with `a, b, c ≥ 2`: `(3,3,3)`, `(2,4,4)`, `(2,3,6)`; one of them
is divisible by the other two. -/
lemma tri_dvd (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (E : a * b * c = b * c + a * c + a * b) :
    (b ∣ a ∧ c ∣ a) ∨ (a ∣ b ∧ c ∣ b) ∨ (a ∣ c ∧ b ∣ c) := by
  obtain ⟨h1, h2, h3⟩ := tri_le_six a b c ha hb hc E
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | decide

/-- Extending a walk between two points of degree three by a neighbour at each end
keeps it non-backtracking, so the new points are off the walk and distinct. -/
lemma IsStop.ext_inj (hc : q.NoCore) {b n : ι} {k : ℕ} (hn : n ∈ q.nbrs b)
    (hk : q.IsStop b n k) {x z : ι} (hx : x ∈ (q.nbrs b).erase n)
    (hz : z ∈ (q.nbrs (q.walk b n k)).erase (q.walk b n (k - 1))) :
    (∀ i ≤ k, x ≠ q.walk b n i) ∧ (∀ i ≤ k, z ≠ q.walk b n i) ∧ x ≠ z := by
  have hk1 := hk.1
  set W := q.walk b n with hW
  set e : ℕ → ι := fun i ↦ if i = 0 then x else if i ≤ k + 1 then W (i - 1) else z with he
  have e0 : e 0 = x := by simp [he]
  have eW : ∀ i ≤ k, e (i + 1) = W i := fun i hi ↦ by
    simp [he, show i ≤ k by omega]
  have ez : e (k + 2) = z := by simp [he]
  have hstep : ∀ i < k + 2, e (i + 1) ∈ q.nbrs (e i) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [e0, eW 0 (by omega)]
      exact mem_nbrs_comm.1 (Finset.mem_of_mem_erase hx)
    · by_cases hik : i ≤ k
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [eW (j + 1) hik, eW j (by omega)]
        exact hk.step hn (i := j) (by omega)
      · obtain rfl : i = k + 1 := by omega
        rw [ez, eW k le_rfl]
        exact Finset.mem_of_mem_erase hz
  have hnb : ∀ i, i + 2 ≤ k + 2 → e (i + 2) ≠ e i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [e0, eW 1 (by omega)]
      exact fun h ↦ Finset.ne_of_mem_erase hx (h.symm.trans (walk_one b n))
    · by_cases hik : i < k
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [eW (j + 2) (by omega), eW j (by omega)]
        exact hk.nb (i := j) (by omega)
      · obtain rfl : i = k := by omega
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [ez, eW j (by omega)]
        exact Finset.ne_of_mem_erase hz
  have inj := fun {i j : ℕ} (hij : i < j) (hj : j ≤ k + 2) ↦
    nb_inj hc e (k + 2) hstep hnb hij hj
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
  · have := inj (i := 0) (j := i + 1) (by omega) (by omega)
    rwa [e0, eW i hi] at this
  · have := inj (i := i + 1) (j := k + 2) (by omega) le_rfl
    rw [ez, eW i hi] at this
    exact Ne.symm this
  · have := inj (i := 0) (j := k + 2) (by omega) le_rfl
    rwa [e0, ez] at this

/-- **Case `D̃ₙ`**: a walk from a point of degree three to another one. -/
lemma Rad1.good_of_branch (hg : q.IsGraph) {y : ι → ℤ} (h : q.Rad1 y) (hc : q.NoCore)
    {b n : ι} (hn : n ∈ q.nbrs b) (hb : (q.nbrs b).card = 3) {k : ℕ} (hk : q.IsStop b n k)
    (hend : (q.nbrs (q.walk b n k)).card = 3) : q.Good := by
  have hk1 := hk.1
  set W := q.walk b n with hW
  have hWk : W (k - 1) ∈ q.nbrs (W k) := by
    have := mem_nbrs_comm.1 (hk.step hn (i := k - 1) (by omega))
    rwa [show k - 1 + 1 = k by omega] at this
  obtain ⟨x1, x2, hx12, hX⟩ := Finset.card_eq_two.1
    (by rw [Finset.card_erase_of_mem hn, hb] : ((q.nbrs b).erase n).card = 2)
  obtain ⟨z1, z2, hz12, hZ⟩ := Finset.card_eq_two.1
    (by rw [Finset.card_erase_of_mem hWk, hend] : ((q.nbrs (W k)).erase (W (k - 1))).card = 2)
  have hx1 : x1 ∈ (q.nbrs b).erase n := by rw [hX]; simp
  have hx2 : x2 ∈ (q.nbrs b).erase n := by rw [hX]; simp
  have hz1 : z1 ∈ (q.nbrs (W k)).erase (W (k - 1)) := by rw [hZ]; simp
  have hz2 : z2 ∈ (q.nbrs (W k)).erase (W (k - 1)) := by rw [hZ]; simp
  have E11 := hk.ext_inj hc hn hx1 hz1
  have E12 := hk.ext_inj hc hn hx1 hz2
  have E21 := hk.ext_inj hc hn hx2 hz1
  have E22 := hk.ext_inj hc hn hx2 hz2
  set P := (Finset.range (k + 1)).image W with hP
  have memP : ∀ i ≤ k, W i ∈ P := fun i hi ↦
    Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))
  have notP : ∀ v, (∀ i ≤ k, v ≠ W i) → v ∉ P := by
    intro v hv hvP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hvP
    exact hv i (by rw [Finset.mem_range] at hi; omega) rfl
  set X : Finset ι := {x1, x2, z1, z2} with hXdef
  set u : ι → ℤ := fun v ↦ if v ∈ P then 2 else if v ∈ X then 1 else 0 with hu
  have hu0 : ∀ v, 0 ≤ u v := fun v ↦ by simp only [hu]; split_ifs <;> norm_num
  have uW : ∀ i ≤ k, u (W i) = 2 := fun i hi ↦ by simp [hu, memP i hi]
  have uX : ∀ v ∈ X, (∀ i ≤ k, v ≠ W i) → u v = 1 := fun v hv hv' ↦ by
    simp [hu, notP v hv', hv]
  have ux1 : u x1 = 1 := uX x1 (by simp [hXdef]) E11.1
  have ux2 : u x2 = 1 := uX x2 (by simp [hXdef]) E21.1
  have uz1 : u z1 = 1 := uX z1 (by simp [hXdef]) E11.2.1
  have uz2 : u z2 = 1 := uX z2 (by simp [hXdef]) E12.2.1
  have ub : u b = 2 := uW 0 (by omega)
  have un : u n = 2 := uW 1 hk1
  refine h.good_of_pattern (u := u) ?_ (a := x1) ux1
    (fun c ↦ by simp only [hu]; split_ifs <;> norm_num)
  refine val_le_of_local hg hu0 fun v hv ↦ ?_
  have hsum_ge : ∀ s : Finset ι, ∀ w ∈ s, u w ≤ ∑ t ∈ s, u t :=
    fun s w hw ↦ Finset.single_le_sum (fun t _ ↦ hu0 t) hw
  by_cases hvP : v ∈ P
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hvP
    rw [Finset.mem_range] at hi
    rw [uW i (by omega)]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · -- the point `b`
      show (2 : ℤ) * 2 ≤ ∑ w ∈ q.nbrs b, u w
      rw [← Finset.insert_erase hn, hX,
        Finset.sum_insert (by rw [← hX]; exact Finset.notMem_erase _ _),
        Finset.sum_pair hx12, ux1, ux2, un]
      norm_num
    · by_cases hik : i = k
      · subst hik
        rw [← Finset.insert_erase hWk, hZ,
          Finset.sum_insert (by rw [← hZ]; exact Finset.notMem_erase _ _),
          Finset.sum_pair hz12, uz1, uz2, uW (i - 1) (by omega)]
        norm_num
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [hk.nbrs_eq hn (by omega), Finset.sum_pair (hk.nb (i := j) (by omega)).symm,
          uW j (by omega), uW (j + 2) (by omega)]
        norm_num
  · have hvX : v ∈ X := by by_contra h'; simp [hu, hvP, h'] at hv
    have huv : u v = 1 := by simp [hu, hvP, hvX]
    rw [huv]
    simp only [hXdef, Finset.mem_insert, Finset.mem_singleton] at hvX
    rcases hvX with rfl | rfl | rfl | rfl
    · have hbv : b ∈ q.nbrs v := mem_nbrs_comm.1 (Finset.mem_of_mem_erase hx1)
      have := hsum_ge _ _ hbv
      rw [ub] at this
      linarith
    · have hbv : b ∈ q.nbrs v := mem_nbrs_comm.1 (Finset.mem_of_mem_erase hx2)
      have := hsum_ge _ _ hbv
      rw [ub] at this
      linarith
    · have hbv : W k ∈ q.nbrs v := mem_nbrs_comm.1 (Finset.mem_of_mem_erase hz1)
      have := hsum_ge _ _ hbv
      rw [uW k le_rfl] at this
      linarith
    · have hbv : W k ∈ q.nbrs v := mem_nbrs_comm.1 (Finset.mem_of_mem_erase hz2)
      have := hsum_ge _ _ hbv
      rw [uW k le_rfl] at this
      linarith

/-- **Case `Ẽ₆, Ẽ₇, Ẽ₈`**: all three walks from a point of degree three end at leaves. -/
lemma Rad1.good_of_star (hg : q.IsGraph) {y : ι → ℤ} (h : q.Rad1 y) (hc : q.NoCore) {b : ι}
    (n : Fin 3 → ι) (hinj : Function.Injective n) (hnb : q.nbrs b = Finset.univ.image n)
    (k : Fin 3 → ℕ) (hk : ∀ j, q.IsStop b (n j) (k j))
    (hleaf : ∀ j, (q.nbrs (q.walk b (n j) (k j))).card = 1) : q.Good := by
  have hrad := h.2.2.1
  have hn : ∀ j, n j ∈ q.nbrs b := fun j ↦ by rw [hnb]; exact Finset.mem_image_of_mem _ (by simp)
  set Y := y b with hY
  set d : Fin 3 → ℤ := fun j ↦ Y - y (n j) with hd
  have hval : ∀ j, ∀ i ≤ k j, y (q.walk b (n j) i) = Y - i * d j := fun j i hi ↦ by
    rw [(hk j).val hg hrad (hn j) hi]; simp only [hd]; ring
  have hleafeq : ∀ j, Y = (k j + 1) * d j := by
    intro j
    obtain ⟨m, hm⟩ : ∃ m, k j = m + 1 := ⟨k j - 1, by have := (hk j).1; omega⟩
    have e := additive hg hrad (q.walk b (n j) (k j))
    rw [(hk j).nbrs_end (hn j) (hleaf j), Finset.sum_singleton] at e
    rw [hval j _ le_rfl, hval j _ (by omega)] at e
    rw [hm] at e ⊢
    rw [show m + 1 - 1 = m by omega] at e
    push_cast at e ⊢
    linarith
  have hsum : Y = d 0 + d 1 + d 2 := by
    have e := additive hg hrad b
    rw [hnb, Finset.sum_image fun i _ j _ hij ↦ hinj hij, Fin.sum_univ_three] at e
    simp only [hd]; linarith
  have hYpos : 0 < Y := h.2.1 b
  have hdpos : ∀ j, 0 < d j := fun j ↦ by
    have := hleafeq j
    by_contra hneg; push Not at hneg
    have : (k j + 1 : ℤ) * d j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  -- the numeric condition
  have E : (k 0 + 1) * (k 1 + 1) * (k 2 + 1) =
      (k 1 + 1) * (k 2 + 1) + (k 0 + 1) * (k 2 + 1) + (k 0 + 1) * (k 1 + 1) := by
    have h0 := hleafeq 0; have h1 := hleafeq 1; have h2 := hleafeq 2
    have key : (((k 0 + 1) * (k 1 + 1) * (k 2 + 1) : ℕ) - ((k 1 + 1) * (k 2 + 1) +
        (k 0 + 1) * (k 2 + 1) + (k 0 + 1) * (k 1 + 1) : ℕ) : ℤ) * Y = 0 := by
      push_cast
      linear_combination ((k 0 + 1 : ℤ) * (k 1 + 1) * (k 2 + 1)) * hsum
        - ((k 1 + 1 : ℤ) * (k 2 + 1)) * h0 - ((k 0 + 1 : ℤ) * (k 2 + 1)) * h1
        - ((k 0 + 1 : ℤ) * (k 1 + 1)) * h2
    rcases mul_eq_zero.1 key with h' | h'
    · exact_mod_cast sub_eq_zero.1 h'
    · exact absurd h' hYpos.ne'
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin 3, ∀ j, k j + 1 ∣ k j0 + 1 := by
    have a0 := (hk 0).1; have a1 := (hk 1).1; have a2 := (hk 2).1
    rcases tri_dvd _ _ _ (by omega) (by omega) (by omega) E with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, fun j ↦ by fin_cases j <;> [exact dvd_rfl; exact h1; exact h2]⟩
    · exact ⟨1, fun j ↦ by fin_cases j <;> [exact h1; exact dvd_rfl; exact h2]⟩
    · exact ⟨2, fun j ↦ by fin_cases j <;> [exact h1; exact h2; exact dvd_rfl]⟩
  have hd_dvd : ∀ j, d j0 ∣ d j := by
    intro j
    obtain ⟨t, ht⟩ := hj0 j
    refine ⟨t, ?_⟩
    have e1 := hleafeq j
    have e2 := hleafeq j0
    have hcast : (k j0 + 1 : ℤ) = (k j + 1) * t := by exact_mod_cast ht
    rw [hcast] at e2
    have : (k j + 1 : ℤ) * (d j - d j0 * t) = 0 := by linear_combination e2 - e1
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' (by positivity)
    · linarith
  -- every point lies on one of the three walks
  set S := Finset.univ.biUnion fun j ↦ (Finset.range (k j + 1)).image (q.walk b (n j)) with hS
  have memS : ∀ j, ∀ i ≤ k j, q.walk b (n j) i ∈ S := fun j i hi ↦
    Finset.mem_biUnion.2 ⟨j, by simp, Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))⟩
  have hcl : ∀ v ∈ S, q.nbrs v ⊆ S := by
    intro v hv
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_range] at hi
    have hk1 := (hk j).1
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [walk_zero, hnb]
      intro w hw
      obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hw
      exact memS j' 1 (hk j').1
    · by_cases hik : i = k j
      · subst hik
        rw [(hk j).nbrs_end (hn j) (hleaf j)]
        intro w hw
        rw [Finset.mem_singleton.1 hw]
        exact memS j _ (by omega)
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        rw [(hk j).nbrs_eq (hn j) (by omega)]
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact memS j _ (by omega)
        · exact memS j _ (by omega)
  have hall := h.closed_eq_univ hg S ⟨_, memS 0 0 (by omega)⟩ hcl
  have hya : y (q.walk b (n j0) (k j0)) = d j0 := by
    rw [hval j0 _ le_rfl]; linarith [hleafeq j0]
  have hk6 : k j0 + 1 ≤ 6 := by
    have a0 := (hk 0).1; have a1 := (hk 1).1; have a2 := (hk 2).1
    obtain ⟨b0, b1, b2⟩ := tri_le_six _ _ _ (by omega) (by omega) (by omega) E
    fin_cases j0 <;> simpa using ‹_›
  refine good_of_dvd h.2.1 hrad (a := q.walk b (n j0) (k j0)) (fun c ↦ ?_) fun c ↦ ?_
  · rw [hya]
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (hall c)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_range] at hi
    rw [hval j i (by omega)]
    refine (hd_dvd j).trans ⟨(k j + 1 : ℤ) - i, ?_⟩
    rw [hleafeq j]; ring
  · rw [hya]
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (hall c)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    rw [hval j i (by rw [Finset.mem_range] at hi; omega)]
    have h1 : (i : ℤ) * d j ≥ 0 := mul_nonneg (by positivity) (hdpos j).le
    have h2 : Y = (k j0 + 1) * d j0 := hleafeq j0
    have h3 : ((k j0 : ℤ) + 1) ≤ 6 := by exact_mod_cast hk6
    have h4 := hdpos j0
    nlinarith

/-- **Graph step of Ovsienko's theorem**: a graph form with `Rad1` has a positive radical
vector with a coordinate `1`. -/
theorem Rad1.good_of_graph [Nonempty ι] (hg : q.IsGraph) {y : ι → ℤ} (h : q.Rad1 y) :
    q.Good := by
  classical
  have hrad := h.2.2.1
  by_cases hcore : ∃ S : Finset ι, S.Nonempty ∧ ∀ v ∈ S, 2 ≤ (q.nbrs v ∩ S).card
  · obtain ⟨S, hS, hS2⟩ := hcore
    exact h.good_of_core hg S hS hS2
  have hc : q.NoCore := by
    intro S hS
    by_contra h'
    push Not at h'
    exact hcore ⟨S, hS, fun v hv ↦ h' v hv⟩
  by_cases h4 : ∃ v, 4 ≤ (q.nbrs v).card
  · obtain ⟨v, hv⟩ := h4
    exact h.good_of_deg4 hg v hv
  push Not at h4
  have hpos1 : ∀ v, 1 ≤ (q.nbrs v).card := by
    intro v
    by_contra h0
    have h0 : q.nbrs v = ∅ := Finset.card_eq_zero.1 (by omega)
    have := additive hg hrad v
    rw [h0, Finset.sum_empty] at this
    have := h.2.1 v
    omega
  -- a leaf
  obtain ⟨ℓ, -, hℓ⟩ := hc Finset.univ Finset.univ_nonempty
  rw [Finset.inter_univ] at hℓ
  obtain ⟨n, hnℓ⟩ := Finset.card_eq_one.1 (le_antisymm hℓ (hpos1 ℓ))
  have hn : n ∈ q.nbrs ℓ := by rw [hnℓ]; simp
  have hyn : y n = 2 * y ℓ := by
    have := additive hg hrad ℓ; rw [hnℓ, Finset.sum_singleton] at this; linarith
  -- the walk from the leaf ends at a point of degree three
  obtain ⟨k, hk⟩ := exists_stop hc hn
  have hk1 := hk.1
  have hend : (q.nbrs (q.walk ℓ n k)).card = 3 := by
    have h1 := hpos1 (q.walk ℓ n k)
    have h3 := h4 (q.walk ℓ n k)
    have h2 := hk.2.2
    by_contra h3'
    have hone : (q.nbrs (q.walk ℓ n k)).card = 1 := by omega
    have e := additive hg hrad (q.walk ℓ n k)
    rw [hk.nbrs_end hn hone, Finset.sum_singleton, hk.val hg hrad hn le_rfl,
      hk.val hg hrad hn (by omega), hyn] at e
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [show m + 1 - 1 = m by omega] at e
    push_cast at e
    have := h.2.1 ℓ
    nlinarith
  set b := q.walk ℓ n k with hbdef
  obtain ⟨n0, n1, n2, h01, h02, h12, hnb⟩ := Finset.card_eq_three.1 hend
  set nn : Fin 3 → ι := ![n0, n1, n2] with hnn
  have hinj : Function.Injective nn := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hnn] <;> first | exact absurd hij ‹_› |
      exact absurd hij.symm ‹_›
  have hnb' : q.nbrs b = Finset.univ.image nn := by
    rw [hnb]; ext x; simp [hnn, Fin.exists_fin_succ]; tauto
  have hmem : ∀ j, nn j ∈ q.nbrs b := fun j ↦ by
    rw [hnb']; exact Finset.mem_image_of_mem _ (by simp)
  choose kk hkk using fun j ↦ exists_stop hc (hmem j)
  by_cases hbr : ∃ j, (q.nbrs (q.walk b (nn j) (kk j))).card = 3
  · obtain ⟨j, hj⟩ := hbr
    exact h.good_of_branch hg hc (hmem j) hend (hkk j) hj
  push Not at hbr
  refine h.good_of_star hg hc nn hinj hnb' kk hkk fun j ↦ ?_
  have := hpos1 (q.walk b (nn j) (kk j))
  have := h4 (q.walk b (nn j) (kk j))
  have := (hkk j).2.2
  have := hbr j
  omega

end UnitForm

end LargeIndecomposable.Forms
