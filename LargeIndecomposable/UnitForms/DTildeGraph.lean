module

public import LargeIndecomposable.UnitForms.Tree
public import LargeIndecomposable.UnitForms.DTilde

/-!
# Long induced paths in critical forms

An *induced path* of full edges of length `m` (`LongPath q m`) is a sequence of `m` distinct
points with coefficient `-1` between neighbours and `0` between non-neighbours.

For a graph form with a positive radical vector (`Rad1`): a nonempty set closed under
neighbours is everything (`Rad1.closed_eq_univ`), and a nonzero `u ≥ 0` with `q(u) ≤ 0` is
sincere (`Rad1.pos_of_nonpos`). If the graph has a cycle, it is a single cycle `Ã` and has an
induced path through all points but one (`Rad1.longPath_of_core`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An induced path of full edges with `m` points. -/
def LongPath (q : UnitForm ι) (m : ℕ) : Prop :=
  ∃ P : ℕ → ι, (∀ k l, k < m → l < m → P k = P l → k = l) ∧
    (∀ k, k + 1 < m → q.c (P k) (P (k + 1)) = -1) ∧
    (∀ k l, l < m → k + 2 ≤ l → q.c (P k) (P l) = 0)

variable {q : UnitForm ι} {y : ι → ℤ}

/-- A nonzero `u ≥ 0` with `q(u) ≤ 0` is a positive multiple of the radical vector. -/
lemma Rad1.pos_of_nonpos (h : q.Rad1 y) {u : ι → ℤ} (hu : q.val u ≤ 0) (hu0 : ∀ v, 0 ≤ u v)
    {a : ι} (ha : u a ≠ 0) (v : ι) : 0 < u v := by
  have e := h.prop_of_nonpos hu a v
  have hya := h.2.1 a
  have hyv := h.2.1 v
  have hua : 0 < u a := lt_of_le_of_ne (hu0 a) (Ne.symm ha)
  by_contra hv
  have : u v = 0 := le_antisymm (not_lt.1 hv) (hu0 v)
  rw [this, mul_zero] at e
  have := mul_pos hua hyv
  linarith

lemma mem_nbrs_iff {v w : ι} : w ∈ q.nbrs v ↔ w ≠ v ∧ q.c v w = -1 := by
  simp [nbrs]

lemma c_eq_zero_of_not_mem (hg : q.IsGraph) {v w : ι} (hvw : v ≠ w) (h : w ∉ q.nbrs v) :
    q.c v w = 0 := by
  rcases hg v w hvw with h0 | h1
  · exact h0
  · exact absurd (mem_nbrs_iff.2 ⟨Ne.symm hvw, h1⟩) h

/-- **The cycle case `Ã`**: if some nonempty set has two neighbours inside at each of its points,
the graph is a single cycle, the radical vector is constant, and there is an induced path
through all points but one. -/
lemma Rad1.longPath_of_core (hg : q.IsGraph) (h : q.Rad1 y) (S : Finset ι) (hS : S.Nonempty)
    (hcore : ∀ v ∈ S, 2 ≤ (q.nbrs v ∩ S).card) :
    (∀ u v, y u = y v) ∧ q.LongPath (Fintype.card ι - 1) := by
  classical
  obtain ⟨a, ha⟩ := hS
  have hval := val_indicator_le q hg S hcore
  have e := h.eq_smul_of_nonpos hval (a := a) (by simp [ha])
  have hSu : ∀ v, v ∈ S := fun v ↦ by
    have := congrFun e v
    have hv := h.2.1 v
    by_contra hvS
    simp [hvS] at this
    linarith
  have hconst : ∀ v, y v = y a := fun v ↦ by
    have := congrFun e v; simp [hSu v] at this; exact this
  refine ⟨fun u v ↦ (hconst u).trans (hconst v).symm, ?_⟩
  -- every point has degree two
  have hdeg : ∀ v, (q.nbrs v).card = 2 := fun v ↦ by
    have e2 := additive hg h.2.2.1 v
    rw [Finset.sum_congr rfl fun w _ ↦ hconst w, hconst v, Finset.sum_const, nsmul_eq_mul] at e2
    have hya := h.2.1 a
    have : ((q.nbrs v).card : ℤ) = 2 := by
      have := mul_right_cancel₀ hya.ne' (show ((q.nbrs v).card : ℤ) * y a = 2 * y a by linarith)
      exact this
    exact_mod_cast this
  obtain ⟨n, hn⟩ : (q.nbrs a).Nonempty := by rw [← Finset.card_pos, hdeg a]; norm_num
  set W := q.walk a n with hW
  have hstep : ∀ i, W (i + 1) ∈ q.nbrs (W i) := by
    intro i
    rcases i with _ | i
    · exact hn
    · rw [hW, walk_succ_succ]; exact (other_spec (by rw [hdeg])).1
  have hnb : ∀ i, W (i + 2) ≠ W i := fun i ↦ by
    rw [hW, walk_succ_succ]; exact (other_spec (by rw [hdeg])).2
  have hprev : ∀ i, W i ∈ q.nbrs (W (i + 1)) := fun i ↦ mem_nbrs_comm.1 (hstep i)
  have hnbrs : ∀ i, q.nbrs (W (i + 1)) = {W i, W (i + 2)} := fun i ↦ by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hprev i
      · exact hstep (i + 1)
    · rw [hdeg, Finset.card_pair (hnb i).symm]
  -- the first return
  have hex : ∃ r, ∃ s < r, W s = W r := by
    obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite W
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact ⟨j, i, h', heq⟩
    · exact ⟨i, j, h', heq.symm⟩
  obtain ⟨s, hsr, hs⟩ := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬∃ s < m, W s = W m := fun m hm ↦ Nat.find_min hex hm
  generalize Nat.find hex = r at hsr hs hmin
  have hinj : ∀ i j, i < r → j < r → W i = W j → i = j := by
    intro i j hi hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact hmin j hj ⟨i, h', hij⟩
    · exact hmin i hi ⟨j, h', hij.symm⟩
  have hr1 : 1 ≤ r := by omega
  -- the return is to `W 0`
  have hs0 : s = 0 := by
    by_contra hs0
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hmem : W r' ∈ q.nbrs (W (s' + 1)) := by rw [hs]; exact hprev r'
    have hr's : r' ≠ s' + 1 := fun h' ↦ ne_of_mem_nbrs hmem (by rw [h'])
    rw [hnbrs s'] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · have := hinj r' s' (by omega) (by omega) h1
      omega
    · by_cases hrs : r' = s' + 2
      · subst hrs
        exact hnb (s' + 1) hs.symm
      · have := hinj r' (s' + 2) (by omega) (by omega) h1
        omega
  subst hs0
  have hr3 : 3 ≤ r := by
    by_contra h3
    interval_cases r
    · exact ne_of_mem_nbrs (hstep 0) hs.symm
    · exact hnb 0 hs.symm
  -- the points of the walk are everything
  set T := (Finset.range r).image W with hT
  have memT : ∀ i < r, W i ∈ T := fun i hi ↦ Finset.mem_image_of_mem _ (Finset.mem_range.2 hi)
  have hWr : ∀ i, i ≤ r → W i ∈ T := fun i hi ↦ by
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · rw [← hs]; exact memT 0 (by omega)
    · exact memT i hi
  have hne1 : W 1 ≠ W (r - 1) := fun h' ↦ by
    have := hinj _ _ (by omega) (by omega) h'; omega
  have hn0 : q.nbrs (W 0) = {W 1, W (r - 1)} := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hstep 0
      · rw [hs]; have := hprev (r - 1); rwa [show r - 1 + 1 = r by omega] at this
    · rw [hdeg, Finset.card_pair hne1]
  have hcl : ∀ v ∈ T, q.nbrs v ⊆ T := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
    rw [Finset.mem_range] at hi
    rcases i with _ | i
    · rw [hn0]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact memT 1 (by omega)
      · exact memT _ (by omega)
    · rw [hnbrs i]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact memT i (by omega)
      · exact hWr (i + 2) (by omega)
  have hTu : ∀ v, v ∈ T := Rad1.closed_eq_univ hg h T ⟨_, memT 0 (by omega)⟩ hcl
  have hcard : Fintype.card ι = r := by
    have h1 : T = Finset.univ := Finset.eq_univ_of_forall hTu
    have h2 : T.card = r := by
      rw [hT, Finset.card_image_of_injOn (fun i hi j hj hij ↦ hinj i j
        (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij), Finset.card_range]
    rw [← h2, h1, Finset.card_univ]
  rw [hcard]
  refine ⟨W, fun k l hk hl hkl ↦ hinj k l (by omega) (by omega) hkl,
    fun k _ ↦ (mem_nbrs_iff.1 (hstep k)).2, fun k l hl hkl ↦ ?_⟩
  have hkl' : W k ≠ W l := fun h' ↦ by have := hinj k l (by omega) (by omega) h'; omega
  refine c_eq_zero_of_not_mem hg hkl' fun hmem ↦ ?_
  rcases k with _ | k
  · rw [hn0] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · have := hinj _ _ (by omega) (by omega) h'; omega
    · have := hinj _ _ (by omega) (by omega) h'; omega
  · rw [hnbrs k] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · have := hinj _ _ (by omega) (by omega) h'; omega
    · have := hinj _ _ (by omega) (by omega) h'; omega

/-- **A point of degree four** forces `D̃₄`: at most five points. -/
lemma Rad1.card_le_of_deg4 (hg : q.IsGraph) (h : q.Rad1 y) (v : ι)
    (hv : 4 ≤ (q.nbrs v).card) : Fintype.card ι ≤ 5 := by
  classical
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hv
  obtain ⟨a, ha⟩ : T.Nonempty := by rw [← Finset.card_pos]; omega
  have hvT : v ∉ T := fun h' ↦ not_mem_nbrs v (hT h')
  set u : ι → ℤ := fun w ↦ if w = v then 2 else if w ∈ T then 1 else 0 with hu
  have hav : a ≠ v := fun h' ↦ hvT (h' ▸ ha)
  have hu0 : ∀ w, 0 ≤ u w := fun w ↦ by simp only [hu]; split_ifs <;> norm_num
  have hval : q.val u ≤ 0 := by
    refine val_le_of_local hg hu0 fun w hw ↦ ?_
    have hnn : ∀ s : Finset ι, 0 ≤ ∑ x ∈ s, u x := fun s ↦ Finset.sum_nonneg fun x _ ↦ hu0 x
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
  have hpos := h.pos_of_nonpos hval hu0 (a := a) (by simp [hu, hav, ha])
  have hsub : (Finset.univ : Finset ι) ⊆ insert v T := fun w _ ↦ by
    have := hpos w
    by_cases hwv : w = v
    · simp [hwv]
    · have hwT : w ∈ T := by by_contra h'; simp [hu, hwv, h'] at this
      exact Finset.mem_insert_of_mem hwT
  calc Fintype.card ι = (Finset.univ : Finset ι).card := rfl
    _ ≤ (insert v T).card := Finset.card_le_card hsub
    _ ≤ T.card + 1 := Finset.card_insert_le _ _
    _ = 5 := by rw [hTc]

/-- **A star with three arms** is `Ẽ₆`, `Ẽ₇` or `Ẽ₈`: at most nine points. -/
lemma Rad1.card_le_of_star (hg : q.IsGraph) (h : q.Rad1 y) (hc : q.NoCore) {b : ι}
    (n : Fin 3 → ι) (hinj : Function.Injective n) (hnb : q.nbrs b = Finset.univ.image n)
    (k : Fin 3 → ℕ) (hk : ∀ j, q.IsStop b (n j) (k j))
    (hleaf : ∀ j, (q.nbrs (q.walk b (n j) (k j))).card = 1) : Fintype.card ι ≤ 9 := by
  classical
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
  -- every point lies on one of the three walks
  set S := insert b (Finset.univ.biUnion fun j ↦
    (Finset.Icc 1 (k j)).image (q.walk b (n j))) with hS
  have memS : ∀ j, ∀ i ≤ k j, q.walk b (n j) i ∈ S := fun j i hi ↦ by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨j, by simp,
        Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨hi0, hi⟩)⟩)
  have hcl : ∀ v ∈ S, q.nbrs v ⊆ S := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [hnb]
      intro w hw
      obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hw
      exact memS j' 1 (hk j').1
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_Icc] at hi
    by_cases hik : i = k j
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
  have hall := h.closed_eq_univ hg S ⟨_, Finset.mem_insert_self _ _⟩ hcl
  have hcardS : S.card ≤ 1 + (k 0 + k 1 + k 2) := by
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_biUnion_le (s := Finset.univ)
      (t := fun j ↦ (Finset.Icc 1 (k j)).image (q.walk b (n j)))
    have hj : ∀ j, ((Finset.Icc 1 (k j)).image (q.walk b (n j))).card ≤ k j := fun j ↦
      Finset.card_image_le.trans (by simp)
    rw [Fin.sum_univ_three] at this
    have := hj 0; have := hj 1; have := hj 2
    omega
  have hcard : Fintype.card ι ≤ 1 + (k 0 + k 1 + k 2) := by
    have : (Finset.univ : Finset ι) ⊆ S := fun v _ ↦ hall v
    exact (Finset.card_le_card this).trans hcardS
  have a0 := (hk 0).1; have a1 := (hk 1).1; have a2 := (hk 2).1
  obtain ⟨b0, b1, b2⟩ := tri_le_six _ _ _ (by omega) (by omega) (by omega) E
  have hk9 : k 0 + k 1 + k 2 ≤ 8 := by
    clear hcard hcardS hall hcl memS hleafeq hval
    generalize k 0 = x0 at *; generalize k 1 = x1 at *; generalize k 2 = x2 at *
    have c0 : x0 ≤ 5 := by omega
    have c1 : x1 ≤ 5 := by omega
    have c2 : x2 ≤ 5 := by omega
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> omega
  omega

open DTilde DTilde.Pt in
/-- A shape from a model map `F` defined on the valid model points. -/
lemma DShape.of_model {q : UnitForm ι} {y : ι → ℤ} {M i j : ℕ} (F : Pt → ι) (l : ℤ) (hl : 0 < l)
    (hij : i < j) (hjM : j < M) (hinj : ∀ x x', Valid M x → Valid M x' → F x = F x' → x = x')
    (hsurj : ∀ v, ∃ x, Valid M x ∧ F x = v)
    (hc : ∀ x x', Valid M x → Valid M x' → x ≠ x' → q.c (F x) (F x') = sc M i j x x')
    (hy : ∀ x, Valid M x → y (F x) = l * sy i j x) : q.DShape y := by
  classical
  choose pos hpos using hsurj
  refine ⟨M, i, j, pos, l, hl, hij, hjM, fun u ↦ (hpos u).1, fun u v huv ↦ ?_, fun x hx ↦ ?_,
    fun u v huv ↦ ?_, fun u ↦ ?_⟩
  · rw [← (hpos u).2, ← (hpos v).2, huv]
  · exact ⟨F x, hinj _ _ (hpos (F x)).1 hx (hpos (F x)).2⟩
  · have e := hc (pos u) (pos v) (hpos u).1 (hpos v).1 fun h' ↦ huv (by
      rw [← (hpos u).2, ← (hpos v).2, h'])
    rwa [(hpos u).2, (hpos v).2] at e
  · have e := hy (pos u) (hpos u).1
    rwa [(hpos u).2] at e

set_option maxHeartbeats 1000000 in
/-- **Two points of degree three** joined by a walk through points of degree two: the graph
is `D̃` (a fork at both ends), as a shape. -/
lemma Rad1.dshape_of_branch (hg : q.IsGraph) (h : q.Rad1 y) (hc : q.NoCore)
    {b n : ι} (hn : n ∈ q.nbrs b) (hb : (q.nbrs b).card = 3) {k : ℕ} (hk : q.IsStop b n k)
    (hend : (q.nbrs (q.walk b n k)).card = 3) : q.DShape y := by
  classical
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
  have hval : q.val u ≤ 0 := by
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
  -- the pattern is the radical vector, so it is everything
  have e := h.eq_smul_of_nonpos hval ux1
  set l := y x1 with hl
  have hlpos : 0 < l := h.2.1 x1
  have hyu : ∀ v, y v = l * u v := fun v ↦ by
    have := congrFun e v; simpa using this
  have hsupp : ∀ v, v ∈ P ∨ v ∈ X := by
    intro v
    have h1 := hyu v
    have h2 := h.2.1 v
    by_contra hno
    push Not at hno
    have : u v = 0 := by simp [hu, hno.1, hno.2]
    rw [this, mul_zero] at h1
    linarith
  -- leaves have one neighbour
  have hleaf : ∀ v w, w ∈ q.nbrs v → y w = 2 * y v → q.nbrs v = {w} := by
    intro v w hw hyw
    have e2 := additive hg h.2.2.1 v
    rw [← Finset.add_sum_erase _ _ hw, hyw] at e2
    have hz : ∑ x ∈ (q.nbrs v).erase w, y x = 0 := by linarith
    have hempty : (q.nbrs v).erase w = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have := Finset.single_le_sum (f := y) (fun x _ ↦ (h.2.1 x).le) hx
      have := h.2.1 x
      linarith
    rw [← Finset.insert_erase hw, hempty]; rfl
  have yx1 : y x1 = l := rfl
  have yx2 : y x2 = l := by rw [hyu, ux2, mul_one]
  have yz1 : y z1 = l := by rw [hyu, uz1, mul_one]
  have yz2 : y z2 = l := by rw [hyu, uz2, mul_one]
  have yW : ∀ i ≤ k, y (W i) = 2 * l := fun i hi ↦ by rw [hyu, uW i hi]; ring
  have nx1 : q.nbrs x1 = {b} := hleaf x1 b (mem_nbrs_comm.1 (Finset.mem_of_mem_erase hx1))
    (by rw [show b = W 0 from rfl, yW 0 (by omega), yx1])
  have nx2 : q.nbrs x2 = {b} := hleaf x2 b (mem_nbrs_comm.1 (Finset.mem_of_mem_erase hx2))
    (by rw [show b = W 0 from rfl, yW 0 (by omega), yx2])
  have nz1 : q.nbrs z1 = {W k} := hleaf z1 (W k) (mem_nbrs_comm.1 (Finset.mem_of_mem_erase hz1))
    (by rw [yW k le_rfl, yz1])
  have nz2 : q.nbrs z2 = {W k} := hleaf z2 (W k) (mem_nbrs_comm.1 (Finset.mem_of_mem_erase hz2))
    (by rw [yW k le_rfl, yz2])
  have nb : q.nbrs b = {x1, x2, W 1} := by
    rw [← Finset.insert_erase hn, hX, show n = W 1 from rfl]
    ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have nWk : q.nbrs (W k) = {W (k - 1), z1, z2} := by
    rw [← Finset.insert_erase hWk, hZ]
  have nW : ∀ m, m + 1 < k → q.nbrs (W (m + 1)) = {W m, W (m + 2)} :=
    fun m hm ↦ hk.nbrs_eq hn hm
  have Winj : ∀ i j, i ≤ k → j ≤ k → W i = W j → i = j := by
    intro i j hi hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact hk.inj hc hn h' hj hij
    · exact hk.inj hc hn h' hi hij.symm
  -- the model map
  have hk1' : 1 ≤ k := hk1
  let F : DTilde.Pt → ι := fun x ↦ match x with
    | .s => x2
    | .t => z2
    | .p m => if m = 0 then x1 else if m ≤ k + 1 then W (m - 1) else z1
  have Fs : F .s = x2 := rfl
  have Ft : F .t = z2 := rfl
  have F0 : F (.p 0) = x1 := rfl
  have Fm : ∀ m, 1 ≤ m → m ≤ k + 1 → F (.p m) = W (m - 1) := fun m h1 h2 ↦ by
    change (if m = 0 then x1 else if m ≤ k + 1 then W (m - 1) else z1) = _
    rw [if_neg (by omega), if_pos h2]
  have Fe : F (.p (k + 2)) = z1 := by
    change (if k + 2 = 0 then x1 else if k + 2 ≤ k + 1 then W (k + 2 - 1) else z1) = _
    rw [if_neg (by omega), if_neg (by omega)]
  -- a left inverse
  let idx : ι → ℕ := fun v ↦ if hv : ∃ i, i ≤ k ∧ W i = v then Nat.find hv else 0
  have idxW : ∀ i ≤ k, idx (W i) = i := fun i hi ↦ by
    have hv : ∃ i', i' ≤ k ∧ W i' = W i := ⟨i, hi, rfl⟩
    change (if hv : ∃ i', i' ≤ k ∧ W i' = W i then Nat.find hv else 0) = i
    rw [dif_pos hv]
    obtain ⟨h1, h2⟩ := Nat.find_spec hv
    exact Winj _ _ h1 hi h2
  let G : ι → DTilde.Pt := fun v ↦ if v = x2 then .s else if v = z2 then .t else if v = x1 then
    .p 0 else if v = z1 then .p (k + 2) else .p (idx v + 1)
  have Gdef : ∀ v, G v = if v = x2 then .s else if v = z2 then .t else if v = x1 then
    .p 0 else if v = z1 then .p (k + 2) else .p (idx v + 1) := fun _ ↦ rfl
  have GF : ∀ x, DTilde.Valid (k + 3) x → G (F x) = x := by
    intro x hx
    rcases x with _ | _ | m
    · rw [Fs, Gdef, if_pos rfl]
    · rw [Ft, Gdef, if_neg (Ne.symm E22.2.2), if_pos rfl]
    · simp only [DTilde.Valid] at hx
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [F0, Gdef, if_neg hx12, if_neg E12.2.2, if_pos rfl]
      · by_cases hmk : m ≤ k + 1
        · rw [Fm m hm0 hmk]
          have a1 := E11.1 (m - 1) (by omega)
          have a2 := E21.1 (m - 1) (by omega)
          have a3 := E11.2.1 (m - 1) (by omega)
          have a4 := E12.2.1 (m - 1) (by omega)
          rw [Gdef, if_neg (Ne.symm a2), if_neg (Ne.symm a4), if_neg (Ne.symm a1),
            if_neg (Ne.symm a3), idxW (m - 1) (by omega)]
          congr 1; omega
        · obtain rfl : m = k + 2 := by omega
          rw [Fe]
          rw [Gdef, if_neg (Ne.symm E21.2.2), if_neg hz12, if_neg (Ne.symm E11.2.2), if_pos rfl]
  have Finj : ∀ x x', DTilde.Valid (k + 3) x → DTilde.Valid (k + 3) x' → F x = F x' → x = x' :=
    fun x x' hx hx' hxx ↦ by rw [← GF x hx, ← GF x' hx', hxx]
  -- the neighbours
  have hN : ∀ x, DTilde.Valid (k + 3) x → q.nbrs (F x) = (DTilde.forkNbrs k x).image F := by
    intro x hx
    rcases x with _ | _ | m
    · rw [Fs, nx2, show DTilde.forkNbrs k .s = {.p 1} from rfl, Finset.image_singleton,
        Fm 1 le_rfl (by omega)]; rfl
    · rw [Ft, nz2, show DTilde.forkNbrs k .t = {.p (k + 1)} from rfl, Finset.image_singleton,
        Fm (k + 1) (by omega) le_rfl, show k + 1 - 1 = k by omega]
    · simp only [DTilde.Valid] at hx
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [F0, nx1, show DTilde.forkNbrs k (.p 0) = {.p 1} by simp [DTilde.forkNbrs],
          Finset.image_singleton, Fm 1 le_rfl (by omega)]; rfl
      · by_cases hm1 : m = 1
        · subst hm1
          rw [Fm 1 le_rfl (by omega), show 1 - 1 = 0 from rfl, show W 0 = b from rfl, nb]
          simp only [DTilde.forkNbrs, if_neg one_ne_zero, if_pos rfl, ite_true, Finset.image_insert,
            Finset.image_singleton, F0, Fs, Fm 2 (by omega) (by omega)]
          try (ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        · by_cases hmk : m ≤ k
          · rw [Fm m (by omega) (by omega)]
            obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
            rw [show m' + 2 - 1 = m' + 1 by omega, nW m' (by omega)]
            simp only [DTilde.forkNbrs, if_neg (show m' + 2 ≠ 0 by omega),
              if_neg (show m' + 2 ≠ 1 by omega), if_pos hmk, Finset.image_insert,
              Finset.image_singleton, Fm (m' + 2 - 1) (by omega) (by omega),
              Fm (m' + 2 + 1) (by omega) (by omega)]
            congr 2 <;> congr 1 <;> omega
          · by_cases hmk1 : m = k + 1
            · subst hmk1
              rw [Fm (k + 1) (by omega) le_rfl, show k + 1 - 1 = k by omega, nWk]
              simp only [DTilde.forkNbrs, if_neg (show k + 1 ≠ 0 by omega),
                if_neg (show k + 1 ≠ 1 by omega), if_neg (show ¬ k + 1 ≤ k by omega), if_pos rfl,
                ite_true,
                Finset.image_insert, Finset.image_singleton, Fm k (by omega) (by omega), Fe, Ft]
            · obtain rfl : m = k + 2 := by omega
              rw [Fe, nz1, show DTilde.forkNbrs k (.p (k + 2)) = {.p (k + 1)} by
                simp only [DTilde.forkNbrs, if_neg (show k + 2 ≠ 0 by omega),
                  if_neg (show k + 2 ≠ 1 by omega), if_neg (show ¬ k + 2 ≤ k by omega),
                  if_neg (show k + 2 ≠ k + 1 by omega)],
                Finset.image_singleton, Fm (k + 1) (by omega) le_rfl, show k + 1 - 1 = k by omega]
  refine DShape.of_model (M := k + 3) (i := 0) (j := k + 2) F l hlpos (by omega) (by omega)
    Finj (fun v ↦ ?_) (fun x x' hx hx' hxx ↦ ?_) (fun x hx ↦ ?_)
  · rcases hsupp v with hv | hv
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
      rw [Finset.mem_range] at hi
      exact ⟨.p (i + 1), by simp only [DTilde.Valid]; omega, by
        rw [Fm (i + 1) (by omega) (by omega)]; rfl⟩
    · simp only [hXdef, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨.p 0, by simp only [DTilde.Valid]; omega, F0⟩
      · exact ⟨.s, trivial, Fs⟩
      · exact ⟨.p (k + 2), by simp only [DTilde.Valid]; omega, Fe⟩
      · exact ⟨.t, trivial, Ft⟩
  · have hF : F x ≠ F x' := fun h' ↦ hxx (Finj _ _ hx hx' h')
    rw [DTilde.sc_fork hk1' x x' hx hx' hxx]
    have hmem : F x' ∈ q.nbrs (F x) ↔ x' ∈ DTilde.forkNbrs k x := by
      rw [hN x hx, Finset.mem_image]
      constructor
      · rintro ⟨z, hz, hzx⟩
        have hzv : DTilde.Valid (k + 3) z := by
          rcases x with _ | _ | m <;> simp only [DTilde.forkNbrs] at hz <;> (try split_ifs at hz) <;>
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz <;>
            rcases hz with rfl | rfl | rfl <;> simp only [DTilde.Valid] at hx ⊢ <;> omega
        rwa [← Finj _ _ hzv hx' hzx]
      · exact fun h' ↦ ⟨x', h', rfl⟩
    split_ifs with h'
    · exact (mem_nbrs_iff.1 (hmem.2 h')).2
    · exact c_eq_zero_of_not_mem hg hF fun h'' ↦ h' (hmem.1 h'')
  · rcases x with _ | _ | m
    · rw [Fs, yx2]; simp [DTilde.sy]
    · rw [Ft, yz2]; simp [DTilde.sy]
    · simp only [DTilde.Valid] at hx
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [F0, yx1]; simp [DTilde.sy]
      · by_cases hmk : m ≤ k + 1
        · rw [Fm m hm0 hmk, yW _ (by omega)]
          simp only [DTilde.sy, if_pos (show 0 < m ∧ m < k + 2 by omega)]; ring
        · obtain rfl : m = k + 2 := by omega
          rw [Fe, yz1]; simp [DTilde.sy]

/-- **Graph forms with a positive radical vector in at least ten variables**: the cycle `Ã`
(constant radical vector, an induced path through all points but one) or a `D̃` tree. -/
theorem Rad1.graph_shape (hg : q.IsGraph) (h : q.Rad1 y) (h10 : 10 ≤ Fintype.card ι) :
    ((∀ u v, y u = y v) ∧ q.LongPath (Fintype.card ι - 1)) ∨ q.DShape y := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hrad := h.2.2.1
  by_cases hcore : ∃ S : Finset ι, S.Nonempty ∧ ∀ v ∈ S, 2 ≤ (q.nbrs v ∩ S).card
  · obtain ⟨S, hS, hS2⟩ := hcore
    exact Or.inl (h.longPath_of_core hg S hS hS2)
  right
  have hc : q.NoCore := by
    intro S hS
    by_contra h'
    push Not at h'
    exact hcore ⟨S, hS, fun v hv ↦ h' v hv⟩
  by_cases h4 : ∃ v, 4 ≤ (q.nbrs v).card
  · obtain ⟨v, hv⟩ := h4
    have := h.card_le_of_deg4 hg v hv; omega
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
    exact h.dshape_of_branch hg hc (hmem j) hend (hkk j) hj
  push Not at hbr
  have := h.card_le_of_star hg hc nn hinj hnb' kk hkk fun j ↦ ?_
  · omega
  have := hpos1 (q.walk b (nn j) (kk j))
  have := h4 (q.walk b (nn j) (kk j))
  have := (hkk j).2.2
  have := hbr j
  omega


/-- **The critical diagrams in at least ten variables** (von Höhne 1988, Theorems 1.2 and
2.1): a form with `Rad1` is the cycle `Ã` with a constant radical vector, or a shape of type
`D̃`. Inflate to a graph form (`exists_terminal`) and pull the shape back
(`DShape.of_inflate`); an inflation of `Ã` is impossible, since it makes the radical vector
nonconstant. -/
theorem Rad1.shape (h : q.Rad1 y) (h10 : 10 ≤ Fintype.card ι) :
    ((∀ u v, y u = y v) ∧ q.LongPath (Fintype.card ι - 1)) ∨ q.DShape y := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ q' ∈ {q : UnitForm ι | ∀ x, 0 ≤ q.val x}, q'.rsum ≤ M := by
    obtain ⟨M, hM⟩ := ((finite_nonneg (ι := ι)).image rsum).bddAbove
    exact ⟨M, fun q' hq' ↦ hM ⟨q', hq', rfl⟩⟩
  suffices H : ∀ n, ∀ (q : UnitForm ι) (y : ι → ℤ), q.Rad1 y → M - q.rsum = n →
      ((∀ u v, y u = y v) ∧ q.LongPath (Fintype.card ι - 1)) ∨ q.DShape y from H _ q y h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro q y h hn
  by_cases hterm : ∀ a b, a ≠ b → q.c a b ≠ 1
  · exact h.graph_shape (fun a b hab ↦ h.coeff_graph hterm (by omega) hab) h10
  push Not at hterm
  obtain ⟨a, b, hab, hc⟩ := hterm
  have h1 := h.inflate hab hc
  have hlt := q.rsum_lt_inflate h hab hc
  have hle := hM _ h1.1
  rcases ih (M - (q.inflate hab hc).rsum) (by omega) _ _ h1 rfl with ⟨hconst, -⟩ | hD
  · exfalso
    have e := hconst a b
    rw [deflMap_apply, deflMap_apply, if_pos rfl, if_neg (Ne.symm hab), add_zero] at e
    have := h.2.1 a
    linarith
  · exact Or.inr (DShape.of_inflate hab hc h.2.1 hD)

open DTilde DTilde.Pt in
/-- A shape has an induced path through all points but `s` and `t`. -/
theorem DShape.longPath {q : UnitForm ι} {y : ι → ℤ} (h : q.DShape y) :
    q.LongPath (Fintype.card ι - 2) := by
  classical
  obtain ⟨M, i, j, pos, l, hl, hij, hjM, hval, hinj, hsurj, hcoef, hyy⟩ := h
  choose F hF using hsurj
  have : Nonempty ι := ⟨F s trivial⟩
  -- the number of points
  have hcard : Fintype.card ι = M + 2 := by
    let V : Finset Pt := insert s (insert t ((Finset.range M).image p))
    have hV : V.card = M + 2 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (fun a b h ↦ by injection h), Finset.card_range]
    have hmemV : ∀ x, x ∈ V ↔ Valid M x := fun x ↦ by
      rcases x with _ | _ | k <;> simp [V, Valid]
    have h1 : Fintype.card ι ≤ V.card := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card_of_injOn pos (fun u _ ↦ (hmemV _).2 (hval u))
        (fun u _ v _ huv ↦ hinj huv)
    have h2 : V.card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card_of_injOn (fun x ↦ if hx : Valid M x then F x hx else
        Classical.arbitrary ι) (fun _ _ ↦ Finset.mem_univ _) fun x hx x' hx' hxx ↦ by
          have hx1 := (hmemV x).1 hx
          have hx2 := (hmemV x').1 hx'
          simp only [dif_pos hx1, dif_pos hx2] at hxx
          rw [← hF x hx1, ← hF x' hx2, hxx]
    omega
  rw [hcard, show M + 2 - 2 = M by omega]
  let P : ℕ → ι := fun k ↦ if hk : k < M then F (p k) hk else Classical.arbitrary ι
  have hP : ∀ k (hk : k < M), pos (P k) = p k := fun k hk ↦ by
    simp only [P, dif_pos hk]; exact hF _ _
  refine ⟨P, fun k k' hk hk' hkk ↦ ?_, fun k hk ↦ ?_, fun k k' hk' hkk ↦ ?_⟩
  · have := congrArg pos hkk
    rw [hP k hk, hP k' hk'] at this
    injection this
  · have hne : P k ≠ P (k + 1) := fun h' ↦ by
      have := congrArg pos h'; rw [hP k (by omega), hP (k + 1) hk] at this; injection this; omega
    rw [hcoef _ _ hne, hP k (by omega), hP (k + 1) hk]
    simp [sc]
  · have hne : P k ≠ P k' := fun h' ↦ by
      have := congrArg pos h'; rw [hP k (by omega), hP k' hk'] at this; injection this; omega
    rw [hcoef _ _ hne, hP k (by omega), hP k' hk']
    simp only [sc]
    rw [if_neg (by omega)]

lemma LongPath.mono {q : UnitForm ι} {m m' : ℕ} (h : q.LongPath m) (hm : m' ≤ m) :
    q.LongPath m' := by
  obtain ⟨P, h1, h2, h3⟩ := h
  exact ⟨P, fun k l hk hl ↦ h1 k l (by omega) (by omega), fun k hk ↦ h2 k (by omega),
    fun k l hl hkl ↦ h3 k l (by omega) hkl⟩

/-- **A critical form in at least ten variables has an induced path of full edges through all
points but two.** -/
theorem Critical.longPath (q : UnitForm ι) (hq : q.Critical) (h10 : 10 ≤ Fintype.card ι) :
    q.LongPath (Fintype.card ι - 2) := by
  obtain ⟨y, hy⟩ := Critical.rad1 q hq (by omega)
  rcases hy.shape h10 with ⟨-, hP⟩ | hD
  · exact hP.mono (by omega)
  · exact hD.longPath

end UnitForm

end LargeIndecomposable.Forms
