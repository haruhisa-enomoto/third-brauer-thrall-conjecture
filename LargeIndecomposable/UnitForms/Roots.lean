module

public import LargeIndecomposable.UnitForms.Critical

/-!
# Roots of weakly positive unit forms

Let `q` be a weakly positive unit form. A root is a nonzero `r ≥ 0` with `q(r) = 1`, and
`∂_i(r) = B(r, e_i)`.

* `partial_le_one`, `neg_one_le_partial`: `∂_i(r) ∈ {-1, 0, 1}` on the support.
* `exists_descent`: a root above another root descends to it one coordinate at a time.
* `exists_minimal_pair`: a root containing `u ≠ j` lies above a root `s` with `s_u = s_j = 1`,
  `∂_u(s) = ∂_j(s) = 1`, and `∂_k(s) = 0` elsewhere on the support.
* `end_or_line` (**Lemma R**): for a root `z` and `c` in its support, either `z` is a clean line
  starting at `c`, or there is a good end: `w ≥ 0` with `w_c = 2`, `q(w) ≤ 2`, supported in `z`.
* `false_of_glue`: two good ends at `t` with orthogonal rest contradict weak positivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (q : UnitForm ι)

/-- A positive root. -/
def IsRoot (r : ι → ℤ) : Prop := Pos r ∧ q.val r = 1

lemma val_add_single (z : ι → ℤ) (a : ι) :
    q.val (z + Pi.single a 1) = q.val z + q.B z (Pi.single a 1) + 1 := by
  have h1 := q.two_mul_val (z + Pi.single a 1)
  have h2 := q.two_mul_val z
  have h3 := q.two_mul_val (Pi.single a 1)
  rw [q.val_single] at h3
  rw [B_add_left, B_add_right, B_add_right, B_symm q (Pi.single a 1) z] at h1
  omega

/-- `Σ r_i ∂_i(r) = 2 q(r)`. -/
lemma sum_dd (r : ι → ℤ) : ∑ i, r i * q.B r (Pi.single i 1) = 2 * q.val r := by
  rw [two_mul_val, ← B_eq_sum_single]

lemma two_val_sub (x y : ι → ℤ) : 2 * q.val (x - y) = 2 * q.val x - 2 * q.B x y + 2 * q.val y := by
  rw [two_mul_val, two_mul_val, two_mul_val, B_sub_left, B_sub_right, B_sub_right, B_symm q y x]
  ring

lemma val_add_two_single (w : ι → ℤ) (c : ι) :
    q.val (w + (Pi.single c 1 + Pi.single c 1)) = q.val w + 2 * q.B w (Pi.single c 1) + 4 := by
  rw [← add_assoc, q.val_add_single, q.val_add_single, B_add_left]
  have : q.B (Pi.single c 1) (Pi.single c 1) = 2 := by
    rw [q.B_single_right]; simp [Pi.single_apply, q.diag]
  rw [this]; ring

variable {q}

lemma pos_sub_single {r : ι → ℤ} (hr : ∀ a, 0 ≤ r a) {i : ι} (hi : 1 ≤ r i)
    (hne : r ≠ Pi.single i 1) : Pos (r - Pi.single i 1) := by
  refine ⟨fun a ↦ ?_, fun h ↦ hne ?_⟩
  · by_cases ha : a = i
    · subst ha; simp; omega
    · simpa [Pi.single_eq_of_ne ha] using hr a
  · exact sub_eq_zero.1 h

variable (hw : q.WeaklyPositive)
include hw

/-- Upper bound on the support. -/
lemma partial_le_one {r : ι → ℤ} (hr : q.IsRoot r) {i : ι} (hi : 1 ≤ r i)
    (hne : r ≠ Pi.single i 1) : q.B r (Pi.single i 1) ≤ 1 := by
  have h1 := hw _ (pos_sub_single hr.1.1 hi hne)
  rw [q.val_sub_single, hr.2] at h1
  omega

/-- Lower bound. -/
lemma neg_one_le_partial {r : ι → ℤ} (hr : q.IsRoot r) (i : ι) : -1 ≤ q.B r (Pi.single i 1) := by
  have hp : Pos (r + Pi.single i 1) := by
    refine ⟨fun a ↦ ?_, fun h ↦ ?_⟩
    · have := hr.1.1 a
      by_cases ha : a = i
      · subst ha; simp; omega
      · simpa [Pi.single_eq_of_ne ha] using this
    · have h1 := congrFun h i
      have h2 := hr.1.1 i
      simp at h1
      omega
  have h1 := hw _ hp
  rw [q.val_add_single, hr.2] at h1
  omega

/-- A root minus a coordinate with derivative one is a root. -/
lemma isRoot_sub {r : ι → ℤ} (hr : q.IsRoot r) {i : ι} (hi : 1 ≤ r i) (hne : r ≠ Pi.single i 1)
    (hd : q.B r (Pi.single i 1) = 1) : q.IsRoot (r - Pi.single i 1) := by
  refine ⟨pos_sub_single hr.1.1 hi hne, ?_⟩
  rw [q.val_sub_single, hr.2, hd]
  norm_num

/-- **Descent.** A root strictly above a root has a coordinate of derivative one above it. -/
theorem exists_descent {r t : ι → ℤ} (hr : q.IsRoot r) (ht : q.IsRoot t) (hle : ∀ a, t a ≤ r a)
    (hne : r ≠ t) : ∃ j, t j < r j ∧ q.B r (Pi.single j 1) = 1 := by
  by_contra hno
  push Not at hno
  let y := r - t
  have hy : ∀ a, 0 ≤ y a := fun a ↦ by have := hle a; simp [y]; omega
  have hpos : Pos y := ⟨hy, fun h ↦ hne (sub_eq_zero.1 h)⟩
  have h1 := hw y hpos
  -- `t = r - y`
  have h2 : 2 * q.val t = 2 * q.val r - 2 * q.B r y + 2 * q.val y := by
    have := q.two_val_sub r y
    simpa [y] using this
  rw [ht.2, hr.2] at h2
  have h3 : q.B r y = q.val y := by omega
  have h4 : q.B r y ≤ 0 := by
    rw [B_eq_sum_single]
    refine Finset.sum_nonpos fun a _ ↦ ?_
    by_cases hya : y a = 0
    · simp [hya]
    · have hlt : t a < r a := by
        have := hy a
        simp only [y, Pi.sub_apply] at this hya
        omega
      have hrne : r ≠ Pi.single a 1 := by
        rintro rfl
        have h5 := ht.1.1 a
        have h6 : t ≠ 0 := ht.1.2
        apply h6
        funext b
        by_cases hb : b = a
        · subst hb
          simp at hlt
          simp
          omega
        · have h7 := hle b
          have h8 := ht.1.1 b
          simp [Pi.single_eq_of_ne hb] at h7
          simp
          omega
      have h5 : 1 ≤ r a := by have := ht.1.1 a; omega
      have h6 := partial_le_one hw hr h5 hrne
      have h7 := hno a hlt
      have h8 : q.B r (Pi.single a 1) ≤ 0 := by omega
      have h9 := hy a
      exact mul_nonpos_of_nonneg_of_nonpos h9 h8
  omega

/-- **Descent to a coordinate exactly two.** -/
theorem exists_root_two (c : ι) : ∀ (n : ℕ) (r : ι → ℤ), (∑ i, r i).toNat = n → q.IsRoot r →
    2 ≤ r c → ∃ s, q.IsRoot s ∧ s c = 2 ∧ ∀ a, s a ≤ r a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r hn hr hc
    by_cases h2 : r c = 2
    · exact ⟨r, hr, h2, fun _ ↦ le_rfl⟩
    have hsingle : q.IsRoot (Pi.single c 1) := by
      refine ⟨⟨fun a ↦ ?_, fun h ↦ ?_⟩, q.val_single c⟩
      · by_cases ha : a = c
        · subst ha; simp
        · simp [Pi.single_eq_of_ne ha]
      · have := congrFun h c
        simp at this
    have hne : r ≠ Pi.single c 1 := by
      rintro rfl
      simp at hc
    obtain ⟨j, hj, hd⟩ := exists_descent hw hr hsingle (fun a ↦ by
      by_cases ha : a = c
      · subst ha; simp; omega
      · simpa [Pi.single_eq_of_ne ha] using hr.1.1 a) hne
    have hj1 : 1 ≤ r j := by
      by_cases ha : j = c
      · subst ha; omega
      · have : (Pi.single c 1 : ι → ℤ) j = 0 := Pi.single_eq_of_ne ha _
        omega
    have hnej : r ≠ Pi.single j 1 := by
      rintro h
      by_cases ha : j = c
      · subst ha; rw [h] at hc; simp at hc
      · rw [h] at hc; simp [Pi.single_eq_of_ne (Ne.symm ha)] at hc
    have hroot := isRoot_sub hw hr hj1 hnej hd
    have hsum : ∑ i, (r - Pi.single j 1 : ι → ℤ) i = ∑ i, r i - 1 := by
      simp [Finset.sum_sub_distrib]
    have hnonneg : 0 ≤ ∑ i, (r - Pi.single j 1 : ι → ℤ) i := Finset.sum_nonneg fun a _ ↦ hroot.1.1 a
    obtain ⟨s, hs, hsc, hsle⟩ := ih _ (by omega) (r - Pi.single j 1) rfl hroot (by
      by_cases ha : c = j
      · subst ha; simp; omega
      · simpa [Pi.single_eq_of_ne ha] using hc)
    refine ⟨s, hs, hsc, fun a ↦ (hsle a).trans ?_⟩
    by_cases ha : a = j
    · subst ha; simp
    · simp [Pi.single_eq_of_ne ha]

/-- **The minimal root containing two points.** -/
theorem exists_minimal_pair {u j : ι} (huj : u ≠ j) : ∀ (n : ℕ) (r : ι → ℤ),
    (∑ i, r i).toNat = n → q.IsRoot r → 1 ≤ r u → 1 ≤ r j →
    ∃ s, q.IsRoot s ∧ (∀ a, s a ≤ r a) ∧ s u = 1 ∧ s j = 1 ∧ q.B s (Pi.single u 1) = 1 ∧ q.B s (Pi.single j 1) = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r hn hr hu hj
    have hne : ∀ k, r ≠ Pi.single k 1 := by
      intro k h
      by_cases hk : k = u
      · subst hk
        rw [h] at hj
        simp [Pi.single_eq_of_ne (Ne.symm huj)] at hj
      · rw [h] at hu
        simp [Pi.single_eq_of_ne (Ne.symm hk)] at hu
    by_cases hex : ∃ k, 1 ≤ r k ∧ q.B r (Pi.single k 1) = 1 ∧ (k ≠ u ∨ 2 ≤ r k) ∧ (k ≠ j ∨ 2 ≤ r k)
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hex
      have hroot := isRoot_sub hw hr hk1 (hne k) hk2
      have hsum : ∑ i, (r - Pi.single k 1 : ι → ℤ) i = ∑ i, r i - 1 := by
        simp [Finset.sum_sub_distrib]
      have hnonneg : 0 ≤ ∑ i, (r - Pi.single k 1 : ι → ℤ) i := Finset.sum_nonneg fun a _ ↦ hroot.1.1 a
      have hcoord : ∀ a, (a ≠ k ∨ 2 ≤ r a) → 1 ≤ r a → 1 ≤ (r - Pi.single k 1 : ι → ℤ) a := by
        intro a ha h1
        by_cases hak : a = k
        · subst hak
          rcases ha with ha | ha
          · exact absurd rfl ha
          · simp; omega
        · simpa [Pi.single_eq_of_ne hak] using h1
      obtain ⟨s, hs, hsle, h1, h2, h3, h4⟩ := ih _ (by omega) (r - Pi.single k 1) rfl hroot
        (hcoord u (by
          rcases hk3 with h | h
          · exact Or.inl (Ne.symm h)
          · by_cases hk : u = k
            · subst hk; exact Or.inr h
            · exact Or.inl hk) hu)
        (hcoord j (by
          rcases hk4 with h | h
          · exact Or.inl (Ne.symm h)
          · by_cases hk : j = k
            · subst hk; exact Or.inr h
            · exact Or.inl hk) hj)
      refine ⟨s, hs, fun a ↦ (hsle a).trans ?_, h1, h2, h3, h4⟩
      by_cases ha : a = k
      · subst ha; simp
      · simp [Pi.single_eq_of_ne ha]
    · push Not at hex
      -- only `u`, `j` can have derivative one, and only with coordinate one
      have hle : ∀ k, r k * q.B r (Pi.single k 1) ≤ (if k = u then 1 else 0) + (if k = j then 1 else 0) := by
        intro k
        by_cases hk0 : r k = 0
        · simp only [hk0, zero_mul]
          split_ifs <;> omega
        have hk1 : 1 ≤ r k := by have := hr.1.1 k; omega
        have hd := partial_le_one hw hr hk1 (hne k)
        by_cases hd1 : q.B r (Pi.single k 1) = 1
        · have h := hex k hk1 hd1
          by_cases h2 : 2 ≤ r k
          · by_cases hu' : k = u
            · exact absurd h2 (not_le.2 (by
                have := h (Or.inr h2)
                rcases this with ⟨h3, h4⟩
                exact h4))
            · have := h (Or.inl hu')
              exact absurd h2 (not_le.2 this.2)
          · have hr1 : r k = 1 := by omega
            by_cases hu' : k = u
            · subst hu'
              rw [hd1, hr1]
              simp [huj]
            · by_cases hj' : k = j
              · subst hj'
                rw [hd1, hr1]
                simp [hu']
              · have := h (Or.inl hu')
                exact absurd this.1 hj'
        · have h8 : q.B r (Pi.single k 1) ≤ 0 := by omega
          have h9 : r k * q.B r (Pi.single k 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) h8
          split_ifs <;> omega
      have hsum := q.sum_dd r
      rw [hr.2] at hsum
      have htot : ∑ k, r k * q.B r (Pi.single k 1) ≤
          ∑ k, ((if k = u then (1 : ℤ) else 0) + (if k = j then 1 else 0)) :=
        Finset.sum_le_sum fun k _ ↦ hle k
      rw [Finset.sum_add_distrib] at htot
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at htot
      -- equality forces both terms
      have hrest : ∀ k, r k * q.B r (Pi.single k 1) = (if k = u then 1 else 0) + (if k = j then 1 else 0) := by
        have heq : ∑ k, ((if k = u then (1 : ℤ) else 0) + (if k = j then 1 else 0)) =
            ∑ k, r k * q.B r (Pi.single k 1) := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          omega
        intro k
        have := (Finset.sum_eq_sum_iff_of_le (fun k _ ↦ hle k)).1 heq.symm k (Finset.mem_univ k)
        exact this
      have h1 := hrest u
      have h2 := hrest j
      simp only [ite_true, if_neg huj, if_neg (Ne.symm huj), add_zero, zero_add] at h1 h2
      have hu1 : r u = 1 := by
        have := Int.eq_one_or_neg_one_of_mul_eq_one' h1
        omega
      have hj1 : r j = 1 := by
        have := Int.eq_one_or_neg_one_of_mul_eq_one' h2
        omega
      rw [hu1, one_mul] at h1
      rw [hj1, one_mul] at h2
      exact ⟨r, hr, fun _ ↦ le_rfl, hu1, hj1, h1, h2⟩

/-- A clean line starting at a point. -/
inductive IsLine (q : UnitForm ι) : ι → (ι → ℤ) → Prop
  | single (c : ι) : IsLine q c (Pi.single c 1)
  | cons {c c₁ : ι} {z : ι → ℤ} (h : IsLine q c₁ z) (hzc : z c = 0) (hne : c ≠ c₁)
      (hc : q.c c c₁ = -1) (h0 : ∀ b, b ≠ c₁ → b ≠ c → 0 < z b → q.c c b = 0) :
      IsLine q c (z + Pi.single c 1)

omit hw in
/-- **The sequence of a clean line.** -/
theorem IsLine.exists_seq {c : ι} {z : ι → ℤ} (h : q.IsLine c z) :
    ∃ (n : ℕ) (g : ℕ → ι), g 0 = c ∧ (∀ i j, i ≤ n → j ≤ n → g i = g j → i = j) ∧
      (∀ i < n, q.c (g i) (g (i + 1)) = -1) ∧ (∀ i j, i + 1 < j → j ≤ n → q.c (g i) (g j) = 0) ∧
      (∀ i ≤ n, z (g i) = 1) ∧ ∀ k, (∀ i ≤ n, g i ≠ k) → z k = 0 := by
  induction h with
  | single c =>
    refine ⟨0, fun _ ↦ c, rfl, fun i j hi hj _ ↦ by omega, fun i hi ↦ by omega,
      fun i j h1 h2 ↦ by omega, fun i _ ↦ by simp, fun k hk ↦ ?_⟩
    have := hk 0 le_rfl
    simp [Pi.single_eq_of_ne (Ne.symm this)]
  | @cons c c₁ z _ hzc hne hc h0 ih =>
    obtain ⟨n, g, h1, h2, h3, h4, h5, h6⟩ := ih
    have hnotin : ∀ i ≤ n, g i ≠ c := fun i hi h ↦ by
      have := h5 i hi
      rw [h, hzc] at this
      omega
    let g' : ℕ → ι := fun i ↦ Nat.casesOn i c g
    have hg0 : g' 0 = c := rfl
    have hgs : ∀ i, g' (i + 1) = g i := fun _ ↦ rfl
    refine ⟨n + 1, g', rfl, fun i j hi hj hij ↦ ?_, fun i hi ↦ ?_, fun i j h7 h8 ↦ ?_,
      fun i hi ↦ ?_, fun k hk ↦ ?_⟩
    · rcases i with _ | i
      · rcases j with _ | j
        · rfl
        · exact absurd hij.symm (hnotin j (by omega))
      · rcases j with _ | j
        · exact absurd hij (hnotin i (by omega))
        · rw [h2 i j (by omega) (by omega) hij]
    · rcases i with _ | i
      · change q.c c (g 0) = -1
        rw [h1, hc]
      · exact h3 i (by omega)
    · rcases i with _ | i
      · rcases j with _ | _ | j
        · omega
        · omega
        · change q.c c (g (j + 1)) = 0
          refine h0 _ (fun h ↦ ?_) (hnotin _ (by omega)) ?_
          · have := h2 (j + 1) 0 (by omega) (by omega) (h.trans h1.symm)
            omega
          · rw [h5 _ (by omega)]
            norm_num
      · rcases j with _ | j
        · omega
        · exact h4 i j (by omega) (by omega)
    · rcases i with _ | i
      · simp [g', hzc]
      · have hne' := hnotin i (by omega)
        simp only [g', Pi.add_apply, Pi.single_eq_of_ne hne', add_zero]
        exact h5 i (by omega)
    · have hkc : k ≠ c := fun h ↦ hk 0 (by omega) (h ▸ rfl)
      simp only [Pi.add_apply, Pi.single_eq_of_ne hkc, add_zero]
      exact h6 k fun i hi ↦ hk (i + 1) (by omega)

/-- A good end at `c` supported in `z`. -/
def GoodEnd (q : UnitForm ι) (z : ι → ℤ) (c : ι) : Prop :=
  ∃ w, Pos w ∧ w c = 2 ∧ q.val w ≤ 2 ∧ ∀ a, 0 < w a → 0 < z a

/-- **Lemma R.** A root is a clean line from `c`, or it contains a good end at `c`. -/
theorem end_or_line : ∀ (n : ℕ) (z : ι → ℤ) (c : ι), (∑ i, z i).toNat = n → q.IsRoot z →
    1 ≤ z c → q.IsLine c z ∨ GoodEnd q z c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z c hn hz hc
    by_cases hsingle : z = Pi.single c 1
    · rw [hsingle]
      exact Or.inl (IsLine.single c)
    by_cases h2 : 2 ≤ z c
    · right
      obtain ⟨s, hs, hsc, hle⟩ := exists_root_two hw c _ z rfl hz h2
      exact ⟨s, hs.1, hsc, by rw [hs.2]; norm_num, fun a ha ↦ lt_of_lt_of_le ha (hle a)⟩
    have hc1 : z c = 1 := by omega
    have hd := partial_le_one hw hz hc hsingle
    by_cases hd0 : q.B z (Pi.single c 1) ≤ 0
    · -- `z + e_c`
      right
      refine ⟨z + Pi.single c 1, ⟨fun a ↦ ?_, fun h ↦ ?_⟩, by simp [hc1], ?_, fun a ha ↦ ?_⟩
      · by_cases ha : a = c
        · subst ha; simp; omega
        · simpa [Pi.single_eq_of_ne ha] using hz.1.1 a
      · have := congrFun h c
        simp [hc1] at this
      · rw [q.val_add_single, hz.2]
        omega
      · by_cases hac : a = c
        · subst hac; omega
        · simpa [Pi.single_eq_of_ne hac] using ha
    have hd1 : q.B z (Pi.single c 1) = 1 := by omega
    have hexp : q.B z (Pi.single c 1) = ∑ b, q.c b c * z b := q.B_single_right z c
    -- a dotted neighbour gives the minimal pair root
    by_cases hdot : ∃ b, b ≠ c ∧ 0 < z b ∧ 0 < q.c b c
    · right
      obtain ⟨b, hbc, hzb, hcb⟩ := hdot
      obtain ⟨s, hs, hsle, h1, h2', h3, h4⟩ := exists_minimal_pair hw hbc _ z rfl hz hzb hc
      let w : ι → ℤ := s + Pi.single c 1 - Pi.single b 1
      have hwc : w c = 2 := by simp [w, h2', Pi.single_eq_of_ne (Ne.symm hbc)]
      have hwb : w b = 0 := by simp [w, h1, Pi.single_eq_of_ne hbc]
      have hwnn : ∀ a, 0 ≤ w a := fun a ↦ by
        by_cases ha : a = b
        · subst ha; rw [hwb]
        · by_cases ha' : a = c
          · subst ha'; rw [hwc]; norm_num
          · simpa [w, Pi.single_eq_of_ne ha, Pi.single_eq_of_ne ha'] using hs.1.1 a
      refine ⟨w, ⟨hwnn, fun h ↦ ?_⟩, hwc, ?_, fun a ha ↦ ?_⟩
      · have := congrFun h c
        rw [hwc] at this
        simp at this
      · -- `q(w) = 3 - c_bc`
        have hv : q.val (s + Pi.single c 1) = 2 + q.B s (Pi.single c 1) := by
          rw [q.val_add_single, hs.2]; ring
        have hv2 := q.val_sub_single (s + Pi.single c 1) b
        have hB : q.B (s + Pi.single c 1) (Pi.single b 1) = q.B s (Pi.single b 1) +
            q.B (Pi.single c 1) (Pi.single b 1) := q.B_add_left _ _ _
        have hBc : q.B (Pi.single c 1) (Pi.single b 1) = q.c b c := by
          rw [q.B_single_right]
          simp [Pi.single_apply, q.symm c b]
        change q.val (s + Pi.single c 1 - Pi.single b 1) ≤ 2
        rw [hv2, hv, hB, hBc, h3, h4]
        omega
      · by_cases hab : a = b
        · subst hab; omega
        · by_cases hac : a = c
          · subst hac; omega
          · have h5 : 0 < s a := by
              simpa [w, Pi.single_eq_of_ne hab, Pi.single_eq_of_ne hac] using ha
            exact lt_of_lt_of_le h5 (hsle a)
    · push Not at hdot
      -- exactly one neighbour
      have hsum : ∑ b ∈ Finset.univ.erase c, q.c b c * z b = -1 := by
        have h3 := Finset.add_sum_erase Finset.univ (fun b ↦ q.c b c * z b) (Finset.mem_univ c)
        simp only [q.diag, hc1] at h3
        omega
      have hterm : ∀ b ∈ Finset.univ.erase c, q.c b c * z b ≤ 0 := fun b hb ↦ by
        have hbc := Finset.ne_of_mem_erase hb
        by_cases h0 : z b = 0
        · simp [h0]
        · have h1 : 0 < z b := by have := hz.1.1 b; omega
          exact mul_nonpos_of_nonpos_of_nonneg (hdot b hbc h1) h1.le
      obtain ⟨c₁, hc₁, hneg⟩ : ∃ b ∈ Finset.univ.erase c, q.c b c * z b < 0 := by
        by_contra hno
        push Not at hno
        have : ∑ b ∈ Finset.univ.erase c, q.c b c * z b ≥ 0 := Finset.sum_nonneg hno
        omega
      have hc₁c := Finset.ne_of_mem_erase hc₁
      have hrest : ∑ b ∈ (Finset.univ.erase c).erase c₁, q.c b c * z b ≤ 0 :=
        Finset.sum_nonpos fun b hb ↦ hterm b (Finset.mem_of_mem_erase hb)
      have hsplit := Finset.add_sum_erase _ (fun b ↦ q.c b c * z b) hc₁
      have hval : q.c c₁ c * z c₁ = -1 := by
        have h6 := hterm c₁ hc₁
        have h7 : -1 ≤ q.c c₁ c * z c₁ := by
          omega
        omega
      have hrest0 : ∑ b ∈ (Finset.univ.erase c).erase c₁, q.c b c * z b = 0 := by
        omega
      have hzero : ∀ b ∈ (Finset.univ.erase c).erase c₁, q.c b c * z b = 0 :=
        (Finset.sum_eq_zero_iff_of_nonpos fun b hb ↦
          hterm b (Finset.mem_of_mem_erase hb)).1 hrest0
      have hz1 : z c₁ = 1 := by
        have := Int.eq_one_or_neg_one_of_mul_eq_neg_one' hval
        have h8 := hz.1.1 c₁
        omega
      have hcc : q.c c₁ c = -1 := by
        rw [hz1, mul_one] at hval
        exact hval
      have hroot := isRoot_sub hw hz hc hsingle hd1
      have hsumz : ∑ i, (z - Pi.single c 1 : ι → ℤ) i = ∑ i, z i - 1 := by
        simp [Finset.sum_sub_distrib]
      have hnonneg : 0 ≤ ∑ i, (z - Pi.single c 1 : ι → ℤ) i := Finset.sum_nonneg fun a _ ↦ hroot.1.1 a
      have hc1z : (z - Pi.single c 1 : ι → ℤ) c₁ = 1 := by
        simp [Pi.single_eq_of_ne hc₁c, hz1]
      have hzc0 : (z - Pi.single c 1 : ι → ℤ) c = 0 := by simp [hc1]
      have hother : ∀ b, b ≠ c₁ → b ≠ c → 0 < z b → q.c b c = 0 := fun b hb1 hb2 hb3 ↦ by
        have := hzero b (Finset.mem_erase.2 ⟨hb1, Finset.mem_erase.2 ⟨hb2, Finset.mem_univ _⟩⟩)
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · omega
      rcases ih _ (by omega) (z - Pi.single c 1) c₁ rfl hroot (by omega) with hline | ⟨w, hw1, hw2, hw3, hw4⟩
      · left
        have hz' : z = (z - Pi.single c 1) + Pi.single c 1 := by simp
        rw [hz']
        refine IsLine.cons hline hzc0 (Ne.symm hc₁c) (by rw [q.symm]; exact hcc) ?_
        intro b hb1 hb2 hb3
        rw [q.symm]
        refine hother b hb1 hb2 ?_
        simpa [Pi.single_eq_of_ne hb2] using hb3
      · right
        have hwc : w c = 0 := by
          by_contra hne
          have h1 : 0 < w c := by have := hw1.1 c; omega
          have := hw4 c h1
          omega
        have hsupp : ∀ a, 0 < w a → a ≠ c ∧ 0 < z a := fun a ha ↦ by
          have h1 := hw4 a ha
          have hac : a ≠ c := by rintro rfl; omega
          refine ⟨hac, ?_⟩
          simpa [Pi.single_eq_of_ne hac] using h1
        have hB : q.B w (Pi.single c 1) = -2 := by
          rw [q.B_single_right, Finset.sum_eq_single c₁]
          · rw [hcc, hw2]; norm_num
          · intro b _ hb
            by_cases h0 : w b = 0
            · simp [h0]
            · have h1 : 0 < w b := by have := hw1.1 b; omega
              obtain ⟨h2, h3⟩ := hsupp b h1
              rw [hother b hb h2 h3, zero_mul]
          · simp
        refine ⟨w + (Pi.single c 1 + Pi.single c 1), ⟨fun a ↦ ?_, fun h ↦ ?_⟩, ?_, ?_, fun a ha ↦ ?_⟩
        · by_cases ha : a = c
          · subst ha; simp [hwc]
          · simpa [Pi.single_eq_of_ne ha] using hw1.1 a
        · have := congrFun h c
          simp [hwc] at this
        · simp [hwc]
        · rw [q.val_add_two_single, hB]
          omega
        · by_cases hac : a = c
          · subst hac; omega
          · have h1 : 0 < w a := by simpa [Pi.single_eq_of_ne hac] using ha
            exact (hsupp a h1).2

omit hw in
/-- The value of a sum of three vectors. -/
lemma val_add_three (a b c : ι → ℤ) : q.val (a + b + c) =
    q.val (a + c) + q.val (b + c) - q.val c + q.B a b := by
  have h1 := q.two_mul_val (a + b + c)
  have h2 := q.two_mul_val (a + c)
  have h3 := q.two_mul_val (b + c)
  have h4 := q.two_mul_val c
  simp only [B_add_left, B_add_right] at h1 h2 h3
  have e1 := B_symm q b a
  have e2 := B_symm q c a
  have e3 := B_symm q c b
  linarith

/-- **Gluing.** Two good ends at `t` with orthogonal rest contradict weak positivity. -/
theorem false_of_glue {t : ι} {w₁ w₂ : ι → ℤ} (h1 : Pos w₁) (h2 : Pos w₂) (ht1 : w₁ t = 2)
    (ht2 : w₂ t = 2) (hv1 : q.val w₁ ≤ 2) (hv2 : q.val w₂ ≤ 2)
    (horth : q.B (w₁ - (Pi.single t 1 + Pi.single t 1)) (w₂ - (Pi.single t 1 + Pi.single t 1)) = 0) :
    False := by
  let e : ι → ℤ := Pi.single t 1 + Pi.single t 1
  have he : q.val e = 4 := by
    change q.val (Pi.single t 1 + Pi.single t 1) = 4
    have h1 := q.two_mul_val (Pi.single t 1 + Pi.single t 1)
    have h2 : q.B (Pi.single t 1) (Pi.single t 1) = 2 := by
      rw [q.B_single_right]; simp [Pi.single_apply, q.diag]
    rw [B_add_left, B_add_right, h2] at h1
    omega
  have hpos : Pos ((w₁ - e) + (w₂ - e) + e) := by
    refine ⟨fun a ↦ ?_, fun h ↦ ?_⟩
    · by_cases ha : a = t
      · subst ha; simp [e, ht1, ht2]
      · have h3 := h1.1 a
        have h4 := h2.1 a
        simp [e, Pi.single_eq_of_ne ha]
        omega
    · have := congrFun h t
      simp [e, ht1, ht2] at this
  have := hw _ hpos
  rw [val_add_three] at this
  simp only [sub_add_cancel] at this
  have hB : q.B (w₁ - e) (w₂ - e) = 0 := horth
  rw [he, hB] at this
  omega


omit hw in
lemma val_add (x y : ι → ℤ) : q.val (x + y) = q.val x + q.val y + q.B x y := by
  have h1 := q.two_mul_val (x + y)
  have h2 := q.two_mul_val x
  have h3 := q.two_mul_val y
  rw [B_add_left, B_add_right, B_add_right, B_symm q y x] at h1
  omega

omit hw in
lemma val_sub (x y : ι → ℤ) : q.val (x - y) = q.val x + q.val y - q.B x y := by
  have := q.two_val_sub x y
  omega

/-- Two roots pair to at least `-1`. -/
lemma neg_one_le_B {x y : ι → ℤ} (hx : q.IsRoot x) (hy : q.IsRoot y) : -1 ≤ q.B x y := by
  have hp : Pos (x + y) := by
    refine ⟨fun a ↦ ?_, fun h ↦ hx.1.2 ?_⟩
    · have := hx.1.1 a
      have := hy.1.1 a
      simp only [Pi.add_apply]
      omega
    · funext a
      have h1 := congrFun h a
      have h2 := hx.1.1 a
      have h3 := hy.1.1 a
      simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
      omega
  have := hw _ hp
  rw [val_add, hx.2, hy.2] at this
  omega

/-- **Minimal roots above a vector.** -/
theorem exists_minimal_above {s : ι → ℤ} (hs : Pos s) : ∀ (n : ℕ) (r : ι → ℤ),
    (∑ i, r i).toNat = n → q.IsRoot r → (∀ a, s a ≤ r a) → ∃ y, q.IsRoot y ∧ (∀ a, s a ≤ y a) ∧
      ∀ k, s k < y k → q.B y (Pi.single k 1) ≤ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r hn hr hsr
    by_cases hex : ∃ k, s k < r k ∧ 0 < q.B r (Pi.single k 1)
    · obtain ⟨k, hk1, hk2⟩ := hex
      have hk0 : 1 ≤ r k := by have := hs.1 k; omega
      have hk3 : r ≠ Pi.single k 1 := by
        rintro rfl
        apply hs.2
        funext a
        by_cases ha : a = k
        · subst ha
          have := hs.1 a
          simp only [Pi.single_eq_same] at hk1
          simp only [Pi.zero_apply]
          omega
        · have h1 := hsr a
          have h2 := hs.1 a
          simp only [Pi.single_eq_of_ne ha] at h1
          simp only [Pi.zero_apply]
          omega
      have hd := partial_le_one hw hr hk0 hk3
      have hroot := isRoot_sub hw hr hk0 hk3 (by omega)
      have hsum : ∑ i, (r - Pi.single k 1 : ι → ℤ) i = ∑ i, r i - 1 := by
        simp [Finset.sum_sub_distrib]
      have hnonneg : 0 ≤ ∑ i, (r - Pi.single k 1 : ι → ℤ) i :=
        Finset.sum_nonneg fun a _ ↦ hroot.1.1 a
      refine ih _ (by omega) (r - Pi.single k 1) rfl hroot fun a ↦ ?_
      by_cases ha : a = k
      · subst ha; simp; omega
      · simpa [Pi.single_eq_of_ne ha] using hsr a
    · push Not at hex
      exact ⟨r, hr, hsr, hex⟩

omit hw in
lemma B_fsum_left {κ : Type} (S : Finset κ) (f : κ → ι → ℤ) (y : ι → ℤ) :
    q.B (∑ i ∈ S, f i) y = ∑ i ∈ S, q.B (f i) y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [B_zero_left]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, B_add_left, ih]

omit hw in
lemma B_fsum_right {κ : Type} (S : Finset κ) (f : κ → ι → ℤ) (y : ι → ℤ) :
    q.B y (∑ i ∈ S, f i) = ∑ i ∈ S, q.B y (f i) := by
  rw [B_symm, B_fsum_left]
  exact Finset.sum_congr rfl fun i _ ↦ B_symm q _ _

omit hw in
lemma val_two_single (a : ι) : q.val (Pi.single a 1 + Pi.single a 1) = 4 := by
  have h2 : q.B (Pi.single a 1) (Pi.single a 1) = 2 := by
    rw [q.B_single_right]; simp [Pi.single_apply, q.diag]
  rw [val_add, val_single, h2]
  norm_num

omit hw in
/-- Disjoint orthogonal supports have zero pairing. -/
lemma B_eq_zero_of_orth {x y : ι → ℤ} (hx : ∀ a, 0 ≤ x a) (hy : ∀ a, 0 ≤ y a)
    (h : ∀ k l, 0 < x k → 0 < y l → q.c k l = 0) : q.B x y = 0 := by
  unfold B
  refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
  by_cases h1 : x k = 0
  · simp [h1]
  by_cases h2 : y l = 0
  · simp [h2]
  have h3 := hx k
  have h4 := hy l
  rw [h k l (by omega) (by omega)]
  simp

/-- An anchor: the form-theoretic shadow of a commutative polygon. -/
structure Anchor (q : UnitForm ι) (κ : Type) [Fintype κ] where
  /-- The source. -/
  a : ι
  /-- The sink. -/
  b : ι
  /-- The arms. -/
  r : κ → ι → ℤ
  root_r : ∀ j, q.IsRoot (r j)
  B_a : ∀ j, q.B (Pi.single a 1) (r j) = -1
  B_b : ∀ j, q.B (Pi.single b 1) (r j) = -1
  B_r : ∀ i j, i ≠ j → q.B (r i) (r j) = 0
  two : ∃ i j : κ, i ≠ j

namespace Anchor

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The thin vector of an anchor. -/
def t (A : Anchor q κ) : ι → ℤ := Pi.single A.a 1 + Pi.single A.b 1 + ∑ j, A.r j

omit hw [DecidableEq κ] in
lemma single_nonneg (c k : ι) : 0 ≤ (Pi.single c 1 : ι → ℤ) k := by
  by_cases h : k = c
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

omit hw in
lemma B_t_r (A : Anchor q κ) (j : κ) : q.B A.t (A.r j) = 0 := by
  have h : q.B (∑ i, A.r i) (A.r j) = 2 := by
    rw [B_fsum_left, Finset.sum_eq_single j]
    · have := q.two_mul_val (A.r j)
      rw [(A.root_r j).2] at this
      omega
    · intro i _ hi
      exact A.B_r i j hi
    · simp
  unfold t
  rw [B_add_left, B_add_left, A.B_a, A.B_b, h]
  norm_num

omit hw in
lemma r_add_single_le (A : Anchor q κ) (j : κ) (k : ι) :
    (Pi.single A.a 1 : ι → ℤ) k + (Pi.single A.b 1 : ι → ℤ) k + A.r j k ≤ A.t k := by
  have h : A.r j k ≤ ∑ i, A.r i k :=
    Finset.single_le_sum (f := fun i ↦ A.r i k) (fun i _ ↦ (A.root_r i).1.1 k) (Finset.mem_univ j)
  simp only [t, Pi.add_apply, Finset.sum_apply]
  omega

omit hw in
lemma t_nonneg (A : Anchor q κ) (k : ι) : 0 ≤ A.t k := by
  obtain ⟨i, -, -⟩ := A.two
  have h1 := A.r_add_single_le i k
  have h2 := single_nonneg A.a k
  have h3 := single_nonneg A.b k
  have h4 := (A.root_r i).1.1 k
  omega

omit hw in
lemma t_a_pos (A : Anchor q κ) : 0 < A.t A.a := by
  obtain ⟨i, -, -⟩ := A.two
  have h1 := A.r_add_single_le i A.a
  have h3 := single_nonneg A.b A.a
  have h4 := (A.root_r i).1.1 A.a
  simp only [Pi.single_eq_same] at h1
  omega

omit hw in
lemma t_b_pos (A : Anchor q κ) : 0 < A.t A.b := by
  obtain ⟨i, -, -⟩ := A.two
  have h1 := A.r_add_single_le i A.b
  have h3 := single_nonneg A.a A.b
  have h4 := (A.root_r i).1.1 A.b
  simp only [Pi.single_eq_same] at h1
  omega

omit hw in
lemma t_pos (A : Anchor q κ) : Pos A.t := by
  refine ⟨A.t_nonneg, fun h ↦ ?_⟩
  have := A.t_a_pos
  rw [h] at this
  simp at this

omit hw in
/-- The fork vector at the source or sink of an anchor. -/
lemma fork {A : Anchor q κ} {c : ι} {i j : κ} (hij : i ≠ j) {x : ι → ℤ}
    (hci : q.B (Pi.single c 1) (A.r i) = -1) (hcj : q.B (Pi.single c 1) (A.r j) = -1)
    (hc : 0 < A.t c) (hxc : q.B x (Pi.single c 1) = -1) (hxi : q.B x (A.r i) = 0)
    (hxj : q.B x (A.r j) = 0) :
    ∃ G, Pos G ∧ (∀ k, 0 < G k → 0 < A.t k) ∧ q.val G ≤ 2 ∧ q.B x G ≤ -2 := by
  refine ⟨Pi.single c 1 + Pi.single c 1 + A.r i + A.r j, ⟨fun k ↦ ?_, fun h ↦ ?_⟩, fun k hk ↦ ?_,
    ?_, ?_⟩
  · have := single_nonneg c k
    have := (A.root_r i).1.1 k
    have := (A.root_r j).1.1 k
    simp only [Pi.add_apply]
    omega
  · have h1 := congrFun h c
    have := (A.root_r i).1.1 c
    have := (A.root_r j).1.1 c
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at h1
    omega
  · simp only [Pi.add_apply] at hk
    by_cases hkc : k = c
    · subst hkc; exact hc
    · simp only [Pi.single_eq_of_ne hkc] at hk
      have h1 := A.r_add_single_le i k
      have h2 := A.r_add_single_le j k
      have h3 := single_nonneg A.a k
      have h4 := single_nonneg A.b k
      omega
  · rw [val_add, val_add, val_two_single, (A.root_r i).2, (A.root_r j).2]
    simp only [B_add_left]
    rw [hci, hcj, A.B_r i j hij]
    norm_num
  · rw [B_add_right, B_add_right, B_add_right, hxc, hxi, hxj]
    norm_num

/-- **The local lemma.** A root attached to an anchor pairs to `-2` with a good vector. -/
theorem exists_good (A : Anchor q κ) (hv : q.val A.t = 1) {x : ι → ℤ} (hx : q.IsRoot x)
    (hB : q.B x A.t = -1) :
    ∃ G, Pos G ∧ (∀ k, 0 < G k → 0 < A.t k) ∧ q.val G ≤ 2 ∧ q.B x G ≤ -2 := by
  have hp := neg_one_le_partial hw hx A.a
  have hm := neg_one_le_partial hw hx A.b
  have hs : ∀ j, -1 ≤ q.B x (A.r j) := fun j ↦ neg_one_le_B hw hx (A.root_r j)
  have hsum : q.B x (Pi.single A.a 1) + q.B x (Pi.single A.b 1) + ∑ j, q.B x (A.r j) = -1 := by
    have h := hB
    unfold t at h
    rw [B_add_right, B_add_right, B_fsum_right] at h
    exact h
  by_cases h1 : ∃ j, q.B x (A.r j) = -1
  · obtain ⟨j, hj⟩ := h1
    refine ⟨A.t + A.r j, ⟨fun k ↦ ?_, fun h ↦ ?_⟩, fun k hk ↦ ?_, ?_, ?_⟩
    · have := A.t_nonneg k
      have := (A.root_r j).1.1 k
      simp only [Pi.add_apply]
      omega
    · have h1 := congrFun h A.a
      have := A.t_a_pos
      have := (A.root_r j).1.1 A.a
      simp only [Pi.add_apply, Pi.zero_apply] at h1
      omega
    · simp only [Pi.add_apply] at hk
      have h1 := A.r_add_single_le j k
      have h3 := single_nonneg A.a k
      have h4 := single_nonneg A.b k
      omega
    · rw [val_add, hv, (A.root_r j).2, A.B_t_r]
      norm_num
    · rw [B_add_right, hB, hj]
      norm_num
  by_cases h2 : ∃ j, 1 ≤ q.B x (A.r j)
  · obtain ⟨j, hj⟩ := h2
    refine ⟨A.t - A.r j, ⟨fun k ↦ ?_, fun h ↦ ?_⟩, fun k hk ↦ ?_, ?_, ?_⟩
    · have h1 := A.r_add_single_le j k
      have h3 := single_nonneg A.a k
      have h4 := single_nonneg A.b k
      simp only [Pi.sub_apply]
      omega
    · have h1 := congrFun h A.a
      have h2 := A.r_add_single_le j A.a
      have h4 := single_nonneg A.b A.a
      simp only [Pi.sub_apply, Pi.zero_apply] at h1
      simp only [Pi.single_eq_same] at h2
      omega
    · simp only [Pi.sub_apply] at hk
      have := (A.root_r j).1.1 k
      omega
    · rw [val_sub, hv, (A.root_r j).2, A.B_t_r]
      norm_num
    · rw [B_sub_right, hB]
      omega
  push Not at h1 h2
  have h0 : ∀ j, q.B x (A.r j) = 0 := fun j ↦ by
    have h3 := hs j
    have h4 := h1 j
    have h5 := h2 j
    omega
  obtain ⟨i, j, hij⟩ := A.two
  simp only [h0, Finset.sum_const_zero, add_zero] at hsum
  by_cases hp1 : q.B x (Pi.single A.a 1) = -1
  · exact fork hij (A.B_a i) (A.B_a j) A.t_a_pos hp1 (h0 i) (h0 j)
  · exact fork hij (A.B_b i) (A.B_b j) A.t_b_pos (by omega) (h0 i) (h0 j)

end Anchor

/-- **Two orthogonal anchors are never below a common root.** -/
theorem false_of_anchors {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁]
    [DecidableEq κ₂] (A₁ : Anchor q κ₁) (A₂ : Anchor q κ₂) (hv₁ : q.val A₁.t = 1)
    (hv₂ : q.val A₂.t = 1) {z : ι → ℤ} (hz : q.IsRoot z) (hle : ∀ k, A₁.t k + A₂.t k ≤ z k)
    (horth : ∀ k l, 0 < A₁.t k → 0 < A₂.t l → q.c k l = 0) : False := by
  have h12 : q.B A₁.t A₂.t = 0 := q.B_eq_zero_of_orth A₁.t_nonneg A₂.t_nonneg horth
  have hspos : Pos (A₁.t + A₂.t) := by
    refine ⟨fun k ↦ ?_, fun h ↦ ?_⟩
    · have := A₁.t_nonneg k
      have := A₂.t_nonneg k
      simp only [Pi.add_apply]
      omega
    · have h1 := congrFun h A₁.a
      have h2 := A₁.t_a_pos
      have h3 := A₂.t_nonneg A₁.a
      simp only [Pi.add_apply, Pi.zero_apply] at h1
      omega
  obtain ⟨y, hy, hyle, hmin⟩ := exists_minimal_above hw hspos _ z rfl hz hle
  have hval : q.val (A₁.t + A₂.t) = 2 := by rw [val_add, hv₁, hv₂, h12]; norm_num
  let a : ι → ℤ := y - (A₁.t + A₂.t)
  have ha0 : ∀ k, 0 ≤ a k := fun k ↦ by have := hyle k; simp only [a, Pi.sub_apply]; omega
  have hane : a ≠ 0 := by
    intro h
    have : y = A₁.t + A₂.t := sub_eq_zero.1 h
    rw [this] at hy
    have := hy.2
    omega
  have hapos : Pos a := ⟨ha0, hane⟩
  have hqa := hw a hapos
  have hya : y = (A₁.t + A₂.t) + a := by simp [a]
  -- `B(y, a) ≤ 0`
  have hBya : q.B y a ≤ 0 := by
    rw [B_eq_sum_single]
    refine Finset.sum_nonpos fun k _ ↦ ?_
    by_cases h0 : a k = 0
    · simp [h0]
    · have h1 : (A₁.t + A₂.t) k < y k := by
        have := ha0 k
        simp only [a, Pi.sub_apply] at h0 this
        omega
      exact mul_nonpos_of_nonneg_of_nonpos (ha0 k) (hmin k h1)
  have hq1 : q.val y = 1 := hy.2
  have h1 : q.val y = q.val (A₁.t + A₂.t) + q.val a + q.B (A₁.t + A₂.t) a := by rw [hya, val_add]
  have h2 : q.B y a = q.B (A₁.t + A₂.t) a + 2 * q.val a := by
    rw [two_mul_val]
    conv_lhs => rw [hya]
    rw [B_add_left]
  have hqa1 : q.val a = 1 := by omega
  have har : q.IsRoot a := ⟨hapos, hqa1⟩
  have hB12 : q.B (A₁.t + A₂.t) a = -2 := by omega
  rw [B_add_left] at hB12
  have hrA₁.t : q.IsRoot A₁.t := ⟨A₁.t_pos, hv₁⟩
  have hrA₂.t : q.IsRoot A₂.t := ⟨A₂.t_pos, hv₂⟩
  have hb1 := neg_one_le_B hw hrA₁.t har
  have hb2 := neg_one_le_B hw hrA₂.t har
  have hb1' : q.B a A₁.t = -1 := by rw [B_symm]; omega
  have hb2' : q.B a A₂.t = -1 := by rw [B_symm]; omega
  obtain ⟨G₁, hG₁, hs₁, hv₁', hB₁⟩ := A₁.exists_good hw hv₁ har hb1'
  obtain ⟨G₂, hG₂, hs₂, hv₂', hB₂⟩ := A₂.exists_good hw hv₂ har hb2'
  have hG12 : q.B G₁ G₂ = 0 :=
    q.B_eq_zero_of_orth hG₁.1 hG₂.1 fun k l hk hl ↦ horth k l (hs₁ k hk) (hs₂ l hl)
  have hpos : Pos (a + a + G₁ + G₂) := by
    refine ⟨fun k ↦ ?_, fun h ↦ hane ?_⟩
    · have := ha0 k
      have := hG₁.1 k
      have := hG₂.1 k
      simp only [Pi.add_apply]
      omega
    · funext k
      have h1 := congrFun h k
      have := ha0 k
      have := hG₁.1 k
      have := hG₂.1 k
      simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
      omega
  have hfinal := hw _ hpos
  have h3 : q.val (a + a) = 4 := by
    rw [val_add, hqa1]
    have := q.two_mul_val a
    omega
  rw [val_add, val_add, h3] at hfinal
  simp only [B_add_left] at hfinal
  rw [hG12] at hfinal
  omega

end UnitForm

end LargeIndecomposable.Forms
