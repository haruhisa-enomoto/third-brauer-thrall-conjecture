module

public import LargeIndecomposable.DirectedAlgebras.Sincere.SincereTree
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The underlying graph of a directed algebra

If the underlying graph of a directed algebra is a forest, an edge separates the graph into two
sides. Two edges at a turn give a cut in the sense of `line_of_cut`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module SimpleGraph

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable (D : DirData k A)

/-- The underlying graph. -/
def gr : SimpleGraph D.ι := SimpleGraph.fromRel D.Arr

variable {D}

omit [FiniteDimensional k A] in
lemma gr_adj {a b : D.ι} : D.gr.Adj a b ↔ a ≠ b ∧ (D.Arr a b ∨ D.Arr b a) :=
  SimpleGraph.fromRel_adj _ _ _

omit [FiniteDimensional k A] in
lemma gr_adj_of_arr {a b : D.ι} (h : D.Arr a b) : D.gr.Adj a b :=
  gr_adj.2 ⟨D.ne_of_arr h, Or.inl h⟩

lemma mem_of_reachable {V : Type*} {H : SimpleGraph V} {S : Set V}
    (hS : ∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S) {a b : V} (ha : a ∈ S) (h : H.Reachable a b) : b ∈ S := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ha
  | cons hab _ ih => exact ih (hS _ ha _ hab)

variable (D) in
/-- The graph without an edge. -/
abbrev grCut (t p : D.ι) : SimpleGraph D.ι := D.gr.deleteEdges {s(t, p)}

variable (D) in
/-- The side of `p` of the edge `t — p`. -/
def side (t p : D.ι) : Set D.ι := {c | (D.grCut t p).Reachable p c}

section Side

variable {t p p' : D.ι} (hac : D.gr.IsAcyclic) (htp : D.gr.Adj t p)
include hac htp

lemma self_mem_side : p ∈ D.side t p := Reachable.refl _

lemma not_mem_side : t ∉ D.side t p := by
  have h := (isAcyclic_iff_forall_adj_isBridge.1 hac htp)
  rw [isBridge_iff] at h
  exact fun h' ↦ h (Reachable.symm h')

lemma side_adj {a b : D.ι} (ha : a ∈ D.side t p) (hab : D.gr.Adj a b) :
    b ∈ D.side t p ∨ (a = p ∧ b = t) := by
  by_cases he : s(a, b) = s(t, p)
  · rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact absurd (h1 ▸ ha) (not_mem_side hac htp)
    · exact Or.inr ⟨h1, h2⟩
  · left
    refine Reachable.trans ha (Adj.reachable ?_)
    refine (deleteEdges_adj).2 ⟨hab, ?_⟩
    simpa using he

/-- A step out of a side is the edge. -/
lemma exit_side {a c : D.ι} (ha : a ∈ D.side t p) (hc : c ∉ D.side t p)
    (h : Relation.ReflTransGen D.Arr a c) : D.Arr p t := by
  induction h with
  | refl => exact absurd ha hc
  | tail hab hbc ih =>
    rename_i b c
    by_cases hb : b ∈ D.side t p
    · rcases side_adj hac htp hb (gr_adj_of_arr hbc) with h | ⟨rfl, rfl⟩
      · exact absurd h hc
      · exact hbc
    · exact ih hb

/-- A step into a side is the edge. -/
lemma enter_side {a c : D.ι} (ha : a ∈ D.side t p) (hc : c ∉ D.side t p)
    (h : Relation.ReflTransGen D.Arr c a) : D.Arr t p := by
  induction h with
  | refl => exact absurd ha hc
  | tail hab hbc ih =>
    rename_i b a
    by_cases hb : b ∈ D.side t p
    · exact ih hb
    · rcases side_adj hac htp ha (gr_adj_of_arr hbc).symm with h | ⟨rfl, rfl⟩
      · exact absurd h hb
      · exact hbc

/-- The union of a side and the point. -/
lemma exit_insert {x c : D.ι} (hx : x ∈ insert t (D.side t p)) (hc : c ∉ insert t (D.side t p))
    (h : Relation.ReflTransGen D.Arr x c) : Relation.TransGen D.Arr t c := by
  induction h with
  | refl => exact absurd hx hc
  | tail hab hbc ih =>
    rename_i b c
    by_cases hb : b ∈ insert t (D.side t p)
    · rcases hb with rfl | hb
      · exact Relation.TransGen.single hbc
      · rcases side_adj hac htp hb (gr_adj_of_arr hbc) with h | ⟨-, rfl⟩
        · exact absurd (Or.inr h) hc
        · exact absurd (Or.inl rfl) hc
    · exact (ih hb).tail hbc

lemma enter_insert {x c : D.ι} (hx : x ∈ insert t (D.side t p)) (hc : c ∉ insert t (D.side t p))
    (h : Relation.ReflTransGen D.Arr c x) : Relation.TransGen D.Arr c t := by
  induction h with
  | refl => exact absurd hx hc
  | tail hab hbc ih =>
    rename_i b a
    by_cases hb : b ∈ insert t (D.side t p)
    · exact ih hb
    · rcases hx with rfl | hx
      · exact Relation.TransGen.tail' hab hbc
      · rcases side_adj hac htp hx (gr_adj_of_arr hbc).symm with h | ⟨-, rfl⟩
        · exact absurd (Or.inr h) hb
        · exact absurd (Or.inl rfl) hb

/-- The union of a side and the point is convex. -/
lemma isConvexSet_insert_side : D.IsConvexSet (insert t (D.side t p)) := by
  intro x z c hx hz h1 h2
  by_contra hc
  exact D.acyc _ _ (exit_insert hac htp hx hc h1) (enter_insert hac htp hz hc h2).to_reflTransGen

lemma bdry_insert_side : D.bdry (insert t (D.side t p)) ⊆ {t} := by
  rintro b ⟨hb, c, hc, hbc⟩
  rcases hb with rfl | hb
  · rfl
  · exfalso
    have hadj : D.gr.Adj b c := by
      rcases hbc with h | h
      · exact gr_adj_of_arr h
      · exact (gr_adj_of_arr h).symm
    rcases side_adj hac htp hb hadj with h | ⟨-, rfl⟩
    · exact hc (Or.inr h)
    · exact hc (Or.inl rfl)

/-- Another neighbour of `t` is not on the side of `p`. -/
lemma not_mem_side_of_adj (htp' : D.gr.Adj t p') (hne : p ≠ p') : p' ∉ D.side t p := by
  intro h
  have h1 := side_adj hac htp h htp'.symm
  rcases h1 with h1 | ⟨h1, -⟩
  · exact not_mem_side hac htp h1
  · exact hne h1.symm

lemma not_mem_insert_of_adj (htp' : D.gr.Adj t p') (hne : p ≠ p') :
    p' ∉ insert t (D.side t p) := by
  rintro (h | h)
  · exact htp'.ne h.symm
  · exact not_mem_side_of_adj hac htp htp' hne h

lemma mem_bdry_insert (htp' : D.gr.Adj t p') (hne : p ≠ p') (h' : D.Arr t p' ∨ D.Arr p' t) :
    t ∈ D.bdry (insert t (D.side t p)) :=
  ⟨Or.inl rfl, p', not_mem_insert_of_adj hac htp htp' hne, h'⟩

/-- The two sides of two edges at a point are disjoint. -/
lemma side_disjoint (htp' : D.gr.Adj t p') (hne : p ≠ p') {c : D.ι} (h1 : c ∈ D.side t p)
    (h2 : c ∈ D.side t p') : False := by
  have hcl : ∀ a ∈ D.side t p ∩ D.side t p', ∀ b, (D.grCut t p').Adj a b →
      b ∈ D.side t p ∩ D.side t p' := by
    rintro a ⟨ha1, ha2⟩ b hab
    have hb2 : b ∈ D.side t p' := Reachable.trans ha2 (Adj.reachable hab)
    rcases side_adj hac htp ha1 ((deleteEdges_adj).1 hab).1 with h | ⟨-, rfl⟩
    · exact ⟨h, hb2⟩
    · exact absurd hb2 (not_mem_side hac htp')
  have := mem_of_reachable hcl ⟨h1, h2⟩ (Reachable.symm h2)
  exact not_mem_side_of_adj hac htp htp' hne this.1

end Side

/-- **The points of a path lie on one side.** -/
lemma seq_mem_side (hac : D.gr.IsAcyclic) (h : ℕ → D.ι) (r : ℕ)
    (hadj : ∀ i < r, D.gr.Adj (h i) (h (i + 1)))
    (hinj : ∀ i j, i ≤ r → j ≤ r → h i = h j → i = j) :
    ∀ j, 1 ≤ j → j ≤ r → h j ∈ D.side (h 0) (h 1) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact fun hr ↦ self_mem_side hac (hadj 0 (by omega))
  | succ j hj ih =>
    intro hr
    rcases side_adj hac (hadj 0 (by omega)) (ih (by omega)) (hadj j (by omega)) with h1 | ⟨-, h1⟩
    · exact h1
    · have := hinj (j + 1) 0 hr (by omega) h1
      omega

/-- Two paths from a point to a point agree as long as they both run. -/
lemma seq_unique (hac : D.gr.IsAcyclic) (g h : ℕ → D.ι) {r r' : ℕ} (hr : g r = h r')
    (hg0 : g 0 = h 0) (hadj : ∀ i < r, D.gr.Adj (g i) (g (i + 1)))
    (hadj' : ∀ i < r', D.gr.Adj (h i) (h (i + 1)))
    (hinj : ∀ i j, i ≤ r → j ≤ r → g i = g j → i = j)
    (hinj' : ∀ i j, i ≤ r' → j ≤ r' → h i = h j → i = j) : r = r' := by
  have key : ∀ m, m ≤ r → m ≤ r' → g m = h m := by
    intro m
    induction m with
    | zero => exact fun _ _ ↦ hg0
    | succ m ih =>
      intro h1 h2
      by_contra hne
      have hm := ih (by omega) (by omega)
      have hs1 := seq_mem_side hac (fun j ↦ g (m + j)) (r - m)
        (fun i hi ↦ hadj (m + i) (by omega))
        (fun i j hi hj hij ↦ by
          have := hinj (m + i) (m + j) (by omega) (by omega) hij
          omega) (r - m) (by omega) le_rfl
      have hs2 := seq_mem_side hac (fun j ↦ h (m + j)) (r' - m)
        (fun i hi ↦ hadj' (m + i) (by omega))
        (fun i j hi hj hij ↦ by
          have := hinj' (m + i) (m + j) (by omega) (by omega) hij
          omega) (r' - m) (by omega) le_rfl
      simp only [Nat.add_zero] at hs1 hs2
      have e1 : m + (r - m) = r := by omega
      have e2 : m + (r' - m) = r' := by omega
      have e3 : m + 1 = m + 1 := rfl
      rw [e1] at hs1
      rw [e2, ← hm, ← hr] at hs2
      exact side_disjoint hac (hadj m (by omega)) (by
        have := hadj' m (by omega)
        rwa [← hm] at this) hne hs1 hs2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have h2 := key r le_rfl h1.le
    have := hinj' r r' h1.le le_rfl (h2.symm.trans hr)
    omega
  · have h2 := key r' h1.le le_rfl
    have := hinj r r' le_rfl h1.le (hr.trans h2.symm)
    omega

/-- A turn of two edges at a point. -/
def IsTurn (D : DirData k A) (t p p' : D.ι) : Prop :=
  (D.Arr p t ∧ D.Arr p' t) ∨ (D.Arr t p ∧ D.Arr t p')

lemma not_arr_cycle {a b : D.ι} (h1 : D.Arr a b) (h2 : D.Arr b a) : False :=
  D.acyc _ _ (Relation.TransGen.single h1) (Relation.ReflTransGen.single h2)

/-- **The two sides at a turn are orthogonal.** -/
theorem side_orth {t p p' : D.ι} (hac : D.gr.IsAcyclic) (htp : D.gr.Adj t p)
    (htp' : D.gr.Adj t p') (hne : p ≠ p') (hturn : D.IsTurn t p p') {a b : D.ι}
    (ha : a ∈ D.side t p) (hb : b ∈ D.side t p') :
    ¬Relation.ReflTransGen D.Arr a b ∧ ¬Relation.ReflTransGen D.Arr b a := by
  have hb' : b ∉ D.side t p := fun h ↦ side_disjoint hac htp htp' hne h hb
  have ha' : a ∉ D.side t p' := fun h ↦ side_disjoint hac htp htp' hne ha h
  constructor
  · intro h
    have h1 := exit_side hac htp ha hb' h
    have h2 := enter_side hac htp' hb ha' h
    rcases hturn with ⟨-, h3⟩ | ⟨h3, -⟩
    · exact not_arr_cycle h2 h3
    · exact not_arr_cycle h1 h3
  · intro h
    have h1 := exit_side hac htp' hb ha' h
    have h2 := enter_side hac htp ha hb' h
    rcases hturn with ⟨h3, -⟩ | ⟨-, h3⟩
    · exact not_arr_cycle h2 h3
    · exact not_arr_cycle h1 h3

/-- The bound on directed runs. -/
def RunB (D : DirData k A) (M : ℕ) : Prop :=
  ∀ (x : ℕ → D.ι) (c : ℕ → A) (s t : ℕ) (w : A), (∀ i, s ≤ i → i < t → x i ≠ x (i + 1)) →
    s + M ≤ t → IsChain D x c s t w → D.e (x t) * w * D.e (x s) = 0

section Turn

variable {U : FDMod k A} (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) {M : ℕ}
  (hM : RunB D M) {f : ℕ → D.ι}

include hT hU hs hM in
/-- A directed run in the graph has bounded length. -/
lemma run_lt {x : ℕ → D.ι} {r : ℕ} (h : ∀ i < r, D.Arr (x i) (x (i + 1))) : r < 2 * M := by
  classical
  have hc : ∀ i, ∃ c : A, i < r → D.e (x (i + 1)) * c * D.e (x i) ≠ 0 := fun i ↦ by
    by_cases hi : i < r
    · obtain ⟨c, hc⟩ := D.arrNe _ _ (h i hi)
      exact ⟨c, fun _ ↦ hc⟩
    · exact ⟨0, fun h' ↦ absurd h' hi⟩
  choose c hc using hc
  exact run_bound hT hU hs h c hc M fun s t w h1 h2 h3 ↦
    hM x c s t w (fun i _ hi ↦ D.ne_of_arr (h i (by omega))) h1 h3

include hT hU hs hM in
/-- **A long path has a turn.** -/
theorem exists_turn (a : ℕ) (hadj : ∀ i, a ≤ i → i < a + 2 * M + 1 → D.Arr (f i) (f (i + 1)) ∨
    D.Arr (f (i + 1)) (f i)) :
    ∃ i, a < i ∧ i ≤ a + 2 * M ∧ D.IsTurn (f i) (f (i - 1)) (f (i + 1)) := by
  by_contra hno
  push Not at hno
  have hsame : ∀ i, a < i → i ≤ a + 2 * M →
      (D.Arr (f (i - 1)) (f i) ↔ D.Arr (f i) (f (i + 1))) := by
    intro i h1 h2
    have hi : i - 1 + 1 = i := by omega
    have hno' := hno i h1 h2
    have h3 := hadj (i - 1) (by omega) (by omega)
    have h4 := hadj i (by omega) (by omega)
    rw [hi] at h3
    constructor
    · intro h5
      rcases h4 with h4 | h4
      · exact h4
      · exact absurd (Or.inl ⟨h5, h4⟩) hno'
    · intro h5
      rcases h3 with h3 | h3
      · exact h3
      · exact absurd (Or.inr ⟨h3, h5⟩) hno'
  rcases hadj a le_rfl (by omega) with h0 | h0
  · -- all forward
    have hall : ∀ n, n ≤ 2 * M → D.Arr (f (a + n)) (f (a + n + 1)) := by
      intro n
      induction n with
      | zero => exact fun _ ↦ h0
      | succ n ih =>
        intro hn
        have h1 := (hsame (a + n + 1) (by omega) (by omega))
        have h2 : a + n + 1 - 1 = a + n := by omega
        rw [h2] at h1
        exact h1.1 (ih (by omega))
    have := run_lt hT hU hs hM (x := fun n ↦ f (a + n)) (r := 2 * M) fun i hi ↦ hall i (by omega)
    omega
  · -- all backward
    have hne : ¬D.Arr (f a) (f (a + 1)) := fun h ↦ not_arr_cycle h h0
    have hall : ∀ n, n ≤ 2 * M → D.Arr (f (a + n + 1)) (f (a + n)) := by
      intro n
      induction n with
      | zero => exact fun _ ↦ h0
      | succ n ih =>
        intro hn
        have h1 := (hsame (a + n + 1) (by omega) (by omega))
        have h2 : a + n + 1 - 1 = a + n := by omega
        rw [h2] at h1
        have h3 := hadj (a + n + 1) (by omega) (by omega)
        rcases h3 with h3 | h3
        · exact absurd (h1.2 h3) fun h ↦ not_arr_cycle h (ih (by omega))
        · exact h3
    have := run_lt hT hU hs hM (x := fun n ↦ f (a + 2 * M + 1 - n)) (r := 2 * M + 1) fun i hi ↦ by
      have h1 := hall (2 * M - i) (by omega)
      have e1 : a + (2 * M - i) + 1 = a + 2 * M + 1 - i := by omega
      have e2 : a + (2 * M - i) = a + 2 * M + 1 - (i + 1) := by omega
      rw [e1, e2] at h1
      exact h1
    omega

end Turn

section Forest

variable (hT : ∀ x, x ∈ D.T)

/-- From a side, every path out goes through the near end. -/
lemma reach_near {t p x c : D.ι} (hac : D.gr.IsAcyclic) (htp : D.gr.Adj t p)
    (hx : x ∈ D.side t p) (hc : c ∉ D.side t p) (h : Relation.ReflTransGen D.Arr x c) :
    Relation.ReflTransGen D.Arr x p := by
  induction h with
  | refl => exact absurd hx hc
  | tail hab hbc ih =>
    rename_i b c
    by_cases hb : b ∈ D.side t p
    · rcases side_adj hac htp hb (gr_adj_of_arr hbc) with h | ⟨rfl, -⟩
      · exact absurd h hc
      · exact hab
    · exact ih hb

lemma reach_far {t p x c : D.ι} (hac : D.gr.IsAcyclic) (htp : D.gr.Adj t p)
    (hx : x ∈ D.side t p) (hc : c ∉ D.side t p) (h : Relation.ReflTransGen D.Arr x c) :
    Relation.ReflTransGen D.Arr t c := by
  induction h with
  | refl => exact absurd hx hc
  | tail hab hbc ih =>
    rename_i b c
    by_cases hb : b ∈ D.side t p
    · rcases side_adj hac htp hb (gr_adj_of_arr hbc) with h | ⟨-, rfl⟩
      · exact absurd h hc
      · exact Relation.ReflTransGen.refl
    · exact (ih hb).tail hbc

lemma reach_antisymm {a b : D.ι} (h1 : Relation.ReflTransGen D.Arr a b)
    (h2 : Relation.ReflTransGen D.Arr b a) : a = b := by
  by_contra hne
  exact D.acyc _ _ (D.transGen_of_ne h1 hne) h2

/-- On a forest, nothing lies between the ends of an arrow. -/
lemma between_arr {a b i : D.ι} (hac : D.gr.IsAcyclic) (hab : D.Arr a b)
    (h1 : Relation.ReflTransGen D.Arr a i) (h2 : Relation.ReflTransGen D.Arr i b) :
    i = a ∨ i = b := by
  have hadj : D.gr.Adj b a := (gr_adj_of_arr hab).symm
  have hbs : b ∉ D.side b a := not_mem_side hac hadj
  by_cases hi : i ∈ D.side b a
  · left
    exact reach_antisymm (reach_near hac hadj hi hbs h2) h1
  · right
    exact reach_antisymm h2 (reach_far hac hadj (self_mem_side hac hadj) hi h1)

/-- **On a forest, an arrow has pairing `-1`.** -/
theorem eulerForm_c_arr (hC : ∀ x y, cartan D y x ≤ 1) (hac : D.gr.IsAcyclic) {a b : D.ι}
    (hab : D.Arr a b) : (eulerForm D hT).c a b = -1 := by
  classical
  have hne : b ≠ a := (D.ne_of_arr hab).symm
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  have h1 : (cartan D * (cartan D)⁻¹) b a = 0 := by
    rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_apply_ne hne]
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ b),
    Finset.sum_eq_single_of_mem a (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩),
    cartan_diag D (hT b), cartan_inv_diag D hT, one_mul, mul_one] at h1
  · have hCba : cartan D b a = 1 := by
      refine le_antisymm (hC a b) ?_
      obtain ⟨w, hw⟩ := D.arrNe _ _ hab
      have hmem : (⟨D.e b * w * D.e a, by
        change D.e b * w * D.e a * D.e a = _
        rw [mul_assoc, D.e_mul_e]⟩ : projE (k := k) (D.idem a)) ∈
          eSub (projE (k := k) (D.idem a)) (D.e b) := by
        apply Subtype.ext
        change D.e b * (D.e b * w * D.e a) = _
        rw [← mul_assoc, ← mul_assoc, (D.idem b).eq]
      have : Nontrivial (eSub (projE (k := k) (D.idem a)) (D.e b)) :=
        ⟨⟨⟨_, hmem⟩, 0, fun h ↦ hw (congrArg (fun z : eSub (projE (k := k) (D.idem a)) (D.e b) ↦
          ((z : projE (k := k) (D.idem a)) : A)) h)⟩⟩
      have := finrank_pos (R := k) (M := eSub (projE (k := k) (D.idem a)) (D.e b))
      change 1 ≤ ((finrank k (eSub (projE (k := k) (D.idem a)) (D.e b)) : ℕ) : ℤ)
      omega
    have h2 : (cartan D)⁻¹ a b = 0 := cartan_inv_eq_zero hT b a fun h ↦
      D.acyc _ _ (Relation.TransGen.single hab) h
    change (cartan D)⁻¹ b a + (cartan D)⁻¹ a b = -1
    rw [h2]
    rw [hCba] at h1
    omega
  · intro i hi hia
    have hib := Finset.ne_of_mem_erase hi
    by_cases hr : Relation.ReflTransGen D.Arr i b
    · by_cases hr' : Relation.ReflTransGen D.Arr a i
      · rcases between_arr hac hab hr' hr with h | h
        · exact absurd h hia
        · exact absurd h hib
      · rw [cartan_inv_eq_zero hT a i hr', mul_zero]
    · rw [cartan_eq_zero D hr, zero_mul]

end Forest

section Cross

/-- If the arrows out of `P` act by zero, so do all morphisms out of `P`. -/
lemma corner_smul_eq_zero {Y : FDMod k A} {P : Set D.ι}
    (hz : ∀ x ∈ P, ∀ c, c ∉ P → D.Arr x c → ∀ b (m : Y), (D.e c * b * D.e x) • m = 0) {y : D.ι}
    (hy : y ∉ P) : ∀ x, x ∈ P → ∀ (a : A) (m : Y), (D.e y * a * D.e x) • m = 0 := by
  intro x
  induction x using D.wf_flip.induction with
  | _ x ih =>
    intro hx a m
    have hxy : y ≠ x := fun h ↦ hy (h ▸ hx)
    refine corner_first_step (fun z ↦ z • m = 0) (by simp)
      (fun u v hu hv ↦ by rw [add_smul, hu, hv, zero_add]) hxy (fun c b r hc ↦ ?_) a
    by_cases hcP : c ∈ P
    · have h1 : (D.e y * r * (D.e c * b * D.e x)) • m =
          (D.e y * r * D.e c) • (b • (D.e x • m)) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        simp only [mul_assoc]
      rw [h1]
      exact ih c (Relation.TransGen.single hc) hcP r _
    · rw [mul_smul, hz x hx c hcP hc b m, smul_zero]

/-- **A nonzero arrow crosses every split of an indecomposable.** -/
theorem exists_cross {Y : FDMod k A} (hY : IsIndecMod A Y) (S : Set D.ι) {x₁ x₂ : D.ι} {y₁ y₂ : Y}
    (h1 : x₁ ∈ S) (h1' : D.e x₁ • y₁ ≠ 0) (h2 : x₂ ∉ S) (h2' : D.e x₂ • y₂ ≠ 0) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ ∃ (w : A) (y : Y), (D.Arr a b ∧ (D.e b * w * D.e a) • y ≠ 0) ∨
      (D.Arr b a ∧ (D.e a * w * D.e b) • y ≠ 0) := by
  classical
  by_contra hno
  push Not at hno
  have hS : ∀ y, y ∉ S → ∀ x, x ∈ S → ∀ (a : A) (m : Y), (D.e y * a * D.e x) • m = 0 :=
    fun y hy ↦ corner_smul_eq_zero (fun x hx c hc harr b m ↦ (hno x c hx hc b m).1 harr) hy
  have hS' : ∀ y, y ∈ S → ∀ x, x ∉ S → ∀ (a : A) (m : Y), (D.e y * a * D.e x) • m = 0 :=
    fun y hy ↦ corner_smul_eq_zero (P := Sᶜ) (fun x hx c hc harr b m ↦
      (hno c x (not_not.1 hc) hx b m).2 harr) (not_not.2 hy)
  have hE1 : ∀ x, x ∈ S → D.eT S * D.e x = D.e x := fun x hx ↦ by
    apply ext_e (D := D)
    intro c
    simp only [smul_eq_mul]
    by_cases hc : c ∈ S
    · rw [← mul_assoc, e_mul_eT_of_mem hc]
    · rw [← mul_assoc, e_mul_eT_of_not_mem hc, zero_mul, D.orth c x fun h ↦ hc (h ▸ hx)]
  have hE0 : ∀ x, x ∉ S → D.eT S * D.e x = 0 := fun x hx ↦ by
    apply ext_e (D := D)
    intro c
    simp only [smul_eq_mul, mul_zero]
    by_cases hc : c ∈ S
    · rw [← mul_assoc, e_mul_eT_of_mem hc, D.orth c x fun h ↦ hx (h ▸ hc)]
    · rw [← mul_assoc, e_mul_eT_of_not_mem hc, zero_mul]
  have hcorner : ∀ x y (a : A) (m : Y), D.eT S • ((D.e y * a * D.e x) • m) =
      (D.e y * a * D.e x) • (D.eT S • m) := by
    intro x y a m
    have h3 : (D.e y * a * D.e x) • (D.eT S • m) = (D.e y * a) • ((D.e x * D.eT S) • m) := by
      rw [mul_smul (D.e y * a) (D.e x), mul_smul (D.e x)]
    have h4 : D.eT S • ((D.e y * a * D.e x) • m) = (D.eT S * D.e y) • ((a * D.e x) • m) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      simp only [mul_assoc]
    by_cases hy : y ∈ S
    · by_cases hx : x ∈ S
      · rw [h3, h4, hE1 y hy, e_mul_eT_of_mem hx, ← mul_smul, ← mul_smul, mul_assoc]
      · rw [hS' y hy x hx, smul_zero, hS' y hy x hx]
    · by_cases hx : x ∈ S
      · rw [hS y hy x hx, smul_zero, hS y hy x hx]
      · rw [h3, h4, hE0 y hy, e_mul_eT_of_not_mem hx, zero_smul, zero_smul, smul_zero]
  have hdec : ∀ b : A, b = ∑ y, ∑ x, D.e y * b * D.e x := fun b ↦ by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, D.sum, one_mul, mul_one]
  let ε : Y →ₗ[A] Y :=
    { toFun := fun m ↦ D.eT S • m
      map_add' := smul_add _
      map_smul' := fun a m ↦ by
        change D.eT S • (a • m) = a • (D.eT S • m)
        conv_lhs => rw [hdec a]
        conv_rhs => rw [hdec a]
        simp only [Finset.sum_smul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ hcorner x y a m }
  have hε : ∀ m, ε (ε m) = ε m := fun m ↦ by
    change D.eT S • (D.eT S • m) = D.eT S • m
    rw [← mul_smul, eT_idem]
  have hcompl : IsCompl (LinearMap.range ε) (LinearMap.ker ε) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro m ⟨⟨n, rfl⟩, hm⟩
      have h3 : ε (ε n) = 0 := hm
      rw [hε] at h3
      rw [h3]
      exact Submodule.zero_mem _
    · rw [codisjoint_iff, eq_top_iff]
      intro m _
      have hm : m = ε m + (m - ε m) := by abel
      rw [hm]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨m, rfl⟩) (Submodule.mem_sup_right ?_)
      change ε (m - ε m) = 0
      rw [map_sub, hε, sub_self]
  rcases hY _ _ hcompl with h | h
  · have h3 : ε (D.e x₁ • y₁) ∈ LinearMap.range ε := ⟨_, rfl⟩
    rw [h] at h3
    have h4 : D.eT S • (D.e x₁ • y₁) = 0 := (Submodule.mem_bot A).1 h3
    rw [← mul_smul, hE1 x₁ h1] at h4
    exact h1' h4
  · have h3 : D.e x₂ • y₂ ∈ LinearMap.ker ε := by
      change D.eT S • (D.e x₂ • y₂) = 0
      rw [← mul_smul, hE0 x₂ h2, zero_smul]
    rw [h] at h3
    exact h2' ((Submodule.mem_bot A).1 h3)

end Cross

/-- **The support of an indecomposable on a forest is convex.** -/
theorem isConvexSet_supp (hac : D.gr.IsAcyclic) {Y : FDMod k A} (hY : IsIndecMod A Y) :
    D.IsConvexSet (D.Supp Y) := by
  intro x z c hx hz h1 h2
  by_contra hc
  have hxc : x ≠ c := fun h ↦ hc (h ▸ hx)
  have hcz : c ≠ z := fun h ↦ hc (h ▸ hz)
  -- the last step into `c` and the first step out of `c`
  obtain ⟨p, hp1, hp2⟩ : ∃ p, Relation.ReflTransGen D.Arr x p ∧ D.Arr p c := by
    rcases Relation.ReflTransGen.cases_tail h1 with h | ⟨p, h3, h4⟩
    · exact absurd h.symm hxc
    · exact ⟨p, h3, h4⟩
  obtain ⟨p', hp3, hp4⟩ : ∃ p', D.Arr c p' ∧ Relation.ReflTransGen D.Arr p' z := by
    rcases Relation.ReflTransGen.cases_head h2 with h | ⟨p', h3, h4⟩
    · exact absurd h hcz
    · exact ⟨p', h3, h4⟩
  have hadj1 : D.gr.Adj c p := (gr_adj_of_arr hp2).symm
  have hadj2 : D.gr.Adj c p' := gr_adj_of_arr hp3
  have hne : p ≠ p' := by
    rintro rfl
    exact not_arr_cycle hp2 hp3
  have hxs : x ∈ D.side c p := by
    by_contra hn
    exact not_arr_cycle (enter_side hac hadj1 (self_mem_side hac hadj1) hn hp1) hp2
  have hzs : z ∈ D.side c p' := by
    by_contra hn
    exact not_arr_cycle (exit_side hac hadj2 (self_mem_side hac hadj2) hn hp4) hp3
  have hzn : z ∉ D.side c p := fun h ↦ side_disjoint hac hadj1 hadj2 hne h hzs
  obtain ⟨u₁, hu₁⟩ := hx
  obtain ⟨u₂, hu₂⟩ := hz
  obtain ⟨a, b, ha, hb, w, y, hcase⟩ := exists_cross hY (D.side c p) hxs hu₁ hzn hu₂
  have hadj : D.gr.Adj a b := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact gr_adj_of_arr h
    · exact (gr_adj_of_arr h).symm
  rcases side_adj hac hadj1 ha hadj with h | ⟨-, rfl⟩
  · exact hb h
  · apply hc
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩
    · refine ⟨(w * D.e a) • y, fun h0 ↦ h ?_⟩
      rw [mul_assoc, mul_smul, h0]
    · refine ⟨y, fun h0 ↦ h ?_⟩
      rw [mul_smul, h0, smul_zero]

/-- A nonzero dimension gives a nonzero element. -/
lemma exists_smul_ne_of_dimZ {Y : FDMod k A} {c : D.ι} (hc : dimZ D Y c ≠ 0) :
    ∃ y : Y, D.e c • y ≠ 0 := by
  by_contra h
  push Not at h
  apply hc
  have h0 : eSub Y (D.e c) = ⊥ := eq_bot_iff.2 fun m hm ↦ (Submodule.mem_bot k).2 (by
    have h1 : D.e c • m = m := hm
    rw [← h1, h])
  change ((finrank k (eSub Y (D.e c)) : ℕ) : ℤ) = 0
  rw [h0, finrank_bot]
  rfl

/-- The graph of a module is connected on its support. -/
theorem reachable_of_sincere {Y : FDMod k A} (hY : IsIndecMod A Y)
    (hs : ∀ x, ∃ y : Y, D.e x • y ≠ 0) (a b : D.ι) : D.gr.Reachable a b := by
  by_contra hn
  let R : Set D.ι := {c | D.gr.Reachable a c}
  obtain ⟨ya, hya⟩ := hs a
  obtain ⟨yb, hyb⟩ := hs b
  obtain ⟨u, v, hu, hv, w, y, hcase⟩ := exists_cross hY R (Reachable.refl a) hya hn hyb
  apply hv
  rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
  · exact Reachable.trans hu (gr_adj_of_arr h).reachable
  · exact Reachable.trans hu (gr_adj_of_arr h).symm.reachable

section Line

variable [IsAlgClosed k] {U : FDMod k A} (hT : ∀ x, x ∈ D.T) (hC : ∀ x y, cartan D y x ≤ 1)
  (hDir : ∀ N : FDMod k A, IndNT N → Directing N) (hU : Directing U) (hs : Sincere D U)
  (hac : D.gr.IsAcyclic) {M : ℕ} (hM : RunB D M)
include hT hC hDir hU hs hac hM

/-- **A long path in a forest gives a clean line.** -/
theorem exists_line_of_path {f : ℕ → D.ι} {ℓ N : ℕ} (hN : 2 * ℓ + 2 * M + 1 ≤ N)
    (hadj : ∀ i < N, D.gr.Adj (f i) (f (i + 1)))
    (hinj : ∀ i j, i ≤ N → j ≤ N → f i = f j → i = j) :
    ∃ (Y : FDMod k A) (n : ℕ) (g : ℕ → D.ι), IndNT Y ∧ ℓ ≤ n ∧
      (∀ i j, i ≤ n → j ≤ n → g i = g j → i = j) ∧
      (∀ i ≤ n, dimZ D Y (g i) = 1) ∧ (∀ c, (∀ i ≤ n, g i ≠ c) → dimZ D Y c = 0) ∧
      ∀ i < n, ∃ (w : A) (y : Y), (D.Arr (g i) (g (i + 1)) ∧
          (D.e (g (i + 1)) * w * D.e (g i)) • y ≠ 0) ∨
        (D.Arr (g (i + 1)) (g i) ∧ (D.e (g i) * w * D.e (g (i + 1))) • y ≠ 0) := by
  have harr : ∀ i < N, D.Arr (f i) (f (i + 1)) ∨ D.Arr (f (i + 1)) (f i) := fun i hi ↦
    (gr_adj.1 (hadj i hi)).2
  obtain ⟨i, hi1, hi2, hturn⟩ := exists_turn hT hU hs hM (f := f) ℓ fun i _ h2 ↦ harr i (by omega)
  have hi0 : i - 1 + 1 = i := by omega
  have hadj1 : D.gr.Adj (f i) (f (i - 1)) := by
    have := hadj (i - 1) (by omega)
    rw [hi0] at this
    exact this.symm
  have hadj2 : D.gr.Adj (f i) (f (i + 1)) := hadj i (by omega)
  have hne : f (i - 1) ≠ f (i + 1) := fun h ↦ by
    have := hinj _ _ (by omega) (by omega) h
    omega
  have hseq1 : ∀ j < i, D.gr.Adj (f (i - j)) (f (i - (j + 1))) := fun j hj ↦ by
    have h1 := hadj (i - j - 1) (by omega)
    have e1 : i - j - 1 + 1 = i - j := by omega
    rw [e1] at h1
    have e2 : i - (j + 1) = i - j - 1 := by omega
    rw [e2]
    exact h1.symm
  have hinj1 : ∀ a b, a ≤ i → b ≤ i → f (i - a) = f (i - b) → a = b := fun a b ha hb hab ↦ by
    have := hinj _ _ (by omega) (by omega) hab
    omega
  have hseq2 : ∀ j < N - i, D.gr.Adj (f (i + j)) (f (i + (j + 1))) := fun j hj ↦
    hadj (i + j) (by omega)
  have hinj2 : ∀ a b, a ≤ N - i → b ≤ N - i → f (i + a) = f (i + b) → a = b := fun a b ha hb hab ↦ by
    have := hinj _ _ (by omega) (by omega) hab
    omega
  have hv1 : f 0 ∈ D.side (f i) (f (i - 1)) := by
    have := seq_mem_side hac (fun j ↦ f (i - j)) i hseq1 hinj1 i (by omega) le_rfl
    simpa using this
  have hv2 : f N ∈ D.side (f i) (f (i + 1)) := by
    have := seq_mem_side hac (fun j ↦ f (i + j)) (N - i) hseq2 hinj2 (N - i) (by omega) le_rfl
    have e1 : i + (N - i) = N := by omega
    simpa [e1] using this
  have ht1 := mem_bdry_insert hac hadj1 hadj2 hne (gr_adj.1 hadj2).2
  have ht2 := mem_bdry_insert hac hadj2 hadj1 hne.symm (gr_adj.1 hadj1).2
  obtain ⟨Y, hY, hline, hcase⟩ := line_of_cut hT hDir hU hs (isConvexSet_insert_side hac hadj1)
    (isConvexSet_insert_side hac hadj2) (bdry_insert_side hac hadj1) (bdry_insert_side hac hadj2)
    ht1 ht2 (Or.inr hv1) (Or.inr hv2) (by
      rintro a (rfl | ha) b (rfl | hb) h1 h2
      · exact absurd rfl h1
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact side_orth hac hadj1 hadj2 hne hturn ha hb)
  obtain ⟨n, g, hg0, hginj, hgc1, hgc0, hgz1, hgz0⟩ := hline.exists_seq
  have hnz : ∀ {c : D.ι}, dimZ D Y c ≠ 0 → ∃ y : Y, D.e c • y ≠ 0 := fun {c} hc ↦ by
    by_contra h
    push Not at h
    apply hc
    have h0 : eSub Y (D.e c) = ⊥ := eq_bot_iff.2 fun m hm ↦ (Submodule.mem_bot k).2 (by
      have h1 : D.e c • m = m := hm
      rw [← h1, h])
    change ((finrank k (eSub Y (D.e c)) : ℕ) : ℤ) = 0
    rw [h0, finrank_bot]
    rfl
  have hmem : ∀ {c : D.ι}, dimZ D Y c ≠ 0 → ∃ m ≤ n, g m = c := fun {c} hc ↦ by
    by_contra h
    push Not at h
    exact hc (hgz0 c h)
  have hstep : ∀ i' < n, ∃ (w : A) (y : Y), (D.Arr (g i') (g (i' + 1)) ∧
      (D.e (g (i' + 1)) * w * D.e (g i')) • y ≠ 0) ∨
      (D.Arr (g (i' + 1)) (g i') ∧ (D.e (g i') * w * D.e (g (i' + 1))) • y ≠ 0) := by
    intro i' hi'
    let S : Set D.ι := {c | ∃ j ≤ i', g j = c}
    have h1 : dimZ D Y (g i') ≠ 0 := by rw [hgz1 i' (by omega)]; norm_num
    have h2 : dimZ D Y (g (i' + 1)) ≠ 0 := by rw [hgz1 _ (by omega)]; norm_num
    obtain ⟨y₁, hy₁⟩ := hnz h1
    obtain ⟨y₂, hy₂⟩ := hnz h2
    have hnot : g (i' + 1) ∉ S := by
      rintro ⟨j, hj, hjg⟩
      have := hginj j (i' + 1) (by omega) (by omega) hjg
      omega
    obtain ⟨a, b, ⟨j, hj, rfl⟩, hbS, w, y, hc⟩ :=
      exists_cross hY.1 S ⟨i', le_rfl, rfl⟩ hy₁ hnot hy₂
    have hbz : dimZ D Y b ≠ 0 := by
      rcases hc with ⟨-, h3⟩ | ⟨-, h3⟩
      · have h4 : (D.e b * w * D.e (g j)) • y = D.e b • ((w * D.e (g j)) • y) := by
          rw [← mul_smul, mul_assoc]
        rw [h4] at h3
        exact dimZ_ne_zero h3
      · have h4 : (D.e (g j) * w * D.e b) • y = (D.e (g j) * w) • (D.e b • y) := by
          rw [← mul_smul]
        have h5 : D.e b • y ≠ 0 := fun h0 ↦ h3 (by rw [h4, h0, smul_zero])
        exact dimZ_ne_zero h5
    obtain ⟨l, hl, rfl⟩ := hmem hbz
    have hli : i' < l := by
      by_contra h
      exact hbS ⟨l, by omega, rfl⟩
    have hcv : (eulerForm D hT).c (g j) (g l) = -1 := by
      rcases hc with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact eulerForm_c_arr hT hC hac h3
      · rw [(eulerForm D hT).symm]
        exact eulerForm_c_arr hT hC hac h3
    have hjl : ¬j + 1 < l := fun h ↦ by
      rw [hgc0 j l h hl] at hcv
      norm_num at hcv
    obtain rfl : j = i' := by omega
    obtain rfl : l = j + 1 := by omega
    exact ⟨w, y, hc⟩
  have hgadj : ∀ i' < n, D.gr.Adj (g i') (g (i' + 1)) := fun i' hi' ↦ by
    obtain ⟨w, y, h | h⟩ := hstep i' hi'
    · exact gr_adj_of_arr h.1
    · exact (gr_adj_of_arr h.1).symm
  refine ⟨Y, n, g, hY, ?_, hginj, hgz1, hgz0, hstep⟩
  rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
  · obtain ⟨m, hm, hmg⟩ := hmem h1
    have := seq_unique hac (fun j ↦ g j) (fun j ↦ f (i - j)) (r := m) (r' := i)
      (by simpa using hmg) (by simpa using hg0) (fun j hj ↦ hgadj j (by omega)) hseq1
      (fun a b ha hb hab ↦ hginj a b (by omega) (by omega) hab) hinj1
    omega
  · obtain ⟨m, hm, hmg⟩ := hmem h1
    have e1 : i + (N - i) = N := by omega
    have := seq_unique hac (fun j ↦ g j) (fun j ↦ f (i + j)) (r := m) (r' := N - i)
      (by simpa [e1] using hmg) (by simpa using hg0) (fun j hj ↦ hgadj j (by omega)) hseq2
      (fun a b ha hb hab ↦ hginj a b (by omega) (by omega) hab) hinj2
    omega

end Line

end DirData

end LargeIndecomposable.AR
