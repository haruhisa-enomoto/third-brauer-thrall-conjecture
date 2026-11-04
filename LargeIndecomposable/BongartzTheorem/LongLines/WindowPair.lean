module

public import LargeIndecomposable.BongartzTheorem.LongLines.CoverLine
public import LargeIndecomposable.RayCategories.Linearization.RegularRepresentation

/-!
# A good pair in every window of `3 dim k(P)` arrows

Let `d` be the number of nonzero morphisms of `P`, the dimension of `k(P)`. Every point of a
window `pt 0, …, pt N` of a line has a nonzero morphism to a sink of the window
(`WLine.WSink`), unless it lies on the initial backward run (`cover_or_run`). Points with the
same sink are told apart by the value of this morphism, and the points of the initial run by
the value of their morphism to `pt 0`. If no good pair lies in the window, at most two sinks of
the window have the same image in `P` (`goodPair_of_three`), so `N + 1 ≤ 2d + d`. Hence a
window of `3d` arrows contains a good pair (`exists_goodPair_window`; BO13b, Lemma 7.2 (b),
with the count of BO23, proof of Theorem 7).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

namespace WLine

variable (L : WLine x₀)

/-- A sink of the window `pt 0, …, pt N` at the point `pt s`: the arrow on its left points
to it, and so does the arrow on its right unless `s = N`. -/
def WSink (N s : ℕ) : Prop := 1 ≤ s ∧ s ≤ N ∧ L.fwd (s - 1) = true ∧ (s = N ∨ L.fwd s = false)

/-- Every point of a window has a nonzero morphism to a sink of the window, or lies on the
initial backward run. -/
lemma cover_or_run {N : ℕ} (hN : N ≤ L.n) (a : ℕ) (ha : a ≤ N) :
    (∃ s, L.WSink N s ∧ ∃ f : L.pt a ⟶ L.pt s, f ≠ 0) ∨ ∀ i < a, L.fwd i = false := by
  classical
  have hex : ∃ j, a ≤ j ∧ (j = N ∨ L.fwd j = false) := ⟨N, ha, Or.inl rfl⟩
  have hj : a ≤ Nat.find hex ∧ (Nat.find hex = N ∨ L.fwd (Nat.find hex) = false) :=
    Nat.find_spec hex
  have hjN : Nat.find hex ≤ N := Nat.find_min' hex ⟨ha, Or.inl rfl⟩
  have hfw : ∀ i, a ≤ i → i < Nat.find hex → L.fwd i = true := fun i h1 h2 ↦ by
    have := Nat.find_min hex h2
    by_contra hc
    exact this ⟨h1, Or.inr (by simpa using hc)⟩
  rcases Nat.eq_or_lt_of_le hj.1 with hja | hja
  · -- `pt a` has no arrow to its right: walk to the left
    let Q : ℕ → Prop := fun i ↦ i = 0 ∨ L.fwd (i - 1) = true
    have hi : Q (Nat.findGreatest Q a) := Nat.findGreatest_spec (Nat.zero_le a) (Or.inl rfl)
    have hia : Nat.findGreatest Q a ≤ a := Nat.findGreatest_le a
    have hbw : ∀ m, Nat.findGreatest Q a ≤ m → m < a → L.fwd m = false := fun m h1 h2 ↦ by
      have := Nat.findGreatest_is_greatest (P := Q) (show Nat.findGreatest Q a < m + 1 by omega)
        (by omega)
      simp only [Q, not_or, Nat.add_sub_cancel] at this
      simpa using this.2
    rcases Nat.eq_zero_or_pos (Nat.findGreatest Q a) with h0 | h0
    · right
      intro i hi'
      exact hbw i (by omega) hi'
    · left
      set s := Nat.findGreatest Q a
      have hs1 : L.fwd (s - 1) = true := hi.resolve_left (by omega)
      refine ⟨s, ⟨h0, by omega, hs1, ?_⟩, L.nzB s a hia (by omega) fun i h1 h2 ↦ hbw i h1 h2⟩
      rcases Nat.eq_or_lt_of_le hia with h | h
      · rw [h, hja]; exact hj.2
      · exact Or.inr (hbw s le_rfl h)
  · left
    refine ⟨Nat.find hex, ⟨by omega, hjN, hfw _ (by omega) (by omega), hj.2⟩,
      L.nzF a _ hj.1 (by omega) hfw⟩

/-- Three sinks of a window with the same image give a good pair in the window. -/
lemma goodPair_of_three_wsink {N : ℕ} (hN : N ≤ L.n) {s₁ s₂ s₃ : ℕ} (h₁ : L.WSink N s₁)
    (h₂ : L.WSink N s₂) (h₃ : L.WSink N s₃) (h12 : s₁ < s₂) (h23 : s₂ < s₃)
    (hy₁ : (L.pt s₁).y = (L.pt s₂).y) (hy₂ : (L.pt s₂).y = (L.pt s₃).y) :
    ∃ t t', L.GoodPair t t' ∧ t' < N := by
  have e1 : s₁ - 1 + 1 = s₁ := by have := h₁.1; omega
  have e2 : s₂ - 1 + 1 = s₂ := by have := h₂.1; omega
  have e3 : s₃ - 1 + 1 = s₃ := by have := h₃.1; omega
  have r1 : L.IsRSink (s₁ - 1) := by
    refine ⟨by have := h₁.1; have := h₃.2.1; omega, ?_⟩
    rw [e1]; exact h₁.2.2.2.resolve_left (by have := h₃.2.1; omega)
  have m2 : L.IsSinkAt (s₂ - 1) := by
    refine ⟨by have := h₂.1; have := h₃.2.1; omega, h₂.2.2.1, ?_⟩
    rw [e2]; exact h₂.2.2.2.resolve_left (by have := h₃.2.1; omega)
  have l3 : L.IsLSink (s₃ - 1) := ⟨by have := h₃.2.1; omega, h₃.2.2.1⟩
  obtain ⟨t, t', h, -, ht'⟩ := L.goodPair_of_three r1 m2 l3 (by omega) (by omega)
    (by rw [e1, e2]; exact hy₁) (by rw [e2, e3]; exact hy₂)
  exact ⟨t, t', h, by have := h₃.2.1; omega⟩

/-- Two points with nonzero morphisms of the same value to the same point of the line are
equal. -/
lemma eq_of_sink_val {a a' s s' : ℕ} (ha : a ≤ L.n) (ha' : a' ≤ L.n) (f : L.pt a ⟶ L.pt s)
    (f' : L.pt a' ⟶ L.pt s') (hf : f ≠ 0) (hf' : f' ≠ 0) (hss : s = s')
    (hx : (L.pt a).y = (L.pt a').y)
    (h : HEq (⟨(L.pt s).y, val f⟩ : Σ y : P, ((L.pt a).y ⟶ y))
      (⟨(L.pt s').y, val f'⟩ : Σ y : P, ((L.pt a').y ⟶ y))) : a = a' := by
  subst hss
  have hv := sigma_heq_snd hx h
  exact L.inj _ _ ha ha' (src_eq_of_val hf hf' hx hv)

/-- **A window of `3 d` arrows contains a good pair**, where `d` is the number of nonzero
morphisms of `P`. -/
theorem exists_goodPair_window [Finite P] [∀ x y : P, Finite (x ⟶ y)] {N : ℕ} (hN : N ≤ L.n)
    (h3 : 3 * Nat.card {μ : Σ x y : P, (x ⟶ y) // μ.2.2 ≠ 0} ≤ N) :
    ∃ t t', L.GoodPair t t' ∧ t' < N := by
  classical
  by_contra hno
  have : Fintype (Σ x y : P, (x ⟶ y)) := Fintype.ofFinite _
  let T : Finset (Σ x y : P, (x ⟶ y)) := Finset.univ.filter fun μ ↦ μ.2.2 ≠ 0
  have hT : T.card = Nat.card {μ : Σ x y : P, (x ⟶ y) // μ.2.2 ≠ 0} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- at most two sinks of the window over each point of `P`
  have two : ∀ (y : P) (S : Finset ℕ), (∀ s ∈ S, L.WSink N s ∧ (L.pt s).y = y) → S.card ≤ 2 := by
    intro y S hS
    by_contra hc
    push Not at hc
    obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.1 hc
    have key : ∀ i j l, i ∈ S → j ∈ S → l ∈ S → i < j → j < l → False := by
      intro i j l hi hj hl hij hjl
      exact hno (L.goodPair_of_three_wsink hN (hS i hi).1 (hS j hj).1 (hS l hl).1 hij hjl
        ((hS i hi).2.trans (hS j hj).2.symm) ((hS j hj).2.trans (hS l hl).2.symm))
    rcases lt_trichotomy a b with h1 | h1 | h1 <;> rcases lt_trichotomy b c with h2 | h2 | h2 <;>
      rcases lt_trichotomy a c with h4 | h4 | h4 <;> first
      | exact absurd h1 hab | exact absurd h2 hbc | exact absurd h4 hac
      | exact key a b c ha hb hc' h1 h2 | exact key a c b ha hc' hb h4 h2
      | exact key b a c hb ha hc' h1 h4 | exact key b c a hb hc' ha h2 h4
      | exact key c a b hc' ha hb h4 h1 | exact key c b a hc' hb ha h2 h1
  let C : ℕ → Prop := fun a ↦ ∃ s, L.WSink N s ∧ ∃ f : L.pt a ⟶ L.pt s, f ≠ 0
  let W := Finset.range (N + 1)
  let Cov := W.filter C
  let Run := W.filter fun a ↦ ∀ i < a, L.fwd i = false
  have hW : W ⊆ Cov ∪ Run := fun a ha ↦ by
    have ha' : a ≤ N := by simpa [W, Nat.lt_succ_iff] using ha
    rcases L.cover_or_run hN a ha' with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ha, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ha, h⟩)
  -- the initial run injects into the nonzero morphisms to `pt 0`
  have hRun : Run.card ≤ T.card := by
    have hf : ∀ a ∈ Run, ∃ f : L.pt a ⟶ L.pt 0, f ≠ 0 := fun a ha ↦ by
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      exact L.nzB 0 a (Nat.zero_le a) (by simp [W] at ha1; omega) fun i _ h2 ↦ ha2 i h2
    let g : ℕ → Σ x y : P, (x ⟶ y) := fun a ↦
      if h : ∃ f : L.pt a ⟶ L.pt 0, f ≠ 0 then ⟨(L.pt a).y, (L.pt 0).y, val h.choose⟩
      else ⟨x₀, x₀, 0⟩
    refine Finset.card_le_card_of_injOn g (fun a ha ↦ ?_) (fun a ha a' ha' he ↦ ?_)
    · have h := hf a ha
      simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, g, dif_pos h]
      exact fun h0 ↦ h.choose_spec ((val_eq_zero_iff _).1 h0)
    · have h := hf a ha
      have h' := hf a' ha'
      simp only [g, dif_pos h, dif_pos h'] at he
      obtain ⟨hx, h2⟩ := Sigma.mk.inj he
      have hv := sigma_heq_snd hx h2
      have := src_eq_of_val h.choose_spec h'.choose_spec hx hv
      have hle : a ≤ N := by simpa [W, Nat.lt_succ_iff] using (Finset.mem_filter.1 ha).1
      have hle' : a' ≤ N := by simpa [W, Nat.lt_succ_iff] using (Finset.mem_filter.1 ha').1
      exact L.inj _ _ (by omega) (by omega) this
  -- covered points map at most two-to-one to the nonzero morphisms
  have hCov : Cov.card ≤ 2 * T.card := by
    let sOf : ℕ → ℕ := fun a ↦ if h : C a then h.choose else 0
    have hsOf : ∀ a, (h : C a) → sOf a = h.choose := fun a h ↦ dif_pos h
    let g : ℕ → Σ x y : P, (x ⟶ y) := fun a ↦
      if h : C a then ⟨(L.pt a).y, (L.pt h.choose).y, val h.choose_spec.2.choose⟩
      else ⟨x₀, x₀, 0⟩
    refine Finset.card_le_mul_card_image_of_maps_to (f := g) (fun a ha ↦ ?_) 2 fun μ _ ↦ ?_
    · have h : C a := (Finset.mem_filter.1 ha).2
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, g, dif_pos h]
      exact fun h0 ↦ h.choose_spec.2.choose_spec ((val_eq_zero_iff _).1 h0)
    · set F := Cov.filter fun a ↦ g a = μ
      have hinj : Set.InjOn sOf F := fun a ha a' ha' he ↦ by
        obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
        obtain ⟨ha1', ha2'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ha')
        have h : C a := (Finset.mem_filter.1 ha1).2
        have h' : C a' := (Finset.mem_filter.1 ha1').2
        rw [hsOf a h, hsOf a' h'] at he
        have he2 : g a = g a' := ha2.trans ha2'.symm
        simp only [g, dif_pos h, dif_pos h'] at he2
        obtain ⟨hx, h2⟩ := Sigma.mk.inj he2
        have hle : a ≤ N := by simpa [W, Nat.lt_succ_iff] using (Finset.mem_filter.1 ha1).1
        have hle' : a' ≤ N := by simpa [W, Nat.lt_succ_iff] using (Finset.mem_filter.1 ha1').1
        exact L.eq_of_sink_val (by omega) (by omega) _ _ h.choose_spec.2.choose_spec
          h'.choose_spec.2.choose_spec he hx h2
      have hsub : F.image sOf ⊆ (Finset.range (N + 1)).filter
          fun s ↦ L.WSink N s ∧ (L.pt s).y = μ.2.1 := fun s hs ↦ by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hs
        obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
        have h : C a := (Finset.mem_filter.1 ha1).2
        rw [hsOf a h]
        have hw := h.choose_spec.1
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hw.2.1; omega), hw, ?_⟩
        rw [← ha2]
        change _ = (dite (C a) _ _ : Σ x y : P, (x ⟶ y)).2.1
        rw [dif_pos h]
      rw [← Finset.card_image_of_injOn hinj]
      exact (Finset.card_le_card hsub).trans
        (two μ.2.1 _ fun s hs ↦ (Finset.mem_filter.1 hs).2)
  have hcard : N + 1 ≤ Cov.card + Run.card := by
    have := Finset.card_le_card hW
    rw [Finset.card_range] at this
    exact this.trans (Finset.card_union_le _ _)
  omega

end WLine

end LargeIndecomposable.RayCat
