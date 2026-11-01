module

public import LargeIndecomposable.RayCategories.Basic.Basic
public import Mathlib

/-!
# Balls and connected sets in a ray category

Two objects are adjacent when there is a nonzero morphism between them (`Adj`). Balls
for this relation are finite (`ball_finite`). A finite set `S` is connected when every
set closed under adjacency into `S` contains all of `S` or none of it (`IsConnSet`).
A connected set with `n` elements through `a` lies in the ball of radius `n` around `a`
(`subset_ball`), so there are finitely many such sets (`finite_connSets`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

variable {Q : Type u} [Category.{v} Q] [HasZeroMorphisms Q] [IsRayCategory Q]

/-- Adjacency: a nonzero morphism in either direction. -/
def Adj (a b : Q) : Prop := (∃ f : a ⟶ b, f ≠ 0) ∨ (∃ f : b ⟶ a, f ≠ 0)

lemma adj_finite (a : Q) : {b | Adj a b}.Finite :=
  (IsRayCategory.finite_out a).union (IsRayCategory.finite_in a)

/-- Balls for adjacency. -/
def ball (a : Q) : ℕ → Set Q
  | 0 => {a}
  | r + 1 => ball a r ∪ ⋃ b ∈ ball a r, {c | Adj b c}

lemma ball_finite (a : Q) : ∀ r, (ball a r).Finite
  | 0 => Set.finite_singleton a
  | r + 1 => (ball_finite a r).union ((ball_finite a r).biUnion fun b _ ↦ adj_finite b)

lemma ball_mono (a : Q) {r s : ℕ} (h : r ≤ s) : ball a r ⊆ ball a s := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Set.subset_union_left

lemma mem_ball_succ {a b c : Q} {r : ℕ} (hb : b ∈ ball a r) (hbc : Adj b c) :
    c ∈ ball a (r + 1) :=
  Or.inr (Set.mem_biUnion hb hbc)

/-- Connected finite sets. -/
def IsConnSet (S : Finset Q) : Prop :=
  ∀ T : Set Q, (∀ a b, a ∈ T → b ∈ S → Adj a b → b ∈ T) →
    (∀ a ∈ S, a ∈ T) ∨ (∀ a ∈ S, a ∉ T)

/-- **A connected set through `a` lies in the ball of radius its size.** -/
theorem subset_ball {S : Finset Q} (hS : IsConnSet S) {a : Q} (ha : a ∈ S) :
    ∀ b ∈ S, b ∈ ball a S.card := by
  classical
  let c : ℕ → ℕ := fun r ↦ (S.filter (· ∈ ball a r)).card
  have hstep : ∀ r, (∀ b ∈ S, b ∈ ball a r) ∨ c r < c (r + 1) := by
    intro r
    by_cases hstab : c (r + 1) = c r
    · left
      have hsub : S.filter (· ∈ ball a r) ⊆ S.filter (· ∈ ball a (r + 1)) := fun b hb ↦
        Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hb).1,
          ball_mono a (Nat.le_succ r) (Finset.mem_filter.1 hb).2⟩
      have heq := Finset.eq_of_subset_of_card_le hsub hstab.le
      rcases hS (ball a r) (fun b d hb hd hbd ↦ by
          have : d ∈ S.filter (· ∈ ball a (r + 1)) :=
            Finset.mem_filter.2 ⟨hd, mem_ball_succ hb hbd⟩
          rw [← heq] at this
          exact (Finset.mem_filter.1 this).2) with h | h
      · exact h
      · exact absurd (ball_mono a (Nat.zero_le r) (Set.mem_singleton a)) (h a ha)
    · right
      have hsub : S.filter (· ∈ ball a r) ⊆ S.filter (· ∈ ball a (r + 1)) := fun b hb ↦
        Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hb).1,
          ball_mono a (Nat.le_succ r) (Finset.mem_filter.1 hb).2⟩
      exact lt_of_le_of_ne (Finset.card_le_card hsub) (Ne.symm hstab)
  have hc0 : 1 ≤ c 0 := Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩
  have hcle : ∀ r, c r ≤ S.card := fun r ↦ Finset.card_filter_le _ _
  -- iterate
  have key : ∀ r, (∀ b ∈ S, b ∈ ball a r) ∨ r + 1 ≤ c r := by
    intro r
    induction r with
    | zero => exact Or.inr hc0
    | succ r ih =>
      rcases ih with h | h
      · exact Or.inl fun b hb ↦ ball_mono a (Nat.le_succ r) (h b hb)
      · rcases hstep r with h' | h'
        · exact Or.inl fun b hb ↦ ball_mono a (Nat.le_succ r) (h' b hb)
        · exact Or.inr (by omega)
  rcases key S.card with h | h
  · exact h
  · have := hcle S.card; omega

/-- **Finitely many connected sets of bounded size through a point.** -/
theorem finite_connSets (a : Q) (n : ℕ) :
    {S : Finset Q | a ∈ S ∧ S.card ≤ n ∧ IsConnSet S}.Finite := by
  classical
  have hfin := (ball_finite a n).toFinset
  refine (Finset.finite_toSet ((ball_finite a n).toFinset.powerset)).subset ?_
  rintro S ⟨ha, hn, hc⟩
  rw [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff]
  intro b hb
  rw [Set.Finite.coe_toFinset]
  exact ball_mono a hn (subset_ball hc ha b hb)

end LargeIndecomposable
