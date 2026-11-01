module

public import LargeIndecomposable.AuslanderReiten.Irreducible.IrrTransfer

/-!
# Induction over a preprojective component

Members of a preprojective component have predecessor chains of bounded length (pigeonhole with
no cycles, `PreprojComp.length_le`), which gives induction over proper predecessors
(`PreprojComp.induction`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- A predecessor chain. -/
lemma PredN.chain {X : FDMod k A} : ∀ {n : ℕ} {Y : FDMod k A}, PredN X n Y →
    ∃ c : ℕ → FDMod k A, c 0 = X ∧ c n = Y ∧ ∀ i j, i ≤ j → j ≤ n → PredN (c i) (j - i) (c j) := by
  intro n Y h
  induction h with
  | zero hU =>
    exact ⟨fun _ ↦ X, rfl, rfl, fun i j hij hj ↦ by
      obtain rfl : i = 0 := by omega
      obtain rfl : j = 0 := by omega
      exact PredN.zero hU⟩
  | step h hX i ih =>
    rename_i n W
    obtain ⟨c, h0, hn, hc⟩ := ih
    refine ⟨fun j ↦ if j ≤ n then c j else (chosenMin W hX).d.obj i, by simp [h0], by simp, ?_⟩
    intro a b hab hb
    by_cases hb' : b ≤ n
    · simp only [show a ≤ n by omega, hb', if_true]
      exact hc a b hab hb'
    · obtain rfl : b = n + 1 := by omega
      simp only [show ¬n + 1 ≤ n by omega, if_false]
      by_cases ha : a ≤ n
      · simp only [ha, if_true]
        have := hc a n ha le_rfl
        rw [hn] at this
        rw [show n + 1 - a = (n - a) + 1 by omega]
        exact PredN.step this hX i
      · obtain rfl : a = n + 1 := by omega
        simp only [show ¬n + 1 ≤ n by omega, if_false, Nat.sub_self]
        exact PredN.zero ⟨(chosenMin W hX).d.indec i, (chosenMin W hX).d.nt i⟩

namespace PreprojComp

variable {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞)
include h𝒞

lemma mem_of_predN {X : FDMod k A} (hX : 𝒞 X) : ∀ {n : ℕ} {Y : FDMod k A}, PredN X n Y → 𝒞 Y := by
  intro n Y h
  induction h with
  | zero _ => exact hX
  | step _ hW i ih =>
    exact h𝒞.pred _ _ ih ⟨(chosenMin _ hW).d.indec i, (chosenMin _ hW).d.nt i⟩ _
      (isIrr_summand (chosenMin _ hW).hg (chosenMin _ hW).hmin hW (chosenMin _ hW).d i)

/-- **Predecessor chains have bounded length.** -/
theorem length_le {X : FDMod k A} (hX : 𝒞 X) : ∃ N, ∀ n Y, PredN X n Y → n ≤ N := by
  classical
  obtain ⟨L, hL⟩ := h𝒞.finIso X hX
  refine ⟨L.length, fun n Y hY ↦ ?_⟩
  by_contra hn
  push Not at hn
  obtain ⟨c, h0, hcn, hc⟩ := hY.chain
  -- each `c i` is isomorphic to a member of `L`
  have hmem : ∀ i, i ≤ n → ∃ Z ∈ L, IsoM (c i) Z := fun i hi ↦ by
    have := hc 0 i (Nat.zero_le _) hi
    rw [h0, Nat.sub_zero] at this
    exact hL i (c i) this
  let f : ℕ → FDMod k A := fun i ↦ if h : i ≤ n then (hmem i h).choose else X
  have hf : ∀ i (hi : i ≤ n), f i ∈ L ∧ IsoM (c i) (f i) := by
    intro i hi
    simp only [f, dif_pos hi]
    exact (hmem i hi).choose_spec
  have hmaps : ∀ i ∈ Finset.range (n + 1), f i ∈ L.toFinset := fun i hi ↦
    List.mem_toFinset.2 (hf i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).1
  have hcard : L.toFinset.card < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    have := List.toFinset_card_le L
    omega
  obtain ⟨i, hi, j, hj, hij, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hiso : IsoM (c j) (c i) := (hf j hj').2.trans (hfeq ▸ (hf i hi').2.symm)
  have hiso' : IsoM (c i) (c j) := hiso.symm
  rcases lt_or_gt_of_ne hij with h | h
  · have hci : 𝒞 (c i) := by
      have := hc 0 i (Nat.zero_le _) hi'
      rw [h0] at this
      exact h𝒞.mem_of_predN hX this
    exact h𝒞.noCycle (c i) hci (j - i) (c j) (by omega) (hc i j h.le hj') hiso
  · have hcj : 𝒞 (c j) := by
      have := hc 0 j (Nat.zero_le _) hj'
      rw [h0] at this
      exact h𝒞.mem_of_predN hX this
    exact h𝒞.noCycle (c j) hcj (i - j) (c i) (by omega) (hc j i h.le hi') hiso'

/-- **Induction over proper predecessors.** -/
theorem induction (P : FDMod k A → Prop)
    (step : ∀ X, 𝒞 X → (∀ m V, 0 < m → PredN X m V → P V) → P X) : ∀ X, 𝒞 X → P X := by
  suffices H : ∀ N X, 𝒞 X → (∀ n Y, PredN X n Y → n ≤ N) → P X from
    fun X hX ↦ by
      obtain ⟨N, hN⟩ := h𝒞.length_le hX
      exact H N X hX hN
  intro N
  induction N with
  | zero =>
    intro X hX hN
    exact step X hX fun m V hm hV ↦ absurd (hN m V hV) (by omega)
  | succ N ih =>
    intro X hX hN
    refine step X hX fun m V hm hV ↦ ih V (h𝒞.mem_of_predN hX hV) fun n Y hY ↦ ?_
    have := hN (m + n) Y (hV.trans hY)
    omega

end PreprojComp

end LargeIndecomposable.AR
