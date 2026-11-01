module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.PreprojDir

/-!
# Good modules

Predecessors are invariant under isomorphism up to isomorphism (`PredN.of_iso`). A module is good
(`Good`) if it is nonzero indecomposable, has finitely many predecessors up to isomorphism, and no
predecessor lies on a cycle. Good modules are closed under predecessors and isomorphism, have
predecessor chains of bounded length, and admit induction over proper predecessors
(`Good.induction`). A class of good modules closed under successors is a preprojective component
(`preprojComp_good`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **Predecessors of isomorphic modules correspond.** -/
lemma PredN.of_iso {M M' : FDMod k A} (hMM : IsoM M M') :
    ∀ {n : ℕ} {Y : FDMod k A}, PredN M n Y → ∃ Y', PredN M' n Y' ∧ IsoM Y Y' := by
  intro n Y h
  induction h with
  | zero hM =>
    exact ⟨M', PredN.zero (DirData.indNT_of_iso hMM hM), hMM⟩
  | step h hX i ih =>
    obtain ⟨X', hX', a, ha⟩ := ih
    have hirr := (isIrr_summand (chosenMin _ hX).hg (chosenMin _ hX).hmin hX
      (chosenMin _ hX).d i).comp_iso a ha
    obtain ⟨j, hj⟩ := hirr.iso_chosenMin ⟨(chosenMin _ hX).d.indec i, (chosenMin _ hX).d.nt i⟩
      hX'.indNT
    exact ⟨_, PredN.step hX' hX'.indNT j, hj⟩

/-- No proper predecessor is isomorphic to `Y`. -/
def NoCyc (Y : FDMod k A) : Prop := ∀ m Z, 0 < m → PredN Y m Z → ¬IsoM Z Y

/-- Good modules. -/
def Good (M : FDMod k A) : Prop :=
  IndNT M ∧ (∃ L : List (FDMod k A), ∀ n Y, PredN M n Y → ∃ Z ∈ L, IsoM Y Z) ∧
    ∀ n Y, PredN M n Y → NoCyc Y

lemma Good.pred {M : FDMod k A} (hM : Good M) {n : ℕ} {Y : FDMod k A} (hY : PredN M n Y) :
    Good Y := by
  obtain ⟨-, ⟨L, hL⟩, hc⟩ := hM
  exact ⟨hY.indNT, ⟨L, fun m Z hZ ↦ hL _ _ (hY.trans hZ)⟩, fun m Z hZ ↦ hc _ _ (hY.trans hZ)⟩

lemma NoCyc.of_iso {Y Y' : FDMod k A} (h : IsoM Y Y') (hY : NoCyc Y) : NoCyc Y' := by
  intro m Z hm hZ hZY
  obtain ⟨Z', hZ', hZZ⟩ := PredN.of_iso h.symm hZ
  exact hY m Z' hm hZ' (hZZ.symm.trans (hZY.trans h.symm))

lemma Good.of_iso {M M' : FDMod k A} (hM : Good M) (h : IsoM M M') : Good M' := by
  obtain ⟨hi, ⟨L, hL⟩, hc⟩ := hM
  refine ⟨DirData.indNT_of_iso h hi, ⟨L, fun n Y hY ↦ ?_⟩, fun n Y hY ↦ ?_⟩
  · obtain ⟨Y', hY', hYY⟩ := PredN.of_iso h.symm hY
    obtain ⟨Z, hZ, hZY⟩ := hL n Y' hY'
    exact ⟨Z, hZ, hYY.trans hZY⟩
  · obtain ⟨Y', hY', hYY⟩ := PredN.of_iso h.symm hY
    exact (hc n Y' hY').of_iso hYY.symm

/-- **Predecessor chains of good modules have bounded length.** -/
theorem Good.length_le {M : FDMod k A} (hM : Good M) : ∃ N, ∀ n Y, PredN M n Y → n ≤ N := by
  classical
  obtain ⟨-, ⟨L, hL⟩, hc⟩ := hM
  refine ⟨L.length, fun n Y hY ↦ ?_⟩
  by_contra hn
  push Not at hn
  obtain ⟨c, h0, hcn, hcc⟩ := hY.chain
  have hmem : ∀ i, i ≤ n → ∃ Z ∈ L, IsoM (c i) Z := fun i hi ↦ by
    have := hcc 0 i (Nat.zero_le _) hi
    rw [h0, Nat.sub_zero] at this
    exact hL i (c i) this
  let f : ℕ → FDMod k A := fun i ↦ if h : i ≤ n then (hmem i h).choose else M
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
  have hpred : ∀ l, l ≤ n → PredN M l (c l) := fun l hl ↦ by
    have := hcc 0 l (Nat.zero_le _) hl
    rwa [h0, Nat.sub_zero] at this
  rcases lt_or_gt_of_ne hij with h | h
  · exact hc i (c i) (hpred i hi') (j - i) (c j) (by omega) (hcc i j h.le hj') hiso
  · exact hc j (c j) (hpred j hj') (i - j) (c i) (by omega) (hcc j i h.le hi') hiso.symm

/-- **Induction over proper predecessors of good modules.** -/
theorem Good.induction (P : FDMod k A → Prop)
    (step : ∀ X, Good X → (∀ m V, 0 < m → PredN X m V → P V) → P X) :
    ∀ X, Good X → P X := by
  suffices H : ∀ N X, Good X → (∀ n Y, PredN X n Y → n ≤ N) → P X from
    fun X hX ↦ by
      obtain ⟨N, hN⟩ := hX.length_le
      exact H N X hX hN
  intro N
  induction N with
  | zero =>
    intro X hX hN
    exact step X hX fun m V hm hV ↦ absurd (hN m V hV) (by omega)
  | succ N ih =>
    intro X hX hN
    refine step X hX fun m V hm hV ↦ ih V (hX.pred hV) fun n Y hY ↦ ?_
    have := hN (m + n) Y (hV.trans hY)
    omega

/-- **Good modules closed under successors form a preprojective component.** -/
theorem preprojComp_good (hne : ∃ M : FDMod k A, Good M)
    (hsucc : ∀ X Y : FDMod k A, Good X → IndNT Y → ∀ f : X ⟶ Y, IsIrr f → Good Y) :
    PreprojComp (Good (k := k) (A := A)) where
  nonempty := hne
  indNT X hX := hX.1
  iso X Y hX h := hX.of_iso h
  pred X Y hX hY f hf := by
    obtain ⟨i, hi⟩ := hf.iso_chosenMin hY hX.1
    exact (hX.pred (PredN.step (PredN.zero hX.1) hX.1 i)).of_iso hi.symm
  succ := hsucc
  finPred X hX := by
    obtain ⟨-, ⟨L, hL⟩, -⟩ := hX
    refine ⟨(L.map fun Z : FDMod k A ↦ finrank k Z.carrier).sum, fun n Y hY ↦ ?_⟩
    obtain ⟨Z, hZ, g, hg⟩ := hL n Y hY
    have h1 : finrank k Y = finrank k Z :=
      (LinearEquiv.ofBijective ((FDMod.lin g).restrictScalars k) hg).finrank_eq
    rw [h1]
    exact List.le_sum_of_mem (List.mem_map_of_mem hZ)
  finIso X hX := hX.2.1
  noCycle X hX := hX.2.2 0 X (PredN.zero hX.1)

end LargeIndecomposable.AR
