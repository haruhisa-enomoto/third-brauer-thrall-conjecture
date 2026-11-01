module

public import LargeIndecomposable.Modules.KrullSchmidt.KrullSchmidtStep
public import LargeIndecomposable.DirectedAlgebras.Directing.Directing

/-!
# Modules with finitely many predecessors and no cycle are directing

`PredN U n X`: `X` is reached from `U` by `n` steps into summands of chosen minimal right almost
split maps. If the predecessors of `U` have bounded dimension, a nonzero non-bijective map from an
indecomposable `N` into an `n`-step predecessor makes `N` isomorphic to an `(n + m)`-step
predecessor with `m ≥ 1` (`iso_predN_of_hom`). Hence if no proper predecessor is isomorphic to `U`,
then `U` is directing (`directing_of_noCycle`), so a brick.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- Predecessors with step count. -/
inductive PredN (U : FDMod k A) : ℕ → FDMod k A → Prop
  | zero (hU : IndNT U) : PredN U 0 U
  | step {n : ℕ} {X : FDMod k A} (h : PredN U n X) (hX : IndNT X) (i : (chosenMin X hX).d.ι) :
      PredN U (n + 1) ((chosenMin X hX).d.obj i)

lemma PredN.indNT {U X : FDMod k A} {n : ℕ} (h : PredN U n X) : IndNT X := by
  cases h with
  | zero hU => exact hU
  | step _ hX i => exact ⟨(chosenMin _ hX).d.indec i, (chosenMin _ hX).d.nt i⟩

lemma PredN.trans {U X : FDMod k A} {n : ℕ} (hX : PredN U n X) :
    ∀ {m : ℕ} {Y : FDMod k A}, PredN X m Y → PredN U (n + m) Y := by
  intro m Y h
  induction h with
  | zero _ => exact hX
  | step _ hY i ih => exact PredN.step ih hY i

lemma IsoM.symm {X Y : FDMod k A} (h : IsoM X Y) : IsoM Y X := by
  obtain ⟨g, hg⟩ := h
  exact ⟨(LinearEquiv.ofBijective (FDMod.lin g) hg).symm.toLinearMap,
    (LinearEquiv.ofBijective (FDMod.lin g) hg).symm.bijective⟩

lemma IsoM.trans {X Y Z : FDMod k A} (h : IsoM X Y) (h' : IsoM Y Z) : IsoM X Z := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g ≫ g', hg'.comp hg⟩

/-- **A nonzero non-bijective map into a predecessor comes from a further predecessor.** -/
theorem iso_predN_of_hom {U : FDMod k A} {b : ℕ}
    (hb : ∀ n X, PredN U n X → finrank k X ≤ b) {n : ℕ} {X : FDMod k A} (hX : PredN U n X)
    (N : FDMod k A) (hN : IsIndecMod A N) (f : N ⟶ X) (hf : FDMod.lin f ≠ 0)
    (hnb : ¬Function.Bijective (FDMod.lin f)) :
    ∃ m, 0 < m ∧ ∃ Y, PredN U (n + m) Y ∧ IsoM N Y := by
  classical
  have hXi := hX.indNT
  let F := (chosenMin X hXi).fam (fun Y ↦ ∃ m, PredN X m Y)
    (fun i ↦ ⟨1, PredN.step (PredN.zero hXi) hXi i⟩)
  -- `f` is not split epi, so it factors through the family
  have hns : ¬∃ s : X ⟶ N, FDMod.lin f ∘ₗ FDMod.lin s = LinearMap.id :=
    fun ⟨s, hs⟩ ↦ hnb (bijective_of_split hN hXi.2 f s hs)
  obtain ⟨h, hh⟩ := F.factor N f hns
  obtain ⟨i, hi⟩ : ∃ i, FDMod.lin (h i) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf
    rw [hh]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [hall i, LinearMap.comp_zero]
  -- continue from the summand `E i`, a one-step predecessor of `X`
  have hEi : PredN X 1 ((chosenMin X hXi).d.obj i) := PredN.step (PredN.zero hXi) hXi i
  have hEU := hX.trans hEi
  obtain ⟨Y, ⟨m', hY⟩, e, he⟩ := auslander' (P := fun Y ↦ ∃ m, PredN ((chosenMin X hXi).d.obj i) m Y)
    (b := b) (fun Y ⟨m, h⟩ ↦ h.indNT.1) (fun Y ⟨m, h⟩ ↦ hb _ _ (hEU.trans h))
    (fun Y ⟨m, h⟩ ↦ h.indNT.2)
    (fun Y ⟨m, hY⟩ ↦ ⟨(chosenMin Y hY.indNT).fam _ fun j ↦ ⟨m + 1, PredN.step hY hY.indNT j⟩⟩)
    N hN _ ⟨0, PredN.zero hEi.indNT⟩ (h i) hi
  refine ⟨1 + m', by omega, Y, ?_, e, he⟩
  rw [← add_assoc]
  exact hEU.trans hY

/-- Reachability into a predecessor, through isomorphisms. -/
lemma reach_pred {U : FDMod k A} {b : ℕ} (hb : ∀ n X, PredN U n X → finrank k X ≤ b) :
    ∀ {X Y : FDMod k A}, Reach₁ X Y → ∀ {n : ℕ} {Z : FDMod k A}, PredN U n Z → IsoM Y Z →
      ∃ m, 0 < m ∧ ∃ Z', PredN U (n + m) Z' ∧ IsoM X Z' := by
  intro X Y h
  induction h with
  | step hX hY f hf hnb =>
    intro n Z hZ hYZ
    obtain ⟨g, hg⟩ := hYZ
    apply iso_predN_of_hom hb hZ _ hX.1 (f ≫ g)
    · intro h0
      apply hf
      have hinj := hg.1
      ext x
      have := LinearMap.congr_fun h0 x
      exact hinj (by simpa using this)
    · intro hb'
      have hc := (LinearEquiv.ofBijective (FDMod.lin g) hg).symm.bijective.comp hb'
      have heq : ⇑(LinearEquiv.ofBijective (FDMod.lin g) hg).symm ∘ ⇑(FDMod.lin (f ≫ g)) =
          ⇑(FDMod.lin f) := funext fun x ↦
        (LinearEquiv.ofBijective (FDMod.lin g) hg).symm_apply_apply (FDMod.lin f x)
      rw [heq] at hc
      exact hnb hc
  | trans _ _ ih1 ih2 =>
    intro n Z hZ hYZ
    obtain ⟨m, hm, Z', hZ', hiso⟩ := ih2 hZ hYZ
    obtain ⟨m', hm', Z'', hZ'', hiso'⟩ := ih1 hZ' hiso
    exact ⟨m + m', by omega, Z'', by rwa [← add_assoc], hiso'⟩

/-- **No proper predecessor isomorphic to `U` makes `U` directing.** -/
theorem directing_of_noCycle {U : FDMod k A} (hU : IndNT U) {b : ℕ}
    (hb : ∀ n X, PredN U n X → finrank k X ≤ b)
    (hnc : ∀ n X, 0 < n → PredN U n X → ¬IsoM X U) : Directing U := by
  refine ⟨hU, fun h ↦ ?_⟩
  have hid : IsoM U U := ⟨𝟙 U, Function.bijective_id⟩
  obtain ⟨m, hm, Z, hZ, hiso⟩ := reach_pred hb h (PredN.zero hU) hid
  rw [zero_add] at hZ
  exact hnc m Z hm hZ hiso.symm

end LargeIndecomposable.AR
