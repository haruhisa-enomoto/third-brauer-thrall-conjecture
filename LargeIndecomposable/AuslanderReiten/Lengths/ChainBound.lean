module

public import LargeIndecomposable.AuslanderReiten.Lengths.GoodSucc
public import LargeIndecomposable.DirectedAlgebras.Sincere.SincereEuler

/-!
# Bounded chains and good modules

`ChainTo Y n X` is a chain `X → ⋯ → Y` of `n` nonzero non-bijective maps between nonzero
indecomposables. A module is good iff such chains have bounded length (`Good.chain_bdd`,
`good_of_bdd`). This is the content of ASS IX.5.1 in the form used here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- Chains of nonzero non-bijective maps ending at `Y`. -/
inductive ChainTo (Y : FDMod k A) : ℕ → FDMod k A → Prop
  | nil (h : IndNT Y) : ChainTo Y 0 Y
  | step {n : ℕ} {X W : FDMod k A} (h : ChainTo Y n X) (hW : IndNT W) (f : W ⟶ X)
      (hf : FDMod.lin f ≠ 0) (hnb : ¬Function.Bijective (FDMod.lin f)) : ChainTo Y (n + 1) W

lemma ChainTo.indNT {Y X : FDMod k A} {n : ℕ} (h : ChainTo Y n X) : IndNT X := by
  cases h with
  | nil h => exact h
  | step _ hW _ _ _ => exact hW

/-- Irreducible maps between nonzero modules are nonzero. -/
lemma IsIrr.lin_ne_zero {X Y : FDMod k A} (hX : Nontrivial X) (hY : Nontrivial Y) {f : X ⟶ Y}
    (hf : IsIrr f) : FDMod.lin f ≠ 0 := by
  intro h0
  let a : X ⟶ FDMod.zero k A := show X →ₗ[A] FDMod.zero k A from 0
  let b : FDMod.zero k A ⟶ Y := show FDMod.zero k A →ₗ[A] Y from 0
  have hab : a ≫ b = f := by
    refine LinearMap.ext fun x ↦ ?_
    exact (LinearMap.congr_fun h0 x).symm
  rcases hf.2.2 _ a b hab with ⟨r, hr⟩ | ⟨s, hs⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : X)
    apply hx
    have h1 : FDMod.lin r (FDMod.lin a x) = x := LinearMap.congr_fun hr x
    have h2 : FDMod.lin a x = 0 := rfl
    rw [h2, map_zero] at h1
    exact h1.symm
  · obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    apply hy
    have h1 : FDMod.lin b (FDMod.lin s y) = y := LinearMap.congr_fun hs y
    exact h1.symm

/-- Irreducible maps are not bijective. -/
lemma IsIrr.not_bijective {X Y : FDMod k A} {f : X ⟶ Y} (hf : IsIrr f) :
    ¬Function.Bijective (FDMod.lin f) := fun hb ↦
  hf.1 ⟨invOf f hb, comp_invOf f hb⟩

/-- Chains extend at the end. -/
lemma ChainTo.extend {W Y X : FDMod k A} {n : ℕ} (h : ChainTo W n X) (hY : IndNT Y) (f : W ⟶ Y)
    (hf : FDMod.lin f ≠ 0) (hnb : ¬Function.Bijective (FDMod.lin f)) : ChainTo Y (n + 1) X := by
  induction h with
  | nil hW => exact ChainTo.step (ChainTo.nil hY) hW f hf hnb
  | step _ hW g hg hgb ih => exact ChainTo.step ih hW g hg hgb

/-- A bound on the dimension of predecessors of a good module. -/
lemma Good.finrank_le {M : FDMod k A} (hM : Good M) :
    ∃ b, ∀ n X, PredN M n X → finrank k X ≤ b := by
  classical
  obtain ⟨-, ⟨L, hL⟩, -⟩ := hM
  refine ⟨(L.map fun Z : FDMod k A ↦ finrank k Z.carrier).sum, fun n Y hY ↦ ?_⟩
  obtain ⟨Z, hZ, g, hg⟩ := hL n Y hY
  have h1 : finrank k Y = finrank k Z :=
    (LinearEquiv.ofBijective ((FDMod.lin g).restrictScalars k) hg).finrank_eq
  rw [h1]
  exact List.le_sum_of_mem (List.mem_map_of_mem hZ)

/-- **Chains ending at a good module have bounded length.** -/
theorem Good.chain_bdd {M : FDMod k A} (hM : Good M) : ∃ N, ∀ n X, ChainTo M n X → n ≤ N := by
  obtain ⟨N, hN⟩ := hM.length_le
  obtain ⟨b, hb⟩ := hM.finrank_le
  have aux : ∀ n X, ChainTo M n X → ∃ N' Y, n ≤ N' ∧ PredN M N' Y ∧ IsoM X Y := by
    intro n X h
    induction h with
    | nil h => exact ⟨0, M, le_rfl, PredN.zero h, 𝟙 M, Function.bijective_id⟩
    | step _ hW f hf hnb ih =>
      obtain ⟨N', Y, hle, hY, g, hg⟩ := ih
      have hf' : FDMod.lin (f ≫ g) ≠ 0 := by
        intro h0
        apply hf
        refine LinearMap.ext fun x ↦ hg.1 ?_
        have := LinearMap.congr_fun h0 x
        simpa using this
      have hnb' : ¬Function.Bijective (FDMod.lin (f ≫ g)) := fun hb' ↦ hnb (by
        have hc := (LinearEquiv.ofBijective (FDMod.lin g) hg).symm.bijective.comp hb'
        have heq : ⇑(LinearEquiv.ofBijective (FDMod.lin g) hg).symm ∘ ⇑(FDMod.lin (f ≫ g)) =
            ⇑(FDMod.lin f) := funext fun x ↦
          (LinearEquiv.ofBijective (FDMod.lin g) hg).symm_apply_apply (FDMod.lin f x)
        rwa [heq] at hc)
      obtain ⟨m, hm, Z, hZ, hiso⟩ := iso_predN_of_hom hb hY _ hW.1 (f ≫ g) hf' hnb'
      exact ⟨N' + m, Z, by omega, hZ, hiso⟩
  refine ⟨N, fun n X h ↦ ?_⟩
  obtain ⟨N', Y, hle, hY, -⟩ := aux n X h
  exact hle.trans (hN N' Y hY)

/-- **A bound on chains makes a module good.** -/
theorem good_of_bdd : ∀ (m : ℕ) (Y : FDMod k A), IndNT Y → (∀ n X, ChainTo Y n X → n ≤ m) → Good Y := by
  intro m
  induction m with
  | zero =>
    intro Y hY h
    refine good_of_preds hY fun i ↦ ?_
    have hW : IndNT ((chosenMin Y hY).d.obj i) :=
      ⟨(chosenMin Y hY).d.indec i, (chosenMin Y hY).d.nt i⟩
    have hirr := isIrr_summand (chosenMin Y hY).hg (chosenMin Y hY).hmin hY (chosenMin Y hY).d i
    have := h 1 _ (ChainTo.step (ChainTo.nil hY) hW _ (hirr.lin_ne_zero hW.2 hY.2) hirr.not_bijective)
    omega
  | succ m ih =>
    intro Y hY h
    refine good_of_preds hY fun i ↦ ?_
    have hW : IndNT ((chosenMin Y hY).d.obj i) :=
      ⟨(chosenMin Y hY).d.indec i, (chosenMin Y hY).d.nt i⟩
    have hirr := isIrr_summand (chosenMin Y hY).hg (chosenMin Y hY).hmin hY (chosenMin Y hY).d i
    refine ih _ hW fun n X hc ↦ ?_
    have := h (n + 1) X (hc.extend hY _ (hirr.lin_ne_zero hW.2 hY.2) hirr.not_bijective)
    omega

end LargeIndecomposable.AR
