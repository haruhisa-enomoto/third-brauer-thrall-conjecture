module

public import LargeIndecomposable.AuslanderReiten.Lengths.Good

/-!
# Successors of good modules

If every nonzero indecomposable summand of a free module is good, then irreducible successors of
good modules are good (`good_succ`): for a non-projective successor `Y`, the Auslander–Reiten
sequence `0 → τY → E → Y → 0` has `τY` a proper predecessor of the given module, and the summands
of `E` are successors of `τY`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

lemma PredN.eq_of_zero {Y X : FDMod k A} (h : PredN Y 0 X) : X = Y := by
  cases h
  rfl

/-- One-step predecessors are summands of the chosen minimal right almost split map. -/
lemma PredN.one {Y W : FDMod k A} (hY : IndNT Y) (h : PredN Y 1 W) :
    ∃ i, W = (chosenMin Y hY).d.obj i := by
  cases h with
  | step h' hX i =>
    obtain rfl := h'.eq_of_zero
    exact ⟨i, rfl⟩

/-- Longer predecessors pass through a one-step predecessor. -/
lemma PredN.succ_split {Y Z : FDMod k A} (hY : IndNT Y) {m : ℕ} (h : PredN Y (m + 1) Z) :
    ∃ i, PredN ((chosenMin Y hY).d.obj i) m Z := by
  obtain ⟨c, h0, hc1, hc⟩ := h.chain
  have h1 := hc 0 1 (Nat.zero_le _) (by omega)
  rw [h0] at h1
  obtain ⟨i, hi⟩ := PredN.one hY h1
  refine ⟨i, ?_⟩
  have h2 := hc 1 (m + 1) (by omega) le_rfl
  rw [hc1, hi] at h2
  simpa using h2

/-- **A module whose one-step predecessors are good is good, if it lies on no cycle through
them.** -/
lemma good_of_preds {Y : FDMod k A} (hY : IndNT Y)
    (hW : ∀ i, Good ((chosenMin Y hY).d.obj i)) : Good Y := by
  classical
  choose L hL using fun i ↦ (hW i).2.1
  refine ⟨hY, ⟨Y :: (Finset.univ.toList.flatMap L), fun n Z hZ ↦ ?_⟩, fun n Z hZ ↦ ?_⟩
  · rcases n with _ | m
    · rw [hZ.eq_of_zero]
      exact ⟨Y, List.mem_cons_self, ⟨𝟙 Y, Function.bijective_id⟩⟩
    · obtain ⟨i, hi⟩ := hZ.succ_split hY
      obtain ⟨Z', hZ', hZZ⟩ := hL i m Z hi
      exact ⟨Z', List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨i, by simp, hZ'⟩), hZZ⟩
  · rcases n with _ | m
    · rw [hZ.eq_of_zero]
      intro m' Z' hm' hZ' hZY
      obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
      obtain ⟨i, hi⟩ := hZ'.succ_split hY
      -- `W_i` would lie on a cycle
      obtain ⟨W', hW', hWW⟩ := PredN.of_iso hZY.symm (PredN.step (PredN.zero hY) hY i)
      exact (hW i).2.2 0 _ (PredN.zero (hW i).1) (m'' + 1) W' (by omega) (hi.trans hW') hWW.symm
    · obtain ⟨i, hi⟩ := hZ.succ_split hY
      exact (hW i).2.2 m Z hi

/-- **Successors of good modules are good.** -/
theorem good_succ (hproj : ∀ Y : FDMod k A, IndNT Y → IsFreeSummand A Y → Good Y) :
    ∀ X : FDMod k A, Good X → ∀ Y : FDMod k A, IndNT Y → ∀ f : X ⟶ Y, IsIrr f → Good Y := by
  refine Good.induction _ fun X hX ih Y hY f hf ↦ ?_
  classical
  by_cases hp : IsFreeSummand A Y
  · exact hproj Y hY hp
  haveI := hY.2
  haveI : IsLocalRing (Module.End A Y) := hY.1.isLocalRing (k := k)
  obtain ⟨E, g, hg, hgs, hmin, hleft, hKind, hKnt⟩ := exists_arSeq Y hp
  let K : FDMod k A := FDMod.ofSub (LinearMap.ker (FDMod.lin g))
  let fK : K ⟶ E := (LinearMap.ker (FDMod.lin g)).subtype
  have hfKinj : Function.Injective (FDMod.lin fK) := Subtype.val_injective
  have hexK : LinearMap.range (FDMod.lin fK) = LinearMap.ker (FDMod.lin g) :=
    Submodule.range_subtype _
  have hK : IndNT K := ⟨hKind, hKnt⟩
  have hleftmin := leftMinimal_of_arSeq hleft hfKinj hg hgs hexK hmin
  obtain ⟨d⟩ := FDMod.exists_decomp E
  -- `X` is a summand of `E`, so `τY = K` is a proper predecessor of `X`
  obtain ⟨v, -, r, hr⟩ := hf.factor_rightAS hg
  obtain ⟨j, hj⟩ := iso_summand_of_splitMono hX.1 d v r hr
  obtain ⟨b, hb⟩ := hj.symm
  have hirr := (isIrr_summandL hleft hleftmin hK d j).comp_iso b hb
  obtain ⟨j1, c, hc⟩ := hirr.iso_chosenMin hK hX.1
  have hK1 : PredN X 1 ((chosenMin X hX.1).d.obj j1) := PredN.step (PredN.zero hX.1) hX.1 j1
  -- successors of `K` are good
  have hKsucc : ∀ Z : FDMod k A, IndNT Z → ∀ h : K ⟶ Z, IsIrr h → Good Z := fun Z hZ h hh ↦
    ih 1 _ one_pos hK1 Z hZ (invOf c hc ≫ h) (hh.iso_comp _ (LinearEquiv.ofBijective _ hc).symm.bijective)
  -- the one-step predecessors of `Y` are summands of `E`, hence successors of `K`
  refine good_of_preds hY fun i ↦ ?_
  have hWi : IndNT ((chosenMin Y hY).d.obj i) :=
    ⟨(chosenMin Y hY).d.indec i, (chosenMin Y hY).d.nt i⟩
  have hirrW := isIrr_summand (chosenMin Y hY).hg (chosenMin Y hY).hmin hY (chosenMin Y hY).d i
  obtain ⟨v', -, r', hr'⟩ := hirrW.factor_rightAS hg
  obtain ⟨l, hl⟩ := iso_summand_of_splitMono hWi d v' r' hr'
  exact (hKsucc _ ⟨d.indec l, d.nt l⟩ _ (isIrr_summandL hleft hleftmin hK d l)).of_iso hl.symm

end LargeIndecomposable.AR
