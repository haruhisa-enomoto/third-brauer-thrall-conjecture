module

public import LargeIndecomposable.AuslanderReiten.Lengths.GoodSucc

/-!
# Good modules from a preprojective component of `Bᵢ(x)`

Let `C` be a preprojective component over the quotient for `B = Bᵢ(x)` and `U₀ ∈ C` with no proper
predecessor restricting to `Rᵢ(x)`. Then `A`-predecessors of `res U₀` are restrictions of
predecessors of `U₀` (`predA_of_pred`), and `res U₀` is good (`good_res`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} (sd : ∀ z, Decomp (D.RadP z)) (hsd : ∀ z, z ∈ D.T → D.SepDecomp z (sd z))
  {x : D.ι} (i0 : (sd x).ι) {𝒞 : FDMod k (D.QAlg (Bset x (sd x) i0)) → Prop}
  (h𝒞 : PreprojComp 𝒞)

include hsd h𝒞 in
/-- **`A`-predecessors of `res U₀` come from predecessors of `U₀`.** -/
theorem predA_of_pred {U₀ : FDMod k (D.QAlg (Bset x (sd x) i0))} (hU₀ : 𝒞 U₀)
    (habove : ∀ m V, 0 < m → PredN U₀ m V →
      ¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) V) ((sd x).obj i0)) :
    ∀ {n : ℕ} {Y : FDMod k A}, PredN (resFD (D.qmap (Bset x (sd x) i0)) U₀) n Y →
      ∃ W, PredN U₀ n W ∧ IsoM Y (resFD (D.qmap (Bset x (sd x) i0)) W) := by
  have hφ := D.qmap_surjective (Bset x (sd x) i0)
  have hL := lemma24b sd hsd i0 h𝒞 hU₀ habove
  intro n Y h
  induction h with
  | zero _ => exact ⟨U₀, PredN.zero (h𝒞.indNT U₀ hU₀), ⟨𝟙 _, Function.bijective_id⟩⟩
  | step h hX i ih =>
    obtain ⟨W, hW, a, ha⟩ := ih
    have hYi : IndNT ((chosenMin _ hX).d.obj i) :=
      ⟨(chosenMin _ hX).d.indec i, (chosenMin _ hX).d.nt i⟩
    have hirr := (isIrr_summand (chosenMin _ hX).hg (chosenMin _ hX).hmin hX
      (chosenMin _ hX).d i).comp_iso a ha
    have hl := (hL _ W hW).1 _ hYi _ hirr
    -- descend the summand and read off a predecessor of `W`
    have hiso := isoM_descend' _ hl
    have hD : IndNT (descendQ _ hl) :=
      (indNT_res_iff hφ _).1 (indNT_of_iso hiso hYi)
    have hirr3 : IsIrr (unresHom hφ (descIsoQ _ hl ≫ ((chosenMin _ hX).d.inc i ≫
        (chosenMin _ hX).g) ≫ a)) :=
      IsIrr.unres hφ (hirr.iso_comp (descIsoQ _ hl) Function.bijective_id)
    obtain ⟨j, hj⟩ := hirr3.iso_chosenMin hD hW.indNT
    exact ⟨_, PredN.step hW hW.indNT j, hiso.trans hj.res⟩

include hsd h𝒞 in
/-- **`res U₀` is good.** -/
theorem good_res {U₀ : FDMod k (D.QAlg (Bset x (sd x) i0))} (hU₀ : 𝒞 U₀)
    (habove : ∀ m V, 0 < m → PredN U₀ m V →
      ¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) V) ((sd x).obj i0)) :
    Good (resFD (D.qmap (Bset x (sd x) i0)) U₀) := by
  have hφ := D.qmap_surjective (Bset x (sd x) i0)
  refine ⟨(indNT_res_iff hφ U₀).2 (h𝒞.indNT U₀ hU₀), ?_, fun n Y hY ↦ ?_⟩
  · obtain ⟨L, hL⟩ := h𝒞.finIso U₀ hU₀
    refine ⟨L.map (resFD (D.qmap (Bset x (sd x) i0))), fun n Y hY ↦ ?_⟩
    obtain ⟨W, hW, hYW⟩ := predA_of_pred sd hsd i0 h𝒞 hU₀ habove hY
    obtain ⟨Z, hZ, hWZ⟩ := hL n W hW
    exact ⟨_, List.mem_map_of_mem hZ, hYW.trans hWZ.res⟩
  · -- `Y ≅ res W` with `W` a predecessor of `U₀`
    obtain ⟨W, hW, hYW⟩ := predA_of_pred sd hsd i0 h𝒞 hU₀ habove hY
    have hWC := h𝒞.mem_of_predN hU₀ hW
    have habW : ∀ m V, 0 < m → PredN W m V →
        ¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) V) ((sd x).obj i0) := fun m V hm hV ↦
      habove (n + m) V (by omega) (hW.trans hV)
    intro m Z hm hZ hZY
    obtain ⟨Z', hZ', hZZ⟩ := PredN.of_iso hYW hZ
    obtain ⟨W'', hW'', hZW⟩ := predA_of_pred sd hsd i0 h𝒞 hWC habW hZ'
    have h1 : IsoM (resFD (D.qmap (Bset x (sd x) i0)) W'')
        (resFD (D.qmap (Bset x (sd x) i0)) W) := hZW.symm.trans (hZZ.symm.trans (hZY.trans hYW))
    exact h𝒞.noCycle W hWC m W'' hm hW'' (IsoM.unres hφ h1)

end DirData

end LargeIndecomposable.AR
