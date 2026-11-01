module

public import LargeIndecomposable.AuslanderReiten.Lengths.GoodTransfer

/-!
# The two cases of the separation theorem

Case 1 (`preprojComp_transport`): a preprojective component over the quotient for `Bᵢ(x)` none of
whose members restricts to `Rᵢ(x)` restricts to a preprojective component of `A`.

Case 2 (`preprojComp_of_good_R`): if all summands `Rⱼ(y)` of all radicals are good, all
indecomposable projectives are good, and the good modules form a preprojective component.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

lemma Good.finPred {M : FDMod k A} (hM : Good M) : ∃ b, ∀ n Y, PredN M n Y → finrank k Y ≤ b := by
  obtain ⟨-, ⟨L, hL⟩, -⟩ := hM
  refine ⟨(L.map fun Z : FDMod k A ↦ finrank k Z.carrier).sum, fun n Y hY ↦ ?_⟩
  obtain ⟨Z, hZ, g, hg⟩ := hL n Y hY
  have h1 : finrank k Y = finrank k Z :=
    (LinearEquiv.ofBijective ((FDMod.lin g).restrictScalars k) hg).finrank_eq
  rw [h1]
  exact List.le_sum_of_mem (List.mem_map_of_mem hZ)

namespace DirData

variable {D : DirData k A} (sd : ∀ z, Decomp (D.RadP z)) (hsd : ∀ z, z ∈ D.T → D.SepDecomp z (sd z))

include hsd in
/-- **Case 1: transport of a preprojective component.** -/
theorem preprojComp_transport {x : D.ι} (i0 : (sd x).ι)
    {𝒞 : FDMod k (D.QAlg (Bset x (sd x) i0)) → Prop} (h𝒞 : PreprojComp 𝒞)
    (hR : ∀ V, 𝒞 V → ¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) V) ((sd x).obj i0)) :
    PreprojComp (fun M : FDMod k A ↦
      ∃ V, 𝒞 V ∧ IsoM M (resFD (D.qmap (Bset x (sd x) i0)) V)) := by
  have hφ := D.qmap_surjective (Bset x (sd x) i0)
  have habove : ∀ V, 𝒞 V → ∀ m W, 0 < m → PredN V m W →
      ¬IsoM (resFD (D.qmap (Bset x (sd x) i0)) W) ((sd x).obj i0) := fun V hV m W _ hW ↦
    hR W (h𝒞.mem_of_predN hV hW)
  have hIO : ∀ V, 𝒞 V → IrrIn (Bset x (sd x) i0) V ∧ IrrOut (Bset x (sd x) i0) V := fun V hV ↦
    let h := lemma24b sd hsd i0 h𝒞 hV (habove V hV) 0 V (PredN.zero (h𝒞.indNT V hV))
    ⟨h.1, h.2 (hR V hV)⟩
  have hgood : ∀ M, (∃ V, 𝒞 V ∧ IsoM M (resFD (D.qmap (Bset x (sd x) i0)) V)) → Good M :=
    fun M ⟨V, hV, hMV⟩ ↦ (good_res sd hsd i0 h𝒞 hV (habove V hV)).of_iso hMV.symm
  refine
  { nonempty := ?_
    indNT := fun M hM ↦ (hgood M hM).1
    iso := fun M N ⟨V, hV, hMV⟩ hMN ↦ ⟨V, hV, hMN.symm.trans hMV⟩
    pred := ?_
    succ := ?_
    finPred := fun M hM ↦ (hgood M hM).finPred
    finIso := fun M hM ↦ (hgood M hM).2.1
    noCycle := fun M hM ↦ (hgood M hM).2.2 0 M (PredN.zero (hgood M hM).1) }
  · obtain ⟨V, hV⟩ := h𝒞.nonempty
    exact ⟨_, V, hV, ⟨𝟙 _, Function.bijective_id⟩⟩
  · rintro M Y ⟨V, hV, a, ha⟩ hY f hf
    have hirr := hf.comp_iso a ha
    have hl := (hIO V hV).1 Y hY _ hirr
    have hiso := isoM_descend' Y hl
    have hD : IndNT (descendQ Y hl) := (indNT_res_iff hφ _).1 (indNT_of_iso hiso hY)
    have hirr3 : IsIrr (unresHom hφ (descIsoQ Y hl ≫ f ≫ a)) :=
      IsIrr.unres hφ (hirr.iso_comp (descIsoQ Y hl) Function.bijective_id)
    exact ⟨_, h𝒞.pred V _ hV hD _ hirr3, hiso⟩
  · rintro M Y ⟨V, hV, a, ha⟩ hY f hf
    have hirr := hf.iso_comp (invOf a ha) (LinearEquiv.ofBijective _ ha).symm.bijective
    have hl := (hIO V hV).2 Y hY _ hirr
    have hiso := isoM_descend' Y hl
    have hD : IndNT (descendQ Y hl) := (indNT_res_iff hφ _).1 (indNT_of_iso hiso hY)
    have hirr3 : IsIrr (unresHom hφ ((invOf a ha ≫ f) ≫ descIsoQInv Y hl)) :=
      IsIrr.unres hφ (hirr.comp_iso (descIsoQInv Y hl) Function.bijective_id)
    exact ⟨_, h𝒞.succ V _ hV hD _ hirr3, hiso⟩

/-- **Vertex projectives are good when the radical summands are.** -/
theorem good_proj (y : D.ι) (hy : y ∈ D.T) (hR : ∀ j, Good ((sd y).obj j)) :
    Good (projE (k := k) (D.idem y)) := by
  have hP := D.projIndNT y hy
  refine good_of_preds hP fun i ↦ ?_
  have hWi : IndNT ((chosenMin _ hP).d.obj i) :=
    ⟨(chosenMin _ hP).d.indec i, (chosenMin _ hP).d.nt i⟩
  have hirr := isIrr_summand (chosenMin _ hP).hg (chosenMin _ hP).hmin hP (chosenMin _ hP).d i
  obtain ⟨v, -, r, hr⟩ := hirr.factor_rightAS (D.isRightAS_radP y hy)
  obtain ⟨j, hj⟩ := iso_summand_of_splitMono hWi (sd y) v r hr
  exact (hR j).of_iso hj.symm

/-- **Case 2: good radical summands give a preprojective component.** -/
theorem preprojComp_of_good_R (hT : D.T.Nonempty)
    (hR : ∀ y, y ∈ D.T → ∀ j, Good ((sd y).obj j)) : PreprojComp (Good (k := k) (A := A)) := by
  have hproj : ∀ P : FDMod k A, IndNT P → IsFreeSummand A P → Good P := fun P hP hfree ↦ by
    obtain ⟨y, hy, hiso⟩ := D.iso_proj_of_freeSummand hP hfree
    exact (good_proj sd y hy (hR y hy)).of_iso hiso.symm
  obtain ⟨y, hy⟩ := hT
  exact preprojComp_good ⟨_, good_proj sd y hy (hR y hy)⟩
    fun X Y hX hY f hf ↦ good_succ hproj X hX Y hY f hf

end DirData

end LargeIndecomposable.AR
