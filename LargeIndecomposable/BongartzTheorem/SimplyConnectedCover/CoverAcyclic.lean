module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullStage

/-!
# The universal cover has no oriented cycles

`CoverAcyclic x₀`: no irreducible morphism `a → b` of the universal cover is followed by a path
back from `b` to `a`. It holds for good covers (`coverAcyclic_of_cycleFree`), for covers with a
positive cocycle (`coverAcyclic_of_posCocycle`), and passes from the residue `P/μ` to `P`
(`coverAcyclic_of_residue`). Hence it holds for the ray category of a minimal
representation-infinite distributive algebra with torsion-free fundamental group
(`coverIsAcyclic`), by the case split of `intervalFiniteCover_of_stage`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

section General

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- No oriented cycles in the universal cover. -/
def CoverAcyclic (x₀ : P) : Prop :=
  ∀ (a b : Cover x₀) (f : a ⟶ b), IsIrreducible f → ¬Reach b a

lemma coverAcyclic_of_cycleFree {x₀ : P}
    (h : ∀ (c : RayVert (Cover x₀)) (p : Quiver.Path c c), p.length = 0) : CoverAcyclic x₀ := by
  intro a b f hf hba
  obtain ⟨q⟩ := reaches_of_reach hba
  have := h _ ((Quiver.Path.nil.cons (⟨f, hf⟩ : (RayVert.mk a : RayVert (Cover x₀)) ⟶
    RayVert.mk b)).comp q)
  rw [Quiver.Path.length_comp, Quiver.Path.length_cons] at this
  omega

end General

section Cocycle

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

lemma coverHt_le_of_reach (c : ArrowWeight P) (hc : IsCocycle c)
    (hpos : ∀ {x y : RayVert P} (e : x ⟶ y), 1 ≤ c e) {a d : Cover x₀} (h : Reach a d) :
    coverHt c hc a ≤ coverHt c hc d := by
  induction h with
  | refl => exact le_rfl
  | step f hf _ ih => exact (coverHt_lt c hc hpos hf).le.trans ih

lemma coverAcyclic_of_posCocycle (c : ArrowWeight P) (hc : IsCocycle c)
    (hpos : ∀ {x y : RayVert P} (e : x ⟶ y), 1 ≤ c e) : CoverAcyclic x₀ := fun a b f hf hba ↦
  absurd (coverHt_le_of_reach c hc hpos hba) (not_le.2 (coverHt_lt c hc hpos hf))

lemma isCocycle_one_of_not_hasLong (h : ¬HasLong P) : IsCocycle (oneWeight (P := P)) := by
  intro x y s t hst h0
  rw [pathWeight_one, pathWeight_one]
  by_cases hiso : IsIso (pathVal s)
  · have hs : s.length = 0 := by
      by_contra hl
      exact not_isIso_pathVal s (by omega) hiso
    have ht : t.length = 0 := by
      by_contra hl
      exact not_isIso_pathVal t (by omega) (hst ▸ hiso)
    rw [hs, ht]
  · have hirr : IsIrreducible (pathVal s) := by
      by_contra hni
      exact h ⟨_, _, _, h0, hiso, hni⟩
    obtain ⟨e, rfl⟩ := eq_toPath_of_isIrreducible s hirr
    obtain ⟨e', rfl⟩ := eq_toPath_of_isIrreducible t (hst ▸ hirr)
    rfl

lemma coverAcyclic_of_not_hasLong (h : ¬HasLong P) : CoverAcyclic x₀ :=
  coverAcyclic_of_posCocycle oneWeight (isCocycle_one_of_not_hasLong h) fun _ ↦ le_rfl

end Cocycle

section Residue

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [Fintype P] [DecidableEq P]
  [LargeIndecomposable.IsFiniteRayCategory P] {a b : P} (μ : a ⟶ b) (hμ : ¬IsIso μ)
  (hμr : ¬IsIrreducible μ) (hμ0 : μ ≠ 0) (hlong : IsLongAt μ) (hcont : NotInContour μ)
  {x₀ : P} [IsRayCategory (Res μ)]

attribute [local instance] isRayCategory_of_finiteRayCategory

lemma irr_resCoverMap {c d : Cover x₀} {f : c ⟶ d} (hf : IsIrreducible f) :
    ∃ f' : resCoverMap μ hμ hμr hμ0 hlong hcont c ⟶ resCoverMap μ hμ hμr hμ0 hlong hcont d,
      IsIrreducible f' := by
  obtain ⟨e, he⟩ := exists_arrow_of_irreducible hf
  obtain ⟨f', hf'⟩ := exists_irreducible_of_arrow
    (resCoverMap μ hμ hμr hμ0 hlong hcont c) ((residueQuiverMap μ hμ hμr hμ0).map e)
  have hd : (⟨(resF μ).obj d.y, (resPhi μ hμ hμr hμ0 hlong hcont).map c.u ≫
      arrCls ((residueQuiverMap μ hμ hμr hμ0).map e)⟩ : Cover ((resF μ).obj x₀)) =
      resCoverMap μ hμ hμr hμ0 hlong hcont d := by
    simp only [resCoverMap, he, Functor.map_comp, resPhi_arrCls]
    rfl
  rw [← hd]
  exact ⟨f', hf'⟩

include hμ hμr hμ0 hlong hcont in
/-- **Acyclicity passes from `P/μ` to `P`.** -/
theorem coverAcyclic_of_residue (h : CoverAcyclic ((resF μ).obj x₀)) : CoverAcyclic x₀ := by
  intro c d f hf hdc
  obtain ⟨f', hf'⟩ := irr_resCoverMap μ hμ hμr hμ0 hlong hcont hf
  exact h _ _ f' hf' (reach_resCoverMap μ hμ hμr hμ0 hlong hcont hdc)

end Residue

/-- **Acyclicity for chain-bounded categories** (from Satz 5.1). -/
theorem coverAcyclic_of_chainBounded (hS : SimplyConnectedStageStep) (P : Type) [Category.{0} P]
    [HasZeroMorphisms P] [IsRayCategory P] [Finite P] [Fintype P] [DecidableEq P]
    (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    (hcon : IsConnected (FundGroupoid P)) (x₀ : P) : CoverAcyclic x₀ := by
  letI := isFiniteRayCategory0_of_ray (C := P)
  have hfree : IsFreeGroup (End (vtx x₀)) := isFreeGroup_end_fund _ P hL hR hCB hcon le_rfl _
  have hℓ : ∀ y : P, Nonempty (vtx x₀ ⟶ vtx y) := fun y ↦
    nonempty_hom_of_preconnected_groupoid _ _
  obtain ⟨H, _, _, φ, hLF⟩ := exists_loopFree_gcover x₀ hfree fun y ↦ (hℓ y).some
  letI := isFiniteRayCategory0_of_ray (C := GCover (volt (fun y ↦ (hℓ y).some) φ))
  have hgood := coverGood_of_stage hS _ (GCover (volt (fun y ↦ (hℓ y).some) φ))
    (leftCancel_gcover hL) (rightCancel_gcover hR) (chainBounded_gcover hCB) hLF le_rfl ⟨x₀, 1⟩
  exact coverAcyclic_of_cycleFree (cycleFree_of_gcover hgood.1)

universe u

open Statement in
/-- **The universal cover of a minimal representation-infinite distributive algebra has no
oriented cycles.** -/
theorem coverIsAcyclic (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B]
    [Algebra k B] [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : SplitBasicData k B ι) (hB : IsMinimalRepInfinite B) (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    letI := S.isRayCategory hd
    letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
    letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
    ∀ (x₀ : RaySmall.{0} S.toIdempotents.RayCategory), CoverAcyclic x₀ := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro x₀
  have hι := S.nonempty_of_minimal hB
  have : Nonempty (RaySmall.{0} S.toIdempotents.RayCategory) :=
    ⟨⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩⟩
  have hcon : IsConnected (FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory)) :=
    isConnected_fund_of_nzConnected fun x y ↦ RaySmall.nzConnected
      (S.nzConnected hd (fun e he hc ↦ hB.central_idempotent e he hc) x.as y.as)
  by_cases hCB : ChainBounded S.toIdempotents.RayCategory
  · exact coverAcyclic_of_chainBounded simplyConnectedStageStep _ (RaySmall.leftCancel (S.leftCancel hd))
      (RaySmall.rightCancel (S.rightCancel hd)) (RaySmall.chainBounded hCB) hcon x₀
  by_cases hL : HasLong (RaySmall.{0} S.toIdempotents.RayCategory)
  swap
  · exact coverAcyclic_of_not_hasLong hL
  letI := S.isFiniteRayCategory hd
  obtain ⟨a, b, μ, hμ, hμr, hμ0, hlong, hcont, hCB'⟩ :=
    bongartzProposition2_of twistedMulBasisExists (longMorphismNotInContour_of_mulBasis twistedMulBasisExists) k B ι S hB hd hCB hL
  haveI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory μ hμ
  haveI : Finite (Res μ) :=
    Finite.of_surjective (fun x ↦ (⟨x⟩ : Res μ)) fun ⟨x⟩ ↦ ⟨x, rfl⟩
  haveI : IsRayCategory (Res μ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (Res μ) := Fintype.ofFinite _
  letI : DecidableEq (Res μ) := Classical.decEq _
  have : IsConnected (Quiver.FreeGroupoid (RayVert (RaySmall.{0} S.toIdempotents.RayCategory))) :=
    isConnected_of_quotient homotopy
  have : IsConnected (Quiver.FreeGroupoid (RayVert (Res μ))) :=
    isConnected_of_equivalent (resFGEquiv μ hμ hμr hμ0)
  have hcon' : IsConnected (FundGroupoid (Res μ)) := isConnected_quotient homotopy
  exact coverAcyclic_of_residue μ hμ hμr hμ0 hlong hcont
    (coverAcyclic_of_chainBounded simplyConnectedStageStep _
      (leftCancel_quotient _ (RaySmall.leftCancel (S.leftCancel hd)))
      (rightCancel_quotient _ (RaySmall.rightCancel (S.rightCancel hd))) hCB' hcon' _)

end LargeIndecomposable.RayCat
