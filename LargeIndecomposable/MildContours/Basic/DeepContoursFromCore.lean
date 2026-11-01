module

public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisFromDeep
public import LargeIndecomposable.MildContours.Basic.RayPathBridge
public import LargeIndecomposable.MildContours.Basic.EndCyclic
public import LargeIndecomposable.MildContours.Basic.SetupOp

/-!
# `OnlyDeepNode` from the core case of [mild]

[mild] Lemma 2.1 and duality (`RayCat.MildContour.deep_of_contour`) reduce
Bongartz's Theorem 3 ("contours of a minimal representation-infinite ray
category are deep") to the core case (`ρ = π(y)` factors through the last
arrow of `v`) for the small ray category `P` of `B` and for `Pᵒᵖ`
(`OnlyDeepCoreNode`); `MildHyp` passes to `Pᵒᵖ` (`RayCat.MildHyp.op`). Through the bridge
from the reversed ray paths (`RayCat.toP`) this gives `OnlyDeepNode`
(`onlyDeepNode_of_core`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat LargeIndecomposable

universe u

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]

/-- A radical endomorphism has a non-invertible ray. -/
lemma not_isIso_unitRay_of_mem_jacobson {X : S.toIdempotents.ProjectiveCategory} (a : End X)
    (ha : a ∈ Ring.jacobson (End X)) :
    ¬IsIso (show (BGRSRayCategory.mk X) ⟶ (BGRSRayCategory.mk X) from unitRay a.asHom) := by
  intro h
  haveI : IsIso a.asHom :=
    BGRSRayCategory.representative_isIso_of_isIso (SplitBasicIdempotents.ProjectiveCategory.id_ne_zero S.toIdempotents) a.asHom
  have hunit : IsUnit a := (isUnit_iff_isIso a).2 inferInstance
  exact (mem_ringJacobson_iff_not_isUnit (End X) a).1 ha hunit

end SplitBasicData

/-- The core of [mild] Theorem 3 for the small ray category of a minimal
representation-infinite distributive algebra: the core case for `P` and `Pᵒᵖ`. -/
def OnlyDeepCoreNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isFiniteRayCategory hd
      letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      CoreHyp (RaySmall.{0} S.toIdempotents.RayCategory) ∧
        (letI := isRayCategory_of_finiteRayCategory (C := (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ)
         CoreHyp (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ)

/-- **Only deep contours from the core case, for one algebra** ([mild] Lemma 2.1, duality,
and the bridge from the reversed ray paths). -/
theorem SplitBasicData.deep_of_core (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B]
    [Algebra k B] [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : SplitBasicData k B ι) (hB : IsMinimalRepInfinite B) (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    letI := S.isFiniteRayCategory hd
    letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
    letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
    letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
    CoreHyp (RaySmall.{0} S.toIdempotents.RayCategory) →
      (letI := isRayCategory_of_finiteRayCategory (C := (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ)
       CoreHyp (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ) →
      ∀ {i j : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i j},
        (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := S.toIdempotents.RayCategory))).interlaced p q →
        S.toIdempotents.IsBGRSDeepRayPath p := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro hcore hcoreo i j p q hpq hni
  have hM := S.mildHyp hB hd
  have hMo := hM.op
  have hE := S.endCyclic
  have h0 : pathVal (toP p) ≠ 0 := by
    rw [pathVal_toP]; exact fun h ↦ hpq.1 ((RaySmall.sh_eq_zero_iff _).1 h)
  obtain ⟨hy, hx⟩ := MildContour.deep_of_contour (k := k) hM hMo hE hcore hcoreo (toP p) (toP q)
    (by rw [pathVal_toP, pathVal_toP, hpq.2]) h0 (not_interlaced_toP hpq.1 hni)
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · have hi := S.not_isIso_unitRay_of_mem_jacobson a ha
    have := hx (RaySmall.sh (unitRay a.asHom)) (fun h ↦ hi ((RaySmall.isIso_sh_iff _).1 h))
    rw [pathVal_toP, ← RaySmall.sh_comp, RaySmall.sh_eq_zero_iff] at this
    exact this
  · have hi := S.not_isIso_unitRay_of_mem_jacobson b hb
    have := hy (RaySmall.sh (unitRay b.asHom)) (fun h ↦ hi ((RaySmall.isIso_sh_iff _).1 h))
    rw [pathVal_toP, ← RaySmall.sh_comp, RaySmall.sh_eq_zero_iff] at this
    exact this

/-- **`OnlyDeepNode` from the core case** ([mild] Lemma 2.1, duality, and the
bridge from the reversed ray paths). -/
theorem onlyDeepNode_of_core (h : OnlyDeepCoreNode.{u}) : OnlyDeepNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  exact S.deep_of_core k B ι hB hd (h k B ι S hB hd).1 (h k B ι S hB hd).2

end LargeIndecomposable
