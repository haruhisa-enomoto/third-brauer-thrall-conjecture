module

public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisFromDeep
public import LargeIndecomposable.MildContours.Setup.RayPathBridge
public import LargeIndecomposable.MildContours.Setup.EndCyclic
public import LargeIndecomposable.MildContours.Setup.SetupOp

/-!
# `OnlyDeepContours` from the core case of [mild]

[mild] Lemma 2.1 and duality (`RayCat.MildContour.deep_of_contour`) reduce
Bongartz's Theorem 3 ("contours of a minimal representation-infinite ray
category are deep") to the core case (`ρ = π(y)` factors through the last
arrow of `v`) for the small ray category `P` of `B` and for `Pᵒᵖ`
(`OnlyDeepContoursCore`); `MildHyp` passes to `Pᵒᵖ` (`RayCat.MildHyp.op`). Through the bridge
from the reversed ray paths (`RayCat.toP`) this gives `OnlyDeepContours`
(`onlyDeepContours_of_core`).
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

end LargeIndecomposable
