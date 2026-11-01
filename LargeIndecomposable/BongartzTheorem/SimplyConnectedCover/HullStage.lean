module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullReduction
public import LargeIndecomposable.BongartzTheorem.LongLines.LineSplit
public import LargeIndecomposable.FundamentalGroups.SimplyConnectedStages.ChainHull
public import LargeIndecomposable.FundamentalGroups.SimplyConnectedStages.ReductionStep

/-!
# `HullNode` from Satz 5.1

As `hullNode_of_chainHull`, with the chain-bounded case supplied by `hullFinite_of_chainBounded`
(Satz 5.1 from `StageStepNode`, proved in `stageStepNode`). The connectedness it needs holds for the ray category of a
minimal representation-infinite algebra and passes to the residue `P/μ` (`resFGEquiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Statement

universe u

/-- **`HullNode` from the reduction step.** -/
theorem hullNode_of_stage (hS : StageStepNode) : HullNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro _ x₀ _
  have hι := S.nonempty_of_minimal hB
  have : Nonempty (RaySmall.{0} S.toIdempotents.RayCategory) :=
    ⟨⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩⟩
  have hcon : IsConnected (FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory)) :=
    isConnected_fund_of_nzConnected fun x y ↦ RaySmall.nzConnected
      (S.nzConnected hd (fun e he hc ↦ hB.central_idempotent e he hc) x.as y.as)
  by_cases hCB : ChainBounded S.toIdempotents.RayCategory
  · exact hullFinite_of_chainBounded hS _ (RaySmall.leftCancel (S.leftCancel hd))
      (RaySmall.rightCancel (S.rightCancel hd)) (RaySmall.chainBounded hCB) hcon x₀
  by_cases hL : HasLong (RaySmall.{0} S.toIdempotents.RayCategory)
  swap
  · exact hullFinite_of_not_hasLong hL
  letI := S.isFiniteRayCategory hd
  obtain ⟨a, b, μ, hμ, hμr, hμ0, hlong, hcont, hCB'⟩ :=
    prop2Node_of mulBasisNode (longNotInContourNode_of_mulBasis mulBasisNode) k B ι S hB hd hCB hL
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
  exact hullFinite_of_residue μ hμ hμr hμ0 hlong hcont
    (hullFinite_of_chainBounded hS _ (leftCancel_quotient _ (RaySmall.leftCancel (S.leftCancel hd)))
      (rightCancel_quotient _ (RaySmall.rightCancel (S.rightCancel hd))) hCB' hcon' _)

/-- **Theorem A** from the remaining nodes. -/
theorem theoremA_of_stage (hC : CriticalNode.{u}) (hS : StageStepNode) (hD : D7Node.{u}) :
    TheoremA.{u} :=
  theoremA_of_nodes hC (hullNode_of_stage hS) hD

/-- **Corollary 1.1** from the remaining nodes. -/
theorem corollaryDimension_of_stage (hC : CriticalNode.{u}) (hS : StageStepNode)
    (hD : D7Node.{u}) : CorollaryDimension.{u} :=
  corollaryDimension_of_nodes hC (hullNode_of_stage hS) hD

/-- **The radical corollary** from the remaining nodes. -/
theorem corollaryRadical_of_stage (hC : CriticalNode.{u}) (hS : StageStepNode)
    (hD : D7Node.{u}) : CorollaryRadical.{u} :=
  corollaryRadical_of_nodes hC (hullNode_of_stage hS) hD

/-- **`HullNode`** (interval-finiteness of the universal cover), proved. -/
theorem hullNode : HullNode.{u} := hullNode_of_stage stageStepNode

/-- **Theorem A** from the two remaining nodes. -/
theorem theoremA_of_critical_d7 (hC : CriticalNode.{u}) (hD : D7Node.{u}) : TheoremA.{u} :=
  theoremA_of_stage hC stageStepNode hD

/-- **Corollary 1.1** from the two remaining nodes. -/
theorem corollaryDimension_of_critical_d7 (hC : CriticalNode.{u}) (hD : D7Node.{u}) :
    CorollaryDimension.{u} :=
  corollaryDimension_of_stage hC stageStepNode hD

/-- **The radical corollary** from the two remaining nodes. -/
theorem corollaryRadical_of_critical_d7 (hC : CriticalNode.{u}) (hD : D7Node.{u}) :
    CorollaryRadical.{u} :=
  corollaryRadical_of_stage hC stageStepNode hD

end LargeIndecomposable.RayCat
