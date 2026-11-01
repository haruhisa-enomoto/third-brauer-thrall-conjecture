module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullResidue
public import LargeIndecomposable.BongartzTheorem.Reduction.ThreeSteps

/-!
# `HullNode` from the chain-bounded case

Bongartz (*Indecomposables live in all smaller lengths*, proof of Theorem 2) splits into
three cases: no long morphism (`hullFinite_of_not_hasLong`), a crown and a long morphism
(reduce to `P/μ` by Proposition 2, `prop2Node_of`, and `hullFinite_of_residue`), and the
chain-bounded case (Fischbacher, Satz 5.1). The last case is the node `ChainHullNode`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Statement

universe u

/-- Fischbacher, Satz 5.1: a finite chain-bounded ray category has an interval-finite
universal cover. -/
def ChainHullNode : Prop :=
  ∀ (P : Type) [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Finite P],
    LeftCancel P → RightCancel P → ChainBounded P → ∀ x₀ : P, HullFinite x₀

/-- **`HullNode` from the chain-bounded case.** -/
theorem hullNode_of_chainHull (hC : ChainHullNode) : HullNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro _ x₀ _
  by_cases hCB : ChainBounded S.toIdempotents.RayCategory
  · exact hC _ (RaySmall.leftCancel (S.leftCancel hd)) (RaySmall.rightCancel (S.rightCancel hd))
      (RaySmall.chainBounded hCB) x₀
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
  exact hullFinite_of_residue μ hμ hμr hμ0 hlong hcont
    (hC _ (leftCancel_quotient _ (RaySmall.leftCancel (S.leftCancel hd)))
      (rightCancel_quotient _ (RaySmall.rightCancel (S.rightCancel hd))) hCB' _)

/-- **Theorem A** from the remaining nodes, with `HullNode` reduced to its chain-bounded
case. -/
theorem theoremA_of_chainHull (hC : CriticalNode.{u}) (hH : ChainHullNode)
    (hD : D7Node.{u}) : TheoremA.{u} :=
  theoremA_of_nodes hC (hullNode_of_chainHull hH) hD

/-- **Corollary 1.1** from the remaining nodes. -/
theorem corollaryDimension_of_chainHull (hC : CriticalNode.{u}) (hH : ChainHullNode)
    (hD : D7Node.{u}) : CorollaryDimension.{u} :=
  corollaryDimension_of_nodes hC (hullNode_of_chainHull hH) hD

/-- **The radical corollary** from the remaining nodes. -/
theorem corollaryRadical_of_chainHull (hC : CriticalNode.{u}) (hH : ChainHullNode)
    (hD : D7Node.{u}) : CorollaryRadical.{u} :=
  corollaryRadical_of_nodes hC (hullNode_of_chainHull hH) hD

end LargeIndecomposable.RayCat
