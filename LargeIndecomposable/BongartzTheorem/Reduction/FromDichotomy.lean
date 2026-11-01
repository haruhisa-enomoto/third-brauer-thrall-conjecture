module

public import LargeIndecomposable.MildContours.Basic.ExcAssembly
public import LargeIndecomposable.Crowns.Basic.LongNotInContour
public import LargeIndecomposable.BongartzTheorem.Reduction.DataForm
public import LargeIndecomposable.BongartzTheorem.Reduction.DichotomySteps

/-!
# The main results from the dichotomy node alone

`ScalarNode` is proved (`MildContours/Basic/ExcAssembly.lean`), so BGRS multiplicative bases hold
(`mulBasisNode_of_scalar`). Bongartz's Theorem 6, Theorem A and both corollaries
now depend only on `DichotomyNode` (the dichotomy on the universal cover).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open Statement

universe u

/-- **BGRS multiplicative bases** for minimal representation-infinite distributive
algebras. -/
theorem mulBasisNode : MulBasisNode.{u} := mulBasisNode_of_scalar scalarNode

/-- **Bongartz's Theorem 6 (data form)** from the dichotomy on the universal cover. -/
theorem bongartzDistributive_of_dichotomy (hDich : DichotomyNode.{u}) :
    BongartzDistributive.{u} :=
  bongartzDistributive_of_mulBasis_dichotomy mulBasisNode hDich

/-- **Theorem A** from the dichotomy on the universal cover. -/
theorem theoremA_of_dichotomy (hDich : DichotomyNode.{u}) : TheoremA.{u} :=
  theoremA_of_bongartz (bongartzDistributive_of_dichotomy hDich)

/-- **Corollary 1.1** from the dichotomy on the universal cover. -/
theorem corollaryDimension_of_dichotomy (hDich : DichotomyNode.{u}) : CorollaryDimension.{u} :=
  corollaryDimension_of_bongartz' (bongartzDistributive_of_dichotomy hDich)

/-- **The radical corollary** from the dichotomy on the universal cover. -/
theorem corollaryRadical_of_dichotomy (hDich : DichotomyNode.{u}) : CorollaryRadical.{u} :=
  corollaryRadical_of_bongartz' (bongartzDistributive_of_dichotomy hDich)

/-- **Theorem A** from the critical-piece node and the line node. -/
theorem theoremA_of_critical_line (hC : CriticalNode.{u}) (hL : LineNode.{u}) : TheoremA.{u} :=
  theoremA_of_dichotomy (dichotomyNode_of hC hL)

/-- **Corollary 1.1** from the critical-piece node and the line node. -/
theorem corollaryDimension_of_critical_line (hC : CriticalNode.{u}) (hL : LineNode.{u}) :
    CorollaryDimension.{u} :=
  corollaryDimension_of_dichotomy (dichotomyNode_of hC hL)

/-- **The radical corollary** from the critical-piece node and the line node. -/
theorem corollaryRadical_of_critical_line (hC : CriticalNode.{u}) (hL : LineNode.{u}) :
    CorollaryRadical.{u} :=
  corollaryRadical_of_dichotomy (dichotomyNode_of hC hL)

end LargeIndecomposable
