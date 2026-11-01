module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineSplit
public import LargeIndecomposable.BongartzTheorem.Reduction.FromDichotomy

/-!
# Theorem A from the three remaining nodes

Theorem A, Corollary 1.1 and the radical corollary follow from `CriticalNode`,
`HullNode` (interval-finiteness of the universal cover) and `D7Node` (unbounded supports
over representation-finite pieces give a monomial band). Gabriel's covering theorem
is proved (`lineNode_of`).
-/

@[expose] public section

set_option autoImplicit false

namespace LargeIndecomposable

open Statement

universe u

/-- **Theorem A** from the remaining nodes. -/
theorem theoremA_of_nodes (hC : CriticalNode.{u}) (hH : HullNode.{u}) (hD : D7Node.{u}) :
    TheoremA.{u} :=
  theoremA_of_critical_line hC (lineNode_of hH hD)

/-- **Corollary 1.1** from the remaining nodes. -/
theorem corollaryDimension_of_nodes (hC : CriticalNode.{u}) (hH : HullNode.{u})
    (hD : D7Node.{u}) : CorollaryDimension.{u} :=
  corollaryDimension_of_critical_line hC (lineNode_of hH hD)

/-- **The radical corollary** from the remaining nodes. -/
theorem corollaryRadical_of_nodes (hC : CriticalNode.{u}) (hH : HullNode.{u})
    (hD : D7Node.{u}) : CorollaryRadical.{u} :=
  corollaryRadical_of_critical_line hC (lineNode_of hH hD)

end LargeIndecomposable
