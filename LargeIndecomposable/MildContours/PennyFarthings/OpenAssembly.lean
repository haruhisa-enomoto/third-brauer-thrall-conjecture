module

public import LargeIndecomposable.MildContours.PennyFarthings.OpenTwo
public import LargeIndecomposable.MildContours.Basic.Theorem3

/-!
# The open penny-farthing: [mild] LPF

`LPFStmt` ([mild] LPF): an open penny-farthing has `n = 2`; proved in
`MildContours/PennyFarthings/OpenLengthTwo.lean` (`RayCat.lpfStmt`). The case `n = 2` is handled: exit at `x₀` by a tiny point (`PFData.tiny_x0`), exits
only at `x₁` in `MildContours/PennyFarthings/OpenCase2.lean` (`PFData.case2_exc`), assembled in
`MildContours/Basic/CoreExc.lean` (`pfOpenStmt_of_exc`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

universe w

namespace RayCat

variable (P : Type) [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] (k : Type w) [Field k] [Infinite k]

/-- **[mild] LPF**: an open penny-farthing has `n = 2`. -/
def LPFStmt : Prop :=
  ∀ {x : RayVert P} (D : PFData x x), D.q = .nil → ∀ {c : RayVert P} (a₁ : x ⟶ c)
    (w₁ : Quiver.Path c D.t), D.w' = (Quiver.Path.nil.cons a₁).comp w₁ → MildHyp k P →
    MildHyp k Pᵒᵖ → EndCyclic P → ∀ {z : RayVert P} (μ : x.out ⟶ z.out), μ ≠ 0 →
    (¬∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁) →
    w₁.length = 0

end RayCat

end LargeIndecomposable
