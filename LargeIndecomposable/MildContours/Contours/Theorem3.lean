module

public import LargeIndecomposable.MildContours.PennyFarthings.Contour

/-!
# [mild] Theorem 3, the core case: assembly

`CoreHyp P` (no mild contour with `ρ = ω' ≫ α`) from the three cases of [mild]
Lemma 2.2: penny-farthing (`ω'` invertible, the arrow before `α` is `α`),
dumb-bell (`ω'` invertible, the arrow before `α` is `β`) and diamond (`ω'` not
invertible).

The penny-farthing case is split into the closed case
(`PFData.closed_false`: `ρ³` is projective-injective) and the open case
(`PFData.open_false`, a tiny penny-farthing point), the latter possibly in
`Pᵒᵖ`.

The hypotheses of `coreHyp` are `PFOpenStmt`, `DBStmt` and `DiamondStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

universe w

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type w} [Field k] [Infinite k]

/-- Contour data in case (DB) of [mild] Lemma 2.2: `v = q β α`, `w = w' β`,
`α` a loop at `y` with `ρ = α`. -/
structure DBData (x y : RayVert P) where
  α : y ⟶ y
  t : RayVert P
  w' : Quiver.Path x t
  β : t ⟶ y
  q : Quiver.Path x t
  hval : pathVal ((q.cons β).cons α) = pathVal (w'.cons β)
  h0 : pathVal ((q.cons β).cons α) ≠ 0
  hni : ¬Interlaced ((q.cons β).cons α) (w'.cons β)
  hρ : ∀ f : y.out ⟶ y.out, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow α.1 n
  hωρ : pathVal ((q.cons β).cons α) ≫ α.1 ≠ 0

variable (k P) in
/-- **[mild] Theorem 3, diamond case** (PD, LD, MID). (Open statement.) -/
def DiamondStmt : Prop :=
  ∀ {x y : P} (C : MildContour x y) (ω' : y ⟶ C.sv), ¬IsIso ω' → C.ρ = ω' ≫ C.α.1 →
    MildHyp k P → MildHyp k Pᵒᵖ → EndCyclic P → NoProjInj P → NoTiny P → NoTiny Pᵒᵖ → False

end RayCat

end LargeIndecomposable
