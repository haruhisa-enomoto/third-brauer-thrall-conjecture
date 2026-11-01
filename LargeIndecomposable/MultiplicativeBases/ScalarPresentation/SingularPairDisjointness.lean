module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayOpposite
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure16Retraction
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure15Retraction
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.NormalizedLift

@[expose] public section

/-!
# Singular-pair disjointness

Use opposite-algebra reversal to turn common-second singular pairs into the
common-first configuration excluded by the exact Figure-16 theorem.  Combining
the two orientations with the cross-position transit obstruction yields full
singular-pair disjointness and hence a global zero-detecting normalized lift.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalFigure16Quotient

open LargeIndecomposable.SingularPairNormalization
open LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [HasBGRSPairDichotomy S.ProjectiveCategory]
variable [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]

/-- Two singular pairs with the same second arrow are equal, by reversing
them over the opposite algebra and applying the common-first theorem. -/
theorem singularPair_eq_of_secondArrow_eq
    [Infinite k]
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hfiniteOp : LargeIndecomposable.MildAlg k Aᵐᵒᵖ)
    [HasBGRSDistributiveHomStructure k S.op.ProjectiveCategory]
    (p q : SingularPair (C := S.ProjectiveCategory))
    (hsecond : p.1.secondArrow = q.1.secondArrow) : p = q := by
  let i : S.ProjectiveCategory := p.1.source.obj.as
  have he : S.idempotent (S.projectiveVertex i) ≠ 0 := by
    intro hezero
    apply ProjectiveCategory.id_ne_zero S i
    apply Subtype.ext
    exact hezero
  letI : Nontrivial A := ⟨⟨S.idempotent (S.projectiveVertex i), 0, he⟩⟩
  letI : HasBGRSPairDichotomy S.op.ProjectiveCategory := inferInstance
  let pOp := S.opSingularPair p
  let qOp := S.opSingularPair q
  have hfirstOp : pOp.1.firstArrow = qOp.1.firstArrow := by
    simpa [pOp, qOp] using congrArg S.opArrow hsecond
  have hpqOp : pOp = qOp :=
    singularPair_eq_of_firstArrow_eq S.op hfiniteOp pOp qOp hfirstOp
  have hsecondOp := congrArg
    (fun r : SingularPair (C := S.op.ProjectiveCategory) ↦
      r.1.secondArrow) hpqOp
  have hfirst : p.1.firstArrow = q.1.firstArrow := by
    apply S.opArrow_injective
    simpa [pOp, qOp] using hsecondOp
  exact singularPair_eq_of_firstArrow_eq S hfinite p q hfirst

/-- Any two singular pairs sharing an arrow in either position are equal. -/
theorem singularPair_eq_of_sharedArrow
    [Infinite k]
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hfiniteOp : LargeIndecomposable.MildAlg k Aᵐᵒᵖ)
    [HasBGRSDistributiveHomStructure k S.op.ProjectiveCategory]
    (p q : SingularPair (C := S.ProjectiveCategory))
    (hshare : p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow) : p = q := by
  apply LargeIndecomposable.CriticalSingularFigure16Pairs.singularPair_eq_of_samePosition_disjoint
    (k := k)
    (singularPair_eq_of_firstArrow_eq S hfinite)
    (singularPair_eq_of_secondArrow_eq S hfinite hfiniteOp)
    p q hshare

/-- Representation-finiteness supplies a single representative of every
irreducible ray arrow whose path map detects exactly the zero BGRS paths. -/
theorem exists_zeroDetectingNormalizedLift
    [Infinite k]
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hfiniteOp : LargeIndecomposable.MildAlg k Aᵐᵒᵖ)
    [HasBGRSDistributiveHomStructure k S.op.ProjectiveCategory]
    [LargeIndecomposable.IsFiniteRayCategory S.RayCategory] :
    ∃ L : LargeIndecomposable.BGRSRayArrowLift
        (C := S.ProjectiveCategory),
      ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory}
        (p : Quiver.Path i j),
        L.pathMap p = 0 ↔ LargeIndecomposable.rayPathMap p = 0 := by
  exact LargeIndecomposable.exists_zeroDetectingNormalizedLift_of_no_long_critical
    (k := k)
    (LargeIndecomposable.CriticalFigure15Quotient.no_long_critical S hfinite)
    (singularPair_eq_of_sharedArrow S hfinite hfiniteOp)

end LargeIndecomposable.CriticalFigure16Quotient

