module

public import LargeIndecomposable.Coverings.UniversalCover.CoverGoodOp
public import LargeIndecomposable.Coverings.UniversalCover.GCoverHull
public import LargeIndecomposable.Coverings.UniversalCover.GCoverVolt

/-!
# Fischbacher's Satz 5.1 from the reduction step

`StageStepNode` is the reduction step of Satz 5.1: if `P` has reduction data (Lemma 2.1) and is
loop-free, a good universal cover of `P/⟨αᵢ⟩` (at every point) gives a good universal cover of
`P`. Induction on the number of arrows along Lemma 2.1 (up to duality, `coverGood_of_op`), with
the base case of no essential contours (`coverGood_of_noEss`), gives good covers of all finite
loop-free chain-bounded ray categories with cancellation (`coverGood_of_stage`). A finite
connected chain-bounded ray category with cancellation has a loop-free finite Galois cover
(`exists_loopFree_gcover`), whose good cover makes that of `P` good
(`hullFinite_of_chainBounded`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Opposite

attribute [local instance] isRayCategory_of_finiteRayCategory

/-- **The reduction step of Satz 5.1.** -/
def StageStepNode : Prop :=
  ∀ (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] [LargeIndecomposable.IsFiniteRayCategory0 Q]
    [Finite Q] {ι : Type} {b : Q} {d : ι → Q} {α : ∀ i, b ⟶ d i} (hα : ∀ i, ¬IsIso (α i))
    (D : RedData α), D.EssHyp (hα := hα) → LeftCancel Q → RightCancel Q → ChainBounded Q →
    LoopFree Q →
    (letI := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
      ∀ y : ArrowQuot α, CoverGood y) →
    ∀ x₀ : Q, CoverGood x₀

/-- **Good covers by induction along Lemma 2.1.** -/
theorem coverGood_of_stage (hS : StageStepNode) : ∀ (n : ℕ) (Q : Type) [Category.{0} Q]
    [HasZeroMorphisms Q] [LargeIndecomposable.IsFiniteRayCategory0 Q] [Finite Q],
    LeftCancel Q → RightCancel Q → ChainBounded Q → LoopFree Q → arrowCount Q ≤ n →
    ∀ x₀ : Q, CoverGood x₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ _ hL hR hCB hLF hn x₀
  by_cases hess : NoEssContour (P := Q)
  · letI := Fintype.ofFinite Q
    letI := Classical.decEq Q
    exact coverGood_of_noEss hess x₀
  · simp only [NoEssContour, not_forall] at hess
    obtain ⟨x, y, s, t, hst, h0, hi⟩ := hess
    rcases hasRedData_or_op hL hR hCB s t hst h0 hi with
      ⟨b, ι, d, α, hα, D, hE, -, hι⟩ | ⟨b, ι, d, α, hα, D, hE, -, hι⟩
    · have := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
      have hlt := arrowCount_quot_lt α hα D hι
      exact hS Q hα D hE hL hR hCB hLF (fun y ↦ ih _ (by omega) (ArrowQuot α)
        (leftCancel_quot α hL) (rightCancel_quot α hR) (chainBounded_quot α hCB)
        (loopFree_quot D hE hLF) le_rfl y) x₀
    · have := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
      have hlt := arrowCount_quot_lt α hα D hι
      rw [arrowCount_op] at hlt
      have hLFo : LoopFree Qᵒᵖ := loopFree_op hLF
      exact coverGood_of_op (hS Qᵒᵖ hα D hE (leftCancel_op hR) (rightCancel_op hL)
        (chainBounded_op hCB) hLFo (fun y ↦ ih _ (by omega) (ArrowQuot α)
          (leftCancel_quot α (leftCancel_op hR)) (rightCancel_quot α (rightCancel_op hL))
          (chainBounded_quot α (chainBounded_op hCB)) (loopFree_quot D hE hLFo) le_rfl y) (op x₀))

/-- **Fischbacher's Satz 5.1** (from the reduction step): a finite connected chain-bounded ray
category with cancellation has an interval-finite universal cover. -/
theorem hullFinite_of_chainBounded (hS : StageStepNode) (P : Type) [Category.{0} P]
    [HasZeroMorphisms P] [IsRayCategory P] [Finite P] [Fintype P] [DecidableEq P]
    (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    (hcon : IsConnected (FundGroupoid P)) (x₀ : P) : HullFinite x₀ := by
  letI := isFiniteRayCategory0_of_ray (C := P)
  have hfree : IsFreeGroup (End (vtx x₀)) := isFreeGroup_end_fund _ P hL hR hCB hcon le_rfl _
  have hℓ : ∀ y : P, Nonempty (vtx x₀ ⟶ vtx y) := fun y ↦
    nonempty_hom_of_preconnected_groupoid _ _
  obtain ⟨H, _, _, φ, hLF⟩ := exists_loopFree_gcover x₀ hfree fun y ↦ (hℓ y).some
  letI := isFiniteRayCategory0_of_ray (C := GCover (volt (fun y ↦ (hℓ y).some) φ))
  have hgood := coverGood_of_stage hS _ (GCover (volt (fun y ↦ (hℓ y).some) φ))
    (leftCancel_gcover hL) (rightCancel_gcover hR) (chainBounded_gcover hCB) hLF le_rfl ⟨x₀, 1⟩
  exact hullFinite_of_coverGood ⟨cycleFree_of_gcover hgood.1, intervalFinite_of_gcover hgood.2⟩

end LargeIndecomposable.RayCat
