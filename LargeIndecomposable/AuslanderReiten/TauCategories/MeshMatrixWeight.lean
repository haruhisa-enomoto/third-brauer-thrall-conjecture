module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.AlgebraicallyClosedResidue
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaKrullSchmidtWeight
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaReversedDomination
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaKrullSchmidtDirectFinite
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaRightLadderIteration
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaLadderRadical
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import LargeIndecomposable.AuslanderReiten.TauCategories.FiniteTauCategory
public import LargeIndecomposable.Foundations.CategoryTheory.SplitMorphismComplement
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mesh-matrix evaluation of additive label weights

The categorical Euler defect of a label weight on a chosen right mesh is the
corresponding weighted column sum of the mesh matrix.  This identifies the
matrix unit equations in the frozen manuscript with Iyama's positive
right-additivity hypothesis.

## References

* *The magnitude conjecture for module categories*, <https://github.com/haruhisa-enomoto/magnitude-conjecture>. Numbered statements cited here refer to it.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace LargeIndecomposable.FiniteTauMatrix

open LargeIndecomposable.Iyama

universe s v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

variable (T : FiniteTauCategoryData C Ind)

/-- Regrouping an integral weight over middle-term occurrences by label. -/
theorem sum_arrowMultiplicity_mul_int (target : Ind) (weight : Ind → ℤ) :
    ∑ source, (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) * weight source =
      ∑ i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData target),
        weight (rightMiddleLabel T.toFiniteRightTauCategoryData target i) := by
  classical
  simp only [arrowMultiplicity, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- The additive extension of a label weight evaluates the chosen right
middle term by the arrow-occurrence sum. -/
theorem additiveLabelWeight_rightMiddle (weight : Ind → ℤ) (target : Ind) :
    (T.additiveObjectWeightOfLabelWeight weight).weight
        (T.rightMesh (T.obj target)).X₂ =
      ∑ source, (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) * weight source := by
  let W := T.additiveObjectWeightOfLabelWeight weight
  obtain ⟨e⟩ := rightMiddleIso T.toFiniteRightTauCategoryData target
  calc
    W.weight (T.rightMesh (T.obj target)).X₂ =
        W.weight (⨁ fun i ↦ T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData target i)) :=
      W.iso_invariant ⟨e⟩
    _ = ∑ i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData target),
        W.weight (T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData target i)) :=
      W.weight_biproduct _
    _ = ∑ i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData target),
        weight (rightMiddleLabel T.toFiniteRightTauCategoryData target i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact T.additiveObjectWeightOfLabelWeight_obj weight _
    _ = ∑ source,
        (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) * weight source :=
      (sum_arrowMultiplicity_mul_int T target weight).symm

/-- Weighted column sum of that paper-oriented mesh matrix. -/
def meshColumnWeight [DecidablePred T.IsProjective]
    (weight : Ind → ℤ) (target : Ind) : ℤ :=
  ∑ source, weight source * meshMatrix T source target

end LargeIndecomposable.FiniteTauMatrix
