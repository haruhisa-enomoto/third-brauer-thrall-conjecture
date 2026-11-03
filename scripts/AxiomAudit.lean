module

public import LargeIndecomposable
public import Solution

/-! Axiom report for the main theorems and their intermediate forms.
Run with `lake env lean scripts/AxiomAudit.lean`, or `python3 scripts/audit_axioms.py`. -/

@[expose] public section

#print axioms LargeIndecomposable.theoremA
#print axioms LargeIndecomposable.corollaryDimension
#print axioms LargeIndecomposable.corollaryRadical
#print axioms LargeIndecomposable.linesOfEveryLength
#print axioms LargeIndecomposable.theoremA_of_bongartz
#print axioms LargeIndecomposable.EmbeddingData.theoremA_conclusion
#print axioms LargeIndecomposable.SplitBasicData.nonempty_embeddingData
#print axioms LargeIndecomposable.Covering.PairCoveringData.toCoveringData
#print axioms LargeIndecomposable.Covering.CoveringData.embeddingData
#print axioms LargeIndecomposable.Walk.MonomialBand.toWalkData
#print axioms LargeIndecomposable.Walk.WalkData.embeddingData
#print axioms LargeIndecomposable.exists_brick_of_le_card
#print axioms LargeIndecomposable.kroneckerBricks_of_large
#print axioms LargeIndecomposable.SplitBasicData.presentation_surjective
#print axioms LargeIndecomposable.Challenge.theoremA
#print axioms LargeIndecomposable.Challenge.corollaryDimension
#print axioms LargeIndecomposable.Challenge.corollaryRadical
