module

public import LargeIndecomposable.BongartzTheorem.Reduction.Corollaries
public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.Monomial
public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.SimpleInjectiveFacts
public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerPair
public import LargeIndecomposable.KroneckerBricks.Small
public import LargeIndecomposable.KroneckerBricks.Singular

/-!
# The main results from the data form of Bongartz's Theorem 6

`BongartzDistributive` is the data form of alternatives (2) and (3) of Theorem
3.10 (Bongartz's Theorem 6 and its proof) for distributive algebras: every
distributive split basic minimal representation-infinite algebra over an
algebraically closed field carries covering data with a Kronecker pair (`Covering.PairCoveringData.toCoveringData` builds `L`), or a monomial
presentation with a band (`Walk.MonomialBand.toWalkData` turns a band into walk
data). The representation-embedding property of
the push-down functors is not assumed: the facts about `S₋` (`RepresentationEmbeddings/WalkConstruction/WalkCase.lean`,
`RepresentationEmbeddings/CoveringConstruction/SimpleInjectiveFacts.lean`) and Propositions 4.4, 4.7, 4.8 supply what Theorem 2.7
needs. Alternative (1), for
nondistributive algebras, is proved in `NonDistributive`.

By Propositions 4.4, 4.7 and 4.8 (`PushDown.PdDatum.embeddingData`), it
implies the hypothesis `DistributiveEmbeddingData`, and hence Theorem A
and the two corollaries.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement

universe u

/-- The data form of Bongartz's Theorem 6 in the distributive case: alternative
(2) or (3) of Theorem 3.10. -/
def BongartzDistributive : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι], SplitBasicData k B ι →
      IsMinimalRepInfinite B → IsDistribIdeals B →
        Nonempty (Covering.PairCoveringData k B) ∨ Nonempty (Walk.MonomialBand k B)

/-- Theorem 3.10 for distributive algebras, from the data form of Bongartz's
Theorem 6. -/
theorem distributiveEmbeddingData_of_bongartz (H : BongartzDistributive.{u}) :
    DistributiveEmbeddingData.{u} := by
  intro k _ _ B _ _ _ ι _ S hB hd
  rcases H k B ι S hB hd with h | h
  · obtain ⟨W⟩ := h
    exact ⟨W.toCoveringData.embeddingData⟩
  · obtain ⟨W⟩ := h
    exact ⟨W.toWalkData.embeddingData⟩

/-- Theorem A, conditional on the data form of Bongartz's Theorem 6. -/
theorem theoremA_of_bongartz (H : BongartzDistributive.{u}) : TheoremA.{u} :=
  theoremA_of_distributiveEmbeddingData (distributiveEmbeddingData_of_bongartz H)

/-- Corollary 1.1 (an indecomposable module of every infinite dimension),
conditional on Bongartz's Theorem 6 and Kronecker bricks of every infinite
dimension. -/
theorem corollaryDimension_of_bongartz (H : BongartzDistributive.{u})
    (G : KroneckerBricks.{u}) : CorollaryDimension.{u} :=
  corollaryDimension_of (distributiveEmbeddingData_of_bongartz H) G

/-- The radical corollary, conditional on Bongartz's Theorem 6 and Kronecker
bricks of every infinite dimension. -/
theorem corollaryRadical_of_bongartz (H : BongartzDistributive.{u})
    (G : KroneckerBricks.{u}) : CorollaryRadical.{u} :=
  corollaryRadical_of (distributiveEmbeddingData_of_bongartz H) G


/-- Göbel–Simson, Corollary 1.3: Kronecker bricks of every infinite dimension. -/
theorem kroneckerBricks : KroneckerBricks.{u} :=
  kroneckerBricks_of_large kroneckerBricksLarge

/-- Corollary 1.1 (an indecomposable module of every infinite dimension),
conditional only on the data form of Bongartz's Theorem 6. -/
theorem corollaryDimension_of_bongartz' (H : BongartzDistributive.{u}) :
    CorollaryDimension.{u} :=
  corollaryDimension_of_bongartz H kroneckerBricks

/-- The radical corollary, conditional only on the data form of Bongartz's
Theorem 6. -/
theorem corollaryRadical_of_bongartz' (H : BongartzDistributive.{u}) :
    CorollaryRadical.{u} :=
  corollaryRadical_of_bongartz H kroneckerBricks

end LargeIndecomposable
