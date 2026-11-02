module

public import LargeIndecomposable.BongartzTheorem.LongLines.LinesToBands
public import LargeIndecomposable.Coverings.Pieces.PairRestrict

/-!
# Critical pieces without a support condition

The Kronecker pair of a critical piece need not be supported at every vertex of the piece:
covering data are obtained after restricting the pair to its support
(`PairCoveringData.ofPair`). `CriticalPieceCarriesPair` and `CoverDichotomy` have no support
condition.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement RayCat RayCat.Cover RayQuiver Covering

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- Covering data with a Kronecker pair from a convex piece, without a support condition. -/
def pairCoveringData' (e : Linearization P k ≃ₐ[k] A)
    (htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    (S : Finset (Cover x₀)) (hS : Convex (S : Set (Cover x₀)))
    (K : KroneckerPair k (pieceQuiver S))
    (h₁ : RespectsCover (K.functor.obj (SminusK k)))
    (h₂ : RespectsCover (K.functor.obj (P1K k))) : PairCoveringData k A :=
  PairCoveringData.ofPair (pieceQuiver S) (quiver P) (pieceProj S) (pieceProj_locInj S)
    (coverPieceData S htf) K ((e : Linearization P k →ₐ[k] A).comp (linPres P k))
    (e.surjective.comp (linPres_surjective P k))
    (fun T z hz ↦ K.kills_of_generators _ z
      (pdAct_eq_zero_of_linPres hS h₁ z (e.injective (by simpa using hz)))
      (pdAct_eq_zero_of_linPres hS h₂ z (e.injective (by simpa using hz))) _)

end RayCat

/-- Without a support condition: a critical piece carries a Kronecker pair. -/
def CriticalPieceCarriesPair : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      ∀ (_ : Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k ≃ₐ[k] B)
        (x₀ : RaySmall.{0} S.toIdempotents.RayCategory),
        (∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
        ∀ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) → ¬PieceRepFin k C →
          (∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < C.card →
            PieceRepFin k C') →
          ∃ (Sp : Finset (Cover x₀)) (_ : Convex (Sp : Set (Cover x₀)))
            (K : KroneckerPair k (pieceQuiver Sp)),
              RespectsCover (K.functor.obj (SminusK k)) ∧ RespectsCover (K.functor.obj (P1K k))

/-- The dichotomy on the universal cover, without a support condition. -/
def CoverDichotomy : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      ∀ (_ : Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k ≃ₐ[k] B)
        (x₀ : RaySmall.{0} S.toIdempotents.RayCategory),
        (∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
          (∃ (Sp : Finset (Cover x₀)) (_ : Convex (Sp : Set (Cover x₀)))
            (K : KroneckerPair k (pieceQuiver Sp)),
              RespectsCover (K.functor.obj (SminusK k)) ∧ RespectsCover (K.functor.obj (P1K k))) ∨
          Nonempty (Walk.MonomialBand k B)

theorem coverDichotomy_of (hC : CriticalPieceCarriesPair.{u}) (hL : RepFinitePiecesGiveBand.{u}) : CoverDichotomy.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf
  classical
  by_cases h : ∃ n, ∃ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) ∧ ¬PieceRepFin k C ∧
      C.card = n
  · left
    obtain ⟨C, hC1, hC2, hC3⟩ := Nat.find_spec h
    refine hC k B ι S hB hd e x₀ htf C hC1 hC2 fun C' hC' hlt ↦ ?_
    by_contra hC''
    exact Nat.find_min h (hC3 ▸ hlt) ⟨C', hC', hC'', rfl⟩
  · right
    push Not at h
    exact hL k B ι S hB hd e x₀ htf fun C hC ↦ by
      by_contra h'
      exact h _ C hC h' rfl

/-- **Bongartz's Theorem 6 (data form)** from its steps, without a support condition. -/
theorem bongartzDistributive_of_steps (hStd : AlgebraIsLinearization.{u}) (hCrown : CrownCase.{u})
    (hDich : CoverDichotomy.{u}) : BongartzDistributive.{u} := by
  intro k _ _ B _ _ _ ι _ S hB hd
  classical
  have hι := S.nonempty_of_minimal hB
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  obtain ⟨e⟩ := hStd k B ι S hB hd
  let x₀ : RaySmall.{0} S.toIdempotents.RayCategory :=
    ⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩
  have hfree : ∀ X : FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory), IsFreeGroup (End X) := by
    by_cases hCB : ChainBounded S.toIdempotents.RayCategory
    · exact S.small_isFreeGroup_end hd hB hCB
    · exact hCrown k B ι S hB hd hCB
  have htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1 := fun g hg n hn ↦
    aut_pow_ne_one_of_isFreeGroup_end _ (hfree _) g hg n hn
  rcases hDich k B ι S hB hd e x₀ htf with ⟨Sp, hS, K, h₁, h₂⟩ | hband
  · exact Or.inl ⟨pairCoveringData' e htf Sp hS K h₁ h₂⟩
  · exact Or.inr hband

/-- **Bongartz's Theorem 6 (data form)** from the support-free dichotomy. -/
theorem bongartzDistributive_of_coverDichotomy (hDich : CoverDichotomy.{u}) :
    BongartzDistributive.{u} :=
  bongartzDistributive_of_steps
    (algebraIsLinearization_of_mulBasis twistedMulBasisExists
      (crownSecondCohomologyVanishes_of (crownLongSecondCohomologyVanishes_of (bongartzProposition2_of twistedMulBasisExists
        (longMorphismNotInContour_of_mulBasis twistedMulBasisExists)))))
    (crownCase_of (crownLongCase_of (bongartzProposition2_of twistedMulBasisExists
      (longMorphismNotInContour_of_mulBasis twistedMulBasisExists)))) hDich

end LargeIndecomposable
