module

public import LargeIndecomposable.RayCategories.Quotients.MinimalQuotLin
public import LargeIndecomposable.RayCategories.Distributive.QuotientRayPresentations
public import LargeIndecomposable.FundamentalGroups.Basic.SmallFree
public import LargeIndecomposable.RayCategories.Distributive.Cancel
public import LargeIndecomposable.BongartzTheorem.Reduction.TheoremSix

/-!
# Setting for Bongartz's "On mild contours"

`MildHyp k P`: a finite ray category with cancellation all of whose proper
residues `P/τ` (`τ` nonzero, non-invertible) have representation-finite
linearization. Thin cleaving diagrams into a residue then give contradictions
(`MildHyp.not_thin_cleaving`). The ray category of a minimal
representation-infinite distributive algebra satisfies `MildHyp`
(`SplitBasicData.mildHyp`, via B5).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat RayQuiver

universe u

namespace RayCat

variable (k : Type u) [Field k] (P : Type) [Category.{0} P] [HasZeroMorphisms P]
  [LargeIndecomposable.IsFiniteRayCategory P] [Finite P]

/-- The hypotheses of [mild]: cancellation and representation-finite proper
residues. -/
structure MildHyp : Prop where
  left : LeftCancel P
  right : RightCancel P
  res : ∀ {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ), τ ≠ 0 →
    letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
    letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
    letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
    letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
    Statement.IsRepresentationFinite (Linearization (RayCat.Res τ) k)

variable {k P}

/-- **A representation-infinite thin diagram cannot cleave into a proper residue.** -/
theorem MildHyp.not_thin_cleaving [Infinite k] (h : MildHyp k P) {a b : P} (τ : a ⟶ b)
    (hτ : ¬IsIso τ) (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] {T : ThinData V}
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat T) k))
    (D : ThinFunctorData T (RayCat.Res τ)) (Ar : ThinArrows T)
    (hc : letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
      D.Cleaves Ar) : False := by
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
  have hfin := h.res τ hτ hτ0
  refine hD (isRepresentationFinite_of_cleaving (B := linMulBasis k (RayCat.Res τ))
    (F := D.functor) (D.isCleaving hc (leftCancel_quotient _ h.left) (rightCancel_quotient _ h.right))
    (fun _ _ _ ↦ rfl) hfin)

end RayCat

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)

/-- **The ray category of a minimal representation-infinite distributive
algebra satisfies the [mild] hypotheses** (B5 and minimality). -/
theorem mildHyp (hB : IsMinimalRepInfinite B) (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    letI := S.isFiniteRayCategory hd
    MildHyp k (RaySmall.{0} S.toIdempotents.RayCategory) := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  have hι := S.nonempty_of_minimal hB
  have : Nontrivial B := by
    obtain ⟨i⟩ := hι
    exact ⟨⟨S.e i, 0, S.ne_zero i⟩⟩
  refine ⟨RaySmall.leftCancel (S.leftCancel hd), RaySmall.rightCancel (S.rightCancel hd), ?_⟩
  intro a b τ hτ hτ0
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
  have hne : S.idealOf τ ≠ ⊥ := by
    intro h
    have hmem : (S.repP τ).1 ∈ S.idealOf τ := TwoSidedIdeal.subset_span rfl
    rw [h] at hmem
    exact hτ0 ((S.repP_eq_zero_iff τ).1 (Subtype.ext hmem))
  exact S.isRepresentationFinite_res τ hτ (hB.2 _ hne)

end SplitBasicData

end LargeIndecomposable
