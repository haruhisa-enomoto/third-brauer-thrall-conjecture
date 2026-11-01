module

public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteDistributiveHom
public import LargeIndecomposable.RayCategories.Contours.RayPathInterlacement
public import Mathlib.Tactic

@[expose] public section

/-!
# Four-arrow quotient obstructions and ray valency

This file isolates the exact quotient-extraction input needed to turn
representation-finiteness into global three-valency of a ray category.
Different quotient obstructions are allowed for outgoing and incoming forks.
Rigidity of irreducible ray arrows leaves two cases at either endpoint: four
noncentral neighbors, or one loop and three noncentral neighbors.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u₁ v₁ w₁ x₁

/-- The exact quotient-extraction interface needed to turn
representation-finiteness into the global three-valency bound.  It deliberately
allows different outward and inward obstruction quotients. -/
structure HasFourRayQuotientObstruction
    (k : Type u₁) [Field k] (A : Type v₁) [Ring A] [Algebra k A]
    (C : Type w₁) [Category.{x₁} C] [HasZeroMorphisms C] : Prop where
  outgoing : ∀ x : RayVertex C,
    4 ≤ Nat.card (OutgoingQuiverArrow x) →
      ∃ I : TwoSidedIdeal A,
        ¬IsRepresentationFinite k (A ⧸ I.asIdeal)
  incoming : ∀ z : RayVertex C,
    4 ≤ Nat.card (IncomingQuiverArrow z) →
      ∃ I : TwoSidedIdeal A,
        ¬IsRepresentationFinite k (A ⧸ I.asIdeal)

/-- Once every four-arrow fork extracts a representation-infinite quotient,
representation-finiteness forces global ray valency at most three. -/
theorem hasRayValencyAtMostThree_of_fourRayQuotientObstruction
    {k : Type u₁} [Field k] {A : Type v₁} [Ring A] [Algebra k A]
    {C : Type w₁} [Category.{x₁} C] [HasZeroMorphisms C]
    (hA : IsRepresentationFinite k A)
    (hfork : HasFourRayQuotientObstruction k A C) :
    HasRayValencyAtMostThree C where
  outgoing_card_le x := by
    by_contra hle
    have hfour : 4 ≤ Nat.card (OutgoingQuiverArrow x) := by omega
    obtain ⟨I, hI⟩ := hfork.outgoing x hfour
    exact hI (hA.quotient I)
  incoming_card_le z := by
    by_contra hle
    have hfour : 4 ≤ Nat.card (IncomingQuiverArrow z) := by omega
    obtain ⟨I, hI⟩ := hfork.incoming z hfour
    exact hI (hA.quotient I)

namespace SplitBasicIdempotents

universe u₂ v₂ x₂

variable {k : Type u₂} [Field k]
variable {A : Type v₂} [Ring A] [Algebra k A]
variable {ι : Type x₂} [Fintype ι] [DecidableEq ι]

/-- The concrete BGRS extraction interface.  For every vertex with four
outgoing or incoming irreducible rays, it asks for a
representation-infinite quotient.  The intended witness carries those arrows,
but this interface retains only the quotient property used downstream. -/
abbrev HasBGRSFourArrowQuotientObstruction
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [Module.Finite k A]
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] : Prop :=
  HasFourRayQuotientObstruction k A S.RayCategory

/-- After installing the distributive-Hom package provided by
representation-finiteness, four-ray quotient extraction implies the global
valency theorem. -/
theorem RayCategory.hasRayValencyAtMostThree_of_fourRayQuotientObstruction
    [Module.Finite k A] [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (hA : IsRepresentationFinite k A)
    (hfork :
      letI : HasBGRSDistributiveHomStructure k S.ProjectiveCategory :=
        ProjectiveCategory.bgrsDistributiveHomStructure_of_isRepresentationFinite
          S hA
      HasBGRSFourArrowQuotientObstruction S) :
    (letI : HasBGRSDistributiveHomStructure k S.ProjectiveCategory :=
      ProjectiveCategory.bgrsDistributiveHomStructure_of_isRepresentationFinite
        S hA
    HasRayValencyAtMostThree S.RayCategory) := by
  letI : HasBGRSDistributiveHomStructure k S.ProjectiveCategory :=
    ProjectiveCategory.bgrsDistributiveHomStructure_of_isRepresentationFinite
      S hA
  exact LargeIndecomposable.hasRayValencyAtMostThree_of_fourRayQuotientObstruction
    hA hfork

end SplitBasicIdempotents

end LargeIndecomposable
