module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResiduePath
public import LargeIndecomposable.RayCategories.ClosedChains.RayInfiniteChain

@[expose] public section

/-!
# Strict induction through ray residue categories

Package the finite induction which annihilates one maximal nonzero ray at a
time.  The only local input is an invisible correction on every maximal ray;
the principal residue has strictly fewer nonzero morphisms, and the concrete
morphism-depth rank closes the lift from quotient exactness.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {k : Type*} [Field k]
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Related ray paths cannot differ if one of them has length zero. -/
theorem rayPath_eq_of_related_of_length_eq_zero
    [IsFiniteRayCategory C]
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpZero : p.length = 0) : p = q := by
  have hpIso : IsIso (rayPathMap p) :=
    rayPathMap_isIso_of_length_eq_zero p hpZero
  have hqIso : IsIso (rayPathMap q) := by
    rw [← hpq.2]
    exact hpIso
  have hqZero : q.length = 0 := by
    by_contra hqNonzero
    exact rayPathMap_not_isIso_of_length_ne_zero q hqNonzero hqIso
  have hij : i = j := Quiver.Path.eq_of_length_zero p hpZero
  subst j
  rw [Quiver.Path.eq_nil_of_length_zero p hpZero,
    Quiver.Path.eq_nil_of_length_zero q hqZero]

/-- The source-faithful local input for finite residue induction: every
maximal nonzero path through an irreducible arrow admits one correction which
is invisible on surviving essential contours and clings on its whole ray. -/
def HasInvisibleCorrectionsOnMaximalRays
    (k : Type*) [Field k]
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [Finite C] [IsFiniteRayCategory C] : Prop :=
  ∀ (a : BundledQuiverArrow (RayVertex C))
      (p : NonzeroRayPathThroughArrow (C := C) a),
    p.IsMaximal →
      (principalZeroHomIdeal (rayPathMap p.path)).HasInvisibleCorrectionClingingOnIdeal
        (k := k)

/-- A one-arrow hook tackle built from one arrow of the reversed ray quiver. -/
def RayHookTackle.singletonRayArrow
    {i j : RayVertex C} (a : i ⟶ j) : RayHookTackle (C := C) 0 := by
  let f : NonzeroHom j.obj i.obj :=
    ⟨rayArrowMorphism a, a.property.1⟩
  refine
    { x := fun _ ↦ j.obj
      z := fun _ ↦ i.obj
      rho := fun _ ↦ f
      sigma := fun h ↦ Fin.elim0 h
      peak_incomparable := fun h ↦ Fin.elim0 h
      valley_incomparable := fun h ↦ Fin.elim0 h
      last_irreducible := ?_ }
  simpa [f, rayArrowMorphism] using a.property

/-- The last reversed-ray arrow of either shape of tackle. -/
def RayTackle.lastBundledArrow :
    RayTackle C → BundledQuiverArrow (RayVertex C)
  | .hook _ t => bundledQuiverArrow t.lastArrow
  | .cohook _ t => bundledQuiverArrow t.lastArrow

/-- The exact local input used in BGRS 8.6: only maximal rays through the last
arrow of an efficient tackle require an invisible correction. -/
def HasInvisibleCorrectionsOnEfficientMaximalRays
    (k : Type*) [Field k]
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [Finite C] [IsFiniteRayCategory C] : Prop :=
  ∀ (t : RayTackle C) (y : C), t.IsEfficientAt y →
    ∀ (p : NonzeroRayPathThroughArrow (C := C) t.lastBundledArrow),
      p.IsMaximal →
        (principalZeroHomIdeal (rayPathMap p.path)).HasInvisibleCorrectionClingingOnIdeal
          (k := k)

/-- Strict residue induction for contour cohomology.  The local hypothesis is
required uniformly for finite ray categories no larger than the original;
this is exactly the range containing every iterated principal residue. -/
theorem contourFunctionCohomologyVanishes_of_maximalRayResidueInduction
    [Finite C] [IsFiniteRayCategory C]
    (hlocal : ∀ (D : Type u) [Category.{v} D] [HasZeroMorphisms D]
        [Finite D] [IsFiniteRayCategory D],
      Nat.card (NonzeroCategoryMorphism D) ≤
          Nat.card (NonzeroCategoryMorphism C) →
        HasInvisibleCorrectionsOnMaximalRays k D) :
    ContourFunctionCohomologyVanishes (k := k)
      (rayPathContourRelation (C := C)) := by
  let originalCard := Nat.card (NonzeroCategoryMorphism C)
  have hmain : ∀ n : ℕ,
      ∀ (D : Type u) [Category.{v} D] [HasZeroMorphisms D]
        [Finite D] [IsFiniteRayCategory D],
        Nat.card (NonzeroCategoryMorphism D) = n →
        Nat.card (NonzeroCategoryMorphism D) ≤ originalCard →
        ∀ d : contourScalarFunctionSubgroup (k := k)
          (rayPathContourRelation (C := D)),
          IsExactContourFunction (rayPathContourRelation (C := D)) d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro D _ _ _ _ hcard hbound d
        let R := rayPathContourRelation (C := D)
        by_cases hd : d = 1
        · refine ⟨1, ?_⟩
          rw [hd]
          exact (contourFunctionCoboundaryHom (k := k) R).map_one
        · have hexists : ∃ gamma : RelatedContour R,
              contourScalarFamily R d gamma ≠ 1 := by
            by_contra hall
            push Not at hall
            apply hd
            apply Subtype.ext
            funext gamma
            change contourScalarFamily R d gamma = 1
            exact hall gamma
          obtain ⟨⟨⟨i, j, p, q⟩, hpq⟩, hvalue⟩ := hexists
          have hpLength : p.length ≠ 0 := by
            intro hpZero
            have hpqEq := rayPath_eq_of_related_of_length_eq_zero
              p q hpq hpZero
            subst q
            exact hvalue (contourScalarFunction_self R d p hpq)
          let dp := chosenPathInitialDecomposition p hpLength
          let a : BundledQuiverArrow (RayVertex D) :=
            bundledQuiverArrow dp.arrow
          obtain ⟨m, hm⟩ :=
            NonzeroRayPathThroughArrow.exists_isMaximal a
          let J := principalZeroHomIdeal (rayPathMap m.path)
          have hJ : J.IsProper :=
            principalZeroHomIdeal_isProper_of_not_isIso
              (rayPathMap m.path) m.map_not_isIso
          letI : IsFiniteRayCategory
              (RayResidueCategory (rayPathMap m.path)) :=
            rayResidueCategory_isFiniteRayCategory
              (rayPathMap m.path) m.map_not_isIso
          have hlt : Nat.card (NonzeroCategoryMorphism
                (RayResidueCategory (rayPathMap m.path))) < n := by
            rw [← hcard]
            exact m.residue_nonzeroMorphism_card_lt
          have hquotBound : Nat.card (NonzeroCategoryMorphism
                (RayResidueCategory (rayPathMap m.path))) ≤ originalCard :=
            calc
              _ ≤ n := Nat.le_of_lt hlt
              _ = Nat.card (NonzeroCategoryMorphism D) := hcard.symm
              _ ≤ originalCard := hbound
          have hquotExact : IsExactContourFunction
              (rayPathContourRelation
                (C := RayResidueCategory (rayPathMap m.path)))
              (J.quotOutContourScalarFunction hJ d) :=
            ih _ hlt (RayResidueCategory (rayPathMap m.path)) rfl
              hquotBound (J.quotOutContourScalarFunction hJ d)
          have hmaximalLocal :
              J.HasInvisibleCorrectionClingingOnIdeal (k := k) := by
            exact hlocal D (by simpa [originalCard] using hbound) a m hm
          exact J.isExactContourFunction_of_isExact_quotOut_of_invisibleCorrection_finite
            hJ d hmaximalLocal hquotExact
  rw [contourFunctionCohomologyVanishes_iff_forall_isExact]
  intro c
  exact hmain originalCard C rfl (by simp [originalCard]) c

/-- Source-faithful strict residue induction.  A nontrivial contour supplies
one arrow and hence a singleton tackle; maximize its efficiency at the same
start, annihilate a maximal path through the efficient tackle's last arrow,
and recurse on the strictly smaller residue. -/
theorem contourFunctionCohomologyVanishes_of_efficientMaximalRayResidueInduction
    [Finite C] [IsFiniteRayCategory C]
    [HasRayCancellation C] [HasNoInfiniteRayChain C]
    (hlocal : ∀ (D : Type u) [Category.{v} D] [HasZeroMorphisms D]
        [Finite D] [IsFiniteRayCategory D]
        [HasRayCancellation D] [HasNoInfiniteRayChain D],
      Nat.card (NonzeroCategoryMorphism D) ≤
          Nat.card (NonzeroCategoryMorphism C) →
        HasInvisibleCorrectionsOnEfficientMaximalRays k D) :
    ContourFunctionCohomologyVanishes (k := k)
      (rayPathContourRelation (C := C)) := by
  let originalCard := Nat.card (NonzeroCategoryMorphism C)
  have hmain : ∀ n : ℕ,
      ∀ (D : Type u) [Category.{v} D] [HasZeroMorphisms D]
        [Finite D] [IsFiniteRayCategory D]
        [HasRayCancellation D] [HasNoInfiniteRayChain D],
        Nat.card (NonzeroCategoryMorphism D) = n →
        Nat.card (NonzeroCategoryMorphism D) ≤ originalCard →
        ∀ d : contourScalarFunctionSubgroup (k := k)
          (rayPathContourRelation (C := D)),
          IsExactContourFunction (rayPathContourRelation (C := D)) d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro D _ _ _ _ _ _ hcard hbound d
        let R := rayPathContourRelation (C := D)
        by_cases hd : d = 1
        · refine ⟨1, ?_⟩
          rw [hd]
          exact (contourFunctionCoboundaryHom (k := k) R).map_one
        · have hexists : ∃ gamma : RelatedContour R,
              contourScalarFamily R d gamma ≠ 1 := by
            by_contra hall
            push Not at hall
            apply hd
            apply Subtype.ext
            funext gamma
            change contourScalarFamily R d gamma = 1
            exact hall gamma
          obtain ⟨⟨⟨i, j, p, q⟩, hpq⟩, hvalue⟩ := hexists
          have hpLength : p.length ≠ 0 := by
            intro hpZero
            have hpqEq := rayPath_eq_of_related_of_length_eq_zero
              p q hpq hpZero
            subst q
            exact hvalue (contourScalarFunction_self R d p hpq)
          let dp := chosenPathInitialDecomposition p hpLength
          let initialTackle : RayTackle D :=
            .hook 0 (RayHookTackle.singletonRayArrow dp.arrow)
          obtain ⟨t, ht⟩ := RayTackle.exists_isEfficientAt_of_bounded
            initialTackle.start ⟨initialTackle, rfl⟩
          let a := t.lastBundledArrow
          obtain ⟨m, hm⟩ :=
            NonzeroRayPathThroughArrow.exists_isMaximal a
          let J := principalZeroHomIdeal (rayPathMap m.path)
          have hJ : J.IsProper :=
            principalZeroHomIdeal_isProper_of_not_isIso
              (rayPathMap m.path) m.map_not_isIso
          letI : IsFiniteRayCategory
              (RayResidueCategory (rayPathMap m.path)) :=
            rayResidueCategory_isFiniteRayCategory
              (rayPathMap m.path) m.map_not_isIso
          letI : HasRayCancellation
              (RayResidueCategory (rayPathMap m.path)) :=
            J.quotientHasRayCancellation
          letI : HasNoInfiniteRayChain
              (RayResidueCategory (rayPathMap m.path)) :=
            J.quotientHasNoInfiniteRayChain
          have hlt : Nat.card (NonzeroCategoryMorphism
                (RayResidueCategory (rayPathMap m.path))) < n := by
            rw [← hcard]
            exact m.residue_nonzeroMorphism_card_lt
          have hquotBound : Nat.card (NonzeroCategoryMorphism
                (RayResidueCategory (rayPathMap m.path))) ≤ originalCard :=
            calc
              _ ≤ n := Nat.le_of_lt hlt
              _ = Nat.card (NonzeroCategoryMorphism D) := hcard.symm
              _ ≤ originalCard := hbound
          have hquotExact : IsExactContourFunction
              (rayPathContourRelation
                (C := RayResidueCategory (rayPathMap m.path)))
              (J.quotOutContourScalarFunction hJ d) :=
            ih _ hlt (RayResidueCategory (rayPathMap m.path)) rfl
              hquotBound (J.quotOutContourScalarFunction hJ d)
          have hmaximalLocal :
              J.HasInvisibleCorrectionClingingOnIdeal (k := k) := by
            exact hlocal D (by simpa [originalCard] using hbound)
              t initialTackle.start ht m hm
          exact J.isExactContourFunction_of_isExact_quotOut_of_invisibleCorrection_finite
            hJ d hmaximalLocal hquotExact
  rw [contourFunctionCohomologyVanishes_iff_forall_isExact]
  intro c
  exact hmain originalCard C rfl (by simp [originalCard]) c

/-- Source-faithful strict residue induction with the local start/stop
valency bound carried through every principal residue.  This version lets the
uniform local theorem use the valency bound at each recursive category. -/
theorem contourFunctionCohomologyVanishes_of_efficientMaximalRayResidueInduction_with_valency
    [Finite C] [IsFiniteRayCategory C]
    [HasRayCancellation C] [HasNoInfiniteRayChain C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    (hlocal : ∀ (D : Type u) [Category.{v} D] [HasZeroMorphisms D]
        [Finite D] [IsFiniteRayCategory D]
        [HasRayCancellation D] [HasNoInfiniteRayChain D]
        [HasRayLongPathEndpointValencyAtMostThree D],
      Nat.card (NonzeroCategoryMorphism D) ≤
          Nat.card (NonzeroCategoryMorphism C) →
        HasInvisibleCorrectionsOnEfficientMaximalRays k D) :
    ContourFunctionCohomologyVanishes (k := k)
      (rayPathContourRelation (C := C)) := by
  let originalCard := Nat.card (NonzeroCategoryMorphism C)
  have hmain : ∀ n : ℕ,
      ∀ (D : Type u) [Category.{v} D] [HasZeroMorphisms D]
        [Finite D] [IsFiniteRayCategory D]
        [HasRayCancellation D] [HasNoInfiniteRayChain D]
        [HasRayLongPathEndpointValencyAtMostThree D],
        Nat.card (NonzeroCategoryMorphism D) = n →
        Nat.card (NonzeroCategoryMorphism D) ≤ originalCard →
        ∀ d : contourScalarFunctionSubgroup (k := k)
          (rayPathContourRelation (C := D)),
          IsExactContourFunction (rayPathContourRelation (C := D)) d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro D _ _ _ _ _ _ _ hcard hbound d
        let R := rayPathContourRelation (C := D)
        by_cases hd : d = 1
        · refine ⟨1, ?_⟩
          rw [hd]
          exact (contourFunctionCoboundaryHom (k := k) R).map_one
        · have hexists : ∃ gamma : RelatedContour R,
              contourScalarFamily R d gamma ≠ 1 := by
            by_contra hall
            push Not at hall
            apply hd
            apply Subtype.ext
            funext gamma
            change contourScalarFamily R d gamma = 1
            exact hall gamma
          obtain ⟨⟨⟨i, j, p, q⟩, hpq⟩, hvalue⟩ := hexists
          have hpLength : p.length ≠ 0 := by
            intro hpZero
            have hpqEq := rayPath_eq_of_related_of_length_eq_zero
              p q hpq hpZero
            subst q
            exact hvalue (contourScalarFunction_self R d p hpq)
          let dp := chosenPathInitialDecomposition p hpLength
          let initialTackle : RayTackle D :=
            .hook 0 (RayHookTackle.singletonRayArrow dp.arrow)
          obtain ⟨t, ht⟩ := RayTackle.exists_isEfficientAt_of_bounded
            initialTackle.start ⟨initialTackle, rfl⟩
          let a := t.lastBundledArrow
          obtain ⟨m, hm⟩ :=
            NonzeroRayPathThroughArrow.exists_isMaximal a
          let J := principalZeroHomIdeal (rayPathMap m.path)
          have hJ : J.IsProper :=
            principalZeroHomIdeal_isProper_of_not_isIso
              (rayPathMap m.path) m.map_not_isIso
          letI : IsFiniteRayCategory
              (RayResidueCategory (rayPathMap m.path)) :=
            rayResidueCategory_isFiniteRayCategory
              (rayPathMap m.path) m.map_not_isIso
          letI : HasRayCancellation
              (RayResidueCategory (rayPathMap m.path)) :=
            J.quotientHasRayCancellation
          letI : HasNoInfiniteRayChain
              (RayResidueCategory (rayPathMap m.path)) :=
            J.quotientHasNoInfiniteRayChain
          letI : HasRayLongPathEndpointValencyAtMostThree
              (RayResidueCategory (rayPathMap m.path)) :=
            J.quotientHasRayLongPathEndpointValencyAtMostThree hJ
          have hlt : Nat.card (NonzeroCategoryMorphism
                (RayResidueCategory (rayPathMap m.path))) < n := by
            rw [← hcard]
            exact m.residue_nonzeroMorphism_card_lt
          have hquotBound : Nat.card (NonzeroCategoryMorphism
                (RayResidueCategory (rayPathMap m.path))) ≤ originalCard :=
            calc
              _ ≤ n := Nat.le_of_lt hlt
              _ = Nat.card (NonzeroCategoryMorphism D) := hcard.symm
              _ ≤ originalCard := hbound
          have hquotExact : IsExactContourFunction
              (rayPathContourRelation
                (C := RayResidueCategory (rayPathMap m.path)))
              (J.quotOutContourScalarFunction hJ d) :=
            ih _ hlt (RayResidueCategory (rayPathMap m.path)) rfl
              hquotBound (J.quotOutContourScalarFunction hJ d)
          have hmaximalLocal :
              J.HasInvisibleCorrectionClingingOnIdeal (k := k) := by
            exact hlocal D (by simpa [originalCard] using hbound)
              t initialTackle.start ht m hm
          exact J.isExactContourFunction_of_isExact_quotOut_of_invisibleCorrection_finite
            hJ d hmaximalLocal hquotExact
  rw [contourFunctionCohomologyVanishes_iff_forall_isExact]
  intro c
  exact hmain originalCard C rfl (by simp [originalCard]) c

end LargeIndecomposable
