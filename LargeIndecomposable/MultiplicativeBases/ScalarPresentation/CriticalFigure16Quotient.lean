module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure14Retraction
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure16Pairs

@[expose] public section

/-!
# The exact BGRS Figure-16 selected-corner quotient

For two singular pairs with a common first arrow, BGRS 4.5 quotients the full
subcategory on the common source and middle and the two branch targets by the
two relations `alpha tau beta` and `alpha tau gamma`.  In the ordinary
primitive-projective convention these relations are

`(beta ≫ tau) ≫ alpha` and `(gamma ≫ tau) ≫ alpha`.

This file starts the exact duplicate-free selected-corner construction.  The
six vertices in the printed affine-`D5` source are occurrences of only three
ambient objects; the common source is additionally required to form the two
relation generators.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalFigure16Quotient

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.SingularPairNormalization
open LargeIndecomposable.CriticalSingularFigure16Pairs
open LargeIndecomposable.SplitBasicIdempotents
open LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory
open LargeIndecomposable.SplitBasicIdempotents.SelectedCorner

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [HasBGRSPairDichotomy S.ProjectiveCategory]
variable [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]

/-- Duplicate-free primitive vertices of the exact full subcategory used for
Figure 16: the common source and middle and the two branch targets. -/
def selectedVertices (p q : SingularPair (C := S.ProjectiveCategory)) :
    Finset ι :=
  {S.projectiveVertex p.1.source.obj.as,
    S.projectiveVertex p.1.middle.obj.as,
    S.projectiveVertex p.1.target.obj.as,
    S.projectiveVertex q.1.target.obj.as}

omit [IsAlgClosed k] [Module.Finite k A]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
@[simp] theorem source_mem_selectedVertices
    (p q : SingularPair (C := S.ProjectiveCategory)) :
    S.projectiveVertex p.1.source.obj.as ∈ selectedVertices S p q := by
  simp [selectedVertices]

omit [IsAlgClosed k] [Module.Finite k A]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
@[simp] theorem middle_mem_selectedVertices
    (p q : SingularPair (C := S.ProjectiveCategory)) :
    S.projectiveVertex p.1.middle.obj.as ∈ selectedVertices S p q := by
  simp [selectedVertices]

omit [IsAlgClosed k] [Module.Finite k A]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
@[simp] theorem betaTarget_mem_selectedVertices
    (p q : SingularPair (C := S.ProjectiveCategory)) :
    S.projectiveVertex p.1.target.obj.as ∈ selectedVertices S p q := by
  simp [selectedVertices]

omit [IsAlgClosed k] [Module.Finite k A]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
@[simp] theorem gammaTarget_mem_selectedVertices
    (p q : SingularPair (C := S.ProjectiveCategory)) :
    S.projectiveVertex q.1.target.obj.as ∈ selectedVertices S p q := by
  simp [selectedVertices]

/-- Canonical enumeration of the duplicate-free Figure-16 corner. -/
abbrev selectedEmbedding (p q : SingularPair (C := S.ProjectiveCategory)) :=
  finsetPrimitiveEmbedding (selectedVertices S p q)

/-- Exact four-object corner supporting both relation generators. -/
abbrev selectedCorner (p q : SingularPair (C := S.ProjectiveCategory)) :=
  S.SelectedCorner (selectedEmbedding S p q)

/-- Chosen split-basic presentation of the exact Figure-16 corner. -/
abbrev selectedSplitBasic (p q : SingularPair (C := S.ProjectiveCategory)) :=
  SelectedCorner.splitBasic S (selectedEmbedding S p q)

abbrev selectedSourceObj (p q : SingularPair (C := S.ProjectiveCategory)) :=
  finsetProjectiveObj S (selectedVertices S p q) p.1.source.obj.as
    (source_mem_selectedVertices S p q)

abbrev selectedMiddleObj (p q : SingularPair (C := S.ProjectiveCategory)) :=
  finsetProjectiveObj S (selectedVertices S p q) p.1.middle.obj.as
    (middle_mem_selectedVertices S p q)

abbrev selectedBetaObj (p q : SingularPair (C := S.ProjectiveCategory)) :=
  finsetProjectiveObj S (selectedVertices S p q) p.1.target.obj.as
    (betaTarget_mem_selectedVertices S p q)

abbrev selectedGammaObj (p q : SingularPair (C := S.ProjectiveCategory)) :=
  finsetProjectiveObj S (selectedVertices S p q) q.1.target.obj.as
    (gammaTarget_mem_selectedVertices S p q)

abbrev selectedAlpha
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :=
  finsetProjectiveHom S (selectedVertices S p q)
    (middle_mem_selectedVertices S p q)
    (source_mem_selectedVertices S p q) D.alpha.hom

abbrev selectedBeta
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :=
  finsetProjectiveHom S (selectedVertices S p q)
    (betaTarget_mem_selectedVertices S p q)
    (middle_mem_selectedVertices S p q) D.beta.hom

abbrev selectedGamma
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :=
  finsetProjectiveHom S (selectedVertices S p q)
    (gammaTarget_mem_selectedVertices S p q)
    (middle_mem_selectedVertices S p q) D.alignedGamma

abbrev selectedTau
    (p q : SingularPair (C := S.ProjectiveCategory))
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :=
  finsetProjectiveHom S (selectedVertices S p q)
    (middle_mem_selectedVertices S p q)
    (middle_mem_selectedVertices S p q) P.tau.asHom

omit [IsAlgClosed k] in
/-- Every chosen ordinary representative of a packaged irreducible ray arrow
lies in the ambient Jacobson radical. -/
theorem representative_val_mem_jacobson
    {a : Arrow (C := S.ProjectiveCategory)} (r : Representative a) :
    r.hom.1 ∈ Ring.jacobson A := by
  apply ProjectiveCategory.val_mem_jacobson_of_unitRayEquivalent S
    (S.rayQuiverArrowRepresentative_mem_jacobson a.hom)
  apply (LargeIndecomposable.unitRay_eq_iff _ _).1
  rw [r.unitRay_hom]
  exact S.unitRay_rayQuiverArrowRepresentative a.hom

omit [IsAlgClosed k] in
/-- Every chosen ordinary representative of a packaged irreducible ray arrow
has nonzero class in the ambient first radical layer. -/
theorem representative_val_not_mem_jacobson_sq
    {a : Arrow (C := S.ProjectiveCategory)} (r : Representative a) :
    r.hom.1 ∉ Ring.jacobson A * Ring.jacobson A := by
  intro hr
  apply S.rayArrowRepresentative_not_mem_jacobson_sq a.hom
  apply ProjectiveCategory.val_mem_ideal_of_unitRayEquivalent S
    (Ring.jacobson A * Ring.jacobson A) hr
  apply (LargeIndecomposable.unitRay_eq_iff _ _).1
  rw [r.unitRay_hom]
  exact (S.unitRay_rayQuiverArrowRepresentative a.hom).symm

omit [IsAlgClosed k] [Module.Finite k A]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- Aligning the second branch along equality of the common middle object
does not change its ambient algebra value. -/
@[simp] theorem alignedGamma_val
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    D.alignedGamma.1 = D.gamma.hom.1 := by
  simp only [CommonFirstZeroRepresentatives.alignedGamma, comp_val,
    SelectedCorner.projectiveEqToHom_val]
  exact ProjectiveCategory.idempotent_mul_val S D.gamma.hom

/-- Exact two-generator Figure-16 relation ideal in the selected corner. -/
def relationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    TwoSidedIdeal (selectedCorner S p q) :=
  TwoSidedIdeal.span
    ({(selectedBeta S D ≫ selectedTau S p q P ≫ selectedAlpha S D).1,
      (selectedGamma S D ≫ selectedTau S p q P ≫ selectedAlpha S D).1} :
      Set (selectedCorner S p q))

/-- The same two Figure-16 generators in the ambient algebra.  This auxiliary
ideal receives the exact selected-corner relation ideal under the nonunital
corner inclusion. -/
def ambientRelationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    TwoSidedIdeal A :=
  TwoSidedIdeal.span
    ({(D.beta.hom ≫ P.tau.asHom ≫ D.alpha.hom).1,
      (D.alignedGamma ≫ P.tau.asHom ≫ D.alpha.hom).1} : Set A)

omit [IsAlgClosed k] in
/-- The ambient Figure-16 auxiliary ideal lies in `Jac(A)^2`: in each
generator the common first-arrow representative and `tau` are radical, and
the remaining branch factor is absorbed by two-sidedness. -/
theorem ambientRelationIdeal_le_jacobson_sq
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (ambientRelationIdeal S D P).asIdeal ≤ (Ring.jacobson A) ^ 2 := by
  have halpha : D.alpha.hom.1 ∈ Ring.jacobson A :=
    representative_val_mem_jacobson S D.alpha
  have htau : P.tau.1 ∈ Ring.jacobson A :=
    (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      p.1.middle.obj.as P.tau).1 P.mem_jacobson
  have hle : ambientRelationIdeal S D P ≤
      ((Ring.jacobson A) ^ 2).toTwoSided := by
    apply TwoSidedIdeal.span_le.2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · apply Ideal.mem_toTwoSided.2
      rw [show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      have hprod : D.alpha.hom.1 * P.tau.1 ∈
          Ring.jacobson A * Ring.jacobson A :=
        Ideal.mul_mem_mul halpha htau
      simpa only [comp_val, mul_assoc] using
        (Ring.jacobson A * Ring.jacobson A).mul_mem_right D.beta.hom.1 hprod
    · apply Ideal.mem_toTwoSided.2
      rw [show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      have hprod : D.alpha.hom.1 * P.tau.1 ∈
          Ring.jacobson A * Ring.jacobson A :=
        Ideal.mul_mem_mul halpha htau
      simpa only [comp_val, mul_assoc] using
        (Ring.jacobson A * Ring.jacobson A).mul_mem_right
          D.alignedGamma.1 hprod
  intro a ha
  exact Ideal.mem_toTwoSided.1 (hle ha)

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- Forgetting the selected corner sends the exact local Figure-16 relation
ideal into the ambient ideal generated by the same two composites. -/
theorem relationIdeal_le_comap_ambientRelationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    relationIdeal S D P ≤
      (ambientRelationIdeal S D P).comap
        (valNonUnitalRingHom S (selectedEmbedding S p q)) := by
  apply TwoSidedIdeal.span_le.2
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · apply (TwoSidedIdeal.mem_comap
      (valNonUnitalRingHom S (selectedEmbedding S p q))).2
    change (selectedAlpha S D).1.1 * (selectedTau S p q P).1.1 *
      (selectedBeta S D).1.1 ∈ (ambientRelationIdeal S D P).asIdeal
    rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val,
      finsetProjectiveHom_val_val]
    exact TwoSidedIdeal.subset_span (by simp)
  · apply (TwoSidedIdeal.mem_comap
      (valNonUnitalRingHom S (selectedEmbedding S p q))).2
    change (selectedAlpha S D).1.1 * (selectedTau S p q P).1.1 *
      (selectedGamma S D).1.1 ∈ (ambientRelationIdeal S D P).asIdeal
    rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val,
      finsetProjectiveHom_val_val]
    exact TwoSidedIdeal.subset_span (by simp)

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- Elementwise selected-corner-to-ambient containment for the Figure-16
relation ideal. -/
theorem val_mem_ambientRelationIdeal_of_mem_relationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    {z : selectedCorner S p q}
    (hz : z ∈ (relationIdeal S D P).asIdeal) :
    z.1 ∈ (ambientRelationIdeal S D P).asIdeal := by
  exact relationIdeal_le_comap_ambientRelationIdeal S D P hz

omit [IsAlgClosed k] in
/-- The selected common first-arrow representative avoids the exact
Figure-16 relation ideal. -/
theorem selectedAlpha_not_mem_relationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedAlpha S D).1 ∉ (relationIdeal S D P).asIdeal := by
  intro hmem
  apply representative_val_not_mem_jacobson_sq S D.alpha
  have hsq := ambientRelationIdeal_le_jacobson_sq S D P
    (val_mem_ambientRelationIdeal_of_mem_relationIdeal S D P hmem)
  rw [show (2 : ℕ) = 1 + 1 by omega,
    Ideal.IsTwoSided.pow_add, Submodule.pow_one] at hsq
  simpa only [finsetProjectiveHom_val_val] using hsq

omit [IsAlgClosed k] in
/-- Both occurrences of the first branch arrow avoid the exact Figure-16
relation ideal. -/
theorem selectedBeta_not_mem_relationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedBeta S D).1 ∉ (relationIdeal S D P).asIdeal := by
  intro hmem
  apply representative_val_not_mem_jacobson_sq S D.beta
  have hsq := ambientRelationIdeal_le_jacobson_sq S D P
    (val_mem_ambientRelationIdeal_of_mem_relationIdeal S D P hmem)
  rw [show (2 : ℕ) = 1 + 1 by omega,
    Ideal.IsTwoSided.pow_add, Submodule.pow_one] at hsq
  simpa only [finsetProjectiveHom_val_val] using hsq

omit [IsAlgClosed k] in
/-- Both occurrences of the aligned second branch arrow avoid the exact
Figure-16 relation ideal. -/
theorem selectedGamma_not_mem_relationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedGamma S D).1 ∉ (relationIdeal S D P).asIdeal := by
  intro hmem
  apply representative_val_not_mem_jacobson_sq S D.gamma
  have hsq := ambientRelationIdeal_le_jacobson_sq S D P
    (val_mem_ambientRelationIdeal_of_mem_relationIdeal S D P hmem)
  rw [show (2 : ℕ) = 1 + 1 by omega,
    Ideal.IsTwoSided.pow_add, Submodule.pow_one] at hsq
  simpa only [finsetProjectiveHom_val_val, alignedGamma_val] using hsq

omit [IsAlgClosed k] in
/-- In the common-middle corner, every contribution of either Figure-16
generator contains the radical middle parameter and a radical branch cycle.
Hence this corner of the ambient relation ideal lies in the square of the
middle endomorphism radical. -/
theorem ambientRelationIdeal_middle_corner_le_jacobson_sq
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    finiteIdealCorner S (ambientRelationIdeal S D P)
        p.1.middle.obj.as p.1.middle.obj.as ≤
      ((Ring.jacobson (End p.1.middle.obj.as)) ^ 2).restrictScalars k := by
  let J := Ring.jacobson (End p.1.middle.obj.as)
  rw [ambientRelationIdeal, finiteIdealCorner_span_pair_eq]
  apply sup_le
  · apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    let c : End p.1.middle.obj.as := End.of (a ≫ D.beta.hom)
    let d : End p.1.middle.obj.as := End.of (D.alpha.hom ≫ b)
    have hcJ : c ∈ J := by
      rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
      change (a ≫ D.beta.hom).1 ∈ Ring.jacobson A
      simp only [comp_val]
      exact (Ring.jacobson A).mul_mem_right a.1
        (representative_val_mem_jacobson S D.beta)
    have hprod : P.tau * c ∈ J ^ 2 := by
      rw [show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      exact Ideal.mul_mem_mul P.mem_jacobson hcJ
    have hout : d * (P.tau * c) ∈ J ^ 2 :=
      (J ^ 2).mul_mem_left d hprod
    change End.of ((a ≫ (D.beta.hom ≫ P.tau.asHom ≫
      D.alpha.hom)) ≫ b) ∈ J ^ 2
    convert hout using 1
    apply End.ext
    simp only [c, d, End.mul_def, Category.assoc]
  · apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    let c : End p.1.middle.obj.as := End.of (a ≫ D.alignedGamma)
    let d : End p.1.middle.obj.as := End.of (D.alpha.hom ≫ b)
    have hcJ : c ∈ J := by
      rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
      change (a ≫ D.alignedGamma).1 ∈ Ring.jacobson A
      simp only [comp_val, alignedGamma_val]
      exact (Ring.jacobson A).mul_mem_right a.1
        (representative_val_mem_jacobson S D.gamma)
    have hprod : P.tau * c ∈ J ^ 2 := by
      rw [show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      exact Ideal.mul_mem_mul P.mem_jacobson hcJ
    have hout : d * (P.tau * c) ∈ J ^ 2 :=
      (J ^ 2).mul_mem_left d hprod
    change End.of ((a ≫ (D.alignedGamma ≫ P.tau.asHom ≫
      D.alpha.hom)) ≫ b) ∈ J ^ 2
    convert hout using 1
    apply End.ext
    simp only [c, d, End.mul_def, Category.assoc]

omit [IsAlgClosed k] in
/-- The middle radical generator avoids the ambient Figure-16 relation
ideal. -/
theorem tau_not_mem_ambientRelationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    P.tau.1 ∉ (ambientRelationIdeal S D P).asIdeal := by
  intro hmem
  apply P.tau_not_mem_jacobson_sq
  exact ambientRelationIdeal_middle_corner_le_jacobson_sq S D P hmem

omit [IsAlgClosed k] in
/-- The selected middle arrow therefore avoids the exact local Figure-16
relation ideal. -/
theorem selectedTau_not_mem_relationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedTau S p q P).1 ∉ (relationIdeal S D P).asIdeal := by
  intro hmem
  apply tau_not_mem_ambientRelationIdeal S D P
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D P hmem
  simpa only [finsetProjectiveHom_val_val] using hval

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- The selected lift of `tau` remains in the Jacobson radical of the exact
corner. -/
theorem selectedTau_val_mem_jacobson
    (p q : SingularPair (C := S.ProjectiveCategory))
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedTau S p q P).1 ∈ Ring.jacobson (selectedCorner S p q) := by
  apply finsetProjectiveHom_val_mem_jacobson S (selectedVertices S p q)
    (middle_mem_selectedVertices S p q)
    (middle_mem_selectedVertices S p q) P.tau.asHom
  exact (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
    p.1.middle.obj.as P.tau).1 P.mem_jacobson

omit [IsAlgClosed k] in
/-- The common first-arrow representative stays radical in the exact selected
corner. -/
theorem selectedAlpha_val_mem_jacobson
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    (selectedAlpha S D).1 ∈ Ring.jacobson (selectedCorner S p q) := by
  exact finsetProjectiveHom_val_mem_jacobson S (selectedVertices S p q)
    (middle_mem_selectedVertices S p q)
    (source_mem_selectedVertices S p q) D.alpha.hom
    (representative_val_mem_jacobson S D.alpha)

omit [IsAlgClosed k] in
/-- Each Figure-16 relation contains two consecutive radical factors, so the
whole exact relation ideal lies in the square of the selected-corner
Jacobson radical. -/
theorem relationIdeal_le_jacobson_sq
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (relationIdeal S D P).asIdeal ≤
      (Ring.jacobson (selectedCorner S p q)) ^ 2 := by
  let J := Ring.jacobson (selectedCorner S p q)
  have halpha : (selectedAlpha S D).1 ∈ J :=
    selectedAlpha_val_mem_jacobson S D
  have htau : (selectedTau S p q P).1 ∈ J :=
    selectedTau_val_mem_jacobson S p q P
  have hle : relationIdeal S D P ≤ (J ^ 2).toTwoSided := by
    apply TwoSidedIdeal.span_le.2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · apply Ideal.mem_toTwoSided.2
      rw [show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      have hprod : (selectedAlpha S D).1 * (selectedTau S p q P).1 ∈
          J * J := Ideal.mul_mem_mul halpha htau
      simpa only [comp_val, mul_assoc] using
        (J * J).mul_mem_right (selectedBeta S D).1 hprod
    · apply Ideal.mem_toTwoSided.2
      rw [show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      have hprod : (selectedAlpha S D).1 * (selectedTau S p q P).1 ∈
          J * J := Ideal.mul_mem_mul halpha htau
      simpa only [comp_val, mul_assoc] using
        (J * J).mul_mem_right (selectedGamma S D).1 hprod
  intro a ha
  exact Ideal.mem_toTwoSided.1 (hle ha)

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- Both relation generators contain the radical element `tau`, so the exact
Figure-16 relation ideal is radical. -/
theorem relationIdeal_le_jacobson
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (relationIdeal S D P).asIdeal ≤
      Ring.jacobson (selectedCorner S p q) := by
  let J := Ring.jacobson (selectedCorner S p q)
  have htau : (selectedTau S p q P).1 ∈ J :=
    selectedTau_val_mem_jacobson S p q P
  have hle : relationIdeal S D P ≤ J.toTwoSided := by
    apply TwoSidedIdeal.span_le.2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · apply Ideal.mem_toTwoSided.2
      have hinner :
          (selectedTau S p q P).1 * (selectedBeta S D).1 ∈ J :=
        J.mul_mem_right (selectedBeta S D).1 htau
      simpa only [comp_val, mul_assoc] using
        J.mul_mem_left (selectedAlpha S D).1 hinner
    · apply Ideal.mem_toTwoSided.2
      have hinner :
          (selectedTau S p q P).1 * (selectedGamma S D).1 ∈ J :=
        J.mul_mem_right (selectedGamma S D).1 htau
      simpa only [comp_val, mul_assoc] using
        J.mul_mem_left (selectedAlpha S D).1 hinner
  intro a ha
  exact Ideal.mem_toTwoSided.1 (hle ha)

/-- If one Figure-16 branch is a full Hom generator, then the corner of the
two-relation ideal ending at the common middle lies in the principal span of
that branch followed by `tau^2`.  The outer prefix of either relation factors
through the full branch; transit moves the resulting middle endomorphism
past `tau`, while the final cycle through `alpha` is radical and therefore
contributes one further positive `tau`-power. -/
theorem ambientRelationIdeal_branch_corner_le_tauSquareSpan
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    {B : S.ProjectiveCategory}
    (branch : B ⟶ p.1.middle.obj.as)
    (hbranchSpan : LargeIndecomposable.twoSidedEndomorphismSpan k branch = ⊤)
    (hbranchTransit : LargeIndecomposable.AllowsTransit branch) :
    finiteIdealCorner S (ambientRelationIdeal S D P)
        B p.1.middle.obj.as ≤
      LargeIndecomposable.twoSidedEndomorphismSpan k
        (branch ≫ (P.tau ^ 2).asHom) := by
  letI : Module.Finite k (End p.1.middle.obj.as) := by
    change Module.Finite k
      (p.1.middle.obj.as ⟶ p.1.middle.obj.as)
    infer_instance
  have halpha : D.alpha.hom.1 ∈ Ring.jacobson A :=
    representative_val_mem_jacobson S D.alpha
  have hterm : ∀ {T : S.ProjectiveCategory}
      (outer : T ⟶ p.1.middle.obj.as)
      (a : B ⟶ T) (b : p.1.source.obj.as ⟶ p.1.middle.obj.as),
      (a ≫ (outer ≫ P.tau.asHom ≫ D.alpha.hom)) ≫ b ∈
        (↑(LargeIndecomposable.twoSidedEndomorphismSpan k
          (branch ≫ (P.tau ^ 2).asHom)) :
            Set (B ⟶ p.1.middle.obj.as)) := by
    intro T outer a b
    have hprefixMem : a ≫ outer ∈
        LargeIndecomposable.twoSidedEndomorphismSpan k branch := by
      rw [hbranchSpan]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
        hbranchTransit hprefixMem
    obtain ⟨d, hcd⟩ := P.transitData.allows_transit c
    let e : End p.1.middle.obj.as :=
      End.of (d.asHom ≫ D.alpha.hom ≫ b)
    have heJ : e ∈ Ring.jacobson (End p.1.middle.obj.as) := by
      rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
      change (d.asHom ≫ D.alpha.hom ≫ b).1 ∈ Ring.jacobson A
      simp only [comp_val]
      exact (Ring.jacobson A).mul_mem_right d.1
        ((Ring.jacobson A).mul_mem_left b.1 halpha)
    obtain ⟨r, her⟩ := P.transitData.generates e heJ
    have htail : (branch ≫ (P.tau ^ 2).asHom) ≫ r.asHom ∈
        (↑(LargeIndecomposable.twoSidedEndomorphismSpan k
          (branch ≫ (P.tau ^ 2).asHom)) :
            Set (B ⟶ p.1.middle.obj.as)) := SetLike.mem_coe.2
      ((LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan
          (k := k) (branch ≫ (P.tau ^ 2).asHom)).2 r
        (LargeIndecomposable.mem_twoSidedEndomorphismSpan k
          (branch ≫ (P.tau ^ 2).asHom)))
    convert htail using 1
    calc
      (a ≫ (outer ≫ P.tau.asHom ≫ D.alpha.hom)) ≫ b =
          ((a ≫ outer) ≫ P.tau.asHom) ≫
            (D.alpha.hom ≫ b) := by simp only [Category.assoc]
      _ = ((branch ≫ c.asHom) ≫ P.tau.asHom) ≫
            (D.alpha.hom ≫ b) := by rw [hc]
      _ = (branch ≫ (c.asHom ≫ P.tau.asHom)) ≫
            (D.alpha.hom ≫ b) := by simp only [Category.assoc]
      _ = (branch ≫ (P.tau.asHom ≫ d.asHom)) ≫
            (D.alpha.hom ≫ b) := by rw [hcd]
      _ = (branch ≫ P.tau.asHom) ≫ e.asHom := by
        simp only [e, Category.assoc]
      _ = (branch ≫ P.tau.asHom) ≫
            (P.tau.asHom ≫ r.asHom) := by rw [her]
      _ = (branch ≫ (P.tau ^ 2).asHom) ≫ r.asHom := by
        simp only [pow_two, End.mul_def, Category.assoc]
  rw [ambientRelationIdeal, finiteIdealCorner_span_pair_eq]
  apply sup_le
  · apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    convert hterm D.beta.hom a b using 1
  · apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    convert hterm D.alignedGamma a b using 1

omit [IsAlgClosed k] [HasBGRSPairDichotomy S.ProjectiveCategory]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
private theorem eq_zero_of_eq_target_jacobson_action
    {X Y : S.ProjectiveCategory} (f : X ⟶ Y) (b : End Y)
    (hb : b ∈ Ring.jacobson (End Y))
    (hfix : f = f ≫ b.asHom) : f = 0 := by
  obtain ⟨n, hnil⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End Y)
  rw [Ideal.jacobson_bot] at hnil
  have hbPow : b ^ n ∈ (Ring.jacobson (End Y)) ^ n :=
    Ideal.pow_mem_pow hb n
  rw [hnil] at hbPow
  have hbNil : IsNilpotent b := ⟨n, hbPow⟩
  rcases hbNil with ⟨n, hbn⟩
  have hpow : ∀ m : ℕ, f = f ≫ (b ^ m).asHom := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          f = f ≫ (b ^ m).asHom := ih
          _ = (f ≫ b.asHom) ≫ (b ^ m).asHom := by rw [← hfix]
          _ = f ≫ (b ^ (m + 1)).asHom := by
            rw [show b ^ (m + 1) = b ^ m * b by
              simpa only [Nat.add_comm] using pow_succ b m]
            simp only [End.mul_def, Category.assoc]
  have hn := hpow n
  rw [hbn] at hn
  change f = f ≫ (0 : Y ⟶ Y) at hn
  simpa using hn

omit [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- A nonzero branch followed by `tau` cannot lie in the principal span of
the same branch followed by `tau^2`. -/
theorem branch_tau_not_mem_tauSquareSpan
    {p : SingularPair (C := S.ProjectiveCategory)}
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    {B : S.ProjectiveCategory}
    (branch : B ⟶ p.1.middle.obj.as)
    (hbranchTransit : LargeIndecomposable.AllowsTransit branch)
    (hbranchTau : branch ≫ P.tau.asHom ≠ 0) :
    branch ≫ P.tau.asHom ∉
      LargeIndecomposable.twoSidedEndomorphismSpan k
        (branch ≫ (P.tau ^ 2).asHom) := by
  letI : Module.Finite k (End p.1.middle.obj.as) := by
    change Module.Finite k
      (p.1.middle.obj.as ⟶ p.1.middle.obj.as)
    infer_instance
  intro hmem
  have hsquareTransit : LargeIndecomposable.AllowsTransit
      (branch ≫ (P.tau ^ 2).asHom) :=
    hbranchTransit.comp (P.power_allowsTransit 2)
  obtain ⟨b, hb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      hsquareTransit hmem
  let c : End p.1.middle.obj.as :=
    End.of (P.tau.asHom ≫ b.asHom)
  have hcJ : c ∈ Ring.jacobson (End p.1.middle.obj.as) := by
    change b * P.tau ∈ Ring.jacobson (End p.1.middle.obj.as)
    exact (Ring.jacobson (End p.1.middle.obj.as)).mul_mem_left
      b P.mem_jacobson
  have hfix : branch ≫ P.tau.asHom =
      (branch ≫ P.tau.asHom) ≫ c.asHom := by
    calc
      branch ≫ P.tau.asHom =
          (branch ≫ (P.tau ^ 2).asHom) ≫ b.asHom := hb
      _ = (branch ≫ P.tau.asHom) ≫ c.asHom := by
        simp only [c, pow_two, End.mul_def, Category.assoc]
  exact hbranchTau
    (eq_zero_of_eq_target_jacobson_action S
      (branch ≫ P.tau.asHom) c hcJ hfix)

/-- Under representation-finiteness, the ambient first branch followed by
`tau` has exact target-power degree one and therefore avoids the Figure-16
relation ideal. -/
theorem beta_tau_not_mem_ambientRelationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (D.beta.hom ≫ P.tau.asHom).1 ∉
      (ambientRelationIdeal S D P).asIdeal := by
  obtain ⟨Z⟩ := nonempty_zeroPairRadicalSandwich p D.pZero
  have hbetaSpan :
      LargeIndecomposable.twoSidedEndomorphismSpan k D.beta.hom = ⊤ := by
    change LargeIndecomposable.twoSidedEndomorphismSpan k
      D.pZero.second.hom = ⊤
    rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k Z.left_unitRayEquivalent]
    exact (LargeIndecomposable.RoiterFigure13EAmbient.zeroPairRadicalSandwich_full_outer_spans
      S hfinite Z).1
  have hbetaTransit : LargeIndecomposable.AllowsTransit D.beta.hom :=
    zeroRepresentatives_second_allowsTransit (k := k) D.pZero
  letI : LargeIndecomposable.HasRoiterTransitSquareAlternative
      k S.ProjectiveCategory :=
    LargeIndecomposable.RoiterFigure13EAmbient.hasRoiterTransitSquareAlternative
      S hfinite
  letI : Module.Finite k (End p.1.middle.obj.as) := by
    change Module.Finite k
      (p.1.middle.obj.as ⟶ p.1.middle.obj.as)
    infer_instance
  have hbetaTau : D.beta.hom ≫ P.tau.asHom ≠ 0 := by
    intro hzero
    apply D.betaTauAlpha_ne_zero P
    rw [show D.betaTauAlpha P =
        (D.beta.hom ≫ P.tau.asHom) ≫ D.alpha.hom by rfl,
      hzero]
    exact CategoryTheory.Limits.zero_comp
  have hexact := branch_tau_not_mem_tauSquareSpan
    S P D.beta.hom hbetaTransit hbetaTau
  intro hmem
  apply hexact
  apply ambientRelationIdeal_branch_corner_le_tauSquareSpan
    S D P D.beta.hom hbetaSpan hbetaTransit
  exact hmem

/-- The symmetric ambient second branch followed by `tau` also has exact
target-power degree one and avoids the Figure-16 relation ideal. -/
theorem gamma_tau_not_mem_ambientRelationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (D.alignedGamma ≫ P.tau.asHom).1 ∉
      (ambientRelationIdeal S D P).asIdeal := by
  obtain ⟨Z⟩ := D.nonempty_alignedGammaAlphaRadicalSandwich
  have hgammaSpan :
      LargeIndecomposable.twoSidedEndomorphismSpan k D.alignedGamma = ⊤ := by
    rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k Z.left_unitRayEquivalent]
    exact (LargeIndecomposable.RoiterFigure13EAmbient.zeroPairRadicalSandwich_full_outer_spans
      S hfinite Z).1
  have hgammaTransit : LargeIndecomposable.AllowsTransit D.alignedGamma := by
    have hZTransit : LargeIndecomposable.AllowsTransit Z.left :=
      (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := S.ProjectiveCategory) Z.left).resolve_right
          Z.left_not_allowsCotransit
    exact hZTransit.of_unitRayEquivalent
      ((LargeIndecomposable.unitRaySetoid _ _).symm
        Z.left_unitRayEquivalent)
  letI : LargeIndecomposable.HasRoiterTransitSquareAlternative
      k S.ProjectiveCategory :=
    LargeIndecomposable.RoiterFigure13EAmbient.hasRoiterTransitSquareAlternative
      S hfinite
  letI : Module.Finite k (End p.1.middle.obj.as) := by
    change Module.Finite k
      (p.1.middle.obj.as ⟶ p.1.middle.obj.as)
    infer_instance
  have hgammaTau : D.alignedGamma ≫ P.tau.asHom ≠ 0 := by
    intro hzero
    apply D.gammaTauAlpha_ne_zero P
    rw [show D.gammaTauAlpha P =
        (D.alignedGamma ≫ P.tau.asHom) ≫ D.alpha.hom by rfl,
      hzero]
    exact CategoryTheory.Limits.zero_comp
  have hexact := branch_tau_not_mem_tauSquareSpan
    S P D.alignedGamma hgammaTransit hgammaTau
  intro hmem
  apply hexact
  apply ambientRelationIdeal_branch_corner_le_tauSquareSpan
    S D P D.alignedGamma hgammaSpan hgammaTransit
  exact hmem

/-- The selected first length-two source path avoids the exact Figure-16
relation ideal. -/
theorem selectedBetaTau_not_mem_relationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedBeta S D ≫ selectedTau S p q P).1 ∉
      (relationIdeal S D P).asIdeal := by
  intro hmem
  apply beta_tau_not_mem_ambientRelationIdeal S hfinite D P
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D P hmem
  change (selectedTau S p q P).1.1 * (selectedBeta S D).1.1 ∈
    (ambientRelationIdeal S D P).asIdeal at hval
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hval
  simpa only [comp_val] using hval

/-- The selected second length-two source path avoids the exact Figure-16
relation ideal. -/
theorem selectedGammaTau_not_mem_relationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedGamma S D ≫ selectedTau S p q P).1 ∉
      (relationIdeal S D P).asIdeal := by
  intro hmem
  apply gamma_tau_not_mem_ambientRelationIdeal S hfinite D P
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D P hmem
  change (selectedTau S p q P).1.1 * (selectedGamma S D).1.1 ∈
    (ambientRelationIdeal S D P).asIdeal at hval
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hval
  simpa only [comp_val] using hval

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
theorem beta_relation_mem
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedBeta S D ≫ selectedTau S p q P ≫ selectedAlpha S D).1 ∈
      (relationIdeal S D P).asIdeal := by
  exact TwoSidedIdeal.subset_span (Set.mem_insert _ _)

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
theorem gamma_relation_mem
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (selectedGamma S D ≫ selectedTau S p q P ≫ selectedAlpha S D).1 ∈
      (relationIdeal S D P).asIdeal := by
  exact TwoSidedIdeal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- Repeated-object Figure-16 diagram inside the exact selected corner. -/
def selectedAmbientDiagram
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    LargeIndecomposable.CriticalSingularFigure16.DiagramData
      (C := (selectedSplitBasic S p q).ProjectiveCategory) where
  object
    | .upperCenter | .lowerCenter => selectedMiddleObj S p q
    | .upperBeta | .lowerBeta => selectedBetaObj S p q
    | .upperGamma | .lowerGamma => selectedGammaObj S p q
  arrow := by
    intro a b e
    cases e with
    | tau => exact selectedTau S p q P
    | betaUpper => exact selectedBeta S D
    | gammaUpper => exact selectedGamma S D
    | betaLower => exact selectedBeta S D
    | gammaLower => exact selectedGamma S D

/-- Exact quotient functor on the selected Figure-16 primitive projectives. -/
abbrev quotientFunctor
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :=
  (selectedSplitBasic S p q).projectiveQuotientFunctor
    (relationIdeal S D P) (relationIdeal_le_jacobson S D P)

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- A selected-corner morphism survives the exact Figure-16 quotient whenever
its corner element lies outside the two-relation ideal. -/
theorem quotientFunctor_map_ne_zero_of_not_mem_relationIdeal
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    {U V : (selectedSplitBasic S p q).ProjectiveCategory}
    (h : U ⟶ V) (hh : h.1 ∉ (relationIdeal S D P).asIdeal) :
    (quotientFunctor S D P).map h ≠ 0 := by
  intro hzero
  apply hh
  exact ((selectedSplitBasic S p q).projectiveQuotientFunctor_map_eq_zero_iff
    (relationIdeal S D P) (relationIdeal_le_jacobson S D P) h).1 hzero

omit [IsAlgClosed k] in
/-- Both repeated occurrences of the first branch arrow survive the exact
Figure-16 quotient. -/
theorem quotientFunctor_map_selectedBeta_ne_zero
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).map (selectedBeta S D) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D P
    (selectedBeta S D) (selectedBeta_not_mem_relationIdeal S D P)

omit [IsAlgClosed k] in
/-- Both repeated occurrences of the aligned second branch arrow survive the
exact Figure-16 quotient. -/
theorem quotientFunctor_map_selectedGamma_ne_zero
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).map (selectedGamma S D) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D P
    (selectedGamma S D) (selectedGamma_not_mem_relationIdeal S D P)

omit [IsAlgClosed k] in
/-- The central middle arrow survives the exact Figure-16 quotient. -/
theorem quotientFunctor_map_selectedTau_ne_zero
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).map (selectedTau S p q P) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D P
    (selectedTau S p q P) (selectedTau_not_mem_relationIdeal S D P)

/-- Under representation-finiteness, the first length-two source path also
survives the exact Figure-16 quotient. -/
theorem quotientFunctor_map_selectedBetaTau_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).map
      (selectedBeta S D ≫ selectedTau S p q P) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D P
    (selectedBeta S D ≫ selectedTau S p q P)
      (selectedBetaTau_not_mem_relationIdeal S hfinite D P)

/-- Under representation-finiteness, the second length-two source path also
survives the exact Figure-16 quotient. -/
theorem quotientFunctor_map_selectedGammaTau_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).map
      (selectedGamma S D ≫ selectedTau S p q P) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D P
    (selectedGamma S D ≫ selectedTau S p q P)
      (selectedGammaTau_not_mem_relationIdeal S hfinite D P)

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- The first displayed threefold relation is zero in the exact quotient. -/
theorem quotientFunctor_map_beta_relation_eq_zero
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).map
      (selectedBeta S D ≫ selectedTau S p q P ≫ selectedAlpha S D) = 0 := by
  exact (((selectedSplitBasic S p q).projectiveQuotientFunctor_map_eq_zero_iff
    (relationIdeal S D P) (relationIdeal_le_jacobson S D P)
    (selectedBeta S D ≫ selectedTau S p q P ≫ selectedAlpha S D)).2
      (beta_relation_mem S D P))

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- The second displayed threefold relation is zero in the exact quotient. -/
theorem quotientFunctor_map_gamma_relation_eq_zero
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).map
      (selectedGamma S D ≫ selectedTau S p q P ≫ selectedAlpha S D) = 0 := by
  exact (((selectedSplitBasic S p q).projectiveQuotientFunctor_map_eq_zero_iff
    (relationIdeal S D P) (relationIdeal_le_jacobson S D P)
    (selectedGamma S D ≫ selectedTau S p q P ≫ selectedAlpha S D)).2
      (gamma_relation_mem S D P))

/-- Literal Figure-16 diagram after passing to the exact two-relation
quotient. -/
def quotientDiagram
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    LargeIndecomposable.CriticalSingularFigure16.DiagramData
      (C := ((selectedSplitBasic S p q).quotient_of_le_jacobson
        (relationIdeal S D P) (relationIdeal_le_jacobson S D P)).ProjectiveCategory) :=
  let F := quotientFunctor S D P
  LargeIndecomposable.CriticalSingularFigure16.repeatedObjectDiagram
    (End.of (F.map (selectedTau S p q P)))
    (F.map (selectedBeta S D)) (F.map (selectedGamma S D))

end LargeIndecomposable.CriticalFigure16Quotient
