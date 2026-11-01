module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.RepresentationType.Obstructions.RepresentationFiniteRayQuotient
public import LargeIndecomposable.Cleaving.ClosedChains.Figure16CoefficientCompiler
public import LargeIndecomposable.Cleaving.ClosedChains.Figure13EPrintedSeparation
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure16Quotient

@[expose] public section

/-!
# The exact Figure-16 quotient retraction

This file specializes the occurrence-sensitive Figure-16 coefficient compiler
to the exact two-relation selected-corner quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalFigure16Quotient

open LargeIndecomposable.ClosedZigzagCrossUniverse
open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.CriticalFigure14Quotient
open LargeIndecomposable.CriticalSingularFigure16
open LargeIndecomposable.CriticalSingularFigure16Pairs
open LargeIndecomposable.SingularPairNormalization
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

omit [IsAlgClosed k] in
private theorem composablePair_eq_of_firstArrow_eq_of_targetObj_eq
    (p q : ComposablePair (C := S.ProjectiveCategory))
    (hfirst : p.firstArrow = q.firstArrow)
    (htargetObj : p.secondArrow.target.obj.as =
      q.secondArrow.target.obj.as) : p = q := by
  rcases p with ⟨ps, pm, pt, pf, pg⟩
  rcases q with ⟨qs, qm, qt, qf, qg⟩
  dsimp only [ComposablePair.firstArrow, ComposablePair.secondArrow] at hfirst htargetObj ⊢
  cases hfirst
  have htarget : pt = qt := by
    apply LargeIndecomposable.RayVertex.ext
    exact LargeIndecomposable.BGRSRayCategory.ext htargetObj
  cases htarget
  have hg : pg = qg :=
    (LargeIndecomposable.rayQuiver_hom_subsingleton pm pt).allEq pg qg
  cases hg
  rfl

omit [IsAlgClosed k] in
/-- Distinct singular pairs with the same first arrow have distinct branch
targets.  Parallel irreducible ray arrows with the same endpoints are unique. -/
theorem branchTarget_ne_of_ne_of_firstArrow_eq
    {p q : SingularPair (C := S.ProjectiveCategory)}
    (hpq : p ≠ q) (hfirst : p.1.firstArrow = q.1.firstArrow) :
    p.1.secondArrow.target.obj.as ≠
      q.1.secondArrow.target.obj.as := by
  intro htargetObj
  apply hpq
  apply Subtype.ext
  exact composablePair_eq_of_firstArrow_eq_of_targetObj_eq S p.1 q.1
    hfirst htargetObj

omit [IsAlgClosed k] in
/-- The two branch objects remain distinct in the duplicate-free selected
corner whenever the singular pairs themselves are distinct. -/
theorem selectedBeta_ne_gamma
    {p q : SingularPair (C := S.ProjectiveCategory)}
    (hpq : p ≠ q) (hfirst : p.1.firstArrow = q.1.firstArrow) :
    selectedBetaObj S p q ≠ selectedGammaObj S p q := by
  intro hselected
  apply branchTarget_ne_of_ne_of_firstArrow_eq S hpq hfirst
  let E := SelectedCorner.projectiveFunctor S
    (finsetPrimitiveEmbedding (selectedVertices S p q))
  have hamb := congrArg (fun X ↦ E.obj X) hselected
  dsimp only [E, selectedBetaObj, selectedGammaObj] at hamb
  simpa only [SelectedCorner.projectiveFunctor_obj_finsetProjectiveObj_eq,
    ComposablePair.secondArrow]
    using hamb

/-- The split-basic algebra underlying the exact Figure-16 quotient. -/
abbrev quotientSplitBasic
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :=
  (selectedSplitBasic S p q).quotient_of_le_jacobson
    (relationIdeal S D P) (relationIdeal_le_jacobson S D P)

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- The selected copy of the common middle parameter still generates the
full endomorphism Jacobson radical before quotienting. -/
theorem selectedTau_span_eq_jacobson
    {p q : SingularPair (C := S.ProjectiveCategory)}
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    twoSidedEndomorphismSpan k (End.of (selectedTau S p q P)) =
      (Ring.jacobson (End (selectedMiddleObj S p q))).restrictScalars k := by
  exact finsetProjectiveEnd_span_eq_jacobson (k := k) S
    (selectedVertices S p q) p.1.middle.obj.as
    (middle_mem_selectedVertices S p q) P.tau P.span_eq

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- The surviving quotient image of `tau` generates the quotient middle
endomorphism radical. -/
theorem quotientTau_span_eq_jacobson
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    let F := quotientFunctor S D P
    twoSidedEndomorphismSpan k
        (End.of (F.map (selectedTau S p q P))) =
      (Ring.jacobson
        (End (F.obj (selectedMiddleObj S p q)))).restrictScalars k := by
  dsimp only
  letI : Module.Finite k
      (selectedCorner S p q ⧸ (relationIdeal S D P).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D P).asIdeal
  simpa only using
    (selectedSplitBasic S p q).projectiveQuotientFunctor_end_span_eq_jacobson
      (relationIdeal S D P) (relationIdeal_le_jacobson S D P)
      (selectedMiddleObj S p q) (End.of (selectedTau S p q P))
      (selectedTau_span_eq_jacobson S (q := q) P)

/-- The quotient middle parameter, retaining its inherited transit
orientation and exact radical-generation property. -/
def quotientPowerParameter
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    OrientedRadicalPowerParameter (k := k)
      ((quotientFunctor S D P).obj (selectedMiddleObj S p q)) := by
  let F := quotientFunctor S D P
  letI : Module.Finite k
      (selectedCorner S p q ⧸ (relationIdeal S D P).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D P).asIdeal
  let tauBar : End (F.obj (selectedMiddleObj S p q)) :=
    End.of (F.map (selectedTau S p q P))
  have hspan : twoSidedEndomorphismSpan k tauBar =
      (Ring.jacobson
        (End (F.obj (selectedMiddleObj S p q)))).restrictScalars k :=
    quotientTau_span_eq_jacobson S D P
  have htauJ : tauBar ∈
      Ring.jacobson (End (F.obj (selectedMiddleObj S p q))) := by
    have hmem := LargeIndecomposable.mem_twoSidedEndomorphismSpan k tauBar
    rw [hspan] at hmem
    exact hmem
  have htau0 : tauBar ≠ 0 := by
    have hmap := quotientFunctor_map_selectedTau_ne_zero S D P
    intro hzero
    apply hmap
    exact congrArg End.asHom hzero
  have horientSelected :
      LargeIndecomposable.AllowsTransit (selectedTau S p q P) ∨
        LargeIndecomposable.AllowsCotransit (selectedTau S p q P) := by
    rcases P.power_factorization with hT | hC
    · exact Or.inl (finsetProjectiveHom_allowsTransit (k := k) S
        (selectedVertices S p q)
        (middle_mem_selectedVertices S p q)
        (middle_mem_selectedVertices S p q) P.tau.asHom
        hT.allows_transit)
    · exact Or.inr (finsetProjectiveHom_allowsCotransit (k := k) S
        (selectedVertices S p q)
        (middle_mem_selectedVertices S p q)
        (middle_mem_selectedVertices S p q) P.tau.asHom
        hC.allows_cotransit)
  have horientBar :
      LargeIndecomposable.AllowsTransit (F.map (selectedTau S p q P)) ∨
        LargeIndecomposable.AllowsCotransit
          (F.map (selectedTau S p q P)) := by
    rcases horientSelected with hT | hC
    · exact Or.inl
        (LargeIndecomposable.fullLinearFunctor_map_allowsTransit
          (k := k) F (selectedTau S p q P) hT)
    · exact Or.inr
        (LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
          (k := k) F (selectedTau S p q P) hC)
  exact orientedRadicalPowerParameter_of_span_eq
    tauBar htauJ htau0 hspan horientBar

omit [IsAlgClosed k] in
@[simp] theorem quotientPowerParameter_tau
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientPowerParameter S D P).tau =
      End.of ((quotientFunctor S D P).map (selectedTau S p q P)) :=
  rfl

/-- Representation-finiteness makes the chosen beta representative a full
generator of its ambient branch Hom space. -/
theorem beta_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    twoSidedEndomorphismSpan k D.beta.hom = ⊤ := by
  obtain ⟨Z⟩ := nonempty_zeroPairRadicalSandwich p D.pZero
  change twoSidedEndomorphismSpan k D.pZero.second.hom = ⊤
  rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
    k Z.left_unitRayEquivalent]
  exact
    (LargeIndecomposable.RoiterFigure13EAmbient.zeroPairRadicalSandwich_full_outer_spans
      S hfinite Z).1

/-- The aligned gamma representative is likewise a full branch generator. -/
theorem gamma_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    twoSidedEndomorphismSpan k D.alignedGamma = ⊤ := by
  obtain ⟨Z⟩ := D.nonempty_alignedGammaAlphaRadicalSandwich
  rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
    k Z.left_unitRayEquivalent]
  exact
    (LargeIndecomposable.RoiterFigure13EAmbient.zeroPairRadicalSandwich_full_outer_spans
      S hfinite Z).1

/-- The selected beta arrow remains a full branch generator. -/
theorem selectedBeta_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    twoSidedEndomorphismSpan k (selectedBeta S D) = ⊤ :=
  finsetProjectiveHom_span_eq_top (k := k) S
    (selectedVertices S p q)
    (betaTarget_mem_selectedVertices S p q)
    (middle_mem_selectedVertices S p q) D.beta.hom
    (beta_span_eq_top S hfinite D)

/-- The selected gamma arrow remains a full branch generator. -/
theorem selectedGamma_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    twoSidedEndomorphismSpan k (selectedGamma S D) = ⊤ :=
  finsetProjectiveHom_span_eq_top (k := k) S
    (selectedVertices S p q)
    (gammaTarget_mem_selectedVertices S p q)
    (middle_mem_selectedVertices S p q) D.alignedGamma
    (gamma_span_eq_top S hfinite D)

/-- The selected beta branch object is distinct from the common middle. -/
theorem selectedBeta_ne_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    selectedBetaObj S p q ≠ selectedMiddleObj S p q := by
  apply projectiveObj_ne_of_val_mem_jacobson_of_span_eq_top
    (selectedSplitBasic S p q) (selectedBeta S D)
  · exact finsetProjectiveHom_val_mem_jacobson S
      (selectedVertices S p q)
      (betaTarget_mem_selectedVertices S p q)
      (middle_mem_selectedVertices S p q) D.beta.hom
      (representative_val_mem_jacobson S D.beta)
  · exact selectedBeta_span_eq_top S hfinite D

/-- The selected gamma branch object is distinct from the common middle. -/
theorem selectedGamma_ne_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    selectedGammaObj S p q ≠ selectedMiddleObj S p q := by
  apply projectiveObj_ne_of_val_mem_jacobson_of_span_eq_top
    (selectedSplitBasic S p q) (selectedGamma S D)
  · exact finsetProjectiveHom_val_mem_jacobson S
      (selectedVertices S p q)
      (gammaTarget_mem_selectedVertices S p q)
      (middle_mem_selectedVertices S p q) D.alignedGamma
      (by
        rw [alignedGamma_val S D]
        exact representative_val_mem_jacobson S D.gamma)
  · exact selectedGamma_span_eq_top S hfinite D

omit [IsAlgClosed k]
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] in
/-- Quotienting by the radical Figure-16 ideal preserves distinct selected
primitive-projective objects. -/
theorem quotientFunctor_obj_ne_of_ne
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    {X Y : (selectedSplitBasic S p q).ProjectiveCategory}
    (hXY : X ≠ Y) :
    (quotientFunctor S D P).obj X ≠ (quotientFunctor S D P).obj Y := by
  intro h
  apply hXY
  apply (selectedSplitBasic S p q).projectiveVertex_injective
  have hv := congrArg (quotientSplitBasic S D P).projectiveVertex h
  simpa only
      [SplitBasicIdempotents.projectiveQuotientFunctor_obj_projectiveVertex]
    using hv

/-- The quotient beta object remains distinct from the quotient middle. -/
theorem quotientBeta_ne_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).obj (selectedBetaObj S p q) ≠
      (quotientFunctor S D P).obj (selectedMiddleObj S p q) :=
  quotientFunctor_obj_ne_of_ne S D P (selectedBeta_ne_middle S hfinite D)

/-- The quotient gamma object remains distinct from the quotient middle. -/
theorem quotientGamma_ne_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).obj (selectedGammaObj S p q) ≠
      (quotientFunctor S D P).obj (selectedMiddleObj S p q) :=
  quotientFunctor_obj_ne_of_ne S D P (selectedGamma_ne_middle S hfinite D)

omit [IsAlgClosed k] in
/-- Distinct common-first singular pairs retain distinct branch objects in
the exact quotient. -/
theorem quotientBeta_ne_gamma
    {p q : SingularPair (C := S.ProjectiveCategory)}
    (hpq : p ≠ q) {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    (quotientFunctor S D P).obj (selectedBetaObj S p q) ≠
      (quotientFunctor S D P).obj (selectedGammaObj S p q) :=
  quotientFunctor_obj_ne_of_ne S D P
    (selectedBeta_ne_gamma S hpq hfirst)

/-- Full beta generation survives the exact quotient. -/
theorem quotientBeta_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    twoSidedEndomorphismSpan k
      ((quotientFunctor S D P).map (selectedBeta S D)) = ⊤ :=
  LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (quotientFunctor S D P) (selectedBeta S D)
    (selectedBeta_span_eq_top S hfinite D)

/-- Full gamma generation survives the exact quotient. -/
theorem quotientGamma_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    twoSidedEndomorphismSpan k
      ((quotientFunctor S D P).map (selectedGamma S D)) = ⊤ :=
  LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (quotientFunctor S D P) (selectedGamma S D)
    (selectedGamma_span_eq_top S hfinite D)

omit [IsAlgClosed k] in
/-- The selected beta representative retains a nonzero class in the first
radical layer of the selected corner. -/
theorem selectedBeta_val_not_mem_jacobson_sq
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    (selectedBeta S D).1 ∉
      Ring.jacobson (selectedCorner S p q) *
        Ring.jacobson (selectedCorner S p q) := by
  intro hsq
  apply representative_val_not_mem_jacobson_sq S D.beta
  have hamb := SelectedCorner.val_mem_jacobson_sq_of_mem_jacobson_sq
    S (finsetPrimitiveEmbedding (selectedVertices S p q))
      (selectedBeta S D).1 hsq
  simpa only [finsetProjectiveHom_val_val] using hamb

omit [IsAlgClosed k] in
/-- The selected aligned gamma representative likewise retains a nonzero
first-radical-layer class. -/
theorem selectedGamma_val_not_mem_jacobson_sq
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    (selectedGamma S D).1 ∉
      Ring.jacobson (selectedCorner S p q) *
        Ring.jacobson (selectedCorner S p q) := by
  intro hsq
  apply representative_val_not_mem_jacobson_sq S D.gamma
  have hamb := SelectedCorner.val_mem_jacobson_sq_of_mem_jacobson_sq
    S (finsetPrimitiveEmbedding (selectedVertices S p q))
      (selectedGamma S D).1 hsq
  simpa only [finsetProjectiveHom_val_val, alignedGamma_val] using hamb

omit [IsAlgClosed k] in
/-- The quotient beta arrow retains its nonzero first-radical-layer class. -/
theorem quotientBeta_val_not_mem_jacobson_sq
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    ((quotientFunctor S D P).map (selectedBeta S D)).1 ∉
      Ring.jacobson (selectedCorner S p q ⧸
          (relationIdeal S D P).asIdeal) *
        Ring.jacobson (selectedCorner S p q ⧸
          (relationIdeal S D P).asIdeal) := by
  simpa only [SplitBasicIdempotents.projectiveQuotientFunctor_map_val] using
    LargeIndecomposable.TwoSidedIdeal.quotient_mk_not_mem_jacobson_sq
      (relationIdeal S D P) (relationIdeal_le_jacobson S D P)
      (by
        simpa only [show (2 : ℕ) = 1 + 1 by omega,
          Ideal.IsTwoSided.pow_add, Submodule.pow_one] using
            relationIdeal_le_jacobson_sq S D P)
      (selectedBeta S D).1 (selectedBeta_val_not_mem_jacobson_sq S D)

omit [IsAlgClosed k] in
/-- The quotient gamma arrow retains its nonzero first-radical-layer class. -/
theorem quotientGamma_val_not_mem_jacobson_sq
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    ((quotientFunctor S D P).map (selectedGamma S D)).1 ∉
      Ring.jacobson (selectedCorner S p q ⧸
          (relationIdeal S D P).asIdeal) *
        Ring.jacobson (selectedCorner S p q ⧸
          (relationIdeal S D P).asIdeal) := by
  simpa only [SplitBasicIdempotents.projectiveQuotientFunctor_map_val] using
    LargeIndecomposable.TwoSidedIdeal.quotient_mk_not_mem_jacobson_sq
      (relationIdeal S D P) (relationIdeal_le_jacobson S D P)
      (by
        simpa only [show (2 : ℕ) = 1 + 1 by omega,
          Ideal.IsTwoSided.pow_add, Submodule.pow_one] using
            relationIdeal_le_jacobson_sq S D P)
      (selectedGamma S D).1 (selectedGamma_val_not_mem_jacobson_sq S D)

omit [IsAlgClosed k] in
/-- The selected beta arrow inherits the singular-pair transit direction. -/
theorem selectedBeta_allowsTransit
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    LargeIndecomposable.AllowsTransit (selectedBeta S D) :=
  finsetProjectiveHom_allowsTransit (k := k) S
    (selectedVertices S p q)
    (betaTarget_mem_selectedVertices S p q)
    (middle_mem_selectedVertices S p q) D.beta.hom
    (zeroRepresentatives_second_allowsTransit (k := k) D.pZero)

omit [IsAlgClosed k] in
/-- The selected aligned gamma arrow inherits the same transit direction. -/
theorem selectedGamma_allowsTransit
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    LargeIndecomposable.AllowsTransit (selectedGamma S D) := by
  obtain ⟨Z⟩ := D.nonempty_alignedGammaAlphaRadicalSandwich
  have hZTransit : LargeIndecomposable.AllowsTransit Z.left :=
    (HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) Z.left).resolve_right
        Z.left_not_allowsCotransit
  apply finsetProjectiveHom_allowsTransit (k := k) S
    (selectedVertices S p q)
    (gammaTarget_mem_selectedVertices S p q)
    (middle_mem_selectedVertices S p q) D.alignedGamma
  exact hZTransit.of_unitRayEquivalent
    ((LargeIndecomposable.unitRaySetoid _ _).symm
      Z.left_unitRayEquivalent)

omit [IsAlgClosed k] in
/-- Beta transit descends through the full quotient functor. -/
theorem quotientBeta_allowsTransit
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    LargeIndecomposable.AllowsTransit
      ((quotientFunctor S D P).map (selectedBeta S D)) :=
  LargeIndecomposable.fullLinearFunctor_map_allowsTransit
    (k := k) (quotientFunctor S D P) (selectedBeta S D)
    (selectedBeta_allowsTransit S D)

omit [IsAlgClosed k] in
/-- Gamma transit descends through the full quotient functor. -/
theorem quotientGamma_allowsTransit
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    LargeIndecomposable.AllowsTransit
      ((quotientFunctor S D P).map (selectedGamma S D)) :=
  LargeIndecomposable.fullLinearFunctor_map_allowsTransit
    (k := k) (quotientFunctor S D P) (selectedGamma S D)
    (selectedGamma_allowsTransit S D)

private theorem quotientBranch_not_allowsCotransit
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    {B : S.ProjectiveCategory}
    (hB : S.projectiveVertex B ∈ selectedVertices S p q)
    (branch : B ⟶ p.1.middle.obj.as)
    (hbranchSpan : twoSidedEndomorphismSpan k branch = ⊤)
    (hbranchTransit : LargeIndecomposable.AllowsTransit branch)
    (hbranchNotC : ¬ LargeIndecomposable.AllowsCotransit branch) :
    ¬ LargeIndecomposable.AllowsCotransit
      ((quotientFunctor S D P).map
        (finsetProjectiveHom S (selectedVertices S p q) hB
          (middle_mem_selectedVertices S p q) branch)) := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let t := selectedVertices S p q
  let Bsel := finsetProjectiveObj S t B hB
  let Msel := selectedMiddleObj S p q
  let branchSel : Bsel ⟶ Msel :=
    finsetProjectiveHom S t hB
      (middle_mem_selectedVertices S p q) branch
  let tauSel : End Msel := End.of (selectedTau S p q P)
  let F := quotientFunctor S D P
  let E := SelectedCorner.projectiveFunctor S (finsetPrimitiveEmbedding t)
  let eB := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S t B hB)
  let eM := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S t
      p.1.middle.obj.as (middle_mem_selectedVertices S p q))
  intro hbarC
  let tauBar : End (F.obj Msel) := End.of (F.map tauSel.asHom)
  obtain ⟨abar, hbarTransfer⟩ := hbarC tauBar
  let aSel : End Bsel := End.of (F.preimage abar.asHom)
  have hmapa : F.map aSel.asHom = abar.asHom := by
    simpa only [aSel] using F.map_preimage abar.asHom
  let dSel : Bsel ⟶ Msel :=
    branchSel ≫ tauSel.asHom - aSel.asHom ≫ branchSel
  have hmapzero : F.map dSel = 0 := by
    dsimp only [dSel]
    rw [F.map_sub, F.map_comp, F.map_comp, hmapa]
    change F.map branchSel ≫ tauBar.asHom -
      abar.asHom ≫ F.map branchSel = 0
    exact sub_eq_zero.mpr hbarTransfer
  have hdmem : dSel.1 ∈ (relationIdeal S D P).asIdeal :=
    ((selectedSplitBasic S p q).projectiveQuotientFunctor_map_eq_zero_iff
      (relationIdeal S D P) (relationIdeal_le_jacobson S D P) dSel).1
      hmapzero
  let dAmb : B ⟶ p.1.middle.obj.as :=
    CategoryTheory.Linear.homCongr k eB eM (E.map dSel)
  have hdval : dAmb.1 = dSel.1.1 := by
    exact homCongr_projectiveFunctorMap_val (k := k) S t hB
      (middle_mem_selectedVertices S p q) dSel
  have hdmemAmbient : dAmb.1 ∈ (ambientRelationIdeal S D P).asIdeal := by
    rw [hdval]
    exact val_mem_ambientRelationIdeal_of_mem_relationIdeal S D P hdmem
  have hdCorner : dAmb ∈
      finiteIdealCorner S (ambientRelationIdeal S D P)
        B p.1.middle.obj.as := hdmemAmbient
  have hdSpan : dAmb ∈ twoSidedEndomorphismSpan k
      (branch ≫ (P.tau ^ 2).asHom) :=
    ambientRelationIdeal_branch_corner_le_tauSquareSpan
      S D P branch hbranchSpan hbranchTransit hdCorner
  let aAmb : End B := End.of
    (CategoryTheory.Linear.homCongr k eB eB (E.map aSel.asHom))
  have haVal : aAmb.1 = aSel.1.1 := by
    exact homCongr_projectiveFunctorMap_val (k := k) S t hB hB aSel.asHom
  have htauSelVal : tauSel.1.1 = P.tau.1 := by
    simpa only [tauSel] using
      (finsetProjectiveHom_val_val S t
        (middle_mem_selectedVertices S p q)
        (middle_mem_selectedVertices S p q) P.tau.asHom)
  have hbranchSelVal : branchSel.1.1 = branch.1 := by
    simpa only [branchSel] using
      (finsetProjectiveHom_val_val S t hB
        (middle_mem_selectedVertices S p q) branch)
  have hdEq : dAmb =
      branch ≫ P.tau.asHom - aAmb.asHom ≫ branch := by
    apply Subtype.ext
    rw [hdval]
    dsimp only [dSel]
    change tauSel.1.1 * branchSel.1.1 -
        branchSel.1.1 * aSel.1.1 =
      P.tau.1 * branch.1 - branch.1 * aAmb.1
    rw [htauSelVal, hbranchSelVal, haVal]
  have hsquareTransit : LargeIndecomposable.AllowsTransit
      (branch ≫ (P.tau ^ 2).asHom) :=
    hbranchTransit.comp (P.power_allowsTransit 2)
  obtain ⟨b, hb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      hsquareTransit hdSpan
  let e : End p.1.middle.obj.as := 1 - b * P.tau
  have hbtauJ : b * P.tau ∈
      Ring.jacobson (End p.1.middle.obj.as) :=
    (Ring.jacobson (End p.1.middle.obj.as)).mul_mem_left
      b P.mem_jacobson
  have he : IsUnit e := isUnit_one_sub_of_mem_jacobson hbtauJ
  have htransfer : aAmb.asHom ≫ branch =
      branch ≫ (P.tau * e).asHom := by
    calc
      aAmb.asHom ≫ branch = branch ≫ P.tau.asHom - dAmb := by
        rw [hdEq]
        module
      _ = branch ≫ P.tau.asHom -
          (branch ≫ (P.tau ^ 2).asHom) ≫ b.asHom := by rw [hb]
      _ = branch ≫ (P.tau * e).asHom := by
        have hcoef : P.tau * e = P.tau - b * P.tau ^ 2 := by
          calc
            P.tau * e = e * P.tau := P.mul_comm P.tau e
            _ = (1 - b * P.tau) * P.tau := by rfl
            _ = 1 * P.tau - (b * P.tau) * P.tau := by rw [sub_mul]
            _ = P.tau - b * (P.tau * P.tau) := by
              rw [one_mul, mul_assoc]
            _ = P.tau - b * P.tau ^ 2 := by rw [pow_two]
        rw [hcoef]
        change branch ≫ P.tau.asHom -
            (branch ≫ (P.tau ^ 2).asHom) ≫ b.asHom =
          branch ≫ (P.tau.asHom - (b * P.tau ^ 2).asHom)
        rw [Preadditive.comp_sub, End.mul_def]
        simp only [Category.assoc]
  apply hbranchNotC
  exact allowsCotransit_of_transfer_of_adjoin_eq_top
    branch aAmb (P.tau * e) (P.adjoin_mul_unit_eq_top e he) htransfer

/-- The exact quotient preserves the prohibited cotransit direction of the
beta branch. -/
theorem quotientBeta_not_allowsCotransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    ¬ LargeIndecomposable.AllowsCotransit
      ((quotientFunctor S D P).map (selectedBeta S D)) := by
  apply quotientBranch_not_allowsCotransit S D P
    (betaTarget_mem_selectedVertices S p q) D.beta.hom
    (beta_span_eq_top S hfinite D)
    (zeroRepresentatives_second_allowsTransit (k := k) D.pZero)
  exact zeroRepresentatives_second_not_allowsCotransit D.pZero

/-- The exact quotient preserves the prohibited cotransit direction of the
aligned gamma branch. -/
theorem quotientGamma_not_allowsCotransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    ¬ LargeIndecomposable.AllowsCotransit
      ((quotientFunctor S D P).map (selectedGamma S D)) := by
  obtain ⟨Z⟩ := D.nonempty_alignedGammaAlphaRadicalSandwich
  have hZTransit : LargeIndecomposable.AllowsTransit Z.left :=
    (HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) Z.left).resolve_right
        Z.left_not_allowsCotransit
  apply quotientBranch_not_allowsCotransit S D P
    (gammaTarget_mem_selectedVertices S p q) D.alignedGamma
    (gamma_span_eq_top S hfinite D)
    (hZTransit.of_unitRayEquivalent
      ((LargeIndecomposable.unitRaySetoid _ _).symm
        Z.left_unitRayEquivalent))
  intro hC
  exact Z.left_not_allowsCotransit
    (hC.of_unitRayEquivalent Z.left_unitRayEquivalent)

set_option maxHeartbeats 3000000 in
/-- Lifting the full branch--`tau` cross obstruction to the selected corner
produces only a relation-ideal error one `tau`-degree deeper.  The deeper
error is absorbed into the ambient endpoint-radical perturbation, where the
original nonzero radical sandwich separates the branch path. -/
private theorem quotientBranchTauCross_separated
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    {B H : S.ProjectiveCategory}
    (hB : S.projectiveVertex B ∈ selectedVertices S p q)
    (hH : S.projectiveVertex H ∈ selectedVertices S p q)
    (branch : B ⟶ p.1.middle.obj.as)
    (opposite : H ⟶ p.1.middle.obj.as)
    (hbranchSpan : twoSidedEndomorphismSpan k branch = ⊤)
    (hbranchTransit : LargeIndecomposable.AllowsTransit branch)
    (Z : BGRSZeroPairRadicalSandwich branch D.alpha.hom)
    (hbranchAlpha : branch ≫ D.alpha.hom = 0)
    (hoppositeAlpha : opposite ≫ D.alpha.hom = 0) :
    let F := quotientFunctor S D P
    let Pbar := quotientPowerParameter S D P
    let branchSel := finsetProjectiveHom S (selectedVertices S p q) hB
      (middle_mem_selectedVertices S p q) branch
    let oppositeSel := finsetProjectiveHom S (selectedVertices S p q) hH
      (middle_mem_selectedVertices S p q) opposite
    F.map branchSel ≫ Pbar.tau.asHom ∉
      branchTauCrossObstruction (k := k) Pbar.tau
        (F.map branchSel) (F.map oppositeSel) := by
  dsimp only
  let t := selectedVertices S p q
  let Bsel := finsetProjectiveObj S t B hB
  let Hsel := finsetProjectiveObj S t H hH
  let Msel := selectedMiddleObj S p q
  let branchSel : Bsel ⟶ Msel :=
    finsetProjectiveHom S t hB
      (middle_mem_selectedVertices S p q) branch
  let oppositeSel : Hsel ⟶ Msel :=
    finsetProjectiveHom S t hH
      (middle_mem_selectedVertices S p q) opposite
  let tauSel : End Msel := End.of (selectedTau S p q P)
  let F := quotientFunctor S D P
  let Pbar := quotientPowerParameter S D P
  let E := SelectedCorner.projectiveFunctor S (finsetPrimitiveEmbedding t)
  let eB := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S t B hB)
  let eH := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S t H hH)
  let eM := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S t
      p.1.middle.obj.as (middle_mem_selectedVertices S p q))
  let landingSel : Bsel ⟶ Msel := branchSel ≫ tauSel.asHom
  let branchBar := F.map branchSel
  let oppositeBar := F.map oppositeSel
  let landingBar := branchBar ≫ Pbar.tau.asHom
  letI : Module.Finite k
      (selectedCorner S p q ⧸ (relationIdeal S D P).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D P).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S p q).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful E
  letI : LargeIndecomposable.HasRoiterTransitSquareAlternative
      k S.ProjectiveCategory :=
    LargeIndecomposable.RoiterFigure13EAmbient.hasRoiterTransitSquareAlternative
      S hfinite
  letI : Module.Finite k (End p.1.middle.obj.as) := by
    change Module.Finite k
      (p.1.middle.obj.as ⟶ p.1.middle.obj.as)
    infer_instance
  intro hmem
  rcases Submodule.mem_sup.mp hmem with ⟨u, hu, x, hx, hux⟩
  rcases Submodule.mem_sup.mp hu with ⟨r, hr, s, hs, hrs⟩
  rcases hr with ⟨cbar, hcbar, dbar, hdbar, hr⟩
  rcases hs with ⟨abar, hs⟩
  rcases hx with ⟨mubar, hx⟩
  have hbarEq :
      (cbar.asHom ≫ landingBar + landingBar ≫ dbar.asHom) +
          abar.asHom ≫ branchBar + mubar ≫ oppositeBar = landingBar := by
    calc
      (cbar.asHom ≫ landingBar + landingBar ≫ dbar.asHom) +
          abar.asHom ≫ branchBar + mubar ≫ oppositeBar =
        (r + s) + x := by
          rw [← hr, ← hs, ← hx]
          rfl
      _ = u + x := by rw [hrs]
      _ = landingBar := hux
  let cSel : End Bsel := End.of (F.preimage cbar.asHom)
  let dSel : End Msel := End.of (F.preimage dbar.asHom)
  let aSel : End Bsel := End.of (F.preimage abar.asHom)
  let muSel : Bsel ⟶ Hsel := F.preimage mubar
  have hmapc : F.map cSel.asHom = cbar.asHom := by
    simpa only [cSel] using F.map_preimage cbar.asHom
  have hmapd : F.map dSel.asHom = dbar.asHom := by
    simpa only [dSel] using F.map_preimage dbar.asHom
  have hmapa : F.map aSel.asHom = abar.asHom := by
    simpa only [aSel] using F.map_preimage abar.asHom
  have hmapmu : F.map muSel = mubar := F.map_preimage mubar
  have hcSel : cSel ∈ Ring.jacobson (End Bsel) :=
    (selectedSplitBasic S p q).projectiveQuotientFunctor_preimage_end_mem_jacobson
      (relationIdeal S D P) (relationIdeal_le_jacobson S D P) cbar hcbar
  have hdSel : dSel ∈ Ring.jacobson (End Msel) :=
    (selectedSplitBasic S p q).projectiveQuotientFunctor_preimage_end_mem_jacobson
      (relationIdeal S D P) (relationIdeal_le_jacobson S D P) dbar hdbar
  let zSel : Bsel ⟶ Msel :=
    landingSel -
      ((cSel.asHom ≫ landingSel + landingSel ≫ dSel.asHom) +
        aSel.asHom ≫ branchSel + muSel ≫ oppositeSel)
  have hzmap : F.map zSel = 0 := by
    dsimp only [zSel, landingSel]
    simp only [F.map_sub, F.map_add, F.map_comp,
      hmapc, hmapd, hmapa, hmapmu]
    change landingBar -
      ((cbar.asHom ≫ landingBar + landingBar ≫ dbar.asHom) +
        abar.asHom ≫ branchBar + mubar ≫ oppositeBar) = 0
    exact sub_eq_zero.mpr hbarEq.symm
  have hzmem : zSel.1 ∈ (relationIdeal S D P).asIdeal :=
    ((selectedSplitBasic S p q).projectiveQuotientFunctor_map_eq_zero_iff
      (relationIdeal S D P) (relationIdeal_le_jacobson S D P) zSel).1 hzmap
  let zAmb : B ⟶ p.1.middle.obj.as :=
    CategoryTheory.Linear.homCongr k eB eM (E.map zSel)
  have hzval : zAmb.1 = zSel.1.1 :=
    homCongr_projectiveFunctorMap_val (k := k) S t hB
      (middle_mem_selectedVertices S p q) zSel
  have hzAmbient : zAmb.1 ∈ (ambientRelationIdeal S D P).asIdeal := by
    rw [hzval]
    exact val_mem_ambientRelationIdeal_of_mem_relationIdeal S D P hzmem
  have hzSpan : zAmb ∈ twoSidedEndomorphismSpan k
      (branch ≫ (P.tau ^ 2).asHom) :=
    ambientRelationIdeal_branch_corner_le_tauSquareSpan
      S D P branch hbranchSpan hbranchTransit hzAmbient
  let cAmb : End B := End.of
    (CategoryTheory.Linear.homCongr k eB eB (E.map cSel.asHom))
  let dAmb : End p.1.middle.obj.as := End.of
    (CategoryTheory.Linear.homCongr k eM eM (E.map dSel.asHom))
  let aAmb : End B := End.of
    (CategoryTheory.Linear.homCongr k eB eB (E.map aSel.asHom))
  let muAmb : B ⟶ H :=
    CategoryTheory.Linear.homCongr k eB eH (E.map muSel)
  have hcVal : cAmb.1 = cSel.1.1 :=
    homCongr_projectiveFunctorMap_val (k := k) S t hB hB cSel.asHom
  have hdVal : dAmb.1 = dSel.1.1 :=
    homCongr_projectiveFunctorMap_val (k := k) S t
      (middle_mem_selectedVertices S p q)
      (middle_mem_selectedVertices S p q) dSel.asHom
  have haVal : aAmb.1 = aSel.1.1 :=
    homCongr_projectiveFunctorMap_val (k := k) S t hB hB aSel.asHom
  have hmuVal : muAmb.1 = muSel.1.1 :=
    homCongr_projectiveFunctorMap_val (k := k) S t hB hH muSel
  have hbranchVal : branchSel.1.1 = branch.1 := by
    simpa only [branchSel] using
      (finsetProjectiveHom_val_val S t hB
        (middle_mem_selectedVertices S p q) branch)
  have hoppositeVal : oppositeSel.1.1 = opposite.1 := by
    simpa only [oppositeSel] using
      (finsetProjectiveHom_val_val S t hH
        (middle_mem_selectedVertices S p q) opposite)
  have htauVal : tauSel.1.1 = P.tau.1 := by
    simpa only [tauSel] using
      (finsetProjectiveHom_val_val S t
        (middle_mem_selectedVertices S p q)
        (middle_mem_selectedVertices S p q) P.tau.asHom)
  have hcAmb : cAmb ∈ Ring.jacobson (End B) := by
    apply (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson B cAmb).2
    rw [hcVal]
    apply (SelectedCorner.mem_jacobson_iff_val_mem_jacobson
      S (finsetPrimitiveEmbedding t) cSel.1).1
    exact ((selectedSplitBasic S p q).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      Bsel cSel).1 hcSel
  have hdAmb : dAmb ∈ Ring.jacobson (End p.1.middle.obj.as) := by
    apply (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      p.1.middle.obj.as dAmb).2
    rw [hdVal]
    apply (SelectedCorner.mem_jacobson_iff_val_mem_jacobson
      S (finsetPrimitiveEmbedding t) dSel.1).1
    exact ((selectedSplitBasic S p q).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      Msel dSel).1 hdSel
  have hzEq : zAmb = branch ≫ P.tau.asHom -
      ((cAmb.asHom ≫ (branch ≫ P.tau.asHom) +
          (branch ≫ P.tau.asHom) ≫ dAmb.asHom) +
        aAmb.asHom ≫ branch + muAmb ≫ opposite) := by
    apply Subtype.ext
    rw [hzval]
    dsimp only [zSel, landingSel]
    change (tauSel.1.1 * branchSel.1.1) -
        ((tauSel.1.1 * branchSel.1.1) * cSel.1.1 +
          dSel.1.1 * (tauSel.1.1 * branchSel.1.1) +
          branchSel.1.1 * aSel.1.1 +
          oppositeSel.1.1 * muSel.1.1) =
      P.tau.1 * branch.1 -
        ((P.tau.1 * branch.1) * cAmb.1 +
          dAmb.1 * (P.tau.1 * branch.1) +
          branch.1 * aAmb.1 + opposite.1 * muAmb.1)
    rw [hcVal, hdVal, haVal, hmuVal, hbranchVal, hoppositeVal, htauVal]
  have hambientEq :
      (cAmb.asHom ≫ (branch ≫ P.tau.asHom) +
          (branch ≫ P.tau.asHom) ≫ dAmb.asHom) +
        aAmb.asHom ≫ branch + muAmb ≫ opposite + zAmb =
      branch ≫ P.tau.asHom := by
    rw [hzEq]
    module
  exact (branch_tau_not_endpoint_cross_add_deeper
    Z P hbranchTransit hbranchAlpha hoppositeAlpha
    cAmb hcAmb dAmb hdAmb aAmb muAmb zAmb hzSpan) hambientEq

/-- The beta--`tau` path is separated simultaneously from its complete
left-arm supplement and every composite through the gamma branch. -/
theorem quotientBetaTauCross_separated
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    let F := quotientFunctor S D P
    let Pbar := quotientPowerParameter S D P
    F.map (selectedBeta S D) ≫ Pbar.tau.asHom ∉
      branchTauCrossObstruction (k := k) Pbar.tau
        (F.map (selectedBeta S D)) (F.map (selectedGamma S D)) := by
  dsimp only
  obtain ⟨Z⟩ := nonempty_zeroPairRadicalSandwich p D.pZero
  exact quotientBranchTauCross_separated S hfinite D P
    (betaTarget_mem_selectedVertices S p q)
    (gammaTarget_mem_selectedVertices S p q)
    D.beta.hom D.alignedGamma (beta_span_eq_top S hfinite D)
    (zeroRepresentatives_second_allowsTransit (k := k) D.pZero)
    Z D.beta_alpha_zero D.alignedGamma_alpha_zero

/-- The symmetric gamma--`tau` path is separated simultaneously from its
complete left-arm supplement and every composite through beta. -/
theorem quotientGammaTauCross_separated
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    let F := quotientFunctor S D P
    let Pbar := quotientPowerParameter S D P
    F.map (selectedGamma S D) ≫ Pbar.tau.asHom ∉
      branchTauCrossObstruction (k := k) Pbar.tau
        (F.map (selectedGamma S D)) (F.map (selectedBeta S D)) := by
  dsimp only
  obtain ⟨Z⟩ := D.nonempty_alignedGammaAlphaRadicalSandwich
  have hZTransit : LargeIndecomposable.AllowsTransit Z.left :=
    (HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) Z.left).resolve_right
        Z.left_not_allowsCotransit
  have hgammaTransit : LargeIndecomposable.AllowsTransit D.alignedGamma :=
    hZTransit.of_unitRayEquivalent
      ((LargeIndecomposable.unitRaySetoid _ _).symm
        Z.left_unitRayEquivalent)
  exact quotientBranchTauCross_separated S hfinite D P
    (gammaTarget_mem_selectedVertices S p q)
    (betaTarget_mem_selectedVertices S p q)
    D.alignedGamma D.beta.hom (gamma_span_eq_top S hfinite D)
    hgammaTransit Z D.alignedGamma_alpha_zero D.beta_alpha_zero

/-- The exact quotient supplies both cross-compatible branch--`tau`
coefficients. -/
theorem nonempty_quotientBranchTauCrossCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    Nonempty (BranchTauCrossCoefficientData
      (k := k) (quotientPowerParameter S D P).tau
      ((quotientFunctor S D P).map (selectedBeta S D))
      ((quotientFunctor S D P).map (selectedGamma S D))) := by
  exact nonempty_branchTauCrossCoefficientData _ _ _
    (quotientBetaTauCross_separated S hfinite D P)
    (quotientGammaTauCross_separated S hfinite D P)

/-- The surviving beta--`tau` path is separated from its full left-arm
supplement obstruction in the exact Figure-16 quotient. -/
theorem quotientBetaSupplement_separated
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    let F := quotientFunctor S D P
    let Pbar := quotientPowerParameter S D P
    F.map (selectedBeta S D) ≫ Pbar.tau.asHom ∉
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) (F.map (selectedBeta S D)) Pbar.tau := by
  dsimp only
  let F := quotientFunctor S D P
  let Pbar := quotientPowerParameter S D P
  let betaBar := F.map (selectedBeta S D)
  letI : Module.Finite k
      (selectedCorner S p q ⧸ (relationIdeal S D P).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D P).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S p q).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (SelectedCorner.projectiveFunctor S
        (finsetPrimitiveEmbedding (selectedVertices S p q)))
  letI : ∀ U : (quotientSplitBasic S D P).ProjectiveCategory,
      Module.Finite k (End U) := fun U ↦ by
    change Module.Finite k (U ⟶ U)
    infer_instance
  have hnonzero : betaBar ≫ Pbar.tau.asHom ≠ 0 := by
    rw [show Pbar.tau.asHom = F.map (selectedTau S p q P) by rfl]
    rw [← F.map_comp]
    exact quotientFunctor_map_selectedBetaTau_ne_zero S hfinite D P
  exact
    LargeIndecomposable.RoiterFigure13E.leftArmSupplement_separated_of_not_allowsCotransit
      betaBar Pbar (quotientBeta_allowsTransit S D P)
      (quotientBeta_not_allowsCotransit S hfinite D P) hnonzero

/-- The surviving gamma--`tau` path is separated from its full left-arm
supplement obstruction in the exact Figure-16 quotient. -/
theorem quotientGammaSupplement_separated
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    let F := quotientFunctor S D P
    let Pbar := quotientPowerParameter S D P
    F.map (selectedGamma S D) ≫ Pbar.tau.asHom ∉
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) (F.map (selectedGamma S D)) Pbar.tau := by
  dsimp only
  let F := quotientFunctor S D P
  let Pbar := quotientPowerParameter S D P
  let gammaBar := F.map (selectedGamma S D)
  letI : Module.Finite k
      (selectedCorner S p q ⧸ (relationIdeal S D P).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D P).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S p q).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (SelectedCorner.projectiveFunctor S
        (finsetPrimitiveEmbedding (selectedVertices S p q)))
  letI : ∀ U : (quotientSplitBasic S D P).ProjectiveCategory,
      Module.Finite k (End U) := fun U ↦ by
    change Module.Finite k (U ⟶ U)
    infer_instance
  have hnonzero : gammaBar ≫ Pbar.tau.asHom ≠ 0 := by
    rw [show Pbar.tau.asHom = F.map (selectedTau S p q P) by rfl]
    rw [← F.map_comp]
    exact quotientFunctor_map_selectedGammaTau_ne_zero S hfinite D P
  exact
    LargeIndecomposable.RoiterFigure13E.leftArmSupplement_separated_of_not_allowsCotransit
      gammaBar Pbar (quotientGamma_allowsTransit S D P)
      (quotientGamma_not_allowsCotransit S hfinite D P) hnonzero

/-- A normalized beta--`tau` coefficient exists and kills the full beta-arm
supplement obstruction. -/
theorem nonempty_quotientBetaSupplementCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    let F := quotientFunctor S D P
    let Pbar := quotientPowerParameter S D P
    Nonempty (SupplementCoefficientData
      (k := k) (F.map (selectedBeta S D)) Pbar.tau) := by
  dsimp only
  exact nonempty_supplementCoefficientData _ _
    (quotientBetaSupplement_separated S hfinite D P)

/-- A normalized gamma--`tau` coefficient exists and kills the full
gamma-arm supplement obstruction. -/
theorem nonempty_quotientGammaSupplementCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    let F := quotientFunctor S D P
    let Pbar := quotientPowerParameter S D P
    Nonempty (SupplementCoefficientData
      (k := k) (F.map (selectedGamma S D)) Pbar.tau) := by
  dsimp only
  exact nonempty_supplementCoefficientData _ _
    (quotientGammaSupplement_separated S hfinite D P)

/-- A branch--`tau` supplement coefficient restricts along its branch to
the chosen first radical coefficient at the middle object. -/
private theorem branchSupplement_coefficient_eq_radicalCoefficient
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {B M : C} [Module.Finite k (End M)]
    [IsLocalRing (End M)] [IsArtinianRing (End M)]
    (branch : B ⟶ M)
    (P : OrientedRadicalPowerParameter (k := k) M)
    (residue : End M →ₐ[k] k)
    (middle : RadicalCoefficientData residue P.tau)
    (hresidue : ∀ a : End M,
      residue a = 0 ↔ a ∈ Ring.jacobson (End M))
    (supplement : SupplementCoefficientData
      (k := k) branch P.tau)
    (a : End M) :
    supplement.coefficient (branch ≫ a.asHom) =
      middle.coefficientOne a := by
  let c : k := residue a
  let n : End M := a - algebraMap k (End M) c
  have hnres : residue n = 0 := by
    dsimp only [n]
    rw [map_sub, AlgHom.commutes]
    change residue a - c = 0
    exact sub_self _
  have hnJ : n ∈ Ring.jacobson (End M) := (hresidue n).1 hnres
  obtain ⟨q, hq⟩ := P.transitData.generates n hnJ
  have hnRing : n = q * P.tau := by
    apply End.ext
    simpa only [End.mul_def] using hq
  have haRing : a = algebraMap k (End M) c + n := by
    dsimp only [n, c]
    abel
  have hbranchMem : branch ∈
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) branch P.tau := by
    apply (show LargeIndecomposable.RoiterFigure13E.leftOuterActionSubmodule
        (k := k) branch ≤
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) branch P.tau from le_sup_right)
    exact ⟨1, by simp [preEndomorphismLinearMap]⟩
  have hbranchZero : supplement.coefficient branch = 0 :=
    supplement.coefficient_eq_zero_of_mem hbranchMem
  have hlandingRight : supplement.coefficient
      ((branch ≫ P.tau.asHom) ≫ q.asHom) = residue q :=
    endpointRadicalCoefficient_comp_right
      (branch ≫ P.tau.asHom) residue hresidue
      supplement.coefficient supplement.normalized
      supplement.endpointRadical_le_ker q
  rw [haRing]
  change supplement.coefficient
      (branch ≫ ((algebraMap k (End M) c + n).asHom)) = _
  have hscalarHom : (algebraMap k (End M) c).asHom =
      c • (𝟙 M) := by
    change (c • (1 : End M)).asHom = c • (𝟙 M)
    rfl
  have hsumHom : (algebraMap k (End M) c + n).asHom =
      c • (𝟙 M) + n.asHom := by
    change (algebraMap k (End M) c).asHom + n.asHom = _
    rw [hscalarHom]
  rw [hsumHom, Preadditive.comp_add, Linear.comp_smul, Category.comp_id,
    supplement.coefficient.map_add, supplement.coefficient.map_smul,
    hbranchZero, smul_zero, zero_add]
  rw [hq, ← Category.assoc, hlandingRight]
  rw [middle.coefficientOne.map_add]
  have hscalar : middle.coefficientOne
      (algebraMap k (End M) c) = 0 := by
    rw [show algebraMap k (End M) c = c • (1 : End M) by
      symm
      rw [Algebra.smul_def, mul_one],
      middle.coefficientOne.map_smul,
      middle.coefficientOne_one, smul_zero]
  rw [hscalar, zero_add, hnRing, middle.coefficientOne_mul_tau]

/-- A first radical coefficient vanishes on a return through a branch which
prohibits cotransit. -/
private theorem radicalCoefficient_return_eq_zero_of_not_allowsCotransit
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {B M : C} [Module.Finite k (End M)]
    [IsLocalRing (End M)] [IsArtinianRing (End M)]
    (branch : B ⟶ M)
    (P : OrientedRadicalPowerParameter (k := k) M)
    (residue : End M →ₐ[k] k)
    (middle : RadicalCoefficientData residue P.tau)
    (hresidue : ∀ a : End M,
      residue a = 0 ↔ a ∈ Ring.jacobson (End M))
    (hbranchNotC : ¬ LargeIndecomposable.AllowsCotransit branch)
    (g : M ⟶ B)
    (hreturn : residue (End.of (g ≫ branch)) = 0) :
    middle.coefficientOne (End.of (g ≫ branch)) = 0 := by
  let a : End M := End.of (g ≫ branch)
  have haJ : a ∈ Ring.jacobson (End M) :=
    (hresidue a).1 hreturn
  obtain ⟨q, hq⟩ := P.transitData.generates a haJ
  have haRing : a = q * P.tau := by
    apply End.ext
    simpa only [End.mul_def] using hq
  change middle.coefficientOne a = 0
  rw [haRing, middle.coefficientOne_mul_tau]
  by_contra hqres
  have hqUnit : IsUnit q := by
    by_contra hqNotUnit
    exact hqres ((hresidue q).2
      ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End M) q).2 hqNotUnit))
  let b : End B := End.of (branch ≫ g)
  have htransfer : b.asHom ≫ branch =
      branch ≫ (P.tau * q).asHom := by
    calc
      b.asHom ≫ branch = branch ≫ (g ≫ branch) := by
        simp only [b, Category.assoc]
      _ = branch ≫ a.asHom := rfl
      _ = branch ≫ (q * P.tau).asHom := by rw [haRing]
      _ = branch ≫ (P.tau * q).asHom := by rw [P.mul_comm]
  apply hbranchNotC
  exact allowsCotransit_of_transfer_of_adjoin_eq_top
    branch b (P.tau * q) (P.adjoin_mul_unit_eq_top q hqUnit) htransfer

/-- The canonical split-basic residue at each Figure-16 occurrence in the
exact quotient. -/
def quotientVertexResidue
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    (a : LargeIndecomposable.CriticalSingularFigure16.Vertex) :
    End ((quotientDiagram S D P).object a) →ₐ[k] k := by
  cases a <;> exact (quotientSplitBasic S D P).projectiveEndResidue _

omit [IsAlgClosed k] in
/-- The quotient middle parameter admits the normalized first radical
coefficient used at the central `tau` occurrence. -/
theorem nonempty_quotientRadicalCoefficientData
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    let F := quotientFunctor S D P
    let T := quotientSplitBasic S D P
    let Pbar := quotientPowerParameter S D P
    Nonempty (RadicalCoefficientData
      (T.projectiveEndResidue (F.obj (selectedMiddleObj S p q)))
      Pbar.tau) := by
  dsimp only
  let F := quotientFunctor S D P
  let T := quotientSplitBasic S D P
  let Pbar := quotientPowerParameter S D P
  let Mbar := F.obj (selectedMiddleObj S p q)
  let residue := T.projectiveEndResidue Mbar
  letI : Module.Finite k
      (selectedCorner S p q ⧸ (relationIdeal S D P).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D P).asIdeal
  have hresTau : residue Pbar.tau = 0 := by
    dsimp only [residue]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    exact Pbar.mem_jacobson
  exact exists_radicalCoefficientData residue Pbar.tau Pbar.ne_zero
    hresTau (fun a ↦ T.projectiveEnd_isUnit_iff_residue_ne_zero Mbar a)

set_option maxHeartbeats 3000000 in
/-- Once the two branch--`tau` supplement coefficients kill the opposite
branch composites, all remaining Figure-16 coefficient identities follow
from radical-square separation, residues, transit, and the local radical
coefficient. -/
theorem nonempty_quotientRepeatedObjectCoefficientData_of_branchTauCross
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    (hpq : p ≠ q) {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as)
    (cross : BranchTauCrossCoefficientData
      (k := k) (quotientPowerParameter S D P).tau
      ((quotientFunctor S D P).map (selectedBeta S D))
      ((quotientFunctor S D P).map (selectedGamma S D))) :
    Nonempty (RepeatedObjectCoefficientData
      (k := k) (quotientPowerParameter S D P).tau
      ((quotientFunctor S D P).map (selectedBeta S D))
      ((quotientFunctor S D P).map (selectedGamma S D))) := by
  let F := quotientFunctor S D P
  let T := quotientSplitBasic S D P
  let Pbar := quotientPowerParameter S D P
  let Bbar := F.obj (selectedBetaObj S p q)
  let Hbar := F.obj (selectedGammaObj S p q)
  let Mbar := F.obj (selectedMiddleObj S p q)
  let beta : Bbar ⟶ Mbar := F.map (selectedBeta S D)
  let gamma : Hbar ⟶ Mbar := F.map (selectedGamma S D)
  let residueB := T.projectiveEndResidue Bbar
  let residueH := T.projectiveEndResidue Hbar
  let residueM := T.projectiveEndResidue Mbar
  letI : Module.Finite k
      (selectedCorner S p q ⧸ (relationIdeal S D P).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D P).asIdeal
  letI : ∀ Z : T.ProjectiveCategory, Module.Finite k (End Z) :=
    fun Z ↦ by
      change Module.Finite k (Z ⟶ Z)
      infer_instance
  have hBM : Bbar ≠ Mbar := quotientBeta_ne_middle S hfinite D P
  have hHM : Hbar ≠ Mbar := quotientGamma_ne_middle S hfinite D P
  have hBH : Bbar ≠ Hbar := quotientBeta_ne_gamma S hpq D P
  have hresidueM (a : End Mbar) :
      residueM a = 0 ↔ a ∈ Ring.jacobson (End Mbar) := by
    dsimp only [residueM]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hbetaSq : beta.1 ∉
      Ring.jacobson (selectedCorner S p q ⧸
          (relationIdeal S D P).asIdeal) *
        Ring.jacobson (selectedCorner S p q ⧸
          (relationIdeal S D P).asIdeal) :=
    quotientBeta_val_not_mem_jacobson_sq S D P
  have hgammaSq : gamma.1 ∉
      Ring.jacobson (selectedCorner S p q ⧸
          (relationIdeal S D P).asIdeal) *
        Ring.jacobson (selectedCorner S p q ⧸
          (relationIdeal S D P).asIdeal) :=
    quotientGamma_val_not_mem_jacobson_sq S D P
  let betaZero : (Bbar ⟶ Mbar) →ₗ[k] k :=
    T.projectiveHomFirstRadicalCoefficient hBM.symm beta hbetaSq
  let gammaZero : (Hbar ⟶ Mbar) →ₗ[k] k :=
    T.projectiveHomFirstRadicalCoefficient hHM.symm gamma hgammaSq
  obtain ⟨middle⟩ := nonempty_quotientRadicalCoefficientData S D P
  have hresTau : residueM Pbar.tau = 0 :=
    (hresidueM Pbar.tau).2 Pbar.mem_jacobson
  have htauValJ : Pbar.tau.1 ∈
      Ring.jacobson (selectedCorner S p q ⧸
        (relationIdeal S D P).asIdeal) :=
    (T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      Mbar Pbar.tau).1 Pbar.mem_jacobson
  have hbetaValJ : beta.1 ∈
      Ring.jacobson (selectedCorner S p q ⧸
        (relationIdeal S D P).asIdeal) :=
    ProjectiveCategory.offDiagonal_val_mem_jacobson T hBM beta
  have hgammaValJ : gamma.1 ∈
      Ring.jacobson (selectedCorner S p q ⧸
        (relationIdeal S D P).asIdeal) :=
    ProjectiveCategory.offDiagonal_val_mem_jacobson T hHM gamma
  have hbetaT := quotientBeta_allowsTransit S D P
  have hgammaT := quotientGamma_allowsTransit S D P
  have hbetaSpan := quotientBeta_span_eq_top S hfinite D P
  have hgammaSpan := quotientGamma_span_eq_top S hfinite D P
  have hbetaNotC := quotientBeta_not_allowsCotransit S hfinite D P
  have hgammaNotC := quotientGamma_not_allowsCotransit S hfinite D P
  have hbetaTauRight (a : End Mbar) :
      cross.betaSupplement.coefficient
          ((beta ≫ Pbar.tau.asHom) ≫ a.asHom) = residueM a :=
    endpointRadicalCoefficient_comp_right
      (beta ≫ Pbar.tau.asHom) residueM hresidueM
      cross.betaSupplement.coefficient cross.betaSupplement.normalized
      cross.betaSupplement.endpointRadical_le_ker a
  have hgammaTauRight (a : End Mbar) :
      cross.gammaSupplement.coefficient
          ((gamma ≫ Pbar.tau.asHom) ≫ a.asHom) = residueM a :=
    endpointRadicalCoefficient_comp_right
      (gamma ≫ Pbar.tau.asHom) residueM hresidueM
      cross.gammaSupplement.coefficient cross.gammaSupplement.normalized
      cross.gammaSupplement.endpointRadical_le_ker a
  refine ⟨{
    residueM := residueM
    residueB := residueB
    residueH := residueH
    tauOne := middle.coefficientOne
    betaZero := betaZero
    gammaZero := gammaZero
    betaTau := cross.betaSupplement.coefficient
    gammaTau := cross.gammaSupplement.coefficient
    tauOne_post := ?_
    tauOne_pre := ?_
    residueM_tau_post := ?_
    residueM_tau_pre := ?_
    betaZero_post := ?_
    betaZero_pre := ?_
    gammaZero_post := ?_
    gammaZero_pre := ?_
    residueB_beta_return := ?_
    residueH_gamma_return := ?_
    residueM_beta_return := ?_
    residueM_gamma_return := ?_
    tauOne_beta_return := ?_
    tauOne_gamma_return := ?_
    betaZero_tau := ?_
    gammaZero_tau := ?_
    betaZero_cross := ?_
    gammaZero_cross := ?_
    betaTau_post := ?_
    gammaTau_post := ?_
    betaTau_tau := ?_
    gammaTau_tau := ?_
    betaTau_outer := ?_
    gammaTau_outer := ?_
    betaTau_cross := cross.beta_cross
    gammaTau_cross := cross.gamma_cross }⟩
  · intro a
    simpa only [End.mul_def] using middle.coefficientOne_mul_tau a
  · intro a
    have hcomm := Pbar.mul_comm Pbar.tau a
    rw [show End.of (a.asHom ≫ Pbar.tau.asHom) =
        Pbar.tau * a by
      apply End.ext
      rfl,
      hcomm, middle.coefficientOne_mul_tau]
  · intro a
    rw [show End.of (Pbar.tau.asHom ≫ a.asHom) =
        a * Pbar.tau by
      apply End.ext
      rfl,
      map_mul, hresTau, mul_zero]
  · intro a
    rw [show End.of (a.asHom ≫ Pbar.tau.asHom) =
        Pbar.tau * a by
      apply End.ext
      rfl,
      map_mul, hresTau, zero_mul]
  · intro a
    exact T.projectiveHomFirstRadicalCoefficient_comp_right
      hBM.symm beta hbetaSq a
  · intro a
    exact T.projectiveHomFirstRadicalCoefficient_comp_left
      hBM.symm beta hbetaSq a
  · intro a
    exact T.projectiveHomFirstRadicalCoefficient_comp_right
      hHM.symm gamma hgammaSq a
  · intro a
    exact T.projectiveHomFirstRadicalCoefficient_comp_left
      hHM.symm gamma hgammaSq a
  · intro g
    exact projectiveEndResidue_comp_eq_zero_of_ne T hBM beta g
  · intro g
    exact projectiveEndResidue_comp_eq_zero_of_ne T hHM gamma g
  · intro g
    exact projectiveEndResidue_comp_eq_zero_of_ne T hBM.symm g beta
  · intro g
    exact projectiveEndResidue_comp_eq_zero_of_ne T hHM.symm g gamma
  · intro g
    apply radicalCoefficient_return_eq_zero_of_not_allowsCotransit
      beta Pbar residueM middle hresidueM hbetaNotC g
    exact projectiveEndResidue_comp_eq_zero_of_ne T hBM.symm g beta
  · intro g
    apply radicalCoefficient_return_eq_zero_of_not_allowsCotransit
      gamma Pbar residueM middle hresidueM hgammaNotC g
    exact projectiveEndResidue_comp_eq_zero_of_ne T hHM.symm g gamma
  · intro g
    apply T.projectiveHomFirstRadicalCoefficient_eq_zero_of_mem_jacobson_sq
      hBM.symm beta hbetaSq
    exact Ideal.mul_mem_mul htauValJ
      (ProjectiveCategory.offDiagonal_val_mem_jacobson T hBM g)
  · intro g
    apply T.projectiveHomFirstRadicalCoefficient_eq_zero_of_mem_jacobson_sq
      hHM.symm gamma hgammaSq
    exact Ideal.mul_mem_mul htauValJ
      (ProjectiveCategory.offDiagonal_val_mem_jacobson T hHM g)
  · intro g
    apply T.projectiveHomFirstRadicalCoefficient_eq_zero_of_mem_jacobson_sq
      hBM.symm beta hbetaSq
    exact Ideal.mul_mem_mul hgammaValJ
      (ProjectiveCategory.offDiagonal_val_mem_jacobson T hBH g)
  · intro g
    apply T.projectiveHomFirstRadicalCoefficient_eq_zero_of_mem_jacobson_sq
      hHM.symm gamma hgammaSq
    exact Ideal.mul_mem_mul hbetaValJ
      (ProjectiveCategory.offDiagonal_val_mem_jacobson T hBH.symm g)
  · intro a
    exact branchSupplement_coefficient_eq_radicalCoefficient
      beta Pbar residueM middle hresidueM cross.betaSupplement a
  · intro a
    exact branchSupplement_coefficient_eq_radicalCoefficient
      gamma Pbar residueM middle hresidueM cross.gammaSupplement a
  · intro g
    have hg : g ∈ twoSidedEndomorphismSpan k beta := by
      rw [hbetaSpan]
      exact Submodule.mem_top
    obtain ⟨a, rfl⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit hbetaT hg
    have harg : (beta ≫ a.asHom) ≫ Pbar.tau.asHom =
        (beta ≫ Pbar.tau.asHom) ≫ a.asHom := by
      simpa only [End.mul_def, Category.assoc] using
        congrArg (fun z : End Mbar ↦ beta ≫ z.asHom)
          (Pbar.mul_comm a Pbar.tau).symm
    rw [harg, hbetaTauRight]
    exact (T.projectiveHomFirstRadicalCoefficient_comp_right
      hBM.symm beta hbetaSq a).symm
  · intro g
    have hg : g ∈ twoSidedEndomorphismSpan k gamma := by
      rw [hgammaSpan]
      exact Submodule.mem_top
    obtain ⟨a, rfl⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit hgammaT hg
    have harg : (gamma ≫ a.asHom) ≫ Pbar.tau.asHom =
        (gamma ≫ Pbar.tau.asHom) ≫ a.asHom := by
      simpa only [End.mul_def, Category.assoc] using
        congrArg (fun z : End Mbar ↦ gamma ≫ z.asHom)
          (Pbar.mul_comm a Pbar.tau).symm
    rw [harg, hgammaTauRight]
    exact (T.projectiveHomFirstRadicalCoefficient_comp_right
      hHM.symm gamma hgammaSq a).symm
  · intro a
    apply LinearMap.mem_ker.mp
    apply cross.betaSupplement.outer_le_ker
    exact ⟨a, rfl⟩
  · intro a
    apply LinearMap.mem_ker.mp
    apply cross.gammaSupplement.outer_le_ker
    exact ⟨a, rfl⟩

/-- The exact Figure-16 quotient has the complete occurrence-sensitive
coefficient system: thirteen endpoint entries satisfying all sixty finite
generator equations. -/
theorem nonempty_quotientRepeatedObjectCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    (hpq : p ≠ q) {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    Nonempty (RepeatedObjectCoefficientData
      (k := k) (quotientPowerParameter S D P).tau
      ((quotientFunctor S D P).map (selectedBeta S D))
      ((quotientFunctor S D P).map (selectedGamma S D))) := by
  obtain ⟨cross⟩ := nonempty_quotientBranchTauCrossCoefficientData
    S hfinite D P
  exact nonempty_quotientRepeatedObjectCoefficientData_of_branchTauCross
    S hfinite hpq D P cross

/-- The thirteen-entry coefficient system compiles to the actual
Hom-bifunctor retraction of the literal exact Figure-16 quotient diagram. -/
theorem quotientDiagram_homBifunctorRetraction
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    (hpq : p ≠ q) {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    Nonempty (HomBifunctorRetraction (k := k)
      ((quotientDiagram S D P).functor (k := k))) := by
  obtain ⟨coefficients⟩ := nonempty_quotientRepeatedObjectCoefficientData
    S hfinite hpq D P
  have hdiagram : quotientDiagram S D P =
      repeatedObjectDiagram (quotientPowerParameter S D P).tau
        ((quotientFunctor S D P).map (selectedBeta S D))
        ((quotientFunctor S D P).map (selectedGamma S D)) := by
    rfl
  rw [hdiagram]
  exact ⟨coefficients.homBifunctorRetraction⟩

/-- Representation-finiteness descends first to the selected corner and
then to its exact two-relation quotient, so that quotient cannot carry a
cleaving Figure-16 retraction. -/
theorem quotientDiagram_not_homBifunctorRetraction
    [Infinite k]
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) :
    ¬ Nonempty (HomBifunctorRetraction (k := k)
      ((quotientDiagram S D P).functor (k := k))) := by
  rintro ⟨hret⟩
  letI : Module.Finite k
      (selectedCorner S p q ⧸ (relationIdeal S D P).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D P).asIdeal
  letI : Module.Finite k (End p.1.middle.obj.as) := by
    change Module.Finite k (p.1.middle.obj.as ⟶ p.1.middle.obj.as)
    infer_instance
  letI : LargeIndecomposable.HasRoiterTransitSquareAlternative
      k S.ProjectiveCategory :=
    LargeIndecomposable.RoiterFigure13EAmbient.hasRoiterTransitSquareAlternative
      S hfinite
  have hne : relationIdeal S D P ≠ ⊥ := by
    intro hbot
    have hmem : (selectedBeta S D ≫ selectedTau S p q P ≫ selectedAlpha S D).1 ∈
        relationIdeal S D P := TwoSidedIdeal.subset_span (Set.mem_insert _ _)
    rw [hbot] at hmem
    apply D.betaTauAlpha_ne_zero P
    apply Subtype.ext
    have h1 : (selectedBeta S D ≫ selectedTau S p q P ≫ selectedAlpha S D).1 = 0 := hmem
    have h3 : ((selectedBeta S D ≫ selectedTau S p q P ≫ selectedAlpha S D).1).1 = 0 := by
      rw [h1]; rfl
    rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val,
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val] at h3
    change (selectedAlpha S D).1.1 * (selectedTau S p q P).1.1 * (selectedBeta S D).1.1 = 0
      at h3
    rw [SelectedCorner.finsetProjectiveHom_val_val, SelectedCorner.finsetProjectiveHom_val_val,
      SelectedCorner.finsetProjectiveHom_val_val, mul_assoc] at h3
    change ((D.beta.hom ≫ P.tau.asHom) ≫ D.alpha.hom).1 = 0
    rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val,
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact h3
  have hq := LargeIndecomposable.isRepresentationFinite_corner_quotient
    (S.selectedIdempotent_isIdempotentElem
      (finsetPrimitiveEmbedding (selectedVertices S p q))) hfinite (relationIdeal S D P) hne
  exact
    (LargeIndecomposable.CriticalSingularFigure16.not_isRepresentationFinite_of_figure16Data
      (quotientSplitBasic S D P) (quotientDiagram S D P) hret) hq

/-- The exact Figure-16 hard branch is impossible under
representation-finiteness. -/
theorem false_of_figure16_exact_hard_branch
    [Infinite k]
    (hfinite : LargeIndecomposable.MildAlg k A)
    {p q : SingularPair (C := S.ProjectiveCategory)}
    (hpq : p ≠ q) {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : OrientedRadicalPowerParameter (k := k) p.1.middle.obj.as) : False :=
  quotientDiagram_not_homBifunctorRetraction S hfinite D P
    (quotientDiagram_homBifunctorRetraction S hfinite hpq D P)

/-- Consequently, two singular pairs in a representation-finite
split-basic algebra cannot have the same first arrow unless they are equal. -/
theorem singularPair_eq_of_firstArrow_eq
    [Infinite k]
    (hfinite : LargeIndecomposable.MildAlg k A)
    (p q : SingularPair (C := S.ProjectiveCategory))
    (hfirst : p.1.firstArrow = q.1.firstArrow) : p = q := by
  by_contra hpq
  obtain ⟨D⟩ := nonempty_commonFirstZeroRepresentatives p q hfirst
  letI : ∀ X : S.ProjectiveCategory,
      Module.Finite k (X ⟶ X) := fun X ↦ by infer_instance
  obtain ⟨P⟩ := D.nonempty_middleRadicalPowerParameter (k := k)
  exact false_of_figure16_exact_hard_branch S hfinite hpq D P

end LargeIndecomposable.CriticalFigure16Quotient
