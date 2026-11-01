module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.Cleaving.ClosedChains.Figure13ESupplementCompiler
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.RoiterFigure13Quotient

@[expose] public section

/-!
# Ambient specialization boundary for BGRS Figure 13E

The preceding Figure-13D argument proves that the two outer rays form a BGRS
special zero.  The pair dichotomy therefore supplies representatives with
zero ordinary composite.  This file records those representatives and proves
that, in the same radical quotient used for Figure 13D, the four supplement
statements printed by BGRS produce a forbidden Figure-13E Hom-bifunctor
retraction.  Distributivity combines the two middle statements into the one
middle coefficient supplement at `tau^2`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.RoiterFigure13EAmbient

open LargeIndecomposable.ClosedZigzagCrossUniverse
open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- Public spelling of the split-basic quotient used in Figure 13. -/
abbrev figure13QuotientSplitBasic
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y) :=
  S.quotient_of_le_jacobson
    (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal S f g P)
    (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_le_jacobson
      S f g P)

/-- Public spelling of the projective functor to the Figure-13 quotient. -/
abbrev figure13QuotientFunctor
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y) :=
  S.projectiveQuotientFunctor
    (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal S f g P)
    (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_le_jacobson
      S f g P)

/-- Representatives in the two prescribed unit rays whose ordinary
composite is zero. -/
structure ZeroRepresentativePair
    {X Y Z : S.ProjectiveCategory} (f : X ⟶ Y) (g : Y ⟶ Z) where
  alpha : X ⟶ Y
  beta : Y ⟶ Z
  alpha_equivalent : LargeIndecomposable.UnitRayEquivalent f alpha
  beta_equivalent : LargeIndecomposable.UnitRayEquivalent g beta
  comp_zero : alpha ≫ beta = 0

omit [IsAlgClosed k] in
/-- A BGRS special zero has representatives with zero ordinary composite. -/
theorem nonempty_zeroRepresentativePair_of_special
    {X Y Z : S.ProjectiveCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hspecial : LargeIndecomposable.IsBGRSSpecialZero f g) :
    Nonempty (ZeroRepresentativePair S f g) := by
  obtain ⟨alpha, beta, halpha, hbeta, hzero⟩ :=
    (LargeIndecomposable.HasBGRSPairDichotomy.pair f g).zero_representatives_of_special
      hspecial
  exact ⟨⟨alpha, beta, halpha, hbeta, hzero⟩⟩

/-- The bound Figure-13E diagram in the same quotient used for Figure 13D. -/
def quotientDiagramE
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0) :
    LargeIndecomposable.RoiterFigure13E.DiagramData
      (C := (figure13QuotientSplitBasic S f g P).ProjectiveCategory) := by
  let F := figure13QuotientFunctor S f g P
  let alpha := F.map R.alpha
  let beta := F.map R.beta
  let tau :=
    (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
      S f g P hXY hYZ hleft).tau
  exact LargeIndecomposable.RoiterFigure13E.repeatedMiddleDiagram
    alpha beta tau (by
      change F.map R.alpha ≫ F.map R.beta = 0
      rw [← Functor.map_comp, R.comp_zero, F.map_zero])

/-- In the Figure-13 radical quotient, the three combined supplement
nonmemberships are the only remaining input needed to construct the bound
Figure-13E retraction. -/
theorem quotientFigure13E_homBifunctorRetraction_of_supplements
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (alpha :
      (figure13QuotientFunctor S f g P).obj X ⟶
      (figure13QuotientFunctor S f g P).obj Y)
    (beta :
      (figure13QuotientFunctor S f g P).obj Y ⟶
      (figure13QuotientFunctor S f g P).obj Z)
    (hspecial : alpha ≫ beta = 0)
    (hAlphaSpan : twoSidedEndomorphismSpan k alpha = ⊤)
    (hBetaSpan : twoSidedEndomorphismSpan k beta = ⊤)
    (hAlphaTransit : LargeIndecomposable.AllowsTransit alpha)
    (hBetaCotransit : LargeIndecomposable.AllowsCotransit beta)
    (supplement : LargeIndecomposable.RoiterFigure13E.Figure13ESupplementData
      (k := k) alpha beta
      (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft).tau) :
    Nonempty (LargeIndecomposable.ClosedZigzagCrossUniverse.HomBifunctorRetraction (k := k)
      ((LargeIndecomposable.RoiterFigure13E.repeatedMiddleDiagram
        alpha beta
        (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
          S f g P hXY hYZ hleft).tau hspecial).functor (k := k))) := by
  let Q := figure13QuotientSplitBasic S f g P
  let F := figure13QuotientFunctor S f g P
  let Xbar := F.obj X
  let Ybar := F.obj Y
  let Zbar := F.obj Z
  let Pbar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
      S f g P hXY hYZ hleft
  let residue := Q.projectiveEndResidue Ybar
  letI : Module.Finite k (End Ybar) := by
    change Module.Finite k (Ybar ⟶ Ybar)
    infer_instance
  have hresidue : ∀ a : End Ybar,
      residue a = 0 ↔ a ∈ Ring.jacobson (End Ybar) := by
    intro a
    rw [Q.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← Q.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hfactor : ∀ a : End Ybar, residue a = 0 →
      ∃ q : End Ybar, a = q * Pbar.tau := by
    intro a ha
    have haJ : a ∈ Ring.jacobson (End Ybar) := (hresidue a).1 ha
    rcases Pbar.power_factorization with hT | hC
    · obtain ⟨q, hq⟩ := hT.generates a haJ
      refine ⟨q, ?_⟩
      apply End.ext
      simpa only [End.mul_def] using hq
    · obtain ⟨q, hq⟩ := hC.generates a haJ
      refine ⟨q, ?_⟩
      rw [Pbar.mul_comm q Pbar.tau]
      apply End.ext
      simpa only [End.mul_def] using hq
  have hAlphaFactor : ∀ h : Xbar ⟶ Ybar,
      ∃ a : End Ybar, h = alpha ≫ a.asHom := by
    intro h
    have hmem : h ∈ twoSidedEndomorphismSpan k alpha := by
      rw [hAlphaSpan]
      exact Submodule.mem_top
    exact exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit
      (k := k) hAlphaTransit hmem
  have hBetaFactor : ∀ h : Ybar ⟶ Zbar,
      ∃ a : End Ybar, h = a.asHom ≫ beta := by
    intro h
    have hmem : h ∈ twoSidedEndomorphismSpan k beta := by
      rw [hBetaSpan]
      exact Submodule.mem_top
    exact exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit
      (k := k) hBetaCotransit hmem
  have hXbarYbar : Xbar ≠ Ybar := by
    intro h
    apply hXY
    apply S.projectiveVertex_injective
    have hv := congrArg Q.projectiveVertex h
    dsimp only [Q, Xbar, Ybar, F] at hv
    simpa only [LargeIndecomposable.SplitBasicIdempotents.projectiveQuotientFunctor_obj_projectiveVertex]
      using hv
  have hYbarZbar : Ybar ≠ Zbar := by
    intro h
    apply hYZ
    apply S.projectiveVertex_injective
    have hv := congrArg Q.projectiveVertex h
    dsimp only [Q, Ybar, Zbar, F] at hv
    simpa only [LargeIndecomposable.SplitBasicIdempotents.projectiveQuotientFunctor_obj_projectiveVertex]
      using hv
  have hThroughXZero : ∀ (l : Ybar ⟶ Xbar) (r : Xbar ⟶ Ybar),
      residue (End.of (l ≫ r)) = 0 := by
    intro l r
    rw [Q.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    change r.1 * l.1 ∈ Ring.jacobson _
    exact (Ring.jacobson _).mul_mem_left r.1
      (offDiagonal_val_mem_jacobson Q hXbarYbar.symm l)
  have hThroughZZero : ∀ (l : Ybar ⟶ Zbar) (r : Zbar ⟶ Ybar),
      residue (End.of (l ≫ r)) = 0 := by
    intro l r
    rw [Q.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    change r.1 * l.1 ∈ Ring.jacobson _
    exact (Ring.jacobson _).mul_mem_left r.1
      (offDiagonal_val_mem_jacobson Q hYbarZbar l)
  obtain ⟨coefficients⟩ :=
    LargeIndecomposable.RoiterFigure13E.exists_repeatedMiddleThinQuotientPathCoefficientData_of_supplements
      alpha beta Pbar.tau hspecial residue hresidue Pbar.mem_jacobson
      hfactor (fun a ↦ Pbar.mul_comm a Pbar.tau)
      hAlphaFactor hBetaFactor hThroughXZero hThroughZZero supplement
  exact ⟨coefficients.homBifunctorRetraction⟩

/-- For zero representatives of the two prescribed outer rays, the span and
transit hypotheses of the generic quotient theorem are automatic. -/
theorem quotientDiagramE_homBifunctorRetraction_of_supplements
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (supplement : LargeIndecomposable.RoiterFigure13E.Figure13ESupplementData
      (k := k)
      ((figure13QuotientFunctor S f g P).map R.alpha)
      ((figure13QuotientFunctor S f g P).map R.beta)
      (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft).tau) :
    Nonempty (LargeIndecomposable.ClosedZigzagCrossUniverse.HomBifunctorRetraction
      (k := k) ((quotientDiagramE S f g P R hXY hYZ hleft).functor (k := k))) := by
  let F := figure13QuotientFunctor S f g P
  let alpha := F.map R.alpha
  let beta := F.map R.beta
  have hzero : alpha ≫ beta = 0 := by
    change F.map R.alpha ≫ F.map R.beta = 0
    rw [← Functor.map_comp, R.comp_zero, F.map_zero]
  have hfT : LargeIndecomposable.AllowsTransit f :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) f).resolve_right hfNotC
  have hgC : LargeIndecomposable.AllowsCotransit g :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) g).resolve_left hgNotT
  have hRAlphaSpan : twoSidedEndomorphismSpan k R.alpha = ⊤ := by
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k R.alpha_equivalent, hfspan]
  have hRBetaSpan : twoSidedEndomorphismSpan k R.beta = ⊤ := by
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k R.beta_equivalent, hgspan]
  have hAlphaSpan : twoSidedEndomorphismSpan k alpha = ⊤ :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_span_eq_top
      S f g P R.alpha hRAlphaSpan
  have hBetaSpan : twoSidedEndomorphismSpan k beta = ⊤ :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_span_eq_top
      S f g P R.beta hRBetaSpan
  have hAlphaTransit : LargeIndecomposable.AllowsTransit alpha :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_allowsTransit
      S f g P R.alpha (hfT.of_unitRayEquivalent R.alpha_equivalent)
  have hBetaCotransit : LargeIndecomposable.AllowsCotransit beta :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_allowsCotransit
      S f g P R.beta (hgC.of_unitRayEquivalent R.beta_equivalent)
  have hret := quotientFigure13E_homBifunctorRetraction_of_supplements
    S f g P hXY hYZ hleft alpha beta hzero hAlphaSpan hBetaSpan
      hAlphaTransit hBetaCotransit supplement
  simpa only [quotientDiagramE, alpha, beta, F] using hret

/-- Representation-finiteness forbids the three Figure-13E supplements in
the radical quotient. -/
theorem not_figure13ESupplements_of_isRepresentationFinite
    [Infinite k]
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (alpha :
      (figure13QuotientFunctor S f g P).obj X ⟶
      (figure13QuotientFunctor S f g P).obj Y)
    (beta :
      (figure13QuotientFunctor S f g P).obj Y ⟶
      (figure13QuotientFunctor S f g P).obj Z)
    (hspecial : alpha ≫ beta = 0)
    (hAlphaSpan : twoSidedEndomorphismSpan k alpha = ⊤)
    (hBetaSpan : twoSidedEndomorphismSpan k beta = ⊤)
    (hAlphaTransit : LargeIndecomposable.AllowsTransit alpha)
    (hBetaCotransit : LargeIndecomposable.AllowsCotransit beta) :
    ¬ LargeIndecomposable.RoiterFigure13E.Figure13ESupplementData
      (k := k) alpha beta
      (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft).tau := by
  intro supplement
  obtain ⟨hret⟩ := quotientFigure13E_homBifunctorRetraction_of_supplements
    S f g P hXY hYZ hleft alpha beta hspecial hAlphaSpan hBetaSpan
    hAlphaTransit hBetaCotransit supplement
  exact
    (LargeIndecomposable.RoiterFigure13E.not_isRepresentationFinite_of_figure13EData
      (figure13QuotientSplitBasic S f g P)
      (LargeIndecomposable.RoiterFigure13E.repeatedMiddleDiagram
        alpha beta
        (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
          S f g P hXY hYZ hleft).tau hspecial) hret)
      (hfinite _
        (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_ne_bot_of_left S f g P hleft))

/-- In the exact hard branch, after Figure 13D has supplied zero
representatives, representation-finiteness rules out their three Figure-13E
supplements.  No additional span, factorization, or coefficient hypothesis
remains. -/
theorem not_zeroRepresentativePair_figure13ESupplements
    [Infinite k]
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0) :
    ¬ LargeIndecomposable.RoiterFigure13E.Figure13ESupplementData
      (k := k)
      ((figure13QuotientFunctor S f g P).map R.alpha)
      ((figure13QuotientFunctor S f g P).map R.beta)
      (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft).tau := by
  intro supplement
  obtain ⟨hret⟩ := quotientDiagramE_homBifunctorRetraction_of_supplements
    S f g P R hfspan hgspan hXY hYZ hfNotC hgNotT hleft supplement
  exact
    (LargeIndecomposable.RoiterFigure13E.not_isRepresentationFinite_of_figure13EData
      (figure13QuotientSplitBasic S f g P)
      (quotientDiagramE S f g P R hXY hYZ hleft) hret)
      (hfinite _
        (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_ne_bot_of_left S f g P hleft))

/-- The source-printed four Figure-13E supplements are impossible for the
zero representatives furnished by the exact hard branch.  The only extra
step beyond the three-supplement theorem is comparability of the two
factor-through subbimodules. -/
theorem not_zeroRepresentativePair_figure13EPrintedSupplements
    [Infinite k]
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0) :
    ¬ LargeIndecomposable.RoiterFigure13E.Figure13EPrintedSupplementData
      (k := k)
      ((figure13QuotientFunctor S f g P).map R.alpha)
      ((figure13QuotientFunctor S f g P).map R.beta)
      (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft).tau := by
  intro supplement
  apply not_zeroRepresentativePair_figure13ESupplements
    S f g P R hfinite hfspan hgspan hXY hYZ hfNotC hgNotT hleft
  exact supplement.toFigure13ESupplementData

/-- The completed Figure-13D hard branch now hands off to exactly one
source-faithful Figure-13E obligation: it chooses zero representatives and
proves that their three supplements cannot all hold. -/
theorem exists_zeroRepresentativePair_not_figure13ESupplements_of_exact_hard_branch
    [Infinite k]
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (hright : (P.tau ^ 2).asHom ≫ g ≠ 0) :
    ∃ R : ZeroRepresentativePair S f g,
      ¬ LargeIndecomposable.RoiterFigure13E.Figure13ESupplementData
        (k := k)
        ((figure13QuotientFunctor S f g P).map R.alpha)
        ((figure13QuotientFunctor S f g P).map R.beta)
        (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
          S f g P hXY hYZ hleft).tau := by
  have hspecial : LargeIndecomposable.IsBGRSSpecialZero f g :=
    LargeIndecomposable.RoiterFigure13Quotient.isBGRSSpecialZero_of_exact_hard_branch
      S f g P hfinite hfspan hgspan hXY hYZ hfNotC hgNotT hleft hright
  obtain ⟨R⟩ := nonempty_zeroRepresentativePair_of_special S f g hspecial
  exact ⟨R, not_zeroRepresentativePair_figure13ESupplements
    S f g P R hfinite hfspan hgspan hXY hYZ hfNotC hgNotT hleft⟩

/-- Source-faithful endpoint of the exact Figure-13 hard branch: one can
choose zero representatives for which the four supplement nonmemberships
printed after BGRS Figure 13 cannot all hold. -/
theorem exists_zeroRepresentativePair_not_figure13EPrintedSupplements_of_exact_hard_branch
    [Infinite k]
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (hright : (P.tau ^ 2).asHom ≫ g ≠ 0) :
    ∃ R : ZeroRepresentativePair S f g,
      ¬ LargeIndecomposable.RoiterFigure13E.Figure13EPrintedSupplementData
        (k := k)
        ((figure13QuotientFunctor S f g P).map R.alpha)
        ((figure13QuotientFunctor S f g P).map R.beta)
        (LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
          S f g P hXY hYZ hleft).tau := by
  obtain ⟨R, hR⟩ :=
    exists_zeroRepresentativePair_not_figure13ESupplements_of_exact_hard_branch
      S f g P hfinite hfspan hgspan hXY hYZ hfNotC hgNotT hleft hright
  refine ⟨R, ?_⟩
  intro supplement
  exact hR supplement.toFigure13ESupplementData

end LargeIndecomposable.RoiterFigure13EAmbient
