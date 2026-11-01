module

public import LargeIndecomposable.RayCategories.Contours.EssentialPathContour
public import LargeIndecomposable.RayCategories.Contours.RayPathInterlacement

@[expose] public section

/-!
# Local contour corrections in Roiter's vanishing argument

Package the formal scalar content of the `N = 1,2,3` cases in BGRS 8.6.
The remaining ray-category work is to produce the paths and balanced arrow
selectors required by these lemmas from an efficient tackle.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- The path-level `N = 1` case: if every related representative is
interlaced with `p`, every contour function clings to the ray selected by
`p`. -/
theorem contourFunctionClingsToPath_of_related_interlaced
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {x y : Q} (p : Quiver.Path x y)
    (hone : ∀ (q : Quiver.Path x y),
      R.related p q → I.interlaced p q) :
    ContourFunctionClingsToPath R I c p := by
  intro q hpq
  have hpp : R.related p p := R.trans hpq (R.symm hpq)
  exact ⟨p, p, I.refl p, hpp, I.symm (hone q hpq),
    R.symm hpq, hpp, contourScalarFunction_self R c p hpp⟩

/-- Correct a contour function by the inverse coboundary of an arrow-weight
family. -/
def inverseCoboundaryCorrection (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (e : ArrowUnitWeight k Q) :
    contourScalarFunctionSubgroup (k := k) R :=
  c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹

/-- The `N = 1` case of BGRS 8.6: if every related pair from one source lies
in one interlacement class, every contour function already clings there. -/
theorem contourFunctionClingsAtSource_of_related_interlaced
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R) (x : Q)
    (hone : ∀ {y : Q} (p q : Quiver.Path x y),
      R.related p q → I.interlaced p q) :
    ContourFunctionClingsAtSource R I c x := by
  intro y p q hpq
  have hpp : R.related p p := R.trans hpq (R.symm hpq)
  refine ⟨p, p, I.refl p, hpp, I.symm (hone p q hpq),
    R.symm hpq, hpp, ?_⟩
  exact contourScalarFunction_self R c p hpp

variable {C : Type v} [Category.{w} C] [HasZeroMorphisms C]

/-- The concrete ray-category `N = 1` branch of BGRS 8.6. -/
theorem rayContourFunctionClingsToPath_of_card_eq_one
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 1) :
    ContourFunctionClingsToPath
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) c p := by
  apply contourFunctionClingsToPath_of_related_interlaced
  intro q hpq
  exact rayPaths_interlaced_of_card_eq_one p hp hpp hcard q hpq

/-- Triviality of a contour scalar is preserved when the contour is
reversed. -/
theorem contourScalarFamily_reverse_eq_one_of_eq_one
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q : Quiver.Path i j) (hpq : R.related p q)
    (hone : contourScalarFamily R c (relatedContour R p q hpq) = 1) :
    contourScalarFamily R c
      (relatedContour R q p (R.symm hpq)) = 1 := by
  have hreverse :
      contourScalarFamily R c
          (relatedContour R q p (R.symm hpq)) =
        (contourScalarFamily R c
          (relatedContour R p q hpq))⁻¹ := by
    simpa [contourScalarFamily, relatedContour] using
      (contourScalarFunction_reverse R c p q hpq)
  rw [hreverse, hone]
  simp

/-- In a two-class related ray, normalizing one contour between representatives
of the two distinct classes makes the contour function cling to every path on
that ray. -/
theorem contourFunctionClingsToRelatedPaths_of_card_eq_two_of_anchor_eq_one
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q : Quiver.Path i j)
    (hpp : R.related p p) (hpq : R.related p q)
    (hpqNot : ¬I.interlaced p q)
    [Finite (RelatedPathInterlacementClass I p)]
    (hcard : Nat.card (RelatedPathInterlacementClass I p) = 2)
    (hone : contourScalarFamily R c (relatedContour R p q hpq) = 1) :
    ∀ (r : Quiver.Path i j), R.related p r →
      ContourFunctionClingsToPath R I c r := by
  intro r hpr s hrs
  have hps : R.related p s := R.trans hpr hrs
  have hrClass := interlaced_with_first_or_second_of_card_eq_two
    I p hpp hcard q hpq hpqNot r hpr
  have hsClass := interlaced_with_first_or_second_of_card_eq_two
    I p hpp hcard q hpq hpqNot s hps
  rcases hrClass with hrP | hrQ <;>
    rcases hsClass with hsP | hsQ
  · have hrsI : I.interlaced r s := I.trans (I.symm hrP) hsP
    have hrr : R.related r r := R.trans hrs (R.symm hrs)
    exact ⟨r, r, I.refl r, hrr, I.symm hrsI, R.symm hrs,
      hrr, contourScalarFunction_self R c r hrr⟩
  · have hqs : R.related q s := R.trans (R.symm hpq) hps
    exact ⟨p, q, I.symm hrP, R.symm hpr, I.symm hsQ,
      R.symm hqs, hpq, hone⟩
  · have hqr : R.related q r := R.trans (R.symm hpq) hpr
    have hqp : R.related q p := R.symm hpq
    have hreverse :
        contourScalarFamily R c (relatedContour R q p hqp) = 1 :=
      contourScalarFamily_reverse_eq_one_of_eq_one R c p q hpq hone
    exact ⟨q, p, I.symm hrQ, R.symm hqr, I.symm hsP,
      R.symm hps, hqp, hreverse⟩
  · have hrsI : I.interlaced r s := I.trans (I.symm hrQ) hsQ
    have hrr : R.related r r := R.trans hrs (R.symm hrs)
    exact ⟨r, r, I.refl r, hrr, I.symm hrsI, R.symm hrs,
      hrr, contourScalarFunction_self R c r hrr⟩

/-- In a three-class related ray, normalizing the three contours between
pairwise noninterlaced class representatives makes the contour function cling
to every path on that ray. -/
theorem contourFunctionClingsToRelatedPaths_of_card_eq_three_of_anchors_eq_one
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q r : Quiver.Path i j)
    (hpp : R.related p p) (hpq : R.related p q) (hqr : R.related q r)
    (hpqNot : ¬I.interlaced p q)
    (hprNot : ¬I.interlaced p r)
    (hqrNot : ¬I.interlaced q r)
    [Finite (RelatedPathInterlacementClass I p)]
    (hcard : Nat.card (RelatedPathInterlacementClass I p) = 3)
    (honePQ : contourScalarFamily R c
      (relatedContour R p q hpq) = 1)
    (honePR : contourScalarFamily R c
      (relatedContour R p r (R.trans hpq hqr)) = 1)
    (honeQR : contourScalarFamily R c
      (relatedContour R q r hqr) = 1) :
    ∀ (s : Quiver.Path i j), R.related p s →
      ContourFunctionClingsToPath R I c s := by
  intro s hps t hst
  have hpr : R.related p r := R.trans hpq hqr
  have hpt : R.related p t := R.trans hps hst
  have hqs : R.related q s := R.trans (R.symm hpq) hps
  have hqt : R.related q t := R.trans (R.symm hpq) hpt
  have hrs : R.related r s := R.trans (R.symm hpr) hps
  have hrt : R.related r t := R.trans (R.symm hpr) hpt
  have hsClass :=
    interlaced_with_first_or_second_or_third_of_card_eq_three
      I p hpp hcard q r hpq hpr hpqNot hprNot hqrNot s hps
  have htClass :=
    interlaced_with_first_or_second_or_third_of_card_eq_three
      I p hpp hcard q r hpq hpr hpqNot hprNot hqrNot t hpt
  have hss : R.related s s := R.trans hst (R.symm hst)
  have honeQP : contourScalarFamily R c
      (relatedContour R q p (R.symm hpq)) = 1 :=
    contourScalarFamily_reverse_eq_one_of_eq_one R c p q hpq honePQ
  have honeRP : contourScalarFamily R c
      (relatedContour R r p (R.symm hpr)) = 1 :=
    contourScalarFamily_reverse_eq_one_of_eq_one R c p r hpr honePR
  have honeRQ : contourScalarFamily R c
      (relatedContour R r q (R.symm hqr)) = 1 :=
    contourScalarFamily_reverse_eq_one_of_eq_one R c q r hqr honeQR
  rcases hsClass with hsP | hsQ | hsR <;>
    rcases htClass with htP | htQ | htR
  · have hstI : I.interlaced s t := I.trans (I.symm hsP) htP
    exact ⟨s, s, I.refl s, hss, I.symm hstI, R.symm hst,
      hss, contourScalarFunction_self R c s hss⟩
  · exact ⟨p, q, I.symm hsP, R.symm hps, I.symm htQ,
      R.symm hqt, hpq, honePQ⟩
  · exact ⟨p, r, I.symm hsP, R.symm hps, I.symm htR,
      R.symm hrt, hpr, honePR⟩
  · exact ⟨q, p, I.symm hsQ, R.symm hqs, I.symm htP,
      R.symm hpt, R.symm hpq, honeQP⟩
  · have hstI : I.interlaced s t := I.trans (I.symm hsQ) htQ
    exact ⟨s, s, I.refl s, hss, I.symm hstI, R.symm hst,
      hss, contourScalarFunction_self R c s hss⟩
  · exact ⟨q, r, I.symm hsQ, R.symm hqs, I.symm htR,
      R.symm hrt, hqr, honeQR⟩
  · exact ⟨r, p, I.symm hsR, R.symm hrs, I.symm htP,
      R.symm hpt, R.symm hpr, honeRP⟩
  · exact ⟨r, q, I.symm hsR, R.symm hrs, I.symm htQ,
      R.symm hqt, R.symm hqr, honeRQ⟩
  · have hstI : I.interlaced s t := I.trans (I.symm hsR) htR
    exact ⟨s, s, I.refl s, hss, I.symm hstI, R.symm hst,
      hss, contourScalarFunction_self R c s hss⟩

/-- If an arrow-weight family realizes a contour function's ratios from two
paths to a common third path, its inverse coboundary makes all three pairwise
contours trivial.  This is the scalar core of BGRS 8.6(d). -/
theorem inverseCoboundaryCorrection_eq_one_on_relatedTriple
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (e : ArrowUnitWeight k Q)
    {i j : Q} (p q r : Quiver.Path i j)
    (hpq : R.related p q) (hqr : R.related q r)
    (hprRatio : pathWeightRatio e p r =
      contourScalarFamily R c
        (relatedContour R p r (R.trans hpq hqr)))
    (hqrRatio : pathWeightRatio e q r =
      contourScalarFamily R c (relatedContour R q r hqr)) :
    contourScalarFamily R (inverseCoboundaryCorrection R c e)
        (relatedContour R p q hpq) = 1 ∧
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
        (relatedContour R p r (R.trans hpq hqr)) = 1 ∧
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
        (relatedContour R q r hqr) = 1 := by
  have hpqRatio : pathWeightRatio e p q =
      contourScalarFamily R c (relatedContour R p q hpq) := by
    apply mul_right_cancel (b := pathWeightRatio e q r)
    rw [← pathWeightRatio_trans]
    rw [hprRatio, hqrRatio]
    exact c.property.1 p q r hpq hqr
  constructor
  · simpa [inverseCoboundaryCorrection] using
      contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
        R c e (relatedContour R p q hpq) hpqRatio
  constructor
  · simpa [inverseCoboundaryCorrection] using
      contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
        R c e (relatedContour R p r (R.trans hpq hqr)) hprRatio
  · simpa [inverseCoboundaryCorrection] using
      contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
        R c e (relatedContour R q r hqr) hqrRatio

/-- The paired-arrow correction needed in BGRS 8.6(c).  A primary selector
occurs once versus zero on the contour, while a companion selector has equal
counts; giving both selectors the same weight normalizes the contour. -/
theorem exists_roiterTwoClassPairedCorrection
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q : Quiver.Path i j) (hpq : R.related p q)
    (primary companion : ArrowSelector Q)
    (hprimaryP : selectedArrowCount primary p = 1)
    (hprimaryQ : selectedArrowCount primary q = 0)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
        (relatedContour R p q hpq) = 1 := by
  let d := contourScalarFamily R c (relatedContour R p q hpq)
  let e : ArrowUnitWeight k Q :=
    selectorUnitWeight primary d⁻¹ * selectorUnitWeight companion d⁻¹
  refine ⟨e, ?_⟩
  apply contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
  change pathWeightRatio e p q =
    contourScalarFamily R c (relatedContour R p q hpq)
  dsimp [e]
  rw [pathWeightRatio_mul,
    pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
      primary d p q hprimaryP hprimaryQ,
    pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
      companion d⁻¹ p q hcompanion]
  simp [d]

/-- The paired `N = 2` correction obtained by selecting the initial arrow of
`p`.  The remaining geometric input is exactly that this arrow does not occur
in either tail and that the companion selector is balanced on the pair. -/
theorem exists_roiterTwoClassInitialArrowPairedCorrection
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q : Quiver.Path i j) (hpq : R.related p q)
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (harrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow)
    (htailP : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dp.tail = 0)
    (htailQ : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dq.tail = 0)
    (companion : ArrowSelector Q)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
        (relatedContour R p q hpq) = 1 := by
  apply exists_roiterTwoClassPairedCorrection R c p q hpq
    (singleArrowSelector (bundledQuiverArrow dp.arrow)) companion
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dp.arrow.toPath.comp dp.tail) :=
              congrArg _ dp.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_initial_eq_one
        dp.arrow dp.tail htailP
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dq.arrow.toPath.comp dq.tail) :=
              congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dp.arrow dq.arrow dq.tail harrow htailQ
  · exact hcompanion

/-- The initial-arrow `N = 2` correction with both tail conditions derived
from the prefix-triviality consequence of BGRS 8.4. -/
theorem exists_roiterTwoClassInitialArrowPairedCorrection_of_essential_prefixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q : Quiver.Path i j)
    (hessential : IsEssentialPathContour R I p q)
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (harrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow)
    (hprefix : EssentialContourArrowPrefixTrivial R I
      (bundledQuiverArrow dp.arrow))
    (companion : ArrowSelector Q)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
        (relatedContour R p q hessential.1) = 1 := by
  refine exists_roiterTwoClassInitialArrowPairedCorrection
    R c p q hessential.1 dp dq harrow ?_ ?_ companion hcompanion
  · apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R I (bundledQuiverArrow dp.arrow) dp.arrow dp.tail q
    · simpa only [dp.path_eq] using hessential
    · exact hprefix
  · apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R I (bundledQuiverArrow dp.arrow) dq.arrow dq.tail p
    · simpa only [dq.path_eq] using hessential.symm
    · exact hprefix

/-- The paired `N = 2` correction obtained by selecting the final arrow of
`p`.  This is the path-orientation dual of the initial-arrow interface. -/
theorem exists_roiterTwoClassFinalArrowPairedCorrection
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q : Quiver.Path i j) (hpq : R.related p q)
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (harrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow)
    (hheadP : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dp.head = 0)
    (hheadQ : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dq.head = 0)
    (companion : ArrowSelector Q)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
        (relatedContour R p q hpq) = 1 := by
  apply exists_roiterTwoClassPairedCorrection R c p q hpq
    (singleArrowSelector (bundledQuiverArrow dp.arrow)) companion
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dp.head.comp dp.arrow.toPath) := congrArg _ dp.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_final_eq_one
        dp.head dp.arrow hheadP
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dp.arrow dq.head dq.arrow harrow hheadQ
  · exact hcompanion

/-- The final-arrow `N = 2` correction with both head conditions derived
from the suffix-triviality consequence of BGRS 8.4. -/
theorem exists_roiterTwoClassFinalArrowPairedCorrection_of_essential_suffixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q : Quiver.Path i j)
    (hessential : IsEssentialPathContour R I p q)
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (harrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow)
    (hsuffix : EssentialContourArrowSuffixTrivial R I
      (bundledQuiverArrow dp.arrow))
    (companion : ArrowSelector Q)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
        (relatedContour R p q hessential.1) = 1 := by
  refine exists_roiterTwoClassFinalArrowPairedCorrection
    R c p q hessential.1 dp dq harrow ?_ ?_ companion hcompanion
  · apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R I (bundledQuiverArrow dp.arrow) dp.head dp.arrow q
    · simpa only [dp.path_eq] using hessential
    · exact hsuffix
  · apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R I (bundledQuiverArrow dp.arrow) dq.head dq.arrow p
    · simpa only [dq.path_eq] using hessential.symm
    · exact hsuffix
/-- The two-selector correction of BGRS 8.6(d).  Paths `p`, `q`, and `r`
use the distinguished `gamma`, `beta`, and neither selected arrow,
respectively.  Weighting `beta` and `gamma` by the two anchor contour values
normalizes all three contours simultaneously. -/
theorem exists_roiterThreeClassCorrection
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q r : Quiver.Path i j)
    (hpq : R.related p q) (hqr : R.related q r)
    (beta gamma : ArrowSelector Q)
    (hbetaP : selectedArrowCount beta p = 0)
    (hbetaQ : selectedArrowCount beta q = 1)
    (hbetaR : selectedArrowCount beta r = 0)
    (hgammaP : selectedArrowCount gamma p = 1)
    (hgammaQ : selectedArrowCount gamma q = 0)
    (hgammaR : selectedArrowCount gamma r = 0) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p q hpq) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p r (R.trans hpq hqr)) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R q r hqr) = 1 := by
  let dpr := contourScalarFamily R c
    (relatedContour R p r (R.trans hpq hqr))
  let dqr := contourScalarFamily R c (relatedContour R q r hqr)
  let e : ArrowUnitWeight k Q :=
    selectorUnitWeight beta dqr⁻¹ * selectorUnitWeight gamma dpr⁻¹
  refine ⟨e, ?_⟩
  apply inverseCoboundaryCorrection_eq_one_on_relatedTriple
  · dsimp [e]
    rw [pathWeightRatio_mul,
      pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
        beta dqr⁻¹ p r (hbetaP.trans hbetaR.symm),
      pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
        gamma dpr p r hgammaP hgammaR]
    simp [dpr]
  · dsimp [e]
    rw [pathWeightRatio_mul,
      pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
        beta dqr q r hbetaQ hbetaR,
      pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
        gamma dpr⁻¹ q r (hgammaQ.trans hgammaR.symm)]
    simp [dqr]

/-- The `N = 3` correction using the distinct initial arrows of `q` and `p`
as the `beta` and `gamma` selectors.  Once neither selected arrow reappears in
any tail, all six occurrence equations follow automatically. -/
theorem exists_roiterThreeClassInitialArrowCorrection
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q r : Quiver.Path i j)
    (hpq : R.related p q) (hqr : R.related q r)
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r)
    (hpqArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dq.arrow)
    (hprArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dr.arrow)
    (hqrArrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dr.arrow)
    (hbetaP : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dq.arrow)) dp.tail = 0)
    (hbetaQ : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dq.arrow)) dq.tail = 0)
    (hbetaR : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dq.arrow)) dr.tail = 0)
    (hgammaP : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dp.tail = 0)
    (hgammaQ : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dq.tail = 0)
    (hgammaR : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dr.tail = 0) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p q hpq) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p r (R.trans hpq hqr)) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R q r hqr) = 1 := by
  apply exists_roiterThreeClassCorrection R c p q r hpq hqr
    (singleArrowSelector (bundledQuiverArrow dq.arrow))
    (singleArrowSelector (bundledQuiverArrow dp.arrow))
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dp.arrow.toPath.comp dp.tail) := congrArg _ dp.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dq.arrow dp.arrow dp.tail hpqArrow hbetaP
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dq.arrow.toPath.comp dq.tail) := congrArg _ dq.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_initial_eq_one
        dq.arrow dq.tail hbetaQ
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) r =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dr.arrow.toPath.comp dr.tail) := congrArg _ dr.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dq.arrow dr.arrow dr.tail hqrArrow.symm hbetaR
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dp.arrow.toPath.comp dp.tail) := congrArg _ dp.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_initial_eq_one
        dp.arrow dp.tail hgammaP
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dq.arrow.toPath.comp dq.tail) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dp.arrow dq.arrow dq.tail hpqArrow.symm hgammaQ
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) r =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dr.arrow.toPath.comp dr.tail) := congrArg _ dr.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dp.arrow dr.arrow dr.tail hprArrow.symm hgammaR

/-- The initial-arrow `N = 3` correction with all six tail conditions derived
from prefix triviality for the two selected arrows.  The three paths must be
pairwise essential; this is the exact path-level input supplied by three
distinct interlacement classes. -/
theorem exists_roiterThreeClassInitialArrowCorrection_of_essential_prefixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q r : Quiver.Path i j)
    (hpq : IsEssentialPathContour R I p q)
    (hqr : IsEssentialPathContour R I q r)
    (hpr : IsEssentialPathContour R I p r)
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r)
    (hpqArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dq.arrow)
    (hprArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dr.arrow)
    (hqrArrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dr.arrow)
    (hbetaPrefix : EssentialContourArrowPrefixTrivial R I
      (bundledQuiverArrow dq.arrow))
    (hgammaPrefix : EssentialContourArrowPrefixTrivial R I
      (bundledQuiverArrow dp.arrow)) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p q hpq.1) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p r (R.trans hpq.1 hqr.1)) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R q r hqr.1) = 1 := by
  apply exists_roiterThreeClassInitialArrowCorrection
    R c p q r hpq.1 hqr.1 dp dq dr hpqArrow hprArrow hqrArrow
  · apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R I (bundledQuiverArrow dq.arrow) dp.arrow dp.tail q
    · simpa only [dp.path_eq] using hpq
    · exact hbetaPrefix
  · apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R I (bundledQuiverArrow dq.arrow) dq.arrow dq.tail p
    · simpa only [dq.path_eq] using hpq.symm
    · exact hbetaPrefix
  · apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R I (bundledQuiverArrow dq.arrow) dr.arrow dr.tail q
    · simpa only [dr.path_eq] using hqr.symm
    · exact hbetaPrefix
  · apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R I (bundledQuiverArrow dp.arrow) dp.arrow dp.tail q
    · simpa only [dp.path_eq] using hpq
    · exact hgammaPrefix
  · apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R I (bundledQuiverArrow dp.arrow) dq.arrow dq.tail p
    · simpa only [dq.path_eq] using hpq.symm
    · exact hgammaPrefix
  · apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R I (bundledQuiverArrow dp.arrow) dr.arrow dr.tail p
    · simpa only [dr.path_eq] using hpr.symm
    · exact hgammaPrefix

/-- The `N = 3` correction using the distinct final arrows of `q` and `p` as
the `beta` and `gamma` selectors. -/
theorem exists_roiterThreeClassFinalArrowCorrection
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q r : Quiver.Path i j)
    (hpq : R.related p q) (hqr : R.related q r)
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r)
    (hpqArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dq.arrow)
    (hprArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dr.arrow)
    (hqrArrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dr.arrow)
    (hbetaP : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dq.arrow)) dp.head = 0)
    (hbetaQ : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dq.arrow)) dq.head = 0)
    (hbetaR : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dq.arrow)) dr.head = 0)
    (hgammaP : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dp.head = 0)
    (hgammaQ : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dq.head = 0)
    (hgammaR : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow dp.arrow)) dr.head = 0) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p q hpq) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p r (R.trans hpq hqr)) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R q r hqr) = 1 := by
  apply exists_roiterThreeClassCorrection R c p q r hpq hqr
    (singleArrowSelector (bundledQuiverArrow dq.arrow))
    (singleArrowSelector (bundledQuiverArrow dp.arrow))
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dp.head.comp dp.arrow.toPath) := congrArg _ dp.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dq.arrow dp.head dp.arrow hpqArrow hbetaP
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_final_eq_one
        dq.head dq.arrow hbetaQ
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) r =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dr.head.comp dr.arrow.toPath) := congrArg _ dr.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dq.arrow dr.head dr.arrow hqrArrow.symm hbetaR
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dp.head.comp dp.arrow.toPath) := congrArg _ dp.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_final_eq_one
        dp.head dp.arrow hgammaP
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dp.arrow dq.head dq.arrow hpqArrow.symm hgammaQ
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) r =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dr.head.comp dr.arrow.toPath) := congrArg _ dr.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dp.arrow dr.head dr.arrow hprArrow.symm hgammaR

/-- The final-arrow `N = 3` correction with all six head conditions derived
from suffix triviality for the two selected arrows. -/
theorem exists_roiterThreeClassFinalArrowCorrection_of_essential_suffixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q r : Quiver.Path i j)
    (hpq : IsEssentialPathContour R I p q)
    (hqr : IsEssentialPathContour R I q r)
    (hpr : IsEssentialPathContour R I p r)
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r)
    (hpqArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dq.arrow)
    (hprArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dr.arrow)
    (hqrArrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dr.arrow)
    (hbetaSuffix : EssentialContourArrowSuffixTrivial R I
      (bundledQuiverArrow dq.arrow))
    (hgammaSuffix : EssentialContourArrowSuffixTrivial R I
      (bundledQuiverArrow dp.arrow)) :
    ∃ e : ArrowUnitWeight k Q,
      contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p q hpq.1) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R p r (R.trans hpq.1 hqr.1)) = 1 ∧
        contourScalarFamily R (inverseCoboundaryCorrection R c e)
          (relatedContour R q r hqr.1) = 1 := by
  apply exists_roiterThreeClassFinalArrowCorrection
    R c p q r hpq.1 hqr.1 dp dq dr hpqArrow hprArrow hqrArrow
  · apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R I (bundledQuiverArrow dq.arrow) dp.head dp.arrow q
    · simpa only [dp.path_eq] using hpq
    · exact hbetaSuffix
  · apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R I (bundledQuiverArrow dq.arrow) dq.head dq.arrow p
    · simpa only [dq.path_eq] using hpq.symm
    · exact hbetaSuffix
  · apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R I (bundledQuiverArrow dq.arrow) dr.head dr.arrow q
    · simpa only [dr.path_eq] using hqr.symm
    · exact hbetaSuffix
  · apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R I (bundledQuiverArrow dp.arrow) dp.head dp.arrow q
    · simpa only [dp.path_eq] using hpq
    · exact hgammaSuffix
  · apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R I (bundledQuiverArrow dp.arrow) dq.head dq.arrow p
    · simpa only [dq.path_eq] using hpq.symm
    · exact hgammaSuffix
  · apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R I (bundledQuiverArrow dp.arrow) dr.head dr.arrow p
    · simpa only [dr.path_eq] using hpr.symm
    · exact hgammaSuffix

end LargeIndecomposable
