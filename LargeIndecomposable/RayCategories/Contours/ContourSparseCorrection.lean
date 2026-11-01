module

public import LargeIndecomposable.RayCategories.Contours.ContourClinging

@[expose] public section

/-!
# Sparse arrow corrections for contour functions

Formalize the elementary arrow-supported corrections used in the local cases
of the BGRS clinging lemma.  A Boolean selector marks arrows; the resulting
path weight is a power of one unit scalar, with exponent equal to the number
of selected arrows along the path.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- A Boolean marking of arrows in a quiver. -/
abbrev ArrowSelector (Q : Type v) [Quiver.{w} Q] :=
  ∀ {i j : Q}, (i ⟶ j) → Bool

/-- An arrow bundled together with both of its endpoints. -/
abbrev BundledQuiverArrow (Q : Type v) [Quiver.{w} Q] :=
  Σ i : Q, Σ j : Q, i ⟶ j

/-- Bundle an arrow with its endpoints. -/
def bundledQuiverArrow {i j : Q} (a : i ⟶ j) : BundledQuiverArrow Q :=
  ⟨i, j, a⟩

/-- Select exactly one bundled quiver arrow. -/
def singleArrowSelector (a : BundledQuiverArrow Q) : ArrowSelector Q := by
  classical
  intro i j b
  exact decide (bundledQuiverArrow b = a)

/-- The number of selected arrows occurring in a path. -/
def selectedArrowCount (select : ArrowSelector Q) :
    ∀ {i j : Q}, Quiver.Path i j → ℕ
  | _, _, .nil => 0
  | _, _, .cons p a =>
      selectedArrowCount select p + if select a then 1 else 0

/-- Selected-arrow counts add under path concatenation. -/
theorem selectedArrowCount_comp (select : ArrowSelector Q)
    {i j l : Q} (p : Quiver.Path i j) (q : Quiver.Path j l) :
    selectedArrowCount select (p.comp q) =
      selectedArrowCount select p + selectedArrowCount select q := by
  induction q with
  | nil => simp [selectedArrowCount]
  | cons q a ih =>
      simp only [Quiver.Path.comp_cons, selectedArrowCount, ih]
      omega

/-- The singleton selector counts its selected one-arrow path once. -/
@[simp]
theorem selectedArrowCount_singleArrowSelector_toPath
    {i j : Q} (a : i ⟶ j) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
      a.toPath = 1 := by
  simp [Quiver.Hom.toPath, selectedArrowCount, singleArrowSelector,
    bundledQuiverArrow]

/-- A different one-arrow path is not counted by a singleton selector. -/
theorem selectedArrowCount_singleArrowSelector_toPath_of_ne
    {i j i' j' : Q} (a : i ⟶ j) (b : i' ⟶ j')
    (hba : bundledQuiverArrow b ≠ bundledQuiverArrow a) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
      b.toPath = 0 := by
  simp [Quiver.Hom.toPath, selectedArrowCount, singleArrowSelector, hba]

/-- Giving two distinct arrows the same selector weight balances the
one-arrow paths in which the two arrows occur on opposite sides: each side
has total selected count one. -/
theorem selectedArrowCount_singleArrowSelector_pair_swap
    {i j i' j' : Q} (a : i ⟶ j) (b : i' ⟶ j')
    (hab : bundledQuiverArrow a ≠ bundledQuiverArrow b) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
          a.toPath +
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow b))
          a.toPath =
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
          b.toPath +
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow b))
          b.toPath := by
  rw [selectedArrowCount_singleArrowSelector_toPath,
    selectedArrowCount_singleArrowSelector_toPath_of_ne b a hab,
    selectedArrowCount_singleArrowSelector_toPath_of_ne a b hab.symm,
    selectedArrowCount_singleArrowSelector_toPath]

/-- If the selected initial arrow does not occur in the tail, it occurs
exactly once in the whole path. -/
theorem selectedArrowCount_singleArrowSelector_initial_eq_one
    {i j l : Q} (a : i ⟶ j) (tail : Quiver.Path j l)
    (htail : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow a)) tail = 0) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
      (a.toPath.comp tail) = 1 := by
  rw [selectedArrowCount_comp,
    selectedArrowCount_singleArrowSelector_toPath, htail]

/-- A path with a different initial arrow has singleton-selector count zero
when the selected arrow does not occur in its tail. -/
theorem selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
    {i j i' j' l : Q} (a : i ⟶ j) (b : i' ⟶ j')
    (tail : Quiver.Path j' l)
    (hba : bundledQuiverArrow b ≠ bundledQuiverArrow a)
    (htail : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow a)) tail = 0) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
      (b.toPath.comp tail) = 0 := by
  rw [selectedArrowCount_comp,
    selectedArrowCount_singleArrowSelector_toPath_of_ne a b hba, htail]

/-- If the selected final arrow does not occur in the head, it occurs exactly
once in the whole path. -/
theorem selectedArrowCount_singleArrowSelector_final_eq_one
    {i j l : Q} (head : Quiver.Path i j) (a : j ⟶ l)
    (hhead : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow a)) head = 0) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
      (head.comp a.toPath) = 1 := by
  rw [selectedArrowCount_comp, hhead,
    selectedArrowCount_singleArrowSelector_toPath]

/-- A path with a different final arrow has singleton-selector count zero
when the selected arrow does not occur in its head. -/
theorem selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
    {j i' j' l : Q} (a : j ⟶ l) (head : Quiver.Path i' j')
    (b : j' ⟶ l)
    (hba : bundledQuiverArrow b ≠ bundledQuiverArrow a)
    (hhead : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow a)) head = 0) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
      (head.comp b.toPath) = 0 := by
  rw [selectedArrowCount_comp, hhead,
    selectedArrowCount_singleArrowSelector_toPath_of_ne a b hba]

/-- Give every selected arrow weight `c` and every other arrow weight one. -/
def selectorUnitWeight (select : ArrowSelector Q) (c : kˣ) :
    ArrowUnitWeight k Q :=
  fun a ↦ if select a then c else 1

/-- A selector-supported path weight is the corresponding scalar power. -/
theorem path_weight_selectorUnitWeight
    (select : ArrowSelector Q) (c : kˣ)
    {i j : Q} (p : Quiver.Path i j) :
    p.weight (selectorUnitWeight select c) =
      c ^ selectedArrowCount select p := by
  induction p with
  | nil => simp [selectedArrowCount]
  | cons p a ih =>
      cases hselect : select a <;>
        simp [selectedArrowCount, selectorUnitWeight, hselect, ih, pow_succ]

/-- A selector-supported correction is invisible on two paths containing the
same number of selected arrows. -/
theorem pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
    (select : ArrowSelector Q) (c : kˣ)
    {i j : Q} (p q : Quiver.Path i j)
    (hcount : selectedArrowCount select p =
      selectedArrowCount select q) :
    pathWeightRatio (selectorUnitWeight select c) p q = 1 := by
  simp [pathWeightRatio, path_weight_selectorUnitWeight, hcount]

/-- If the left path contains one selected arrow and the right path none,
giving the selected arrow inverse weight realizes the scalar `c` as the path
weight ratio. -/
theorem pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
    (select : ArrowSelector Q) (c : kˣ)
    {i j : Q} (p q : Quiver.Path i j)
    (hp : selectedArrowCount select p = 1)
    (hq : selectedArrowCount select q = 0) :
    pathWeightRatio (selectorUnitWeight select c⁻¹) p q = c := by
  simp [pathWeightRatio, path_weight_selectorUnitWeight, hp, hq]

/-- Pointwise product of a finite family of selector-supported arrow
weights. -/
def selectorFamilyUnitWeight {T : Type z} [Fintype T]
    (select : T → ArrowSelector Q) (d : T → kˣ) :
    ArrowUnitWeight k Q :=
  ∏ t, selectorUnitWeight (select t) (d t)

/-- Path-weight ratios commute with finite pointwise products of arrow
weights. -/
theorem pathWeightRatio_finset_prod {T : Type z}
    (s : Finset T) (e : T → ArrowUnitWeight k Q)
    {i j : Q} (p q : Quiver.Path i j) :
    pathWeightRatio (∏ t ∈ s, e t) p q =
      ∏ t ∈ s, pathWeightRatio (e t) p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pathWeightRatio_one]
  | @insert t s ht ih =>
      simp [ht, pathWeightRatio_mul, ih]

/-- The ratio for a finite selector family is the product of the individual
selector ratios. -/
theorem pathWeightRatio_selectorFamilyUnitWeight {T : Type z} [Fintype T]
    (select : T → ArrowSelector Q) (d : T → kˣ)
    {i j : Q} (p q : Quiver.Path i j) :
    pathWeightRatio (selectorFamilyUnitWeight select d) p q =
      ∏ t, pathWeightRatio (selectorUnitWeight (select t) (d t)) p q := by
  classical
  exact pathWeightRatio_finset_prod Finset.univ
    (fun t ↦ selectorUnitWeight (select t) (d t)) p q

/-- If every selector in a finite family has equal counts on two paths, the
combined correction is invisible on that contour. -/
theorem pathWeightRatio_selectorFamilyUnitWeight_eq_one_of_count_eq
    {T : Type z} [Fintype T]
    (select : T → ArrowSelector Q) (d : T → kˣ)
    {i j : Q} (p q : Quiver.Path i j)
    (hcount : ∀ t, selectedArrowCount (select t) p =
      selectedArrowCount (select t) q) :
    pathWeightRatio (selectorFamilyUnitWeight select d) p q = 1 := by
  classical
  rw [pathWeightRatio_selectorFamilyUnitWeight]
  apply Finset.prod_eq_one
  intro t ht
  exact pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
    (select t) (d t) p q (hcount t)

/-- Applying an inverse contour coboundary multiplies each old contour value
by the inverse path-weight ratio. -/
theorem contourScalarFamily_mul_inv_coboundary_apply
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (e : ArrowUnitWeight k Q) (C : RelatedContour R) :
    contourScalarFamily R
        (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) C =
      contourScalarFamily R c C *
        (pathWeightRatio e C.1.left C.1.right)⁻¹ := by
  rfl

/-- A correction whose path-weight ratio equals the old contour value makes
that contour value one. -/
theorem contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (e : ArrowUnitWeight k Q) (C : RelatedContour R)
    (hratio : pathWeightRatio e C.1.left C.1.right =
      contourScalarFamily R c C) :
    contourScalarFamily R
        (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) C = 1 := by
  rw [contourScalarFamily_mul_inv_coboundary_apply, hratio]
  simp

/-- Equal selected-arrow counts preserve the old contour value under a
selector-supported inverse correction. -/
theorem contourScalarFamily_mul_inv_selectorCoboundary_eq_of_count_eq
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (select : ArrowSelector Q) (d : kˣ) (C : RelatedContour R)
    (hcount : selectedArrowCount select C.1.left =
      selectedArrowCount select C.1.right) :
    contourScalarFamily R
        (c * (contourFunctionCoboundaryHom (k := k) R
          (selectorUnitWeight select d))⁻¹) C =
      contourScalarFamily R c C := by
  rw [contourScalarFamily_mul_inv_coboundary_apply,
    pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
      select d C.1.left C.1.right hcount]
  simp

/-- The one-versus-zero occurrence case gives the elementary single-selector
normalization used in BGRS 8.6(b). -/
theorem contourScalarFamily_mul_inv_selectorCoboundary_eq_one_of_count_one_zero
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (select : ArrowSelector Q) (C : RelatedContour R)
    (hp : selectedArrowCount select C.1.left = 1)
    (hq : selectedArrowCount select C.1.right = 0) :
    contourScalarFamily R
        (c * (contourFunctionCoboundaryHom (k := k) R
          (selectorUnitWeight select (contourScalarFamily R c C)⁻¹))⁻¹)
        C = 1 := by
  apply contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
  exact pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
    select (contourScalarFamily R c C) C.1.left C.1.right hp hq

/-- A selector is balanced at a source when every related pair of paths from
that source contains the same number of selected arrows. -/
def ArrowSelectorBalancedAtSource
    (R : PathContourRelation Q) (select : ArrowSelector Q) (x : Q) : Prop :=
  ∀ {y : Q} (p q : Quiver.Path x y), R.related p q →
    selectedArrowCount select p = selectedArrowCount select q

/-- Every selector in a finite family is balanced at a source. -/
def ArrowSelectorFamilyBalancedAtSource {T : Type z}
    (R : PathContourRelation Q) (select : T → ArrowSelector Q)
    (x : Q) : Prop :=
  ∀ t, ArrowSelectorBalancedAtSource R (select t) x

/-- A selector-balanced inverse correction preserves clinging at one source,
using the same interlacement representatives as before. -/
theorem contourFunctionClingsAtSource_mul_inv_selectorCoboundary
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (select : ArrowSelector Q) (d : kˣ) (x : Q)
    (hclings : ContourFunctionClingsAtSource R I c x)
    (hbalanced : ArrowSelectorBalancedAtSource R select x) :
    ContourFunctionClingsAtSource R I
      (c * (contourFunctionCoboundaryHom (k := k) R
        (selectorUnitWeight select d))⁻¹) x := by
  intro y p q hpq
  obtain ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, hpq'⟩ :=
    hclings p q hpq
  refine ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, ?_⟩
  rw [contourScalarFamily_mul_inv_selectorCoboundary_eq_of_count_eq
    R c select d (relatedContour R p' q' hpq'R)
      (hbalanced p' q' hpq'R), hpq']

/-- A correction balanced at every protected source preserves clinging on the
whole protected finite set. -/
theorem contourFunctionClingsAtSources_mul_inv_selectorCoboundary
    [DecidableEq Q]
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (select : ArrowSelector Q) (d : kˣ) (s : Finset Q)
    (hclings : ContourFunctionClingsAtSources R I c s)
    (hbalanced : ∀ x ∈ s, ArrowSelectorBalancedAtSource R select x) :
    ContourFunctionClingsAtSources R I
      (c * (contourFunctionCoboundaryHom (k := k) R
        (selectorUnitWeight select d))⁻¹) s := by
  intro x hx
  exact contourFunctionClingsAtSource_mul_inv_selectorCoboundary
    R I c select d x (hclings x hx) (hbalanced x hx)

/-- A finite family of selectors balanced at one source preserves clinging
there under their combined inverse correction. -/
theorem contourFunctionClingsAtSource_mul_inv_selectorFamilyCoboundary
    {T : Type z} [Fintype T]
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (select : T → ArrowSelector Q) (d : T → kˣ) (x : Q)
    (hclings : ContourFunctionClingsAtSource R I c x)
    (hbalanced : ArrowSelectorFamilyBalancedAtSource R select x) :
    ContourFunctionClingsAtSource R I
      (c * (contourFunctionCoboundaryHom (k := k) R
        (selectorFamilyUnitWeight select d))⁻¹) x := by
  intro y p q hpq
  obtain ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, hpq'⟩ :=
    hclings p q hpq
  refine ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, ?_⟩
  rw [contourScalarFamily_mul_inv_coboundary_apply]
  change contourScalarFamily R c (relatedContour R p' q' hpq'R) *
      (pathWeightRatio (selectorFamilyUnitWeight select d) p' q')⁻¹ = 1
  rw [
    pathWeightRatio_selectorFamilyUnitWeight_eq_one_of_count_eq
      select d p' q' (fun t ↦ hbalanced t p' q' hpq'R), hpq']
  simp

/-- A finite selector family balanced at every protected source preserves
clinging on the protected finite set. -/
theorem contourFunctionClingsAtSources_mul_inv_selectorFamilyCoboundary
    [DecidableEq Q] {T : Type z} [Fintype T]
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (select : T → ArrowSelector Q) (d : T → kˣ) (s : Finset Q)
    (hclings : ContourFunctionClingsAtSources R I c s)
    (hbalanced : ∀ x ∈ s,
      ArrowSelectorFamilyBalancedAtSource R select x) :
    ContourFunctionClingsAtSources R I
      (c * (contourFunctionCoboundaryHom (k := k) R
        (selectorFamilyUnitWeight select d))⁻¹) s := by
  intro x hx
  exact contourFunctionClingsAtSource_mul_inv_selectorFamilyCoboundary
    R I c select d x (hclings x hx) (hbalanced x hx)

/-- The exact finite combinatorial output needed from a local BGRS source
analysis.  It supplies a finite selector family which is balanced on all
protected sources and whose combined ratio normalizes suitable representatives
for every related pair from the new source. -/
def HasSelectorFamilyClingingSourcePlan
    [DecidableEq Q] (T : Type z) [Fintype T]
    (R : PathContourRelation Q) (I : PathInterlacementRelation R) : Prop :=
  ∀ (c : contourScalarFunctionSubgroup (k := k) R)
      (s : Finset Q) (x : Q),
    ContourFunctionClingsAtSources R I c s →
      ∃ (select : T → ArrowSelector Q) (d : T → kˣ),
        (∀ z ∈ s, ArrowSelectorFamilyBalancedAtSource R select z) ∧
          ∀ {y : Q} (p q : Quiver.Path x y) (_hpq : R.related p q),
            ∃ p' q' : Quiver.Path x y,
              I.interlaced p p' ∧ R.related p p' ∧
                I.interlaced q q' ∧ R.related q q' ∧
                  ∃ hpq' : R.related p' q',
                    pathWeightRatio (selectorFamilyUnitWeight select d)
                        p' q' =
                      contourScalarFamily R c
                        (relatedContour R p' q' hpq')

/-- A finite selector-family source plan implies the source-local clinging
step required by the global Roiter induction. -/
theorem hasClingingSourceStep_of_selectorFamilyPlan
    [DecidableEq Q] (T : Type z) [Fintype T]
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (hplan : HasSelectorFamilyClingingSourcePlan (k := k) T R I) :
    HasClingingSourceStep (k := k) R I := by
  intro c s x hclings
  obtain ⟨select, d, hbalanced, hadd⟩ := hplan c s x hclings
  refine ⟨selectorFamilyUnitWeight select d, ?_⟩
  intro z hz
  rw [Finset.mem_insert] at hz
  rcases hz with rfl | hz
  · intro y p q hpq
    obtain ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, hratio⟩ :=
      hadd p q hpq
    refine ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, ?_⟩
    exact contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
      R c (selectorFamilyUnitWeight select d)
        (relatedContour R p' q' hpq'R) hratio
  · exact contourFunctionClingsAtSource_mul_inv_selectorFamilyCoboundary
      R I c select d z (hclings z hz) (hbalanced z hz)

end LargeIndecomposable
