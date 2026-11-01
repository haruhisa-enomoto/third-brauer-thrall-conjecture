module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure14Retraction

@[expose] public section

/-!
# The exact BGRS Figure-15 quotient

This file constructs the selected-corner quotient used in BGRS 4.3(c).  In
the primitive-projective convention the central Figure-15 chain is the
reversed critical path

`last₀ ≫ middle₀ ≫ first₀ = 0`.

The three representatives come from one zero occurrence-by-occurrence
representative of the critical path.  The exact quotient ideal is generated
by the right-inner radical parameter followed by `middle₀`, the reverse of
the source's relation `delta rho`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalFigure15Quotient

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.CriticalFigure14Quotient
open LargeIndecomposable.SplitBasicIdempotents
open LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory
open LargeIndecomposable.SplitBasicIdempotents.SelectedCorner
open LargeIndecomposable.CriticalSingularLocalQuotientExtraction

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

private theorem unitRayEquivalent_symm
    {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y}
    (h : LargeIndecomposable.UnitRayEquivalent f g) :
    LargeIndecomposable.UnitRayEquivalent g f := by
  rcases h with ⟨a, b, rfl⟩
  refine ⟨a.symm, b.symm, ?_⟩
  simp [Category.assoc]

private theorem eq_zero_of_eq_source_jacobson_action
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [IsArtinianRing (End X)]
    (f : X ⟶ Y) (a : End X) (ha : a ∈ Ring.jacobson (End X))
    (hfix : f = a.asHom ≫ f) : f = 0 := by
  obtain ⟨n, hnil⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End X)
  rw [Ideal.jacobson_bot] at hnil
  have haPow : a ^ n ∈ (Ring.jacobson (End X)) ^ n :=
    Ideal.pow_mem_pow ha n
  rw [hnil] at haPow
  have haNil : IsNilpotent a := ⟨n, haPow⟩
  have hu : IsUnit (1 - a) := haNil.isUnit_one_sub
  letI : IsIso ((1 - a).asHom) := (isUnit_iff_isIso _).1 hu
  have hzero : (1 - a).asHom ≫ f = 0 := by
    change ((𝟙 X) - a.asHom) ≫ f = 0
    rw [Preadditive.sub_comp, Category.id_comp]
    exact sub_eq_zero.mpr hfix
  apply (cancel_epi ((1 - a).asHom)).1
  simpa using hzero

private theorem eq_zero_of_eq_target_jacobson_action
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [IsArtinianRing (End Y)]
    (f : X ⟶ Y) (b : End Y) (hb : b ∈ Ring.jacobson (End Y))
    (hfix : f = f ≫ b.asHom) : f = 0 := by
  obtain ⟨n, hnil⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End Y)
  rw [Ideal.jacobson_bot] at hnil
  have hbPow : b ^ n ∈ (Ring.jacobson (End Y)) ^ n :=
    Ideal.pow_mem_pow hb n
  rw [hnil] at hbPow
  have hbNil : IsNilpotent b := ⟨n, hbPow⟩
  have hu : IsUnit (1 - b) := hbNil.isUnit_one_sub
  letI : IsIso ((1 - b).asHom) := (isUnit_iff_isIso _).1 hu
  have hzero : f ≫ (1 - b).asHom = 0 := by
    change f ≫ ((𝟙 Y) - b.asHom) = 0
    rw [Preadditive.comp_sub, Category.comp_id]
    exact sub_eq_zero.mpr hfix
  apply (cancel_mono ((1 - b).asHom)).1
  simpa using hzero

omit [IsAlgClosed k] in
/-- If `delta : X ⟶ Y` is a full cotransit generator, the span of
endomorphisms of `Y` factoring through `X` consists exactly of composites
ending in `delta`. -/
private theorem exists_reverse_comp_of_mem_throughObjectSubmodule
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {X Y : C} (delta : X ⟶ Y)
    (hspan : LargeIndecomposable.twoSidedEndomorphismSpan k delta = ⊤)
    (hcotransit : LargeIndecomposable.AllowsCotransit delta)
    {q : Y ⟶ Y}
    (hq : q ∈ LargeIndecomposable.RoiterFigure13E.throughObjectSubmodule
      (k := k) X Y) :
    ∃ lambda : Y ⟶ X, q = lambda ≫ delta := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨l, r, rfl⟩
      have hr : r ∈ LargeIndecomposable.twoSidedEndomorphismSpan k delta := by
        rw [hspan]
        exact Submodule.mem_top
      obtain ⟨a, ha⟩ :=
        LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
          hcotransit hr
      refine ⟨l ≫ a.asHom, ?_⟩
      rw [ha]
      simp only [Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | add q r _ _ hq hr =>
      rcases hq with ⟨l, hl⟩
      rcases hr with ⟨m, hm⟩
      refine ⟨l + m, ?_⟩
      rw [hl, hm, Preadditive.add_comp]
  | smul c q _ hq =>
      rcases hq with ⟨l, hl⟩
      refine ⟨c • l, ?_⟩
      rw [hl, Linear.smul_comp]

omit [IsAlgClosed k] in
/-- Transit gives the source-dual normal form for endomorphisms factoring
through the target of a full generator. -/
private theorem exists_comp_reverse_of_mem_throughObjectSubmodule
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {X Y : C} (delta : X ⟶ Y)
    (hspan : LargeIndecomposable.twoSidedEndomorphismSpan k delta = ⊤)
    (htransit : LargeIndecomposable.AllowsTransit delta)
    {q : X ⟶ X}
    (hq : q ∈ LargeIndecomposable.RoiterFigure13E.throughObjectSubmodule
      (k := k) Y X) :
    ∃ lambda : Y ⟶ X, q = delta ≫ lambda := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨l, r, rfl⟩
      have hl : l ∈ LargeIndecomposable.twoSidedEndomorphismSpan k delta := by
        rw [hspan]
        exact Submodule.mem_top
      obtain ⟨b, hb⟩ :=
        exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit htransit hl
      refine ⟨b.asHom ≫ r, ?_⟩
      rw [hb]
      simp only [Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | add q r _ _ hq hr =>
      rcases hq with ⟨l, hl⟩
      rcases hr with ⟨m, hm⟩
      refine ⟨l + m, ?_⟩
      rw [hl, hm, Preadditive.comp_add]
  | smul c q _ hq =>
      rcases hq with ⟨l, hl⟩
      refine ⟨c • l, ?_⟩
      rw [hl, Linear.comp_smul]

/-- The initial `P₁` zero-representative cut used to choose one literal
zero representative of the complete critical path. -/
abbrev InitialZeroCut
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :=
  LargeIndecomposable.BGRSZeroRepresentativeCut spine.first.toPath
    (spine.middle.comp spine.last.toPath)

/-- The selected first-arrow representative in the zero path. -/
abbrev zeroFirst
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    spine.leftInner.obj.as ⟶ i.obj.as :=
  D.leftRep.composite

/-- The selected middle-path representative obtained by splitting the right
piece of the initial zero cut. -/
abbrev zeroMiddle
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    spine.rightInner.obj.as ⟶ spine.leftInner.obj.as :=
  (LargeIndecomposable.BGRSPathRepresentative.splitComp
    spine.middle spine.last.toPath D.rightRep).1.composite

/-- The selected last-arrow representative obtained from the same split. -/
abbrev zeroLast
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    j.obj.as ⟶ spine.rightInner.obj.as :=
  (LargeIndecomposable.BGRSPathRepresentative.splitComp
    spine.middle spine.last.toPath D.rightRep).2.composite

omit [IsAlgClosed k] in
/-- The three chosen representatives have literal zero composite. -/
theorem zeroLast_middle_first_eq_zero
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    zeroLast S D ≫ zeroMiddle S D ≫ zeroFirst S D = 0 := by
  rw [← Category.assoc,
    ← LargeIndecomposable.BGRSPathRepresentative.composite_splitComp
      spine.middle spine.last.toPath D.rightRep]
  exact D.comp_eq_zero

omit [IsAlgClosed k] in
/-- A literal zero cut exists for every critical spine. -/
theorem nonempty_initialZeroCut
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    Nonempty (InitialZeroCut (S := S) spine) :=
  spine.initialZeroRepresentativeCut

omit [IsAlgClosed k] in
/-- The zero first representative lies on the same ordinary unit ray as the
fixed spine lift. -/
theorem zeroFirst_unitRayEquivalent
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    LargeIndecomposable.UnitRayEquivalent
      (spine.lift.representative spine.first) (zeroFirst S D) := by
  change LargeIndecomposable.UnitRayEquivalent
    (spine.lift.representative spine.first) D.leftRep.composite
  let liftFirst := LargeIndecomposable.BGRSPathRepresentative.ofArrowLift
    spine.lift spine.first.toPath
  have hfirstRay : LargeIndecomposable.rayPathMap spine.first.toPath ≠ 0 :=
    (LargeIndecomposable.rayPathMap_isIrreducible_of_length_eq_one
      spine.first.toPath (by simp)).1
  simpa only [liftFirst,
    LargeIndecomposable.BGRSPathRepresentative.composite_ofArrowLift,
    LargeIndecomposable.BGRSRayArrowLift.pathMap, Quiver.Hom.toPath,
    LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
    Category.comp_id] using
    liftFirst.unitRayEquivalent_of_rayPathMap_ne_zero
      D.leftRep hfirstRay

omit [IsAlgClosed k] in
/-- The zero middle representative lies on the same ordinary unit ray as the
fixed middle lift. -/
theorem zeroMiddle_unitRayEquivalent
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    LargeIndecomposable.UnitRayEquivalent
      (spine.lift.pathMap spine.middle) (zeroMiddle S D) := by
  let liftMiddle := LargeIndecomposable.BGRSPathRepresentative.ofArrowLift
    spine.lift spine.middle
  simpa only [liftMiddle,
    LargeIndecomposable.BGRSPathRepresentative.composite_ofArrowLift] using
    liftMiddle.unitRayEquivalent_of_rayPathMap_ne_zero
      (LargeIndecomposable.BGRSPathRepresentative.splitComp
        spine.middle spine.last.toPath D.rightRep).1
      spine.middle_ray_ne_zero

/-- The Figure-14 contradiction from BGRS 4.3(b) is independent of the
chosen occurrence-sensitive middle representative: the left local radical
generator cannot factor through `zeroMiddle`. -/
theorem leftTau_ne_reverse_comp_zeroMiddle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as) :
    P.tau.asHom ≠ lambda ≫ zeroMiddle S D := by
  intro hfactor
  rcases zeroMiddle_unitRayEquivalent S D with ⟨a, b, hmiddle⟩
  have hcommInv : b.inv ≫ P.tau.asHom = P.tau.asHom ≫ b.inv := by
    have hcomm := ProjectiveCategory.end_mul_comm S
      spine.leftInner.obj.as (End.of b.inv) P.tau
    simpa only [End.mul_def] using congrArg End.asHom hcomm.symm
  apply factorBranch_sigma_ne_reverse_comp_middle
    S hfinite spine P (b.hom ≫ lambda ≫ a.hom)
  calc
    P.tau.asHom = b.hom ≫ (P.tau.asHom ≫ b.inv) := by
      rw [← hcommInv]
      simp only [← Category.assoc, b.hom_inv_id, Category.id_comp]
    _ = b.hom ≫ ((lambda ≫ zeroMiddle S D) ≫ b.inv) := by
      rw [← hfactor]
    _ = (b.hom ≫ lambda ≫ a.hom) ≫
        spine.lift.pathMap spine.middle := by
      rw [hmiddle]
      simp only [Category.assoc, b.hom_inv_id, Category.comp_id]

/-- Dual middle-factor supplement from BGRS 4.3(c): the right local radical
generator cannot factor through the occurrence-sensitive middle
representative.  A hypothetical factorization produces the opposite
left-inner radical generator, which is ruled out by the closed Figure-14
factor branch. -/
theorem rightTau_ne_zeroMiddle_comp_reverse
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as) :
    Q.tau.asHom ≠ zeroMiddle S D ≫ lambda := by
  intro hfactorZero
  rcases zeroMiddle_unitRayEquivalent S D with ⟨a, b, hmiddle⟩
  have hcommInv : a.inv ≫ Q.tau.asHom = Q.tau.asHom ≫ a.inv := by
    have hcomm := ProjectiveCategory.end_mul_comm S
      spine.rightInner.obj.as (End.of a.inv) Q.tau
    simpa only [End.mul_def] using congrArg End.asHom hcomm.symm
  let lambda' : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as :=
    b.hom ≫ lambda ≫ a.hom
  have hfactor : Q.tau.asHom =
      spine.lift.pathMap spine.middle ≫ lambda' := by
    calc
      Q.tau.asHom = (a.inv ≫ Q.tau.asHom) ≫ a.hom := by
        rw [hcommInv]
        simp only [Category.assoc, a.inv_hom_id, Category.comp_id]
      _ = (a.inv ≫ (zeroMiddle S D ≫ lambda)) ≫ a.hom := by
        rw [← hfactorZero]
      _ = spine.lift.pathMap spine.middle ≫ lambda' := by
        rw [hmiddle]
        simp only [lambda', Category.assoc, a.inv_hom_id_assoc]
  let P := spine.reverseCompMiddleRadicalPowerParameter
    S hfinite Q lambda' hfactor
  apply factorBranch_sigma_ne_reverse_comp_middle
    S hfinite spine P lambda'
  change (End.of (lambda' ≫ spine.lift.pathMap spine.middle)).asHom =
    lambda' ≫ spine.lift.pathMap spine.middle
  rfl

/-- The first printed outer supplement of BGRS 4.3(c), before quotienting:
the left-inner radical generator cannot transfer across the occurrence-
sensitive first arrow.  Such a transfer would make the first arrow allow
transit, contradicting the critical endpoint cut. -/
theorem leftTau_zeroFirst_ne_zeroFirst_comp
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (b : End i.obj.as) :
    P.tau.asHom ≫ zeroFirst S D ≠
      zeroFirst S D ≫ b.asHom := by
  letI : Module.Finite k (End spine.leftInner.obj.as) := by
    change Module.Finite k
      (spine.leftInner.obj.as ⟶ spine.leftInner.obj.as)
    infer_instance
  intro htransfer
  apply spine.first_not_allowsTransit S
  have hzeroFirstT : LargeIndecomposable.AllowsTransit (zeroFirst S D) :=
    allowsTransit_of_transfer_of_adjoin_eq_top
      (zeroFirst S D) P.tau b P.adjoin_eq_top htransfer
  exact hzeroFirstT.of_unitRayEquivalent
    (unitRayEquivalent_symm (zeroFirst_unitRayEquivalent S D))

omit [IsAlgClosed k] in
/-- The zero last representative lies on the same ordinary unit ray as the
fixed spine lift. -/
theorem zeroLast_unitRayEquivalent
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    LargeIndecomposable.UnitRayEquivalent
      (spine.lift.representative spine.last) (zeroLast S D) := by
  change LargeIndecomposable.UnitRayEquivalent
    (spine.lift.representative spine.last)
      (LargeIndecomposable.BGRSPathRepresentative.splitComp
        spine.middle spine.last.toPath D.rightRep).2.composite
  let liftLast := LargeIndecomposable.BGRSPathRepresentative.ofArrowLift
    spine.lift spine.last.toPath
  have hlastRay : LargeIndecomposable.rayPathMap spine.last.toPath ≠ 0 :=
    (LargeIndecomposable.rayPathMap_isIrreducible_of_length_eq_one
      spine.last.toPath (by simp)).1
  simpa only [liftLast,
    LargeIndecomposable.BGRSPathRepresentative.composite_ofArrowLift,
    LargeIndecomposable.BGRSRayArrowLift.pathMap, Quiver.Hom.toPath,
    LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
    Category.comp_id] using
    liftLast.unitRayEquivalent_of_rayPathMap_ne_zero
      (LargeIndecomposable.BGRSPathRepresentative.splitComp
        spine.middle spine.last.toPath D.rightRep).2 hlastRay

/-- The dual printed outer supplement of BGRS 4.3(c), before quotienting:
the right-inner radical generator cannot cotransfer across the occurrence-
sensitive last arrow. -/
theorem zeroLast_rightTau_ne_comp_zeroLast
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (a : End j.obj.as) :
    zeroLast S D ≫ Q.tau.asHom ≠
      a.asHom ≫ zeroLast S D := by
  letI : Module.Finite k (End spine.rightInner.obj.as) := by
    change Module.Finite k
      (spine.rightInner.obj.as ⟶ spine.rightInner.obj.as)
    infer_instance
  intro htransfer
  apply spine.last_not_allowsCotransit S
  have hzeroLastC : LargeIndecomposable.AllowsCotransit (zeroLast S D) :=
    allowsCotransit_of_transfer_of_adjoin_eq_top
      (zeroLast S D) a Q.tau Q.adjoin_eq_top htransfer.symm
  exact hzeroLastC.of_unitRayEquivalent
    (unitRayEquivalent_symm (zeroLast_unitRayEquivalent S D))

omit [IsAlgClosed k] in
/-- The chosen middle--first prefix lies on the same ordinary unit ray as the
fixed nonzero critical prefix. -/
theorem zeroMiddle_first_unitRayEquivalent
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    LargeIndecomposable.UnitRayEquivalent
      (spine.lift.pathMap (spine.first.toPath.comp spine.middle))
      (zeroMiddle S D ≫ zeroFirst S D) := by
  let liftPrefix := LargeIndecomposable.BGRSPathRepresentative.ofArrowLift
    spine.lift (spine.first.toPath.comp spine.middle)
  let zeroPrefix := D.leftRep.comp
    (LargeIndecomposable.BGRSPathRepresentative.splitComp
      spine.middle spine.last.toPath D.rightRep).1
  simpa only [liftPrefix, zeroPrefix,
    LargeIndecomposable.BGRSPathRepresentative.composite_ofArrowLift,
    LargeIndecomposable.BGRSPathRepresentative.composite_comp] using
    liftPrefix.unitRayEquivalent_of_rayPathMap_ne_zero
      zeroPrefix spine.prefix_ray_ne_zero

omit [IsAlgClosed k] in
/-- The chosen last--middle suffix lies on the same ordinary unit ray as the
fixed nonzero critical suffix. -/
theorem zeroLast_middle_unitRayEquivalent
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    LargeIndecomposable.UnitRayEquivalent
      (spine.lift.pathMap (spine.middle.comp spine.last.toPath))
      (zeroLast S D ≫ zeroMiddle S D) := by
  let liftSuffix := LargeIndecomposable.BGRSPathRepresentative.ofArrowLift
    spine.lift (spine.middle.comp spine.last.toPath)
  let zeroSuffix :=
    (LargeIndecomposable.BGRSPathRepresentative.splitComp
      spine.middle spine.last.toPath D.rightRep).1.comp
    (LargeIndecomposable.BGRSPathRepresentative.splitComp
      spine.middle spine.last.toPath D.rightRep).2
  simpa only [liftSuffix, zeroSuffix,
    LargeIndecomposable.BGRSPathRepresentative.composite_ofArrowLift,
    LargeIndecomposable.BGRSPathRepresentative.composite_comp] using
    liftSuffix.unitRayEquivalent_of_rayPathMap_ne_zero
      zeroSuffix spine.suffix_ray_ne_zero

/-- Lift the zero first representative to the exact selected corner. -/
abbrev selectedZeroFirst
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :=
  finsetProjectiveHom S (selectedVertices S spine)
    (leftInner_mem_selectedVertices S spine)
    (initial_mem_selectedVertices S spine) (zeroFirst S D)

/-- Lift the zero middle representative to the exact selected corner. -/
abbrev selectedZeroMiddle
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :=
  finsetProjectiveHom S (selectedVertices S spine)
    (rightInner_mem_selectedVertices S spine)
    (leftInner_mem_selectedVertices S spine) (zeroMiddle S D)

/-- Lift the zero last representative to the exact selected corner. -/
abbrev selectedZeroLast
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :=
  finsetProjectiveHom S (selectedVertices S spine)
    (terminal_mem_selectedVertices S spine)
    (rightInner_mem_selectedVertices S spine) (zeroLast S D)

/-- The left radical generator cannot factor through the selected lift of the
occurrence-sensitive middle representative. -/
theorem selectedLeftTau_ne_reverse_comp_selectedZeroMiddle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : selectedLeftInnerObj S spine ⟶
      selectedRightInnerObj S spine) :
    selectedLeftTau S spine P ≠ lambda ≫ selectedZeroMiddle S D := by
  intro hfactor
  let E := selectedProjectiveFunctor S spine
  let eL := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S
      (selectedVertices S spine) spine.leftInner.obj.as
      (leftInner_mem_selectedVertices S spine))
  let eR := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S
      (selectedVertices S spine) spine.rightInner.obj.as
      (rightInner_mem_selectedVertices S spine))
  let lambdaAmbient : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as :=
    CategoryTheory.Linear.homCongr k eL eR (E.map lambda)
  apply leftTau_ne_reverse_comp_zeroMiddle
    S hfinite D P lambdaAmbient
  apply Subtype.ext
  have hval := congrArg (fun f ↦ f.1.1) hfactor
  change (selectedLeftTau S spine P).1.1 =
    (selectedZeroMiddle S D).1.1 * lambda.1.1 at hval
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hval
  have hlambdaVal : lambdaAmbient.1 = lambda.1.1 := by
    simpa only [lambdaAmbient, E, eL, eR] using
      (homCongr_projectiveFunctorMap_val (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) lambda)
  change P.tau.1 = (zeroMiddle S D).1 * lambdaAmbient.1
  rw [hlambdaVal]
  exact hval

/-- Selected-corner form of the dual middle-factor supplement. -/
theorem selectedRightTau_ne_selectedZeroMiddle_comp_reverse
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (lambda : selectedLeftInnerObj S spine ⟶
      selectedRightInnerObj S spine) :
    selectedRightTau S spine Q ≠ selectedZeroMiddle S D ≫ lambda := by
  intro hfactor
  let E := selectedProjectiveFunctor S spine
  let eL := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S
      (selectedVertices S spine) spine.leftInner.obj.as
      (leftInner_mem_selectedVertices S spine))
  let eR := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S
      (selectedVertices S spine) spine.rightInner.obj.as
      (rightInner_mem_selectedVertices S spine))
  let lambdaAmbient : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as :=
    CategoryTheory.Linear.homCongr k eL eR (E.map lambda)
  apply rightTau_ne_zeroMiddle_comp_reverse
    S hfinite D Q lambdaAmbient
  apply Subtype.ext
  have hval := congrArg (fun f ↦ f.1.1) hfactor
  change (selectedRightTau S spine Q).1.1 =
    lambda.1.1 * (selectedZeroMiddle S D).1.1 at hval
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hval
  have hlambdaVal : lambdaAmbient.1 = lambda.1.1 := by
    simpa only [lambdaAmbient, E, eL, eR] using
      (homCongr_projectiveFunctorMap_val (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) lambda)
  change Q.tau.1 = lambdaAmbient.1 * (zeroMiddle S D).1
  rw [hlambdaVal]
  exact hval

/-- Selected-corner form of the left outer transfer exclusion. -/
theorem selectedLeftTau_zeroFirst_ne_zeroFirst_comp
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (b : End (selectedInitialObj S spine)) :
    selectedLeftTau S spine P ≫ selectedZeroFirst S D ≠
      selectedZeroFirst S D ≫ b.asHom := by
  intro htransfer
  let E := selectedProjectiveFunctor S spine
  let eI := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S
      (selectedVertices S spine) i.obj.as
      (initial_mem_selectedVertices S spine))
  let bAmbient : End i.obj.as :=
    CategoryTheory.Linear.homCongr k eI eI (E.map b.asHom)
  apply leftTau_zeroFirst_ne_zeroFirst_comp S D P bAmbient
  apply Subtype.ext
  have hval := congrArg (fun f ↦ f.1.1) htransfer
  change (selectedZeroFirst S D).1.1 *
      (selectedLeftTau S spine P).1.1 =
    b.1.1 * (selectedZeroFirst S D).1.1 at hval
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hval
  have hbVal : bAmbient.1 = b.1.1 := by
    simpa only [bAmbient, E, eI] using
      (homCongr_projectiveFunctorMap_val (k := k) S
        (selectedVertices S spine)
        (initial_mem_selectedVertices S spine)
        (initial_mem_selectedVertices S spine) b.asHom)
  change (zeroFirst S D).1 * P.tau.1 =
    bAmbient.1 * (zeroFirst S D).1
  rw [hbVal]
  exact hval

/-- Selected-corner form of the dual outer cotransfer exclusion. -/
theorem selectedZeroLast_rightTau_ne_comp_selectedZeroLast
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (a : End (selectedTerminalObj S spine)) :
    selectedZeroLast S D ≫ selectedRightTau S spine Q ≠
      a.asHom ≫ selectedZeroLast S D := by
  intro htransfer
  let E := selectedProjectiveFunctor S spine
  let eT := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S
      (selectedVertices S spine) j.obj.as
      (terminal_mem_selectedVertices S spine))
  let aAmbient : End j.obj.as :=
    CategoryTheory.Linear.homCongr k eT eT (E.map a.asHom)
  apply zeroLast_rightTau_ne_comp_zeroLast S D Q aAmbient
  apply Subtype.ext
  have hval := congrArg (fun f ↦ f.1.1) htransfer
  change (selectedRightTau S spine Q).1.1 *
      (selectedZeroLast S D).1.1 =
    (selectedZeroLast S D).1.1 * a.1.1 at hval
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hval
  have haVal : aAmbient.1 = a.1.1 := by
    simpa only [aAmbient, E, eT] using
      (homCongr_projectiveFunctorMap_val (k := k) S
        (selectedVertices S spine)
        (terminal_mem_selectedVertices S spine)
        (terminal_mem_selectedVertices S spine) a.asHom)
  change Q.tau.1 * (zeroLast S D).1 =
    (zeroLast S D).1 * aAmbient.1
  rw [haVal]
  exact hval

omit [IsAlgClosed k] in
/-- The selected-corner zero representatives still have zero composite. -/
theorem selectedZeroLast_middle_first_eq_zero
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine) :
    selectedZeroLast S D ≫ selectedZeroMiddle S D ≫
      selectedZeroFirst S D = 0 := by
  apply Subtype.ext
  simp only [comp_val]
  apply Subtype.ext
  change (selectedZeroFirst S D).1.1 *
    (selectedZeroMiddle S D).1.1 * (selectedZeroLast S D).1.1 = 0
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val,
    finsetProjectiveHom_val_val]
  have hzero := congrArg Subtype.val
    (zeroLast_middle_first_eq_zero S D)
  change (zeroFirst S D).1 * (zeroMiddle S D).1 *
    (zeroLast S D).1 = (0 : A) at hzero
  simpa only [comp_val] using hzero

/-- The exact selected-corner Figure-15 ideal, generated by the reverse of
the source relation `delta rho`. -/
def relationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    TwoSidedIdeal (selectedCorner S spine) :=
  TwoSidedIdeal.span
    ({(selectedRightTau S spine Q ≫ selectedZeroMiddle S D).1} :
      Set (selectedCorner S spine))

/-- BGRS 4.3(c): the relation `ρ δ` of the Figure-15 quotient is nonzero.  It is
a factor of the nonzero terminal sandwich (condition `P_{n-1}` of BGRS 4.2). -/
theorem tau_comp_zeroMiddle_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    Q.tau.asHom ≫ zeroMiddle S D ≠ 0 := by
  intro h0
  apply spine.terminal_parameter_sandwich_ne_zero S hfinite Q
  have hcomp : spine.lift.pathMap (spine.first.toPath.comp spine.middle) =
      spine.lift.pathMap spine.middle ≫ spine.lift.pathMap spine.first.toPath :=
    LinearPathCategory.pathMap_comp _ _ _ _
  rcases zeroMiddle_unitRayEquivalent S D with ⟨a, b, hmiddle⟩
  have hcomm : a.hom ≫ Q.tau.asHom = Q.tau.asHom ≫ a.hom := by
    have hc := ProjectiveCategory.end_mul_comm S
      spine.rightInner.obj.as (End.of a.hom) Q.tau
    simpa only [End.mul_def] using congrArg End.asHom hc.symm
  have hzero : Q.tau.asHom ≫ spine.lift.pathMap spine.middle = 0 := by
    have h1 : a.hom ≫ (Q.tau.asHom ≫ spine.lift.pathMap spine.middle) ≫ b.hom = 0 := by
      rw [← h0, hmiddle]
      simp only [← Category.assoc]
      rw [hcomm]
    have h2 := congrArg (fun t ↦ a.inv ≫ t ≫ b.inv) h1
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc,
      Limits.zero_comp, Limits.comp_zero] using h2
  rw [hcomp, Category.assoc, ← Category.assoc Q.tau.asHom, hzero]
  simp

/-- The Figure-15 relation ideal is nonzero, so mildness applies to its
quotient. -/
theorem relationIdeal_ne_bot
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    relationIdeal S D Q ≠ ⊥ := by
  intro hbot
  have hmem : (selectedRightTau S spine Q ≫ selectedZeroMiddle S D).1 ∈ relationIdeal S D Q :=
    TwoSidedIdeal.subset_span (Set.mem_singleton _)
  rw [hbot] at hmem
  apply tau_comp_zeroMiddle_ne_zero S hfinite D Q
  apply Subtype.ext
  have h1 : (selectedRightTau S spine Q ≫ selectedZeroMiddle S D).1 = 0 := hmem
  have h3 : ((selectedRightTau S spine Q ≫ selectedZeroMiddle S D).1).1 = 0 := by
    rw [h1]; rfl
  rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val] at h3
  change (selectedZeroMiddle S D).1.1 * (selectedRightTau S spine Q).1.1 = 0 at h3
  rw [LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.finsetProjectiveHom_val_val,
    LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.finsetProjectiveHom_val_val] at h3
  rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
  exact h3

/-- The corresponding auxiliary ideal in the ambient algebra.  The exact
selected-corner ideal maps into this ideal under the nonunital corner
inclusion. -/
def ambientRelationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    TwoSidedIdeal A :=
  TwoSidedIdeal.span
    ({(Q.tau.asHom ≫ zeroMiddle S D).1} : Set A)

omit [IsAlgClosed k] in
/-- The ambient Figure-15 auxiliary ideal lies in `Jac(A)^2`. -/
theorem ambientRelationIdeal_le_jacobson_sq
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (ambientRelationIdeal S D Q).asIdeal ≤
      (Ring.jacobson A) ^ 2 := by
  have hmiddle : (zeroMiddle S D).1 ∈ Ring.jacobson A :=
    ProjectiveCategory.val_mem_jacobson_of_unitRayEquivalent S
      (S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
        spine.middle_length_pos)
      (zeroMiddle_unitRayEquivalent S D)
  have hQ : Q.tau.1 ∈ Ring.jacobson A :=
    (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      spine.rightInner.obj.as Q.tau).1 Q.mem_jacobson
  have hle : ambientRelationIdeal S D Q ≤
      ((Ring.jacobson A) ^ 2).toTwoSided := by
    apply TwoSidedIdeal.span_le.2
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    apply Ideal.mem_toTwoSided.2
    rw [show (2 : ℕ) = 1 + 1 by omega,
      Ideal.IsTwoSided.pow_add, Submodule.pow_one]
    simpa only [comp_val] using Ideal.mul_mem_mul hmiddle hQ
  intro a ha
  exact Ideal.mem_toTwoSided.1 (hle ha)

omit [IsAlgClosed k] in
/-- Forgetting the selected corner sends every exact local relation into the
ambient auxiliary ideal generated by the same morphism. -/
theorem relationIdeal_le_comap_ambientRelationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    relationIdeal S D Q ≤
      (ambientRelationIdeal S D Q).comap
        (valNonUnitalRingHom S (selectedEmbedding S spine)) := by
  apply TwoSidedIdeal.span_le.2
  intro a ha
  simp only [Set.mem_singleton_iff] at ha
  subst a
  apply (TwoSidedIdeal.mem_comap
    (valNonUnitalRingHom S (selectedEmbedding S spine))).2
  change (selectedZeroMiddle S D).1.1 *
    (selectedRightTau S spine Q).1.1 ∈
      (ambientRelationIdeal S D Q).asIdeal
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val]
  change (zeroMiddle S D).1 * Q.tau.1 ∈ ambientRelationIdeal S D Q
  exact TwoSidedIdeal.subset_span (Set.mem_singleton
    (Q.tau.asHom ≫ zeroMiddle S D).1)

omit [IsAlgClosed k] in
/-- Elementwise local-to-ambient containment for the Figure-15 relation. -/
theorem val_mem_ambientRelationIdeal_of_mem_relationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    {z : selectedCorner S spine}
    (hz : z ∈ (relationIdeal S D Q).asIdeal) :
    z.1 ∈ (ambientRelationIdeal S D Q).asIdeal := by
  have hz' := relationIdeal_le_comap_ambientRelationIdeal S D Q hz
  exact (TwoSidedIdeal.mem_comap
    (valNonUnitalRingHom S (selectedEmbedding S spine))).1 hz'

omit [IsAlgClosed k] in
/-- In the left-inner endomorphism corner, every ambient Figure-15 relation
term factors through the right-inner object. -/
theorem ambientRelationIdeal_leftInner_corner_le_throughObject
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    finiteIdealCorner S (ambientRelationIdeal S D Q)
        spine.leftInner.obj.as spine.leftInner.obj.as ≤
      LargeIndecomposable.RoiterFigure13E.throughObjectSubmodule
        (k := k) spine.rightInner.obj.as spine.leftInner.obj.as := by
  rw [ambientRelationIdeal,
    finiteIdealCorner_span_singleton_eq_morphismFactorSpan]
  apply Submodule.span_le.2
  rintro q ⟨a, b, rfl⟩
  apply Submodule.subset_span
  refine ⟨a, (Q.tau.asHom ≫ zeroMiddle S D) ≫ b, ?_⟩
  simp only [Category.assoc]

omit [IsAlgClosed k] in
/-- Dually, in the right-inner endomorphism corner every relation term
factors through the left-inner object. -/
theorem ambientRelationIdeal_rightInner_corner_le_throughObject
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    finiteIdealCorner S (ambientRelationIdeal S D Q)
        spine.rightInner.obj.as spine.rightInner.obj.as ≤
      LargeIndecomposable.RoiterFigure13E.throughObjectSubmodule
        (k := k) spine.leftInner.obj.as spine.rightInner.obj.as := by
  rw [ambientRelationIdeal,
    finiteIdealCorner_span_singleton_eq_morphismFactorSpan]
  apply Submodule.span_le.2
  rintro q ⟨a, b, rfl⟩
  apply Submodule.subset_span
  refine ⟨a ≫ (Q.tau.asHom ≫ zeroMiddle S D), b, ?_⟩
  simp only [Category.assoc]

/-- The left local radical generator survives the ambient Figure-15
auxiliary ideal.  Relation-corner membership would give a factorization
through the full middle generator, contradicting the left middle
supplement. -/
theorem leftTau_not_mem_ambientRelationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    P.tau.1 ∉ (ambientRelationIdeal S D Q).asIdeal := by
  intro hmem
  have hcorner : P.tau.asHom ∈ finiteIdealCorner S
      (ambientRelationIdeal S D Q)
        spine.leftInner.obj.as spine.leftInner.obj.as := hmem
  have hthrough :=
    ambientRelationIdeal_leftInner_corner_le_throughObject S D Q hcorner
  have hmiddleRay := zeroMiddle_unitRayEquivalent S D
  have hmiddleSpan : LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroMiddle S D) = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k (zeroMiddle S D) =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.pathMap spine.middle) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hmiddleRay).symm
      _ = ⊤ := spine.middle_full_span S hfinite
  have hmiddleC : LargeIndecomposable.AllowsCotransit (zeroMiddle S D) :=
    (spine.middle_allowsBitransit S hfinite).2.of_unitRayEquivalent hmiddleRay
  obtain ⟨lambda, hfactor⟩ :=
    exists_reverse_comp_of_mem_throughObjectSubmodule
      (zeroMiddle S D) hmiddleSpan hmiddleC hthrough
  exact (leftTau_ne_reverse_comp_zeroMiddle S hfinite D P lambda) hfactor

/-- The right local radical generator also survives the ambient Figure-15
auxiliary ideal. -/
theorem rightTau_not_mem_ambientRelationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    Q.tau.1 ∉ (ambientRelationIdeal S D Q).asIdeal := by
  intro hmem
  have hcorner : Q.tau.asHom ∈ finiteIdealCorner S
      (ambientRelationIdeal S D Q)
        spine.rightInner.obj.as spine.rightInner.obj.as := hmem
  have hthrough :=
    ambientRelationIdeal_rightInner_corner_le_throughObject S D Q hcorner
  have hmiddleRay := zeroMiddle_unitRayEquivalent S D
  have hmiddleSpan : LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroMiddle S D) = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k (zeroMiddle S D) =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.pathMap spine.middle) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hmiddleRay).symm
      _ = ⊤ := spine.middle_full_span S hfinite
  have hmiddleT : LargeIndecomposable.AllowsTransit (zeroMiddle S D) :=
    (spine.middle_allowsBitransit S hfinite).1.of_unitRayEquivalent hmiddleRay
  obtain ⟨lambda, hfactor⟩ :=
    exists_comp_reverse_of_mem_throughObjectSubmodule
      (zeroMiddle S D) hmiddleSpan hmiddleT hthrough
  exact (rightTau_ne_zeroMiddle_comp_reverse S hfinite D Q lambda) hfactor

/-- The left local radical generator admits no arbitrary factorization
through the right-inner object. -/
theorem leftTau_not_factorsThrough_rightInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as) :
    ¬ ∃ (l : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
        (r : spine.rightInner.obj.as ⟶ spine.leftInner.obj.as),
      P.tau.asHom = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  have hmiddleRay := zeroMiddle_unitRayEquivalent S D
  have hmiddleSpan : LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroMiddle S D) = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k (zeroMiddle S D) =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.pathMap spine.middle) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hmiddleRay).symm
      _ = ⊤ := spine.middle_full_span S hfinite
  have hmiddleC : LargeIndecomposable.AllowsCotransit (zeroMiddle S D) :=
    (spine.middle_allowsBitransit S hfinite).2.of_unitRayEquivalent hmiddleRay
  have hr : r ∈ LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroMiddle S D) := by
    rw [hmiddleSpan]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      hmiddleC hr
  apply leftTau_ne_reverse_comp_zeroMiddle S hfinite D P (l ≫ a.asHom)
  calc
    P.tau.asHom = l ≫ r := hlr
    _ = (l ≫ a.asHom) ≫ zeroMiddle S D := by
      rw [ha]
      simp only [Category.assoc]

/-- Dually, the right local radical generator admits no arbitrary
factorization through the left-inner object. -/
theorem rightTau_not_factorsThrough_leftInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    ¬ ∃ (l : spine.rightInner.obj.as ⟶ spine.leftInner.obj.as)
        (r : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as),
      Q.tau.asHom = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  have hmiddleRay := zeroMiddle_unitRayEquivalent S D
  have hmiddleSpan : LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroMiddle S D) = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k (zeroMiddle S D) =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.pathMap spine.middle) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hmiddleRay).symm
      _ = ⊤ := spine.middle_full_span S hfinite
  have hmiddleT : LargeIndecomposable.AllowsTransit (zeroMiddle S D) :=
    (spine.middle_allowsBitransit S hfinite).1.of_unitRayEquivalent hmiddleRay
  have hl : l ∈ LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroMiddle S D) := by
    rw [hmiddleSpan]
    exact Submodule.mem_top
  obtain ⟨b, hb⟩ :=
    exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit hmiddleT hl
  apply rightTau_ne_zeroMiddle_comp_reverse S hfinite D Q (b.asHom ≫ r)
  calc
    Q.tau.asHom = l ≫ r := hlr
    _ = zeroMiddle S D ≫ (b.asHom ≫ r) := by
      rw [hb]
      simp only [Category.assoc]

/-- Selected-corner form of the left generator's exclusion of arbitrary
factorization through the opposite inner object. -/
theorem selectedLeftTau_not_factorsThrough_rightInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as) :
    ¬ ∃ (l : selectedLeftInnerObj S spine ⟶
          selectedRightInnerObj S spine)
        (r : selectedRightInnerObj S spine ⟶
          selectedLeftInnerObj S spine),
      selectedLeftTau S spine P = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  apply leftTau_not_factorsThrough_rightInner S hfinite D P
  let E := selectedProjectiveFunctor S spine
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let lAmbient := CategoryTheory.Linear.homCongr k eL eR (E.map l)
  let rAmbient := CategoryTheory.Linear.homCongr k eR eL (E.map r)
  refine ⟨lAmbient, rAmbient, ?_⟩
  have htau : CategoryTheory.Linear.homCongr k eL eL
      (E.map (selectedLeftTau S spine P)) = P.tau.asHom := by
    simpa [eL, E, selectedProjectiveFunctor, selectedLeftTau] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine) P.tau.asHom)
  have hcomp : CategoryTheory.Linear.homCongr k eL eL
      (E.map l ≫ E.map r) = lAmbient ≫ rAmbient := by
    dsimp only [lAmbient, rAmbient]
    simp only [CategoryTheory.Linear.homCongr_apply, Category.assoc,
      Iso.hom_inv_id_assoc]
  calc
    P.tau.asHom = CategoryTheory.Linear.homCongr k eL eL
        (E.map (selectedLeftTau S spine P)) := htau.symm
    _ = CategoryTheory.Linear.homCongr k eL eL
        (E.map (l ≫ r)) := by rw [hlr]
    _ = lAmbient ≫ rAmbient := by rw [Functor.map_comp, hcomp]

/-- Selected-corner form of the dual arbitrary-factorization exclusion. -/
theorem selectedRightTau_not_factorsThrough_leftInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    ¬ ∃ (l : selectedRightInnerObj S spine ⟶
          selectedLeftInnerObj S spine)
        (r : selectedLeftInnerObj S spine ⟶
          selectedRightInnerObj S spine),
      selectedRightTau S spine Q = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  apply rightTau_not_factorsThrough_leftInner S hfinite D Q
  let E := selectedProjectiveFunctor S spine
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let lAmbient := CategoryTheory.Linear.homCongr k eR eL (E.map l)
  let rAmbient := CategoryTheory.Linear.homCongr k eL eR (E.map r)
  refine ⟨lAmbient, rAmbient, ?_⟩
  have htau : CategoryTheory.Linear.homCongr k eR eR
      (E.map (selectedRightTau S spine Q)) = Q.tau.asHom := by
    simpa [eR, E, selectedProjectiveFunctor, selectedRightTau] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) Q.tau.asHom)
  have hcomp : CategoryTheory.Linear.homCongr k eR eR
      (E.map l ≫ E.map r) = lAmbient ≫ rAmbient := by
    dsimp only [lAmbient, rAmbient]
    simp only [CategoryTheory.Linear.homCongr_apply, Category.assoc,
      Iso.hom_inv_id_assoc]
  calc
    Q.tau.asHom = CategoryTheory.Linear.homCongr k eR eR
        (E.map (selectedRightTau S spine Q)) := htau.symm
    _ = CategoryTheory.Linear.homCongr k eR eR
        (E.map (l ≫ r)) := by rw [hlr]
    _ = lAmbient ≫ rAmbient := by rw [Functor.map_comp, hcomp]

/-- In the first outer-arrow corner, the Figure-15 relation ideal is an
endpoint-radical error around `P.tau ≫ zeroFirst`. -/
theorem ambientRelationIdeal_leftOuter_corner_le_endpointRadical
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    finiteIdealCorner S (ambientRelationIdeal S D Q)
        spine.leftInner.obj.as i.obj.as ≤
      endpointRadicalSubmodule (k := k)
        (P.tau.asHom ≫ zeroFirst S D) := by
  letI : Module.Finite k (End spine.leftInner.obj.as) := by
    change Module.Finite k
      (spine.leftInner.obj.as ⟶ spine.leftInner.obj.as)
    infer_instance
  have hfirstRay := zeroFirst_unitRayEquivalent S D
  have hfirstSpan : LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroFirst S D) = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k (zeroFirst S D) =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.representative spine.first) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hfirstRay).symm
      _ = ⊤ := (spine.initial_full_outer_spans S hfinite).2
  have hfirstC : LargeIndecomposable.AllowsCotransit (zeroFirst S D) :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory)
      (spine.lift.representative spine.first)).resolve_left
        (spine.first_not_allowsTransit S) |>.of_unitRayEquivalent hfirstRay
  rw [ambientRelationIdeal,
    finiteIdealCorner_span_singleton_eq_morphismFactorSpan]
  apply Submodule.span_le.2
  rintro g ⟨a, b, rfl⟩
  have hbMem : b ∈ LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroFirst S D) := by
    rw [hfirstSpan]
    exact Submodule.mem_top
  obtain ⟨d, hd⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      hfirstC hbMem
  let c : End spine.leftInner.obj.as :=
    End.of ((a ≫ (Q.tau.asHom ≫ zeroMiddle S D)) ≫ d.asHom)
  have hmiddleJ : (zeroMiddle S D).1 ∈ Ring.jacobson A :=
    ProjectiveCategory.val_mem_jacobson_of_unitRayEquivalent S
      (S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
        spine.middle_length_pos)
      (zeroMiddle_unitRayEquivalent S D)
  have hcJ : c ∈ Ring.jacobson (End spine.leftInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (((a ≫ (Q.tau.asHom ≫ zeroMiddle S D)) ≫ d.asHom).1) ∈
      Ring.jacobson A
    simp only [comp_val]
    exact (Ring.jacobson A).mul_mem_left d.1
      ((Ring.jacobson A).mul_mem_right a.1
        ((Ring.jacobson A).mul_mem_right Q.tau.1 hmiddleJ))
  by_cases hc0 : c = 0
  · refine ⟨0, (Ring.jacobson (End spine.leftInner.obj.as)).zero_mem,
      0, (Ring.jacobson (End i.obj.as)).zero_mem, ?_⟩
    change (a ≫ (Q.tau.asHom ≫ zeroMiddle S D)) ≫ b =
      (0 : spine.leftInner.obj.as ⟶ spine.leftInner.obj.as) ≫
          (P.tau.asHom ≫ zeroFirst S D) +
        (P.tau.asHom ≫ zeroFirst S D) ≫ (0 : i.obj.as ⟶ i.obj.as)
    rw [Limits.zero_comp, Limits.comp_zero, zero_add]
    rw [hd]
    rw [← Category.assoc]
    have hcHom : c.asHom = 0 := congrArg End.asHom hc0
    change c.asHom ≫ zeroFirst S D = 0
    rw [hcHom]
    simp
  obtain ⟨q, hcq⟩ := P.cotransitData.generates c hcJ
  have hqNotUnit : ¬ IsUnit q := by
    intro hqUnit
    letI : IsIso q.asHom := (isUnit_iff_isIso q).1 hqUnit
    apply leftTau_not_factorsThrough_rightInner S hfinite D P
    refine ⟨inv q.asHom ≫ a ≫ Q.tau.asHom,
      zeroMiddle S D ≫ d.asHom, ?_⟩
    calc
      P.tau.asHom = inv q.asHom ≫ (q.asHom ≫ P.tau.asHom) := by
        rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      _ = inv q.asHom ≫ c.asHom := by rw [← hcq]
      _ = (inv q.asHom ≫ a ≫ Q.tau.asHom) ≫
          (zeroMiddle S D ≫ d.asHom) := by
        simp only [c, Category.assoc]
  have hqJ : q ∈ Ring.jacobson (End spine.leftInner.obj.as) :=
    (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
      (End spine.leftInner.obj.as) q).2 hqNotUnit
  refine ⟨q, hqJ, 0, (Ring.jacobson (End i.obj.as)).zero_mem, ?_⟩
  change (a ≫ (Q.tau.asHom ≫ zeroMiddle S D)) ≫ b =
    q.asHom ≫ (P.tau.asHom ≫ zeroFirst S D) +
      (P.tau.asHom ≫ zeroFirst S D) ≫ (0 : i.obj.as ⟶ i.obj.as)
  rw [hd, Limits.comp_zero, add_zero]
  rw [← Category.assoc]
  change c.asHom ≫ zeroFirst S D =
    q.asHom ≫ (P.tau.asHom ≫ zeroFirst S D)
  rw [hcq]
  exact Category.assoc _ _ _

/-- Source-dually, the last-arrow corner of the relation ideal is an
endpoint-radical error around `zeroLast ≫ Q.tau`. -/
theorem ambientRelationIdeal_rightOuter_corner_le_endpointRadical
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    finiteIdealCorner S (ambientRelationIdeal S D Q)
        j.obj.as spine.rightInner.obj.as ≤
      endpointRadicalSubmodule (k := k)
        (zeroLast S D ≫ Q.tau.asHom) := by
  letI : Module.Finite k (End spine.rightInner.obj.as) := by
    change Module.Finite k
      (spine.rightInner.obj.as ⟶ spine.rightInner.obj.as)
    infer_instance
  have hlastRay := zeroLast_unitRayEquivalent S D
  have hlastSpan : LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroLast S D) = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k (zeroLast S D) =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.representative spine.last) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hlastRay).symm
      _ = ⊤ := (spine.terminal_full_outer_spans S hfinite).1
  have hlastT : LargeIndecomposable.AllowsTransit (zeroLast S D) :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory)
      (spine.lift.representative spine.last)).resolve_right
        (spine.last_not_allowsCotransit S) |>.of_unitRayEquivalent hlastRay
  rw [ambientRelationIdeal,
    finiteIdealCorner_span_singleton_eq_morphismFactorSpan]
  apply Submodule.span_le.2
  rintro g ⟨a, b, rfl⟩
  have haMem : a ∈ LargeIndecomposable.twoSidedEndomorphismSpan k
      (zeroLast S D) := by
    rw [hlastSpan]
    exact Submodule.mem_top
  obtain ⟨d, hd⟩ :=
    exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit hlastT haMem
  let c : End spine.rightInner.obj.as :=
    End.of ((d.asHom ≫ Q.tau.asHom ≫ zeroMiddle S D) ≫ b)
  have hQ : Q.tau.1 ∈ Ring.jacobson A :=
    (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      spine.rightInner.obj.as Q.tau).1 Q.mem_jacobson
  have hcJ : c ∈ Ring.jacobson (End spine.rightInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (((d.asHom ≫ Q.tau.asHom ≫ zeroMiddle S D) ≫ b).1) ∈
      Ring.jacobson A
    simp only [comp_val]
    exact (Ring.jacobson A).mul_mem_left b.1
      ((Ring.jacobson A).mul_mem_right d.1
        ((Ring.jacobson A).mul_mem_left (zeroMiddle S D).1 hQ))
  by_cases hc0 : c = 0
  · refine ⟨0, (Ring.jacobson (End j.obj.as)).zero_mem,
      0, (Ring.jacobson (End spine.rightInner.obj.as)).zero_mem, ?_⟩
    change (a ≫ (Q.tau.asHom ≫ zeroMiddle S D)) ≫ b =
      (0 : j.obj.as ⟶ j.obj.as) ≫
          (zeroLast S D ≫ Q.tau.asHom) +
        (zeroLast S D ≫ Q.tau.asHom) ≫
          (0 : spine.rightInner.obj.as ⟶ spine.rightInner.obj.as)
    rw [Limits.zero_comp, Limits.comp_zero, zero_add]
    rw [hd]
    have hcHom : c.asHom = 0 := congrArg End.asHom hc0
    calc
      ((zeroLast S D ≫ d.asHom) ≫ Q.tau.asHom ≫
            zeroMiddle S D) ≫ b =
          zeroLast S D ≫ c.asHom := by
        simp only [c, Category.assoc]
      _ = 0 := by rw [hcHom]; simp
  obtain ⟨q, hcq⟩ := Q.transitData.generates c hcJ
  have hqNotUnit : ¬ IsUnit q := by
    intro hqUnit
    letI : IsIso q.asHom := (isUnit_iff_isIso q).1 hqUnit
    apply rightTau_not_factorsThrough_leftInner S hfinite D Q
    refine ⟨d.asHom ≫ Q.tau.asHom ≫ zeroMiddle S D,
      b ≫ inv q.asHom, ?_⟩
    calc
      Q.tau.asHom = (Q.tau.asHom ≫ q.asHom) ≫ inv q.asHom := by
        rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      _ = c.asHom ≫ inv q.asHom := by rw [← hcq]
      _ = (d.asHom ≫ Q.tau.asHom ≫ zeroMiddle S D) ≫
          (b ≫ inv q.asHom) := by
        simp only [c, Category.assoc]
  have hqJ : q ∈ Ring.jacobson (End spine.rightInner.obj.as) :=
    (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
      (End spine.rightInner.obj.as) q).2 hqNotUnit
  refine ⟨0, (Ring.jacobson (End j.obj.as)).zero_mem,
    q, hqJ, ?_⟩
  change (a ≫ (Q.tau.asHom ≫ zeroMiddle S D)) ≫ b =
    (0 : j.obj.as ⟶ j.obj.as) ≫
        (zeroLast S D ≫ Q.tau.asHom) +
      (zeroLast S D ≫ Q.tau.asHom) ≫ q.asHom
  rw [hd, Limits.zero_comp, zero_add]
  calc
    ((zeroLast S D ≫ d.asHom) ≫ Q.tau.asHom ≫
          zeroMiddle S D) ≫ b =
        zeroLast S D ≫ c.asHom := by
      simp only [c, Category.assoc]
    _ = zeroLast S D ≫ (Q.tau.asHom ≫ q.asHom) := by rw [hcq]
    _ = (zeroLast S D ≫ Q.tau.asHom) ≫ q.asHom :=
      (Category.assoc _ _ _).symm

/-- The complete first-arrow supplement, including endpoint-radical and
outer-action errors, holds before quotienting. -/
theorem leftOuterSupplement_separated
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as) :
    P.tau.asHom ≫ zeroFirst S D ∉
      LargeIndecomposable.RoiterFigure13E.rightArmSupplementObstruction
        (k := k) (zeroFirst S D) P.tau := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  have hfirstRay := zeroFirst_unitRayEquivalent S D
  have hfirstC : LargeIndecomposable.AllowsCotransit (zeroFirst S D) :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory)
      (spine.lift.representative spine.first)).resolve_left
        (spine.first_not_allowsTransit S) |>.of_unitRayEquivalent hfirstRay
  have hfirstNotT : ¬ LargeIndecomposable.AllowsTransit (zeroFirst S D) := by
    intro hfirstT
    exact spine.first_not_allowsTransit S
      (hfirstT.of_unitRayEquivalent
        (unitRayEquivalent_symm hfirstRay))
  have hnonzero : P.tau.asHom ≫ zeroFirst S D ≠ 0 := by
    intro hzero
    apply leftTau_zeroFirst_ne_zeroFirst_comp S D P
      (0 : End i.obj.as)
    calc
      P.tau.asHom ≫ zeroFirst S D = 0 := hzero
      _ = zeroFirst S D ≫ (0 : i.obj.as ⟶ i.obj.as) := by simp
  exact
    LargeIndecomposable.RoiterFigure13E.rightArmSupplement_separated_of_not_allowsTransit
      (zeroFirst S D) P hfirstC hfirstNotT hnonzero

/-- Source-dual complete last-arrow supplement before quotienting. -/
theorem rightOuterSupplement_separated
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    zeroLast S D ≫ Q.tau.asHom ∉
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) (zeroLast S D) Q.tau := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  have hlastRay := zeroLast_unitRayEquivalent S D
  have hlastT : LargeIndecomposable.AllowsTransit (zeroLast S D) :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory)
      (spine.lift.representative spine.last)).resolve_right
        (spine.last_not_allowsCotransit S) |>.of_unitRayEquivalent hlastRay
  have hlastNotC : ¬ LargeIndecomposable.AllowsCotransit (zeroLast S D) := by
    intro hlastC
    exact spine.last_not_allowsCotransit S
      (hlastC.of_unitRayEquivalent
        (unitRayEquivalent_symm hlastRay))
  have hnonzero : zeroLast S D ≫ Q.tau.asHom ≠ 0 := by
    intro hzero
    apply zeroLast_rightTau_ne_comp_zeroLast S D Q
      (0 : End j.obj.as)
    calc
      zeroLast S D ≫ Q.tau.asHom = 0 := hzero
      _ = (0 : j.obj.as ⟶ j.obj.as) ≫ zeroLast S D := by simp
  exact
    LargeIndecomposable.RoiterFigure13E.leftArmSupplement_separated_of_not_allowsCotransit
      (zeroLast S D) Q hlastT hlastNotC hnonzero

omit [IsAlgClosed k] in
/-- The chosen first irreducible representative stays outside the ambient
Figure-15 auxiliary ideal. -/
theorem zeroFirst_not_mem_ambientRelationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (zeroFirst S D).1 ∉ (ambientRelationIdeal S D Q).asIdeal := by
  intro hmem
  apply S.rayArrowLift_representative_not_mem_jacobson_sq
    spine.lift spine.first
  have hsq := ambientRelationIdeal_le_jacobson_sq S D Q hmem
  rw [show (2 : ℕ) = 1 + 1 by omega,
    Ideal.IsTwoSided.pow_add, Submodule.pow_one] at hsq
  exact ProjectiveCategory.val_mem_ideal_of_unitRayEquivalent S
    (Ring.jacobson A * Ring.jacobson A)
      (f := zeroFirst S D)
      (g := spine.lift.representative spine.first) hsq
      (unitRayEquivalent_symm (zeroFirst_unitRayEquivalent S D))

omit [IsAlgClosed k] in
/-- The chosen last irreducible representative stays outside the ambient
Figure-15 auxiliary ideal. -/
theorem zeroLast_not_mem_ambientRelationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (zeroLast S D).1 ∉ (ambientRelationIdeal S D Q).asIdeal := by
  intro hmem
  apply S.rayArrowLift_representative_not_mem_jacobson_sq
    spine.lift spine.last
  have hsq := ambientRelationIdeal_le_jacobson_sq S D Q hmem
  rw [show (2 : ℕ) = 1 + 1 by omega,
    Ideal.IsTwoSided.pow_add, Submodule.pow_one] at hsq
  exact ProjectiveCategory.val_mem_ideal_of_unitRayEquivalent S
    (Ring.jacobson A * Ring.jacobson A)
      (f := zeroLast S D)
      (g := spine.lift.representative spine.last) hsq
      (unitRayEquivalent_symm (zeroLast_unitRayEquivalent S D))

/-- The central middle--first path survives the ambient Figure-15 auxiliary
ideal.  Every contribution of the relation to this corner is a
source-Jacobson multiple of the full prefix; membership would therefore fix a
nonzero morphism under a nilpotent endomorphism. -/
theorem zeroMiddle_first_not_mem_ambientRelationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (zeroMiddle S D ≫ zeroFirst S D).1 ∉
      (ambientRelationIdeal S D Q).asIdeal := by
  let prefixMap : spine.rightInner.obj.as ⟶ i.obj.as :=
    zeroMiddle S D ≫ zeroFirst S D
  let sourceAction : End spine.rightInner.obj.as →ₗ[k]
      (spine.rightInner.obj.as ⟶ i.obj.as) :=
    { toFun := fun c ↦ c.asHom ≫ prefixMap
      map_add' := by
        intro a b
        change (a.asHom + b.asHom) ≫ prefixMap = _
        rw [Preadditive.add_comp]
      map_smul' := by
        intro c a
        change (c • a.asHom) ≫ prefixMap = c • (a.asHom ≫ prefixMap)
        rw [Linear.smul_comp] }
  let sourceRadicalAction : Submodule k
      (spine.rightInner.obj.as ⟶ i.obj.as) :=
    ((Ring.jacobson (End spine.rightInner.obj.as)).restrictScalars k).map
      sourceAction
  have hprefixRay := zeroMiddle_first_unitRayEquivalent S D
  have hprefixSpan :
      LargeIndecomposable.twoSidedEndomorphismSpan k prefixMap = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k prefixMap =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.pathMap
              (spine.first.toPath.comp spine.middle)) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hprefixRay).symm
      _ = ⊤ := (spine.long_outer_composites_full_spans S hfinite).2
  have hfixedPrefixC : LargeIndecomposable.AllowsCotransit
      (spine.lift.pathMap
        (spine.first.toPath.comp spine.middle)) :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory)
      (spine.lift.pathMap
        (spine.first.toPath.comp spine.middle))).resolve_left
          (spine.prefix_not_allowsTransit S)
  have hprefixC : LargeIndecomposable.AllowsCotransit prefixMap :=
    hfixedPrefixC.of_unitRayEquivalent hprefixRay
  have hprefix0 : prefixMap ≠ 0 := by
    intro hzero
    apply spine.lift_prefix_pathMap_ne_zero
    apply (LargeIndecomposable.unitRay_eq_zero_iff _).1
    calc
      LargeIndecomposable.unitRay
          (spine.lift.pathMap
            (spine.first.toPath.comp spine.middle)) =
          LargeIndecomposable.unitRay prefixMap :=
        (LargeIndecomposable.unitRay_eq_iff _ _).2 hprefixRay
      _ = 0 := (LargeIndecomposable.unitRay_eq_zero_iff _).2 hzero
  have hcornerLe :
      finiteIdealCorner S (ambientRelationIdeal S D Q)
          spine.rightInner.obj.as i.obj.as ≤ sourceRadicalAction := by
    rw [ambientRelationIdeal,
      finiteIdealCorner_span_singleton_eq_morphismFactorSpan]
    apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    have hbaseMem : zeroMiddle S D ≫ b ∈
        LargeIndecomposable.twoSidedEndomorphismSpan k prefixMap := by
      rw [hprefixSpan]
      exact Submodule.mem_top
    obtain ⟨d, hbase⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
        hprefixC hbaseMem
    let c : End spine.rightInner.obj.as :=
      d * (Q.tau * End.of a)
    have hcJ : c ∈ Ring.jacobson (End spine.rightInner.obj.as) :=
      (Ring.jacobson (End spine.rightInner.obj.as)).mul_mem_left d
        ((Ring.jacobson (End spine.rightInner.obj.as)).mul_mem_right
          (End.of a) Q.mem_jacobson)
    apply Submodule.mem_map.2
    refine ⟨c, hcJ, ?_⟩
    change c.asHom ≫ prefixMap =
      (a ≫ (Q.tau.asHom ≫ zeroMiddle S D)) ≫ b
    simp only [c, End.mul_def, Category.assoc]
    rw [← hbase]
  intro hmem
  have hcorner : prefixMap ∈ finiteIdealCorner S
      (ambientRelationIdeal S D Q)
        spine.rightInner.obj.as i.obj.as := hmem
  rcases hcornerLe hcorner with ⟨c, hcJ, hcprefix⟩
  have hfix : prefixMap = c.asHom ≫ prefixMap := hcprefix.symm
  exact hprefix0
    (eq_zero_of_eq_source_jacobson_action prefixMap c hcJ hfix)

/-- Source-dually, the central last--middle path survives the ambient
Figure-15 auxiliary ideal.  Every contribution of the relation to this
corner is a target-Jacobson multiple of the full suffix. -/
theorem zeroLast_middle_not_mem_ambientRelationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (zeroLast S D ≫ zeroMiddle S D).1 ∉
      (ambientRelationIdeal S D Q).asIdeal := by
  let suffixMap : j.obj.as ⟶ spine.leftInner.obj.as :=
    zeroLast S D ≫ zeroMiddle S D
  let targetAction : End spine.leftInner.obj.as →ₗ[k]
      (j.obj.as ⟶ spine.leftInner.obj.as) :=
    { toFun := fun c ↦ suffixMap ≫ c.asHom
      map_add' := by
        intro a b
        change suffixMap ≫ (a.asHom + b.asHom) = _
        rw [Preadditive.comp_add]
      map_smul' := by
        intro c a
        change suffixMap ≫ (c • a.asHom) = c • (suffixMap ≫ a.asHom)
        rw [Linear.comp_smul] }
  let targetRadicalAction : Submodule k
      (j.obj.as ⟶ spine.leftInner.obj.as) :=
    ((Ring.jacobson (End spine.leftInner.obj.as)).restrictScalars k).map
      targetAction
  have hsuffixRay := zeroLast_middle_unitRayEquivalent S D
  have hsuffixSpan :
      LargeIndecomposable.twoSidedEndomorphismSpan k suffixMap = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k suffixMap =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.pathMap
              (spine.middle.comp spine.last.toPath)) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hsuffixRay).symm
      _ = ⊤ := (spine.long_outer_composites_full_spans S hfinite).1
  have hfixedSuffixT : LargeIndecomposable.AllowsTransit
      (spine.lift.pathMap
        (spine.middle.comp spine.last.toPath)) :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory)
      (spine.lift.pathMap
        (spine.middle.comp spine.last.toPath))).resolve_right
          (spine.suffix_not_allowsCotransit S)
  have hsuffixT : LargeIndecomposable.AllowsTransit suffixMap :=
    hfixedSuffixT.of_unitRayEquivalent hsuffixRay
  have hsuffix0 : suffixMap ≠ 0 := by
    intro hzero
    apply spine.lift_suffix_pathMap_ne_zero
    apply (LargeIndecomposable.unitRay_eq_zero_iff _).1
    calc
      LargeIndecomposable.unitRay
          (spine.lift.pathMap
            (spine.middle.comp spine.last.toPath)) =
          LargeIndecomposable.unitRay suffixMap :=
        (LargeIndecomposable.unitRay_eq_iff _ _).2 hsuffixRay
      _ = 0 := (LargeIndecomposable.unitRay_eq_zero_iff _).2 hzero
  have hlastRay := zeroLast_unitRayEquivalent S D
  have hlastSpan :
      LargeIndecomposable.twoSidedEndomorphismSpan k (zeroLast S D) = ⊤ := by
    calc
      LargeIndecomposable.twoSidedEndomorphismSpan k (zeroLast S D) =
          LargeIndecomposable.twoSidedEndomorphismSpan k
            (spine.lift.representative spine.last) :=
        (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
          (k := k) hlastRay).symm
      _ = ⊤ := (spine.terminal_full_outer_spans S hfinite).1
  have hfixedLastT : LargeIndecomposable.AllowsTransit
      (spine.lift.representative spine.last) :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory)
      (spine.lift.representative spine.last)).resolve_right
        (spine.last_not_allowsCotransit S)
  have hlastT : LargeIndecomposable.AllowsTransit (zeroLast S D) :=
    hfixedLastT.of_unitRayEquivalent hlastRay
  have hmiddleRay := zeroMiddle_unitRayEquivalent S D
  have hmiddleT : LargeIndecomposable.AllowsTransit (zeroMiddle S D) :=
    (spine.middle_allowsBitransit S hfinite).1.of_unitRayEquivalent hmiddleRay
  have hmiddle0 : zeroMiddle S D ≠ 0 := by
    intro hzero
    apply spine.lift_middle_pathMap_ne_zero
    apply (LargeIndecomposable.unitRay_eq_zero_iff _).1
    calc
      LargeIndecomposable.unitRay (spine.lift.pathMap spine.middle) =
          LargeIndecomposable.unitRay (zeroMiddle S D) :=
        (LargeIndecomposable.unitRay_eq_iff _ _).2 hmiddleRay
      _ = 0 := (LargeIndecomposable.unitRay_eq_zero_iff _).2 hzero
  have hcornerLe :
      finiteIdealCorner S (ambientRelationIdeal S D Q)
          j.obj.as spine.leftInner.obj.as ≤ targetRadicalAction := by
    rw [ambientRelationIdeal,
      finiteIdealCorner_span_singleton_eq_morphismFactorSpan]
    apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    have haMem : a ∈
        LargeIndecomposable.twoSidedEndomorphismSpan k (zeroLast S D) := by
      rw [hlastSpan]
      exact Submodule.mem_top
    obtain ⟨d, ha⟩ :=
      exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit hlastT haMem
    let r : End spine.rightInner.obj.as := Q.tau * d
    have hrJ : r ∈ Ring.jacobson (End spine.rightInner.obj.as) :=
      (Ring.jacobson (End spine.rightInner.obj.as)).mul_mem_right
        d Q.mem_jacobson
    obtain ⟨e, hre⟩ := hmiddleT r
    have hrNotUnit : ¬ IsUnit r :=
      (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End spine.rightInner.obj.as) r).1 hrJ
    have heNotUnit : ¬ IsUnit e :=
      LargeIndecomposable.not_isUnit_right_of_transfer
        hmiddle0 r e hrNotUnit hre
    have heJ : e ∈ Ring.jacobson (End spine.leftInner.obj.as) :=
      (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End spine.leftInner.obj.as) e).2 heNotUnit
    let c : End spine.leftInner.obj.as := End.of b * e
    have hcJ : c ∈ Ring.jacobson (End spine.leftInner.obj.as) :=
      (Ring.jacobson (End spine.leftInner.obj.as)).mul_mem_left
        (End.of b) heJ
    apply Submodule.mem_map.2
    refine ⟨c, hcJ, ?_⟩
    change suffixMap ≫ c.asHom =
      (a ≫ (Q.tau.asHom ≫ zeroMiddle S D)) ≫ b
    rw [ha]
    calc
      suffixMap ≫ c.asHom =
          (zeroLast S D ≫
            (zeroMiddle S D ≫ e.asHom)) ≫ b := by
        simp only [suffixMap, c, End.mul_def, Category.assoc]
      _ = (zeroLast S D ≫
            (r.asHom ≫ zeroMiddle S D)) ≫ b := by rw [hre]
      _ = ((zeroLast S D ≫ d.asHom) ≫
            (Q.tau.asHom ≫ zeroMiddle S D)) ≫ b := by
        simp only [r, End.mul_def, Category.assoc]
  intro hmem
  have hcorner : suffixMap ∈ finiteIdealCorner S
      (ambientRelationIdeal S D Q)
        j.obj.as spine.leftInner.obj.as := hmem
  rcases hcornerLe hcorner with ⟨c, hcJ, hcsuffix⟩
  have hfix : suffixMap = suffixMap ≫ c.asHom := hcsuffix.symm
  exact hsuffix0
    (eq_zero_of_eq_target_jacobson_action suffixMap c hcJ hfix)

omit [IsAlgClosed k] in
/-- The selected first arm is not killed by the exact local relation. -/
theorem selectedZeroFirst_not_mem_relationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedZeroFirst S D).1 ∉ (relationIdeal S D Q).asIdeal := by
  intro hmem
  apply zeroFirst_not_mem_ambientRelationIdeal S D Q
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D Q hmem
  simpa only [finsetProjectiveHom_val_val] using hval

omit [IsAlgClosed k] in
/-- The selected last arm is not killed by the exact local relation. -/
theorem selectedZeroLast_not_mem_relationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedZeroLast S D).1 ∉ (relationIdeal S D Q).asIdeal := by
  intro hmem
  apply zeroLast_not_mem_ambientRelationIdeal S D Q
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D Q hmem
  simpa only [finsetProjectiveHom_val_val] using hval

/-- The selected left local radical generator is not killed by the exact
Figure-15 relation. -/
theorem selectedLeftTau_not_mem_relationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedLeftTau S spine P).1 ∉
      (relationIdeal S D Q).asIdeal := by
  intro hmem
  apply leftTau_not_mem_ambientRelationIdeal S hfinite D P Q
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D Q hmem
  simpa only [finsetProjectiveHom_val_val] using hval

/-- The selected right local radical generator is not killed either. -/
theorem selectedRightTau_not_mem_relationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedRightTau S spine Q).1 ∉
      (relationIdeal S D Q).asIdeal := by
  intro hmem
  apply rightTau_not_mem_ambientRelationIdeal S hfinite D Q
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D Q hmem
  simpa only [finsetProjectiveHom_val_val] using hval

/-- The selected middle--first path avoids the exact local relation ideal. -/
theorem selectedZeroMiddle_first_not_mem_relationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedZeroMiddle S D ≫ selectedZeroFirst S D).1 ∉
      (relationIdeal S D Q).asIdeal := by
  intro hmem
  apply zeroMiddle_first_not_mem_ambientRelationIdeal S hfinite D Q
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D Q hmem
  change (selectedZeroFirst S D).1.1 *
    (selectedZeroMiddle S D).1.1 ∈
      (ambientRelationIdeal S D Q).asIdeal at hval
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hval
  change (zeroFirst S D).1 * (zeroMiddle S D).1 ∈
    (ambientRelationIdeal S D Q).asIdeal
  exact hval

/-- The selected last--middle path avoids the exact local relation ideal. -/
theorem selectedZeroLast_middle_not_mem_relationIdeal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedZeroLast S D ≫ selectedZeroMiddle S D).1 ∉
      (relationIdeal S D Q).asIdeal := by
  intro hmem
  apply zeroLast_middle_not_mem_ambientRelationIdeal S hfinite D Q
  have hval := val_mem_ambientRelationIdeal_of_mem_relationIdeal S D Q hmem
  change (selectedZeroMiddle S D).1.1 *
    (selectedZeroLast S D).1.1 ∈
      (ambientRelationIdeal S D Q).asIdeal at hval
  rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hval
  change (zeroMiddle S D).1 * (zeroLast S D).1 ∈
    (ambientRelationIdeal S D Q).asIdeal
  exact hval

omit [IsAlgClosed k] in
/-- The Figure-15 generator is a product of two radical morphisms, so its
whole two-sided ideal lies in the square of the selected-corner Jacobson
radical. -/
theorem relationIdeal_le_jacobson_sq
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (relationIdeal S D Q).asIdeal ≤
      (Ring.jacobson (selectedCorner S spine)) ^ 2 := by
  have hmiddleAmbient : (zeroMiddle S D).1 ∈ Ring.jacobson A :=
    ProjectiveCategory.val_mem_jacobson_of_unitRayEquivalent S
      (S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
        spine.middle_length_pos)
      (zeroMiddle_unitRayEquivalent S D)
  have hmiddle : (selectedZeroMiddle S D).1 ∈
      Ring.jacobson (selectedCorner S spine) :=
    finsetProjectiveHom_val_mem_jacobson S (selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine)
      (leftInner_mem_selectedVertices S spine) (zeroMiddle S D)
      hmiddleAmbient
  have hQ : (selectedRightTau S spine Q).1 ∈
      Ring.jacobson (selectedCorner S spine) :=
    finsetProjectiveHom_val_mem_jacobson S (selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine) Q.tau.asHom
      ((S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        spine.rightInner.obj.as Q.tau).1 Q.mem_jacobson)
  have hle : relationIdeal S D Q ≤
      ((Ring.jacobson (selectedCorner S spine)) ^ 2).toTwoSided := by
    apply TwoSidedIdeal.span_le.2
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    apply Ideal.mem_toTwoSided.2
    rw [show (2 : ℕ) = 1 + 1 by omega,
      Ideal.IsTwoSided.pow_add, Submodule.pow_one]
    simpa only [comp_val] using Ideal.mul_mem_mul hmiddle hQ
  intro a ha
  exact Ideal.mem_toTwoSided.1 (hle ha)

omit [IsAlgClosed k] in
/-- The exact Figure-15 relation ideal lies in the selected-corner Jacobson
radical. -/
theorem relationIdeal_le_jacobson
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (relationIdeal S D Q).asIdeal ≤
      Ring.jacobson (selectedCorner S spine) := by
  have hQ : (selectedRightTau S spine Q).1 ∈
      Ring.jacobson (selectedCorner S spine) :=
    finsetProjectiveHom_val_mem_jacobson S (selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine) Q.tau.asHom
      ((S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        spine.rightInner.obj.as Q.tau).1 Q.mem_jacobson)
  have hle : relationIdeal S D Q ≤
      (Ring.jacobson (selectedCorner S spine)).toTwoSided := by
    apply TwoSidedIdeal.span_le.2
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    apply Ideal.mem_toTwoSided.2
    simpa only [comp_val] using
      (Ring.jacobson (selectedCorner S spine)).mul_mem_left
        (selectedZeroMiddle S D).1 hQ
  intro a ha
  exact Ideal.mem_toTwoSided.1 (hle ha)

/-- The repeated-object ambient Figure-15 diagram inside the exact selected
corner. -/
def selectedAmbientDiagram
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    Figure15LocalAmbientDiagram S
      (Fintype.card ↑(selectedVertices S spine))
      (selectedEmbedding S spine) where
  object
    | .leftEndpoint => selectedTerminalObj S spine
    | .leftCenter => selectedRightInnerObj S spine
    | .rightCenter => selectedLeftInnerObj S spine
    | .rightEndpoint => selectedInitialObj S spine
    | .upperCenter => selectedLeftInnerObj S spine
    | .upperEndpoint => selectedInitialObj S spine
    | .lowerCenter => selectedRightInnerObj S spine
    | .lowerEndpoint => selectedTerminalObj S spine
  arrow
    | .alphaLeft => selectedZeroLast S D
    | .delta => selectedZeroMiddle S D
    | .alphaRight => selectedZeroFirst S D
    | .rho => selectedLeftTau S spine P
    | .alphaUpper => selectedZeroFirst S D
    | .sigma => selectedRightTau S spine Q
    | .alphaLower => selectedZeroLast S D

/-- The exact selected-corner quotient candidate for BGRS Figure 15. -/
def localQuotientCandidate
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    Figure15LocalQuotientCandidate S where
  rank := Fintype.card ↑(selectedVertices S spine)
  r := selectedEmbedding S spine
  I := relationIdeal S D Q
  le_jacobson := relationIdeal_le_jacobson S D Q
  ambient := selectedAmbientDiagram S D P Q
  main_mem := by
    change (selectedZeroLast S D ≫ selectedZeroMiddle S D ≫
      selectedZeroFirst S D).1 ∈ (relationIdeal S D Q).asIdeal
    rw [selectedZeroLast_middle_first_eq_zero S D]
    exact (relationIdeal S D Q).zero_mem

omit [IsAlgClosed k] in
/-- Every critical spine supplies an exact local Figure-15 quotient
candidate.  Cleaving of this candidate is the remaining Figure-15
obligation. -/
theorem nonempty_localQuotientCandidate
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    Nonempty (Figure15LocalQuotientCandidate S) := by
  obtain ⟨D⟩ := nonempty_initialZeroCut S spine
  obtain ⟨P⟩ := (spine.nonempty_middle_radicalPowerParameters S).1
  obtain ⟨Q⟩ := (spine.nonempty_middle_radicalPowerParameters S).2
  exact ⟨localQuotientCandidate S D P Q⟩

/-- The exact quotient functor on the selected primitive projectives. -/
abbrev quotientFunctor
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :=
  (selectedSplitBasic S spine).projectiveQuotientFunctor
    (relationIdeal S D Q) (relationIdeal_le_jacobson S D Q)

omit [IsAlgClosed k] in
/-- A selected-corner morphism survives the exact Figure-15 quotient whenever
its corner element is outside the relation ideal. -/
theorem quotientFunctor_map_ne_zero_of_not_mem_relationIdeal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    {U V : (selectedSplitBasic S spine).ProjectiveCategory}
    (h : U ⟶ V) (hh : h.1 ∉ (relationIdeal S D Q).asIdeal) :
    (quotientFunctor S D Q).map h ≠ 0 := by
  intro hzero
  apply hh
  exact ((selectedSplitBasic S spine).projectiveQuotientFunctor_map_eq_zero_iff
    (relationIdeal S D Q) (relationIdeal_le_jacobson S D Q) h).1 hzero

omit [IsAlgClosed k] in
/-- The exact quotient kills the source relation `delta rho`, written in the
reversed primitive-projective convention. -/
theorem quotientFunctor_map_rightTau_middle_eq_zero
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).map
      (selectedRightTau S spine Q ≫ selectedZeroMiddle S D) = 0 := by
  rw [(selectedSplitBasic S spine).projectiveQuotientFunctor_map_eq_zero_iff]
  exact TwoSidedIdeal.subset_span (Set.mem_singleton _)

omit [IsAlgClosed k] in
/-- Both occurrences of the selected first irreducible arrow survive the
exact Figure-15 quotient. -/
theorem quotientFunctor_map_selectedZeroFirst_ne_zero
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).map (selectedZeroFirst S D) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D Q
    (selectedZeroFirst S D) (selectedZeroFirst_not_mem_relationIdeal S D Q)

omit [IsAlgClosed k] in
/-- Both occurrences of the selected last irreducible arrow survive the
exact Figure-15 quotient. -/
theorem quotientFunctor_map_selectedZeroLast_ne_zero
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).map (selectedZeroLast S D) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D Q
    (selectedZeroLast S D) (selectedZeroLast_not_mem_relationIdeal S D Q)

/-- The left local radical generator survives the exact Figure-15 quotient. -/
theorem quotientFunctor_map_selectedLeftTau_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).map (selectedLeftTau S spine P) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D Q
    (selectedLeftTau S spine P)
    (selectedLeftTau_not_mem_relationIdeal S hfinite D P Q)

/-- The right local radical generator survives the exact Figure-15 quotient. -/
theorem quotientFunctor_map_selectedRightTau_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).map (selectedRightTau S spine Q) ≠ 0 :=
  quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D Q
    (selectedRightTau S spine Q)
    (selectedRightTau_not_mem_relationIdeal S hfinite D Q)

set_option maxHeartbeats 800000 in
/-- The surviving left local generator cannot acquire a factorization
through the right-inner object after passage to the exact Figure-15
quotient. -/
theorem quotientLeftTau_not_factorsThrough_rightInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    ¬ ∃ (l : F.obj (selectedLeftInnerObj S spine) ⟶
          F.obj (selectedRightInnerObj S spine))
        (r : F.obj (selectedRightInnerObj S spine) ⟶
          F.obj (selectedLeftInnerObj S spine)),
      F.map (selectedLeftTau S spine P) = l ≫ r := by
  dsimp only
  let T := selectedSplitBasic S spine
  let I := relationIdeal S D Q
  let F := quotientFunctor S D Q
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      T.ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  rintro ⟨lbar, rbar, hbar⟩
  have hIcorner : finiteIdealCorner T I
        (selectedLeftInnerObj S spine) (selectedLeftInnerObj S spine) ≤
      LargeIndecomposable.twoSidedEndomorphismSpan k
        (selectedLeftTau S spine P) := by
    intro g hg
    have hgVal : g.1 ∈ Ring.jacobson (selectedCorner S spine) :=
      relationIdeal_le_jacobson S D Q hg
    have hgEnd : End.of g ∈
        Ring.jacobson (End (selectedLeftInnerObj S spine)) :=
      ((selectedSplitBasic S spine).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (selectedLeftInnerObj S spine) (End.of g)).2 hgVal
    change End.of g ∈ LargeIndecomposable.twoSidedEndomorphismSpan k
      (End.of (selectedLeftTau S spine P))
    rw [factorBranch_selectedLeftTau_span_eq_jacobson S spine P]
    exact hgEnd
  obtain ⟨l, r, hlr⟩ :=
    factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
      T I (relationIdeal_le_jacobson S D Q)
      (selectedLeftTau S spine P) hIcorner
      (quotientFunctor_map_selectedLeftTau_ne_zero
        S hfinite D P Q) lbar rbar hbar
  exact selectedLeftTau_not_factorsThrough_rightInner
    S hfinite D P ⟨l, r, hlr⟩

set_option maxHeartbeats 800000 in
/-- The surviving right local generator cannot acquire a factorization
through the left-inner object in the exact quotient. -/
theorem quotientRightTau_not_factorsThrough_leftInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    ¬ ∃ (l : F.obj (selectedRightInnerObj S spine) ⟶
          F.obj (selectedLeftInnerObj S spine))
        (r : F.obj (selectedLeftInnerObj S spine) ⟶
          F.obj (selectedRightInnerObj S spine)),
      F.map (selectedRightTau S spine Q) = l ≫ r := by
  dsimp only
  let T := selectedSplitBasic S spine
  let I := relationIdeal S D Q
  let F := quotientFunctor S D Q
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      T.ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  rintro ⟨lbar, rbar, hbar⟩
  have hIcorner : finiteIdealCorner T I
        (selectedRightInnerObj S spine) (selectedRightInnerObj S spine) ≤
      LargeIndecomposable.twoSidedEndomorphismSpan k
        (selectedRightTau S spine Q) := by
    intro g hg
    have hgVal : g.1 ∈ Ring.jacobson (selectedCorner S spine) :=
      relationIdeal_le_jacobson S D Q hg
    have hgEnd : End.of g ∈
        Ring.jacobson (End (selectedRightInnerObj S spine)) :=
      ((selectedSplitBasic S spine).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (selectedRightInnerObj S spine) (End.of g)).2 hgVal
    change End.of g ∈ LargeIndecomposable.twoSidedEndomorphismSpan k
      (End.of (selectedRightTau S spine Q))
    rw [selectedRightTau_span_eq_jacobson S spine Q]
    exact hgEnd
  obtain ⟨l, r, hlr⟩ :=
    factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
      T I (relationIdeal_le_jacobson S D Q)
      (selectedRightTau S spine Q) hIcorner
      (quotientFunctor_map_selectedRightTau_ne_zero
        S hfinite D Q) lbar rbar hbar
  exact selectedRightTau_not_factorsThrough_leftInner
    S hfinite D Q ⟨l, r, hlr⟩

/-- Quotient-stable left middle-factor supplement. -/
theorem quotientLeftTau_ne_reverse_comp_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (lambda : (quotientFunctor S D Q).obj
        (selectedLeftInnerObj S spine) ⟶
      (quotientFunctor S D Q).obj (selectedRightInnerObj S spine)) :
    (quotientFunctor S D Q).map (selectedLeftTau S spine P) ≠
      lambda ≫ (quotientFunctor S D Q).map (selectedZeroMiddle S D) := by
  intro hfactor
  exact quotientLeftTau_not_factorsThrough_rightInner
    S hfinite D P Q ⟨lambda,
      (quotientFunctor S D Q).map (selectedZeroMiddle S D), hfactor⟩

/-- Quotient-stable dual middle-factor supplement. -/
theorem quotientRightTau_ne_middle_comp_reverse
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (lambda : (quotientFunctor S D Q).obj
        (selectedLeftInnerObj S spine) ⟶
      (quotientFunctor S D Q).obj (selectedRightInnerObj S spine)) :
    (quotientFunctor S D Q).map (selectedRightTau S spine Q) ≠
      (quotientFunctor S D Q).map (selectedZeroMiddle S D) ≫ lambda := by
  intro hfactor
  exact quotientRightTau_not_factorsThrough_leftInner
    S hfinite D Q ⟨(quotientFunctor S D Q).map (selectedZeroMiddle S D),
      lambda, hfactor⟩

set_option maxHeartbeats 800000 in
/-- The first printed outer supplement remains valid in the exact quotient:
the surviving left local generator cannot transfer across the first arrow. -/
theorem quotientLeftTau_zeroFirst_ne_zeroFirst_comp
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (bbar : End ((quotientFunctor S D Q).obj
      (selectedInitialObj S spine))) :
    (quotientFunctor S D Q).map (selectedLeftTau S spine P) ≫
        (quotientFunctor S D Q).map (selectedZeroFirst S D) ≠
      (quotientFunctor S D Q).map (selectedZeroFirst S D) ≫
        bbar.asHom := by
  let F := quotientFunctor S D Q
  intro htransfer
  obtain ⟨bHom, hbHom⟩ := F.map_surjective bbar.asHom
  let b : End (selectedInitialObj S spine) := End.of bHom
  have hb : F.map b.asHom = bbar.asHom := hbHom
  let dSelected : selectedLeftInnerObj S spine ⟶
      selectedInitialObj S spine :=
    selectedLeftTau S spine P ≫ selectedZeroFirst S D -
      selectedZeroFirst S D ≫ b.asHom
  have hdMap : F.map dSelected = 0 := by
    dsimp only [dSelected]
    rw [F.map_sub, F.map_comp, F.map_comp, hb]
    exact sub_eq_zero.mpr htransfer
  have hdIdeal : dSelected.1 ∈ (relationIdeal S D Q).asIdeal :=
    ((selectedSplitBasic S spine).projectiveQuotientFunctor_map_eq_zero_iff
      (relationIdeal S D Q) (relationIdeal_le_jacobson S D Q)
      dSelected).1 hdMap
  have hdVal := val_mem_ambientRelationIdeal_of_mem_relationIdeal
    S D Q hdIdeal
  let E := selectedProjectiveFunctor S spine
  let eI := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S
      (selectedVertices S spine) i.obj.as
      (initial_mem_selectedVertices S spine))
  let bAmbient : End i.obj.as :=
    CategoryTheory.Linear.homCongr k eI eI (E.map b.asHom)
  have hbVal : bAmbient.1 = b.1.1 := by
    simpa only [bAmbient, E, eI] using
      (homCongr_projectiveFunctorMap_val (k := k) S
        (selectedVertices S spine)
        (initial_mem_selectedVertices S spine)
        (initial_mem_selectedVertices S spine) b.asHom)
  have hdVal' : (zeroFirst S D).1 * P.tau.1 -
      b.1.1 * (zeroFirst S D).1 ∈
        (ambientRelationIdeal S D Q).asIdeal := by
    dsimp only [dSelected] at hdVal
    change (selectedZeroFirst S D).1.1 *
          (selectedLeftTau S spine P).1.1 -
        b.1.1 * (selectedZeroFirst S D).1.1 ∈
      (ambientRelationIdeal S D Q).asIdeal at hdVal
    rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hdVal
    exact hdVal
  let dAmbient : spine.leftInner.obj.as ⟶ i.obj.as :=
    P.tau.asHom ≫ zeroFirst S D -
      zeroFirst S D ≫ bAmbient.asHom
  have hdAmbient : dAmbient.1 ∈
      (ambientRelationIdeal S D Q).asIdeal := by
    change ((P.tau.asHom ≫ zeroFirst S D -
      zeroFirst S D ≫ bAmbient.asHom).1) ∈ _
    change (zeroFirst S D).1 * P.tau.1 -
      bAmbient.1 * (zeroFirst S D).1 ∈ _
    rw [hbVal]
    exact hdVal'
  have hdCorner : dAmbient ∈ finiteIdealCorner S
      (ambientRelationIdeal S D Q)
        spine.leftInner.obj.as i.obj.as := hdAmbient
  have hdEndpoint :=
    ambientRelationIdeal_leftOuter_corner_le_endpointRadical
      S hfinite D P Q hdCorner
  apply leftOuterSupplement_separated S D P
  apply Submodule.mem_sup.2
  refine ⟨dAmbient, hdEndpoint,
    zeroFirst S D ≫ bAmbient.asHom, ?_, ?_⟩
  · exact ⟨bAmbient, rfl⟩
  · dsimp only [dAmbient]
    module

set_option maxHeartbeats 800000 in
/-- Source-dual quotient-stable last-arrow transfer exclusion. -/
theorem quotientZeroLast_rightTau_ne_comp_zeroLast
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (abar : End ((quotientFunctor S D Q).obj
      (selectedTerminalObj S spine))) :
    (quotientFunctor S D Q).map (selectedZeroLast S D) ≫
        (quotientFunctor S D Q).map (selectedRightTau S spine Q) ≠
      abar.asHom ≫
        (quotientFunctor S D Q).map (selectedZeroLast S D) := by
  let F := quotientFunctor S D Q
  intro htransfer
  obtain ⟨aHom, haHom⟩ := F.map_surjective abar.asHom
  let a : End (selectedTerminalObj S spine) := End.of aHom
  have ha : F.map a.asHom = abar.asHom := haHom
  let dSelected : selectedTerminalObj S spine ⟶
      selectedRightInnerObj S spine :=
    selectedZeroLast S D ≫ selectedRightTau S spine Q -
      a.asHom ≫ selectedZeroLast S D
  have hdMap : F.map dSelected = 0 := by
    dsimp only [dSelected]
    rw [F.map_sub, F.map_comp, F.map_comp, ha]
    exact sub_eq_zero.mpr htransfer
  have hdIdeal : dSelected.1 ∈ (relationIdeal S D Q).asIdeal :=
    ((selectedSplitBasic S spine).projectiveQuotientFunctor_map_eq_zero_iff
      (relationIdeal S D Q) (relationIdeal_le_jacobson S D Q)
      dSelected).1 hdMap
  have hdVal := val_mem_ambientRelationIdeal_of_mem_relationIdeal
    S D Q hdIdeal
  let E := selectedProjectiveFunctor S spine
  let eT := eqToIso
    (projectiveFunctor_obj_finsetProjectiveObj_eq S
      (selectedVertices S spine) j.obj.as
      (terminal_mem_selectedVertices S spine))
  let aAmbient : End j.obj.as :=
    CategoryTheory.Linear.homCongr k eT eT (E.map a.asHom)
  have haVal : aAmbient.1 = a.1.1 := by
    simpa only [aAmbient, E, eT] using
      (homCongr_projectiveFunctorMap_val (k := k) S
        (selectedVertices S spine)
        (terminal_mem_selectedVertices S spine)
        (terminal_mem_selectedVertices S spine) a.asHom)
  have hdVal' : Q.tau.1 * (zeroLast S D).1 -
      (zeroLast S D).1 * a.1.1 ∈
        (ambientRelationIdeal S D Q).asIdeal := by
    dsimp only [dSelected] at hdVal
    change (selectedRightTau S spine Q).1.1 *
          (selectedZeroLast S D).1.1 -
        (selectedZeroLast S D).1.1 * a.1.1 ∈
      (ambientRelationIdeal S D Q).asIdeal at hdVal
    rw [finsetProjectiveHom_val_val, finsetProjectiveHom_val_val] at hdVal
    exact hdVal
  let dAmbient : j.obj.as ⟶ spine.rightInner.obj.as :=
    zeroLast S D ≫ Q.tau.asHom -
      aAmbient.asHom ≫ zeroLast S D
  have hdAmbient : dAmbient.1 ∈
      (ambientRelationIdeal S D Q).asIdeal := by
    change ((zeroLast S D ≫ Q.tau.asHom -
      aAmbient.asHom ≫ zeroLast S D).1) ∈ _
    change Q.tau.1 * (zeroLast S D).1 -
      (zeroLast S D).1 * aAmbient.1 ∈ _
    rw [haVal]
    exact hdVal'
  have hdCorner : dAmbient ∈ finiteIdealCorner S
      (ambientRelationIdeal S D Q)
        j.obj.as spine.rightInner.obj.as := hdAmbient
  have hdEndpoint :=
    ambientRelationIdeal_rightOuter_corner_le_endpointRadical
      S hfinite D Q hdCorner
  apply rightOuterSupplement_separated S D Q
  apply Submodule.mem_sup.2
  refine ⟨dAmbient, hdEndpoint,
    aAmbient.asHom ≫ zeroLast S D, ?_, ?_⟩
  · exact ⟨aAmbient, rfl⟩
  · dsimp only [dAmbient]
    module

/-- The central middle--first path survives the exact Figure-15 quotient. -/
theorem quotientFunctor_map_selectedZeroMiddle_first_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).map (selectedZeroMiddle S D) ≫
      (quotientFunctor S D Q).map (selectedZeroFirst S D) ≠ 0 := by
  rw [← Functor.map_comp]
  exact quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D Q
    (selectedZeroMiddle S D ≫ selectedZeroFirst S D)
    (selectedZeroMiddle_first_not_mem_relationIdeal S hfinite D Q)

/-- The central last--middle path survives the exact Figure-15 quotient. -/
theorem quotientFunctor_map_selectedZeroLast_middle_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).map (selectedZeroLast S D) ≫
      (quotientFunctor S D Q).map (selectedZeroMiddle S D) ≠ 0 := by
  rw [← Functor.map_comp]
  exact quotientFunctor_map_ne_zero_of_not_mem_relationIdeal S D Q
    (selectedZeroLast S D ≫ selectedZeroMiddle S D)
    (selectedZeroLast_middle_not_mem_relationIdeal S hfinite D Q)

end LargeIndecomposable.CriticalFigure15Quotient
