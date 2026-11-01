module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.Cleaving.ClosedChains.Figure15CoefficientCompiler
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure15Quotient

@[expose] public section

/-!
# The exact Figure-15 quotient retraction

This file specializes the finite Figure-15 endpoint coefficient compiler to
the source-exact selected-corner quotient constructed in
`CriticalFigure15Quotient`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalFigure15Quotient

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.CriticalFigure14Quotient
open LargeIndecomposable.CriticalSingularFigure15
open LargeIndecomposable.SplitBasicIdempotents
open LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory
open LargeIndecomposable.SplitBasicIdempotents.SelectedCorner

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

private theorem isUnit_of_cotransit_equation
    {C : Type*} [Category C] [Preadditive C]
    {X Y : C} [IsLocalRing (End X)] [IsArtinianRing (End X)]
    {f : X ⟶ Y} (hf0 : f ≠ 0)
    {a : End Y} (ha : IsUnit a) {b : End X}
    (h : f ≫ a.asHom = b.asHom ≫ f) : IsUnit b := by
  by_contra hbUnit
  have hbJ : b ∈ Ring.jacobson (End X) :=
    (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit (End X) b).2 hbUnit
  obtain ⟨n, hbn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End X)
  rw [Ideal.jacobson_bot] at hbn
  have hbPow : b ^ n ∈ (Ring.jacobson (End X)) ^ n :=
    Ideal.pow_mem_pow hbJ n
  rw [hbn] at hbPow
  have hbNil : b ^ n = 0 := hbPow
  have hp : ∀ m : ℕ,
      f ≫ (a ^ m).asHom = (b ^ m).asHom ≫ f := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          f ≫ (a ^ (m + 1)).asHom =
              (f ≫ a.asHom) ≫ (a ^ m).asHom := by
                rw [pow_succ, End.mul_def]
                simp only [Category.assoc]
          _ = (b.asHom ≫ f) ≫ (a ^ m).asHom := by rw [h]
          _ = b.asHom ≫ (f ≫ (a ^ m).asHom) :=
            Category.assoc _ _ _
          _ = b.asHom ≫ ((b ^ m).asHom ≫ f) := by rw [ih]
          _ = (b ^ (m + 1)).asHom ≫ f := by
            rw [pow_succ, End.mul_def]
            simp only [Category.assoc]
  have hzero : f ≫ (a ^ n).asHom = 0 := by
    rw [hp n]
    have hbNilHom : (b ^ n).asHom = 0 := congrArg End.asHom hbNil
    rw [hbNilHom]
    exact Limits.zero_comp
  have haPow : IsUnit (a ^ n) := ha.pow n
  letI : IsIso ((a ^ n).asHom) := (isUnit_iff_isIso _).1 haPow
  apply hf0
  apply (cancel_mono ((a ^ n).asHom)).1
  simpa using hzero

private theorem isUnit_of_transit_equation
    {C : Type*} [Category C] [Preadditive C]
    {X Y : C} [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    {f : X ⟶ Y} (hf0 : f ≠ 0)
    {a : End X} (ha : IsUnit a) {b : End Y}
    (h : a.asHom ≫ f = f ≫ b.asHom) : IsUnit b := by
  by_contra hbUnit
  have hbJ : b ∈ Ring.jacobson (End Y) :=
    (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit (End Y) b).2 hbUnit
  obtain ⟨n, hbn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End Y)
  rw [Ideal.jacobson_bot] at hbn
  have hbPow : b ^ n ∈ (Ring.jacobson (End Y)) ^ n :=
    Ideal.pow_mem_pow hbJ n
  rw [hbn] at hbPow
  have hbNil : b ^ n = 0 := hbPow
  have hp : ∀ m : ℕ,
      (a ^ m).asHom ≫ f = f ≫ (b ^ m).asHom := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          (a ^ (m + 1)).asHom ≫ f =
              a.asHom ≫ ((a ^ m).asHom ≫ f) := by
                rw [pow_succ, End.mul_def]
                simp only [Category.assoc]
          _ = a.asHom ≫ (f ≫ (b ^ m).asHom) := by rw [ih]
          _ = (a.asHom ≫ f) ≫ (b ^ m).asHom :=
            (Category.assoc _ _ _).symm
          _ = (f ≫ b.asHom) ≫ (b ^ m).asHom := by rw [h]
          _ = f ≫ (b ^ (m + 1)).asHom := by
            rw [pow_succ, End.mul_def]
            simp only [Category.assoc]
  have hzero : (a ^ n).asHom ≫ f = 0 := by
    rw [hp n]
    have hbNilHom : (b ^ n).asHom = 0 := congrArg End.asHom hbNil
    rw [hbNilHom]
    exact Limits.comp_zero
  have haPow : IsUnit (a ^ n) := ha.pow n
  letI : IsIso ((a ^ n).asHom) := (isUnit_iff_isIso _).1 haPow
  apply hf0
  apply (cancel_epi ((a ^ n).asHom)).1
  simpa using hzero

private theorem unit_sandwich_ne_zero_of_allowsCotransit_left
    {C : Type*} [Category C] [Preadditive C]
    {X Y Z : C} [IsLocalRing (End X)] [IsArtinianRing (End X)]
    {alpha : X ⟶ Y} {beta : Y ⟶ Z}
    (hcomp : alpha ≫ beta ≠ 0)
    (halpha : LargeIndecomposable.AllowsCotransit alpha)
    (a : End Y) (ha : IsUnit a) :
    (alpha ≫ a.asHom) ≫ beta ≠ 0 := by
  obtain ⟨b, hb⟩ := halpha a
  have halpha0 : alpha ≠ 0 := by
    intro hzero
    apply hcomp
    simp [hzero]
  have hbUnit := isUnit_of_cotransit_equation halpha0 ha hb
  letI : IsIso b.asHom := (isUnit_iff_isIso _).1 hbUnit
  intro hzero
  apply hcomp
  have hz : b.asHom ≫ (alpha ≫ beta) = 0 := by
    rw [← Category.assoc, ← hb]
    exact hzero
  apply (cancel_epi b.asHom).1
  simpa using hz

private theorem unit_sandwich_ne_zero_of_allowsTransit_right
    {C : Type*} [Category C] [Preadditive C]
    {X Y Z : C} [IsLocalRing (End Z)] [IsArtinianRing (End Z)]
    {alpha : X ⟶ Y} {beta : Y ⟶ Z}
    (hcomp : alpha ≫ beta ≠ 0)
    (hbeta : LargeIndecomposable.AllowsTransit beta)
    (a : End Y) (ha : IsUnit a) :
    (alpha ≫ a.asHom) ≫ beta ≠ 0 := by
  obtain ⟨b, hb⟩ := hbeta a
  have hbeta0 : beta ≠ 0 := by
    intro hzero
    apply hcomp
    simp [hzero]
  have hbUnit := isUnit_of_transit_equation hbeta0 ha hb
  letI : IsIso b.asHom := (isUnit_iff_isIso _).1 hbUnit
  intro hzero
  apply hcomp
  have hz : (alpha ≫ beta) ≫ b.asHom = 0 := by
    calc
      (alpha ≫ beta) ≫ b.asHom =
          alpha ≫ (a.asHom ≫ beta) := by rw [hb]; simp only [Category.assoc]
      _ = (alpha ≫ a.asHom) ≫ beta := (Category.assoc _ _ _).symm
      _ = 0 := hzero
  apply (cancel_mono b.asHom).1
  simpa using hz

/-- A first radical coefficient vanishes on a return cycle through an
object through which the chosen radical parameter does not factor. -/
private theorem radicalCoefficient_return_eq_zero_of_not_factorsThrough
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {X Y : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X)
    (residue : End X →ₐ[k] k)
    (middle : RadicalCoefficientData residue P.tau)
    (hresidue : ∀ a : End X,
      residue a = 0 ↔ a ∈ Ring.jacobson (End X))
    (hnot : ¬ ∃ (l : X ⟶ Y) (r : Y ⟶ X),
      P.tau.asHom = l ≫ r)
    (l : X ⟶ Y) (r : Y ⟶ X)
    (hreturn : residue (End.of (l ≫ r)) = 0) :
    middle.coefficientOne (End.of (l ≫ r)) = 0 := by
  let a : End X := End.of (l ≫ r)
  have haJ : a ∈ Ring.jacobson (End X) :=
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
        (End X) q).2 hqNotUnit))
  letI : IsIso q.asHom := (isUnit_iff_isIso q).1 hqUnit
  apply hnot
  refine ⟨l, r ≫ inv q.asHom, ?_⟩
  calc
    P.tau.asHom = P.tau.asHom ≫ (q.asHom ≫ inv q.asHom) := by
      rw [IsIso.hom_inv_id, Category.comp_id]
    _ = (P.tau.asHom ≫ q.asHom) ≫ inv q.asHom :=
      (Category.assoc _ _ _).symm
    _ = a.asHom ≫ inv q.asHom := by rw [← hq]
    _ = l ≫ (r ≫ inv q.asHom) := by
      simp only [a, Category.assoc]

/-- The left-arm supplement coefficient restricts along its outer arrow to
the chosen first radical coefficient. -/
private theorem leftArmSupplement_coefficient_eq_radicalCoefficient
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {X Y : C} [Module.Finite k (End Y)]
    [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    (alpha : X ⟶ Y)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalCoefficientData residue P.tau)
    (hresidue : ∀ a : End Y,
      residue a = 0 ↔ a ∈ Ring.jacobson (End Y))
    (supplement : SupplementCoefficientData
      (LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) alpha P.tau)
      (alpha ≫ P.tau.asHom))
    (a : End Y) :
    supplement.coefficient (alpha ≫ a.asHom) =
      middle.coefficientOne a := by
  let c : k := residue a
  let n : End Y := a - algebraMap k (End Y) c
  have hnres : residue n = 0 := by
    dsimp only [n]
    rw [map_sub, AlgHom.commutes]
    change residue a - c = 0
    dsimp only [c]
    exact sub_self _
  have hnJ : n ∈ Ring.jacobson (End Y) := (hresidue n).1 hnres
  obtain ⟨q, hq⟩ := P.transitData.generates n hnJ
  have hnRing : n = q * P.tau := by
    apply End.ext
    simpa only [End.mul_def] using hq
  have haRing : a = algebraMap k (End Y) c + n := by
    dsimp only [n, c]
    abel
  have halphaMem : alpha ∈
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) alpha P.tau := by
    apply (show LargeIndecomposable.RoiterFigure13E.leftOuterActionSubmodule
        (k := k) alpha ≤
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) alpha P.tau from le_sup_right)
    exact ⟨1, by
      simp [preEndomorphismLinearMap]⟩
  have halphaZero : supplement.coefficient alpha = 0 :=
    supplement.coefficient_eq_zero_of_mem halphaMem
  have hlandingRight : supplement.coefficient
      ((alpha ≫ P.tau.asHom) ≫ q.asHom) = residue q :=
    supplement.coefficient_comp_right le_sup_left residue hresidue q
  rw [haRing]
  change supplement.coefficient
      (alpha ≫ ((algebraMap k (End Y) c + n).asHom)) = _
  have hscalarHom : (algebraMap k (End Y) c).asHom = c • (𝟙 Y) := by
    change (c • (1 : End Y)).asHom = c • (𝟙 Y)
    rfl
  have hsumHom : (algebraMap k (End Y) c + n).asHom =
      c • (𝟙 Y) + n.asHom := by
    change (algebraMap k (End Y) c).asHom + n.asHom = _
    rw [hscalarHom]
  rw [hsumHom,
    Preadditive.comp_add, Linear.comp_smul, Category.comp_id,
    supplement.coefficient.map_add, supplement.coefficient.map_smul,
    halphaZero, smul_zero, zero_add]
  rw [hq, ← Category.assoc, hlandingRight]
  rw [middle.coefficientOne.map_add]
  have hscalar : middle.coefficientOne (algebraMap k (End Y) c) = 0 := by
    rw [show algebraMap k (End Y) c = c • (1 : End Y) by
      symm
      rw [Algebra.smul_def, mul_one],
      middle.coefficientOne.map_smul,
      middle.coefficientOne_one, smul_zero]
  rw [hscalar, zero_add, hnRing, middle.coefficientOne_mul_tau]

/-- Source-dually, the right-arm supplement coefficient restricts along
its outer arrow to the chosen first radical coefficient. -/
private theorem rightArmSupplement_coefficient_eq_radicalCoefficient
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {Y Z : C} [Module.Finite k (End Y)]
    [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    (beta : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalCoefficientData residue P.tau)
    (hresidue : ∀ a : End Y,
      residue a = 0 ↔ a ∈ Ring.jacobson (End Y))
    (supplement : SupplementCoefficientData
      (LargeIndecomposable.RoiterFigure13E.rightArmSupplementObstruction
        (k := k) beta P.tau)
      (P.tau.asHom ≫ beta))
    (a : End Y) :
    supplement.coefficient (a.asHom ≫ beta) =
      middle.coefficientOne a := by
  let c : k := residue a
  let n : End Y := a - algebraMap k (End Y) c
  have hnres : residue n = 0 := by
    dsimp only [n]
    rw [map_sub, AlgHom.commutes]
    change residue a - c = 0
    dsimp only [c]
    exact sub_self _
  have hnJ : n ∈ Ring.jacobson (End Y) := (hresidue n).1 hnres
  obtain ⟨q, hq⟩ := P.transitData.generates n hnJ
  have hnRing : n = q * P.tau := by
    apply End.ext
    simpa only [End.mul_def] using hq
  have haRing : a = algebraMap k (End Y) c + n := by
    dsimp only [n, c]
    abel
  have hbetaMem : beta ∈
      LargeIndecomposable.RoiterFigure13E.rightArmSupplementObstruction
        (k := k) beta P.tau := by
    apply (show LargeIndecomposable.RoiterFigure13E.rightOuterActionSubmodule
        (k := k) beta ≤
      LargeIndecomposable.RoiterFigure13E.rightArmSupplementObstruction
        (k := k) beta P.tau from le_sup_right)
    exact ⟨1, by
      simp [postEndomorphismLinearMap]⟩
  have hbetaZero : supplement.coefficient beta = 0 :=
    supplement.coefficient_eq_zero_of_mem hbetaMem
  have hcomm : P.tau.asHom ≫ q.asHom =
      q.asHom ≫ P.tau.asHom := by
    have h := congrArg End.asHom (P.mul_comm P.tau q)
    simpa only [End.mul_def] using h.symm
  have hlandingLeft : supplement.coefficient
      (q.asHom ≫ (P.tau.asHom ≫ beta)) = residue q :=
    supplement.coefficient_comp_left le_sup_left residue hresidue q
  rw [haRing]
  change supplement.coefficient
      (((algebraMap k (End Y) c + n).asHom) ≫ beta) = _
  have hscalarHom : (algebraMap k (End Y) c).asHom = c • (𝟙 Y) := by
    change (c • (1 : End Y)).asHom = c • (𝟙 Y)
    rfl
  have hsumHom : (algebraMap k (End Y) c + n).asHom =
      c • (𝟙 Y) + n.asHom := by
    change (algebraMap k (End Y) c).asHom + n.asHom = _
    rw [hscalarHom]
  rw [hsumHom,
    Preadditive.add_comp, Linear.smul_comp, Category.id_comp,
    supplement.coefficient.map_add, supplement.coefficient.map_smul,
    hbetaZero, smul_zero, zero_add]
  rw [hq, hcomm, Category.assoc, hlandingLeft]
  rw [middle.coefficientOne.map_add]
  have hscalar : middle.coefficientOne (algebraMap k (End Y) c) = 0 := by
    rw [show algebraMap k (End Y) c = c • (1 : End Y) by
      symm
      rw [Algebra.smul_def, mul_one],
      middle.coefficientOne.map_smul,
      middle.coefficientOne_one, smul_zero]
  rw [hscalar, zero_add, hnRing, middle.coefficientOne_mul_tau]

/-- The split-basic presentation of the exact selected Figure-15 quotient. -/
abbrev quotientSplitBasic
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :=
  (selectedSplitBasic S spine).quotient_of_le_jacobson
    (relationIdeal S D Q) (relationIdeal_le_jacobson S D Q)

omit [IsAlgClosed k] in
/-- A quotient by the radical Figure-15 ideal preserves distinct selected
primitive-projective objects. -/
theorem quotientFunctor_obj_ne_of_ne
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    {X Y : (selectedSplitBasic S spine).ProjectiveCategory}
    (hXY : X ≠ Y) :
    (quotientFunctor S D Q).obj X ≠
      (quotientFunctor S D Q).obj Y := by
  intro h
  apply hXY
  apply (selectedSplitBasic S spine).projectiveVertex_injective
  have hv := congrArg
    (quotientSplitBasic S D Q).projectiveVertex h
  simpa only
      [SplitBasicIdempotents.projectiveQuotientFunctor_obj_projectiveVertex]
    using hv

/-- The two inner Figure-15 quotient objects remain distinct. -/
theorem quotientRightInner_ne_leftInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).obj (selectedRightInnerObj S spine) ≠
      (quotientFunctor S D Q).obj (selectedLeftInnerObj S spine) :=
  quotientFunctor_obj_ne_of_ne S D Q
    (factorBranch_selectedRightInner_ne_leftInner S hfinite spine)

/-- The left-inner and initial Figure-15 quotient objects remain distinct. -/
theorem quotientLeftInner_ne_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).obj (selectedLeftInnerObj S spine) ≠
      (quotientFunctor S D Q).obj (selectedInitialObj S spine) :=
  quotientFunctor_obj_ne_of_ne S D Q
    (factorBranch_selectedLeftInner_ne_initial S hfinite spine)

/-- The terminal and right-inner Figure-15 quotient objects remain distinct. -/
theorem quotientTerminal_ne_rightInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientFunctor S D Q).obj (selectedTerminalObj S spine) ≠
      (quotientFunctor S D Q).obj (selectedRightInnerObj S spine) :=
  quotientFunctor_obj_ne_of_ne S D Q
    (factorBranch_selectedTerminal_ne_rightInner S hfinite spine)

set_option maxHeartbeats 800000 in
/-- The surviving left Figure-15 cycle cannot acquire a factorization through
the initial object in the exact selected quotient. -/
theorem quotientLeftTau_not_factorsThrough_initial
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
          F.obj (selectedInitialObj S spine))
        (r : F.obj (selectedInitialObj S spine) ⟶
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
      twoSidedEndomorphismSpan k (selectedLeftTau S spine P) := by
    intro g hg
    have hgVal : g.1 ∈ Ring.jacobson (selectedCorner S spine) :=
      relationIdeal_le_jacobson S D Q hg
    have hgEnd : End.of g ∈
        Ring.jacobson (End (selectedLeftInnerObj S spine)) :=
      ((selectedSplitBasic S spine).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (selectedLeftInnerObj S spine) (End.of g)).2 hgVal
    change End.of g ∈ twoSidedEndomorphismSpan k
      (End.of (selectedLeftTau S spine P))
    rw [factorBranch_selectedLeftTau_span_eq_jacobson S spine P]
    exact hgEnd
  obtain ⟨l, r, hlr⟩ :=
    factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
      T I (relationIdeal_le_jacobson S D Q)
      (selectedLeftTau S spine P) hIcorner
      (quotientFunctor_map_selectedLeftTau_ne_zero
        S hfinite D P Q) lbar rbar hbar
  exact factorBranch_selectedLeftTau_not_factorsThrough_initial
    S hfinite spine P ⟨l, r, hlr⟩

set_option maxHeartbeats 800000 in
/-- The surviving right Figure-15 cycle cannot acquire a factorization
through the terminal object in the exact selected quotient. -/
theorem quotientRightTau_not_factorsThrough_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    ¬ ∃ (l : F.obj (selectedRightInnerObj S spine) ⟶
          F.obj (selectedTerminalObj S spine))
        (r : F.obj (selectedTerminalObj S spine) ⟶
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
      twoSidedEndomorphismSpan k (selectedRightTau S spine Q) := by
    intro g hg
    have hgVal : g.1 ∈ Ring.jacobson (selectedCorner S spine) :=
      relationIdeal_le_jacobson S D Q hg
    have hgEnd : End.of g ∈
        Ring.jacobson (End (selectedRightInnerObj S spine)) :=
      ((selectedSplitBasic S spine).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (selectedRightInnerObj S spine) (End.of g)).2 hgVal
    change End.of g ∈ twoSidedEndomorphismSpan k
      (End.of (selectedRightTau S spine Q))
    rw [selectedRightTau_span_eq_jacobson S spine Q]
    exact hgEnd
  obtain ⟨l, r, hlr⟩ :=
    factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
      T I (relationIdeal_le_jacobson S D Q)
      (selectedRightTau S spine Q) hIcorner
      (quotientFunctor_map_selectedRightTau_ne_zero
        S hfinite D Q) lbar rbar hbar
  exact factorBranch_selectedRightTau_not_factorsThrough_terminal
    S hfinite spine Q ⟨l, r, hlr⟩

/-- The exact quotient diagram written on its four repeated ambient objects. -/
def quotientRepeatedDiagram
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    LargeIndecomposable.CriticalSingularFigure15.DiagramData
      (C := (quotientSplitBasic S D Q).ProjectiveCategory) :=
  let F := quotientFunctor S D Q
  repeatedObjectDiagram
    (F.map (selectedZeroLast S D))
    (F.map (selectedZeroMiddle S D))
    (F.map (selectedZeroFirst S D))
    (End.of (F.map (selectedLeftTau S spine P)))
    (End.of (F.map (selectedRightTau S spine Q)))
    (by
      rw [← F.map_comp, ← F.map_comp,
        selectedZeroLast_middle_first_eq_zero S D, F.map_zero])

/-- The canonical split-basic residue at each of the eight source
occurrences in the exact quotient diagram.  Repeated occurrences are handled
directly, so no equality transport enters the endpoint table. -/
def quotientVertexResidue
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (a : LargeIndecomposable.CriticalSingularFigure15.Vertex) :
    End (((localQuotientCandidate S D P Q).quotientDiagram).object a) →ₐ[k] k := by
  cases a <;>
    exact (quotientSplitBasic S D Q).projectiveEndResidue _

omit [IsAlgClosed k] in
@[simp] theorem quotientVertexResidue_identity
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (a : LargeIndecomposable.CriticalSingularFigure15.Vertex) :
    quotientVertexResidue S D P Q a
      (1 : End (((localQuotientCandidate S D P Q).quotientDiagram).object a)) = 1 := by
  exact map_one (quotientVertexResidue S D P Q a)

omit [IsAlgClosed k] in
/-- The surviving left cycle generates the left-inner endomorphism radical
after passage to the exact Figure-15 quotient. -/
theorem quotientLeftTau_span_eq_jacobson
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    twoSidedEndomorphismSpan k
        (End.of (F.map (selectedLeftTau S spine P))) =
      (Ring.jacobson
        (End (F.obj (selectedLeftInnerObj S spine)))).restrictScalars k := by
  dsimp only
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  simpa only using
    (selectedSplitBasic S spine).projectiveQuotientFunctor_end_span_eq_jacobson
      (relationIdeal S D Q) (relationIdeal_le_jacobson S D Q)
      (selectedLeftInnerObj S spine)
      (End.of (selectedLeftTau S spine P))
      (factorBranch_selectedLeftTau_span_eq_jacobson S spine P)

/-- The surviving left Figure-15 cycle, with its inherited transit
orientation, is an oriented radical-power parameter in the quotient. -/
def quotientLeftPowerParameter
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    OrientedRadicalPowerParameter (k := k)
      ((quotientFunctor S D Q).obj (selectedLeftInnerObj S spine)) := by
  let F := quotientFunctor S D Q
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  let tauBar : End (F.obj (selectedLeftInnerObj S spine)) :=
    End.of (F.map (selectedLeftTau S spine P))
  have hspan : twoSidedEndomorphismSpan k tauBar =
      (Ring.jacobson
        (End (F.obj (selectedLeftInnerObj S spine)))).restrictScalars k :=
    quotientLeftTau_span_eq_jacobson S D P Q
  have htauJ : tauBar ∈
      Ring.jacobson (End (F.obj (selectedLeftInnerObj S spine))) := by
    have hmem := LargeIndecomposable.mem_twoSidedEndomorphismSpan k tauBar
    rw [hspan] at hmem
    exact hmem
  have htau0 : tauBar ≠ 0 := by
    have hmap := quotientFunctor_map_selectedLeftTau_ne_zero
      S hfinite D P Q
    intro hzero
    apply hmap
    exact congrArg End.asHom hzero
  have horientSelected :
      LargeIndecomposable.AllowsTransit (selectedLeftTau S spine P) ∨
        LargeIndecomposable.AllowsCotransit
          (selectedLeftTau S spine P) := by
    rcases P.power_factorization with hT | hC
    · exact Or.inl (finsetProjectiveHom_allowsTransit (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine) P.tau.asHom
        hT.allows_transit)
    · exact Or.inr (finsetProjectiveHom_allowsCotransit (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine) P.tau.asHom
        hC.allows_cotransit)
  have horientBar :
      LargeIndecomposable.AllowsTransit
          (F.map (selectedLeftTau S spine P)) ∨
        LargeIndecomposable.AllowsCotransit
          (F.map (selectedLeftTau S spine P)) := by
    rcases horientSelected with hT | hC
    · exact Or.inl
        (LargeIndecomposable.fullLinearFunctor_map_allowsTransit
          (k := k) F (selectedLeftTau S spine P) hT)
    · exact Or.inr
        (LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
          (k := k) F (selectedLeftTau S spine P) hC)
  exact
    LargeIndecomposable.ClosedZigzagTransfer.orientedRadicalPowerParameter_of_span_eq
      tauBar htauJ htau0 hspan horientBar

@[simp] theorem quotientLeftPowerParameter_tau
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientLeftPowerParameter S hfinite D P Q).tau =
      End.of ((quotientFunctor S D Q).map
        (selectedLeftTau S spine P)) := by
  rfl

omit [IsAlgClosed k] in
/-- The surviving right cycle generates the right-inner endomorphism radical
after passage to the exact Figure-15 quotient. -/
theorem quotientRightTau_span_eq_jacobson
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    twoSidedEndomorphismSpan k
        (End.of (F.map (selectedRightTau S spine Q))) =
      (Ring.jacobson
        (End (F.obj (selectedRightInnerObj S spine)))).restrictScalars k := by
  dsimp only
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  simpa only using
    (selectedSplitBasic S spine).projectiveQuotientFunctor_end_span_eq_jacobson
      (relationIdeal S D Q) (relationIdeal_le_jacobson S D Q)
      (selectedRightInnerObj S spine)
      (End.of (selectedRightTau S spine Q))
      (selectedRightTau_span_eq_jacobson S spine Q)

/-- The surviving right Figure-15 cycle, with its inherited transit
orientation, is an oriented radical-power parameter in the quotient. -/
def quotientRightPowerParameter
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    OrientedRadicalPowerParameter (k := k)
      ((quotientFunctor S D Q).obj (selectedRightInnerObj S spine)) := by
  let F := quotientFunctor S D Q
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  let tauBar : End (F.obj (selectedRightInnerObj S spine)) :=
    End.of (F.map (selectedRightTau S spine Q))
  have hspan : twoSidedEndomorphismSpan k tauBar =
      (Ring.jacobson
        (End (F.obj (selectedRightInnerObj S spine)))).restrictScalars k :=
    quotientRightTau_span_eq_jacobson S D Q
  have htauJ : tauBar ∈
      Ring.jacobson (End (F.obj (selectedRightInnerObj S spine))) := by
    have hmem := LargeIndecomposable.mem_twoSidedEndomorphismSpan k tauBar
    rw [hspan] at hmem
    exact hmem
  have htau0 : tauBar ≠ 0 := by
    have hmap := quotientFunctor_map_selectedRightTau_ne_zero
      S hfinite D Q
    intro hzero
    apply hmap
    exact congrArg End.asHom hzero
  have horientSelected :
      LargeIndecomposable.AllowsTransit (selectedRightTau S spine Q) ∨
        LargeIndecomposable.AllowsCotransit
          (selectedRightTau S spine Q) := by
    rcases Q.power_factorization with hT | hC
    · exact Or.inl (finsetProjectiveHom_allowsTransit (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) Q.tau.asHom
        hT.allows_transit)
    · exact Or.inr (finsetProjectiveHom_allowsCotransit (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) Q.tau.asHom
        hC.allows_cotransit)
  have horientBar :
      LargeIndecomposable.AllowsTransit
          (F.map (selectedRightTau S spine Q)) ∨
        LargeIndecomposable.AllowsCotransit
          (F.map (selectedRightTau S spine Q)) := by
    rcases horientSelected with hT | hC
    · exact Or.inl
        (LargeIndecomposable.fullLinearFunctor_map_allowsTransit
          (k := k) F (selectedRightTau S spine Q) hT)
    · exact Or.inr
        (LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
          (k := k) F (selectedRightTau S spine Q) hC)
  exact
    LargeIndecomposable.ClosedZigzagTransfer.orientedRadicalPowerParameter_of_span_eq
      tauBar htauJ htau0 hspan horientBar

@[simp] theorem quotientRightPowerParameter_tau
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (quotientRightPowerParameter S hfinite D Q).tau =
      End.of ((quotientFunctor S D Q).map
        (selectedRightTau S spine Q)) := by
  rfl

/-- The left quotient cycle admits the normalized first-order coefficient
used on the `rho` occurrence of Figure 15. -/
theorem nonempty_quotientLeftRadicalCoefficientData
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
    let T := quotientSplitBasic S D Q
    let Pbar := quotientLeftPowerParameter S hfinite D P Q
    Nonempty (RadicalCoefficientData
      (T.projectiveEndResidue (F.obj (selectedLeftInnerObj S spine)))
      Pbar.tau) := by
  dsimp only
  let F := quotientFunctor S D Q
  let T := quotientSplitBasic S D Q
  let Pbar := quotientLeftPowerParameter S hfinite D P Q
  let Xbar := F.obj (selectedLeftInnerObj S spine)
  let residue := T.projectiveEndResidue Xbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  have hresTau : residue Pbar.tau = 0 := by
    dsimp only [residue]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    exact Pbar.mem_jacobson
  exact exists_radicalCoefficientData residue Pbar.tau Pbar.ne_zero
    hresTau (fun a ↦ T.projectiveEnd_isUnit_iff_residue_ne_zero Xbar a)

/-- The right quotient cycle admits the normalized first-order coefficient
used on the `sigma` occurrence of Figure 15. -/
theorem nonempty_quotientRightRadicalCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    let T := quotientSplitBasic S D Q
    let Qbar := quotientRightPowerParameter S hfinite D Q
    Nonempty (RadicalCoefficientData
      (T.projectiveEndResidue (F.obj (selectedRightInnerObj S spine)))
      Qbar.tau) := by
  dsimp only
  let F := quotientFunctor S D Q
  let T := quotientSplitBasic S D Q
  let Qbar := quotientRightPowerParameter S hfinite D Q
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let residue := T.projectiveEndResidue Xbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  have hresTau : residue Qbar.tau = 0 := by
    dsimp only [residue]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    exact Qbar.mem_jacobson
  exact exists_radicalCoefficientData residue Qbar.tau Qbar.ne_zero
    hresTau (fun a ↦ T.projectiveEnd_isUnit_iff_residue_ne_zero Xbar a)

/-- The chosen first zero representative remains a full Hom generator in the
exact quotient. -/
theorem quotientZeroFirst_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    twoSidedEndomorphismSpan k
      ((quotientFunctor S D Q).map (selectedZeroFirst S D)) = ⊤ := by
  have hambient : twoSidedEndomorphismSpan k (zeroFirst S D) = ⊤ := by
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k (zeroFirst_unitRayEquivalent S D)]
    exact (spine.initial_full_outer_spans S hfinite).2
  have hselected : twoSidedEndomorphismSpan k
      (selectedZeroFirst S D) = ⊤ :=
    finsetProjectiveHom_span_eq_top (k := k) S
      (selectedVertices S spine)
      (leftInner_mem_selectedVertices S spine)
      (initial_mem_selectedVertices S spine) (zeroFirst S D) hambient
  exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (quotientFunctor S D Q) (selectedZeroFirst S D) hselected

/-- The chosen middle zero representative remains a full Hom generator in
the exact quotient. -/
theorem quotientZeroMiddle_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    twoSidedEndomorphismSpan k
      ((quotientFunctor S D Q).map (selectedZeroMiddle S D)) = ⊤ := by
  have hambient : twoSidedEndomorphismSpan k (zeroMiddle S D) = ⊤ := by
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k (zeroMiddle_unitRayEquivalent S D)]
    exact spine.middle_full_span S hfinite
  have hselected : twoSidedEndomorphismSpan k
      (selectedZeroMiddle S D) = ⊤ :=
    finsetProjectiveHom_span_eq_top (k := k) S
      (selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine)
      (leftInner_mem_selectedVertices S spine) (zeroMiddle S D) hambient
  exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (quotientFunctor S D Q) (selectedZeroMiddle S D) hselected

/-- The chosen last zero representative remains a full Hom generator in the
exact quotient. -/
theorem quotientZeroLast_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    twoSidedEndomorphismSpan k
      ((quotientFunctor S D Q).map (selectedZeroLast S D)) = ⊤ := by
  have hambient : twoSidedEndomorphismSpan k (zeroLast S D) = ⊤ := by
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k (zeroLast_unitRayEquivalent S D)]
    exact (spine.terminal_full_outer_spans S hfinite).1
  have hselected : twoSidedEndomorphismSpan k
      (selectedZeroLast S D) = ⊤ :=
    finsetProjectiveHom_span_eq_top (k := k) S
      (selectedVertices S spine)
      (terminal_mem_selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine) (zeroLast S D) hambient
  exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (quotientFunctor S D Q) (selectedZeroLast S D) hselected

omit [IsAlgClosed k] in
/-- The first zero representative retains cotransit in the exact quotient. -/
theorem quotientZeroFirst_allowsCotransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    LargeIndecomposable.AllowsCotransit
      ((quotientFunctor S D Q).map (selectedZeroFirst S D)) := by
  have hfixed : LargeIndecomposable.AllowsCotransit
      (spine.lift.representative spine.first) := by
    rcases LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (spine.lift.representative spine.first) with h | h
    · exact False.elim ((spine.first_not_allowsTransit S) h)
    · exact h
  have hambient : LargeIndecomposable.AllowsCotransit (zeroFirst S D) :=
    hfixed.of_unitRayEquivalent (zeroFirst_unitRayEquivalent S D)
  have hselected : LargeIndecomposable.AllowsCotransit
      (selectedZeroFirst S D) :=
    finsetProjectiveHom_allowsCotransit (k := k) S
      (selectedVertices S spine)
      (leftInner_mem_selectedVertices S spine)
      (initial_mem_selectedVertices S spine) (zeroFirst S D) hambient
  exact LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
    (k := k) (quotientFunctor S D Q) (selectedZeroFirst S D) hselected

/-- The middle zero representative retains both transit directions in the
exact quotient. -/
theorem quotientZeroMiddle_allowsBitransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    LargeIndecomposable.AllowsTransit
        ((quotientFunctor S D Q).map (selectedZeroMiddle S D)) ∧
      LargeIndecomposable.AllowsCotransit
        ((quotientFunctor S D Q).map (selectedZeroMiddle S D)) := by
  have hmiddle := spine.middle_allowsBitransit S hfinite
  have hambientT := hmiddle.1.of_unitRayEquivalent
    (zeroMiddle_unitRayEquivalent S D)
  have hambientC := hmiddle.2.of_unitRayEquivalent
    (zeroMiddle_unitRayEquivalent S D)
  have hselectedT := finsetProjectiveHom_allowsTransit (k := k) S
    (selectedVertices S spine)
    (rightInner_mem_selectedVertices S spine)
    (leftInner_mem_selectedVertices S spine) (zeroMiddle S D) hambientT
  have hselectedC := finsetProjectiveHom_allowsCotransit (k := k) S
    (selectedVertices S spine)
    (rightInner_mem_selectedVertices S spine)
    (leftInner_mem_selectedVertices S spine) (zeroMiddle S D) hambientC
  exact
    ⟨LargeIndecomposable.fullLinearFunctor_map_allowsTransit
        (k := k) (quotientFunctor S D Q) (selectedZeroMiddle S D) hselectedT,
      LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
        (k := k) (quotientFunctor S D Q) (selectedZeroMiddle S D) hselectedC⟩

omit [IsAlgClosed k] in
/-- The last zero representative retains transit in the exact quotient. -/
theorem quotientZeroLast_allowsTransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    LargeIndecomposable.AllowsTransit
      ((quotientFunctor S D Q).map (selectedZeroLast S D)) := by
  have hfixed : LargeIndecomposable.AllowsTransit
      (spine.lift.representative spine.last) := by
    rcases LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (spine.lift.representative spine.last) with h | h
    · exact h
    · exact False.elim ((spine.last_not_allowsCotransit S) h)
  have hambient : LargeIndecomposable.AllowsTransit (zeroLast S D) :=
    hfixed.of_unitRayEquivalent (zeroLast_unitRayEquivalent S D)
  have hselected : LargeIndecomposable.AllowsTransit
      (selectedZeroLast S D) :=
    finsetProjectiveHom_allowsTransit (k := k) S
      (selectedVertices S spine)
      (terminal_mem_selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine) (zeroLast S D) hambient
  exact LargeIndecomposable.fullLinearFunctor_map_allowsTransit
    (k := k) (quotientFunctor S D Q) (selectedZeroLast S D) hselected

/-- No invertible twist at the left-inner quotient object can kill the
surviving middle--first arm. -/
theorem quotientInitial_unit_sandwich_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (a : End ((quotientFunctor S D Q).obj
      (selectedLeftInnerObj S spine))) (ha : IsUnit a) :
    ((quotientFunctor S D Q).map (selectedZeroMiddle S D) ≫ a.asHom) ≫
        (quotientFunctor S D Q).map (selectedZeroFirst S D) ≠ 0 := by
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  exact unit_sandwich_ne_zero_of_allowsCotransit_left
    (quotientFunctor_map_selectedZeroMiddle_first_ne_zero
      S hfinite D Q)
    (quotientZeroMiddle_allowsBitransit S hfinite D Q).2 a ha

/-- No invertible twist at the right-inner quotient object can kill the
surviving last--middle arm. -/
theorem quotientTerminal_unit_sandwich_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (a : End ((quotientFunctor S D Q).obj
      (selectedRightInnerObj S spine))) (ha : IsUnit a) :
    ((quotientFunctor S D Q).map (selectedZeroLast S D) ≫ a.asHom) ≫
        (quotientFunctor S D Q).map (selectedZeroMiddle S D) ≠ 0 := by
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  exact unit_sandwich_ne_zero_of_allowsTransit_right
    (quotientFunctor_map_selectedZeroLast_middle_ne_zero
      S hfinite D Q)
    (quotientZeroMiddle_allowsBitransit S hfinite D Q).1 a ha

/-- The directed middle--first arm carries coherent arrow and length-two
coefficients in the exact quotient. -/
theorem nonempty_quotientInitialArmCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    let T := quotientSplitBasic S D Q
    Nonempty (Figure14ArmCoefficientData
      (F.map (selectedZeroMiddle S D))
      (F.map (selectedZeroFirst S D))
      (T.projectiveEndResidue (F.obj (selectedRightInnerObj S spine)))
      (T.projectiveEndResidue (F.obj (selectedLeftInnerObj S spine)))
      (T.projectiveEndResidue (F.obj (selectedInitialObj S spine)))) := by
  dsimp only
  let F := quotientFunctor S D Q
  let T := quotientSplitBasic S D Q
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  let Zbar := F.obj (selectedInitialObj S spine)
  let delta := F.map (selectedZeroMiddle S D)
  let first := F.map (selectedZeroFirst S D)
  let residueX := T.projectiveEndResidue Xbar
  let residueY := T.projectiveEndResidue Ybar
  let residueZ := T.projectiveEndResidue Zbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  have hresidueX (a : End Xbar) :
      residueX a = 0 ↔ a ∈ Ring.jacobson (End Xbar) := by
    dsimp only [residueX]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueY (a : End Ybar) :
      residueY a = 0 ↔ a ∈ Ring.jacobson (End Ybar) := by
    dsimp only [residueY]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueZ (a : End Zbar) :
      residueZ a = 0 ↔ a ∈ Ring.jacobson (End Zbar) := by
    dsimp only [residueZ]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  exact exists_figure14ArmCoefficientData delta first
    residueX residueY residueZ hresidueX hresidueY hresidueZ
    (quotientZeroMiddle_span_eq_top S hfinite D Q)
    (quotientZeroFirst_span_eq_top S hfinite D Q)
    (quotientZeroMiddle_allowsBitransit S hfinite D Q).1
    (quotientZeroFirst_allowsCotransit S D Q)
    (quotientInitial_unit_sandwich_ne_zero S hfinite D Q)

/-- The directed last--middle arm carries coherent arrow and length-two
coefficients in the exact quotient. -/
theorem nonempty_quotientTerminalArmCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    let T := quotientSplitBasic S D Q
    Nonempty (Figure14ArmCoefficientData
      (F.map (selectedZeroLast S D))
      (F.map (selectedZeroMiddle S D))
      (T.projectiveEndResidue (F.obj (selectedTerminalObj S spine)))
      (T.projectiveEndResidue (F.obj (selectedRightInnerObj S spine)))
      (T.projectiveEndResidue (F.obj (selectedLeftInnerObj S spine)))) := by
  dsimp only
  let F := quotientFunctor S D Q
  let T := quotientSplitBasic S D Q
  let Xbar := F.obj (selectedTerminalObj S spine)
  let Ybar := F.obj (selectedRightInnerObj S spine)
  let Zbar := F.obj (selectedLeftInnerObj S spine)
  let last := F.map (selectedZeroLast S D)
  let delta := F.map (selectedZeroMiddle S D)
  let residueX := T.projectiveEndResidue Xbar
  let residueY := T.projectiveEndResidue Ybar
  let residueZ := T.projectiveEndResidue Zbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  have hresidueX (a : End Xbar) :
      residueX a = 0 ↔ a ∈ Ring.jacobson (End Xbar) := by
    dsimp only [residueX]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueY (a : End Ybar) :
      residueY a = 0 ↔ a ∈ Ring.jacobson (End Ybar) := by
    dsimp only [residueY]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueZ (a : End Zbar) :
      residueZ a = 0 ↔ a ∈ Ring.jacobson (End Zbar) := by
    dsimp only [residueZ]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  exact exists_figure14ArmCoefficientData last delta
    residueX residueY residueZ hresidueX hresidueY hresidueZ
    (quotientZeroLast_span_eq_top S hfinite D Q)
    (quotientZeroMiddle_span_eq_top S hfinite D Q)
    (quotientZeroLast_allowsTransit S D Q)
    (quotientZeroMiddle_allowsBitransit S hfinite D Q).2
    (quotientTerminal_unit_sandwich_ne_zero S hfinite D Q)

/-- The upper `rho`--first side composite is separated from its complete
right-arm obstruction in the exact quotient. -/
theorem quotientUpperSupplement_separated
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
    let Pbar := quotientLeftPowerParameter S hfinite D P Q
    Pbar.tau.asHom ≫ F.map (selectedZeroFirst S D) ∉
      LargeIndecomposable.RoiterFigure13E.rightArmSupplementObstruction
        (k := k) (F.map (selectedZeroFirst S D)) Pbar.tau := by
  dsimp only
  let F := quotientFunctor S D Q
  let Pbar := quotientLeftPowerParameter S hfinite D P Q
  let first := F.map (selectedZeroFirst S D)
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  letI : ∀ U : (quotientSplitBasic S D Q).ProjectiveCategory,
      Module.Finite k (End U) := fun U ↦ by
    change Module.Finite k (U ⟶ U)
    infer_instance
  have hPtau : Pbar.tau.asHom =
      F.map (selectedLeftTau S spine P) := by
    exact congrArg End.asHom
      (quotientLeftPowerParameter_tau S hfinite D P Q)
  have hfirstNotT : ¬ LargeIndecomposable.AllowsTransit first := by
    intro hfirstT
    obtain ⟨b, hb⟩ := hfirstT Pbar.tau
    apply quotientLeftTau_zeroFirst_ne_zeroFirst_comp
      S hfinite D P Q b
    rw [← hPtau]
    exact hb
  have hnonzero : Pbar.tau.asHom ≫ first ≠ 0 := by
    intro hzero
    apply quotientLeftTau_zeroFirst_ne_zeroFirst_comp
      S hfinite D P Q (0 : End (F.obj (selectedInitialObj S spine)))
    rw [← hPtau]
    have hzeroEnd : (0 : End (F.obj
        (selectedInitialObj S spine))).asHom = 0 := rfl
    rw [hzeroEnd, Limits.comp_zero]
    exact hzero
  exact
    LargeIndecomposable.RoiterFigure13E.rightArmSupplement_separated_of_not_allowsTransit
      first Pbar (quotientZeroFirst_allowsCotransit S D Q)
      hfirstNotT hnonzero

/-- The lower last--`sigma` side composite is separated from its complete
left-arm obstruction in the exact quotient. -/
theorem quotientLowerSupplement_separated
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    let Qbar := quotientRightPowerParameter S hfinite D Q
    F.map (selectedZeroLast S D) ≫ Qbar.tau.asHom ∉
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) (F.map (selectedZeroLast S D)) Qbar.tau := by
  dsimp only
  let F := quotientFunctor S D Q
  let Qbar := quotientRightPowerParameter S hfinite D Q
  let last := F.map (selectedZeroLast S D)
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  letI : ∀ U : (quotientSplitBasic S D Q).ProjectiveCategory,
      Module.Finite k (End U) := fun U ↦ by
    change Module.Finite k (U ⟶ U)
    infer_instance
  have hQtau : Qbar.tau.asHom =
      F.map (selectedRightTau S spine Q) := by
    exact congrArg End.asHom
      (quotientRightPowerParameter_tau S hfinite D Q)
  have hlastNotC : ¬ LargeIndecomposable.AllowsCotransit last := by
    intro hlastC
    obtain ⟨a, ha⟩ := hlastC Qbar.tau
    apply quotientZeroLast_rightTau_ne_comp_zeroLast
      S hfinite D Q a
    rw [← hQtau]
    exact ha
  have hnonzero : last ≫ Qbar.tau.asHom ≠ 0 := by
    intro hzero
    apply quotientZeroLast_rightTau_ne_comp_zeroLast
      S hfinite D Q (0 : End (F.obj (selectedTerminalObj S spine)))
    rw [← hQtau]
    have hzeroEnd : (0 : End (F.obj
        (selectedTerminalObj S spine))).asHom = 0 := rfl
    rw [hzeroEnd, Limits.zero_comp]
    exact hzero
  exact
    LargeIndecomposable.RoiterFigure13E.leftArmSupplement_separated_of_not_allowsCotransit
      last Qbar (quotientZeroLast_allowsTransit S D Q)
      hlastNotC hnonzero

/-- A normalized coefficient exists on the surviving upper `rho`--first
side composite and kills its complete supplement obstruction. -/
theorem nonempty_quotientUpperSupplementCoefficientData
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
    let Pbar := quotientLeftPowerParameter S hfinite D P Q
    let first := F.map (selectedZeroFirst S D)
    Nonempty (LargeIndecomposable.CriticalSingularFigure15.SupplementCoefficientData
      (LargeIndecomposable.RoiterFigure13E.rightArmSupplementObstruction
        (k := k) first Pbar.tau)
      (Pbar.tau.asHom ≫ first)) := by
  dsimp only
  exact
    LargeIndecomposable.CriticalSingularFigure15.nonempty_supplementCoefficientData
      _ _ (quotientUpperSupplement_separated S hfinite D P Q)

/-- A normalized coefficient exists on the surviving lower last--`sigma`
side composite and kills its complete supplement obstruction. -/
theorem nonempty_quotientLowerSupplementCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    let F := quotientFunctor S D Q
    let Qbar := quotientRightPowerParameter S hfinite D Q
    let last := F.map (selectedZeroLast S D)
    Nonempty (LargeIndecomposable.CriticalSingularFigure15.SupplementCoefficientData
      (LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) last Qbar.tau)
      (last ≫ Qbar.tau.asHom)) := by
  dsimp only
  exact
    LargeIndecomposable.CriticalSingularFigure15.nonempty_supplementCoefficientData
      _ _ (quotientLowerSupplement_separated S hfinite D Q)

/-- All 19 supported entries of the exact quotient endpoint table have
simultaneous concrete coefficient maps. -/
theorem nonempty_quotientLiteralEndpointTable
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    Nonempty
      (LargeIndecomposable.CriticalSingularFigure15.LiteralEndpointTable
      (k := k) (localQuotientCandidate S D P Q).quotientDiagram) := by
  let G := (localQuotientCandidate S D P Q).quotientDiagram
  obtain ⟨leftRadical⟩ :=
    nonempty_quotientLeftRadicalCoefficientData S hfinite D P Q
  obtain ⟨rightRadical⟩ :=
    nonempty_quotientRightRadicalCoefficientData S hfinite D Q
  obtain ⟨initialArm⟩ :=
    nonempty_quotientInitialArmCoefficientData S hfinite D Q
  obtain ⟨terminalArm⟩ :=
    nonempty_quotientTerminalArmCoefficientData S hfinite D Q
  obtain ⟨upperSupplement⟩ :=
    nonempty_quotientUpperSupplementCoefficientData S hfinite D P Q
  obtain ⟨lowerSupplement⟩ :=
    nonempty_quotientLowerSupplementCoefficientData S hfinite D Q
  refine ⟨{
    residue := quotientVertexResidue S D P Q
    alphaLeftZero := terminalArm.alphaZero
    mainSuffix := terminalArm.crossZero
    lowerComposite := lowerSupplement.coefficient
    deltaZero := initialArm.alphaZero
    mainPrefix := initialArm.crossZero
    sigmaOne := rightRadical.coefficientOne
    alphaRightZero := initialArm.betaZero
    rhoOne := leftRadical.coefficientOne
    upperComposite := upperSupplement.coefficient
    alphaUpperZero := initialArm.betaZero
    alphaLowerZero := terminalArm.alphaZero }⟩

set_option maxHeartbeats 3000000 in
/-- The exact quotient endpoint table satisfies every generator
compatibility equation needed by the bound Figure-15 compiler. -/
theorem nonempty_quotientCompatibleLiteralEndpointTable
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    Nonempty
      (LargeIndecomposable.CriticalSingularFigure15.CompatibleLiteralEndpointTable
      (k := k) (localQuotientCandidate S D P Q).quotientDiagram) := by
  let G := (localQuotientCandidate S D P Q).quotientDiagram
  let F := quotientFunctor S D Q
  let T := quotientSplitBasic S D Q
  let Pbar := quotientLeftPowerParameter S hfinite D P Q
  let Qbar := quotientRightPowerParameter S hfinite D Q
  let Abar := F.obj (selectedTerminalObj S spine)
  let Dbar := F.obj (selectedRightInnerObj S spine)
  let Cbar := F.obj (selectedLeftInnerObj S spine)
  let Bbar := F.obj (selectedInitialObj S spine)
  let last : Abar ⟶ Dbar := F.map (selectedZeroLast S D)
  let middle : Dbar ⟶ Cbar := F.map (selectedZeroMiddle S D)
  let first : Cbar ⟶ Bbar := F.map (selectedZeroFirst S D)
  let residueA := T.projectiveEndResidue Abar
  let residueD := T.projectiveEndResidue Dbar
  let residueC := T.projectiveEndResidue Cbar
  let residueB := T.projectiveEndResidue Bbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸ (relationIdeal S D Q).asIdeal) :=
    Module.Finite.quotient k (relationIdeal S D Q).asIdeal
  letI : ∀ Z : T.ProjectiveCategory, Module.Finite k (End Z) :=
    fun Z ↦ by
      change Module.Finite k (Z ⟶ Z)
      infer_instance
  obtain ⟨leftRadical⟩ :=
    nonempty_quotientLeftRadicalCoefficientData S hfinite D P Q
  obtain ⟨rightRadical⟩ :=
    nonempty_quotientRightRadicalCoefficientData S hfinite D Q
  obtain ⟨initialArm⟩ :=
    nonempty_quotientInitialArmCoefficientData S hfinite D Q
  obtain ⟨terminalArm⟩ :=
    nonempty_quotientTerminalArmCoefficientData S hfinite D Q
  obtain ⟨upperSupplement⟩ :=
    nonempty_quotientUpperSupplementCoefficientData S hfinite D P Q
  obtain ⟨lowerSupplement⟩ :=
    nonempty_quotientLowerSupplementCoefficientData S hfinite D Q
  have hresidueD (a : End Dbar) :
      residueD a = 0 ↔ a ∈ Ring.jacobson (End Dbar) := by
    dsimp only [residueD]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueC (a : End Cbar) :
      residueC a = 0 ↔ a ∈ Ring.jacobson (End Cbar) := by
    dsimp only [residueC]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hAD : Abar ≠ Dbar :=
    quotientTerminal_ne_rightInner S hfinite D Q
  have hDC : Dbar ≠ Cbar :=
    quotientRightInner_ne_leftInner S hfinite D Q
  have hCB : Cbar ≠ Bbar :=
    quotientLeftInner_ne_initial S hfinite D Q
  have hPNotD : ¬ ∃ (l : Cbar ⟶ Dbar) (r : Dbar ⟶ Cbar),
      Pbar.tau.asHom = l ≫ r := by
    change ¬ ∃ (l : Cbar ⟶ Dbar) (r : Dbar ⟶ Cbar),
      F.map (selectedLeftTau S spine P) = l ≫ r
    exact quotientLeftTau_not_factorsThrough_rightInner S hfinite D P Q
  have hPNotB : ¬ ∃ (l : Cbar ⟶ Bbar) (r : Bbar ⟶ Cbar),
      Pbar.tau.asHom = l ≫ r := by
    change ¬ ∃ (l : Cbar ⟶ Bbar) (r : Bbar ⟶ Cbar),
      F.map (selectedLeftTau S spine P) = l ≫ r
    exact quotientLeftTau_not_factorsThrough_initial S hfinite D P Q
  have hQNotC : ¬ ∃ (l : Dbar ⟶ Cbar) (r : Cbar ⟶ Dbar),
      Qbar.tau.asHom = l ≫ r := by
    change ¬ ∃ (l : Dbar ⟶ Cbar) (r : Cbar ⟶ Dbar),
      F.map (selectedRightTau S spine Q) = l ≫ r
    exact quotientRightTau_not_factorsThrough_leftInner S hfinite D Q
  have hQNotA : ¬ ∃ (l : Dbar ⟶ Abar) (r : Abar ⟶ Dbar),
      Qbar.tau.asHom = l ≫ r := by
    change ¬ ∃ (l : Dbar ⟶ Abar) (r : Abar ⟶ Dbar),
      F.map (selectedRightTau S spine Q) = l ≫ r
    exact quotientRightTau_not_factorsThrough_terminal S hfinite D Q
  have hLeftThroughDZero (l : Cbar ⟶ Dbar) (r : Dbar ⟶ Cbar) :
      leftRadical.coefficientOne (End.of (l ≫ r)) = 0 :=
    radicalCoefficient_return_eq_zero_of_not_factorsThrough
      Pbar residueC leftRadical hresidueC hPNotD l r
      (projectiveEndResidue_comp_eq_zero_of_ne T hDC.symm l r)
  have hLeftThroughBZero (l : Cbar ⟶ Bbar) (r : Bbar ⟶ Cbar) :
      leftRadical.coefficientOne (End.of (l ≫ r)) = 0 :=
    radicalCoefficient_return_eq_zero_of_not_factorsThrough
      Pbar residueC leftRadical hresidueC hPNotB l r
      (projectiveEndResidue_comp_eq_zero_of_ne T hCB l r)
  have hRightThroughCZero (l : Dbar ⟶ Cbar) (r : Cbar ⟶ Dbar) :
      rightRadical.coefficientOne (End.of (l ≫ r)) = 0 :=
    radicalCoefficient_return_eq_zero_of_not_factorsThrough
      Qbar residueD rightRadical hresidueD hQNotC l r
      (projectiveEndResidue_comp_eq_zero_of_ne T hDC l r)
  have hRightThroughAZero (l : Dbar ⟶ Abar) (r : Abar ⟶ Dbar) :
      rightRadical.coefficientOne (End.of (l ≫ r)) = 0 :=
    radicalCoefficient_return_eq_zero_of_not_factorsThrough
      Qbar residueD rightRadical hresidueD hQNotA l r
      (projectiveEndResidue_comp_eq_zero_of_ne T hAD.symm l r)
  have hUpperBridge (a : End Cbar) :
      upperSupplement.coefficient (a.asHom ≫ first) =
        leftRadical.coefficientOne a :=
    rightArmSupplement_coefficient_eq_radicalCoefficient
      first Pbar residueC leftRadical hresidueC upperSupplement a
  have hLowerBridge (a : End Dbar) :
      lowerSupplement.coefficient (last ≫ a.asHom) =
        rightRadical.coefficientOne a :=
    leftArmSupplement_coefficient_eq_radicalCoefficient
      last Qbar residueD rightRadical hresidueD lowerSupplement a
  have hMiddlePost (g : Dbar ⟶ Cbar) :
      ∃ a : End Cbar, g = middle ≫ a.asHom := by
    have hg : g ∈ twoSidedEndomorphismSpan k middle := by
      rw [quotientZeroMiddle_span_eq_top S hfinite D Q]
      exact Submodule.mem_top
    exact LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) (quotientZeroMiddle_allowsBitransit S hfinite D Q).1 hg
  have hMiddlePre (g : Dbar ⟶ Cbar) :
      ∃ a : End Dbar, g = a.asHom ≫ middle := by
    have hg : g ∈ twoSidedEndomorphismSpan k middle := by
      rw [quotientZeroMiddle_span_eq_top S hfinite D Q]
      exact Submodule.mem_top
    exact LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      (k := k) (quotientZeroMiddle_allowsBitransit S hfinite D Q).2 hg
  have hFirstPre (g : Cbar ⟶ Bbar) :
      ∃ a : End Cbar, g = a.asHom ≫ first := by
    have hg : g ∈ twoSidedEndomorphismSpan k first := by
      rw [quotientZeroFirst_span_eq_top S hfinite D Q]
      exact Submodule.mem_top
    exact LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      (k := k) (quotientZeroFirst_allowsCotransit S D Q) hg
  have hLastPost (g : Abar ⟶ Dbar) :
      ∃ a : End Dbar, g = last ≫ a.asHom := by
    have hg : g ∈ twoSidedEndomorphismSpan k last := by
      rw [quotientZeroLast_span_eq_top S hfinite D Q]
      exact Submodule.mem_top
    exact LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) (quotientZeroLast_allowsTransit S D Q) hg
  have hprefixAmbient : twoSidedEndomorphismSpan k
      (zeroMiddle S D ≫ zeroFirst S D) = ⊤ := by
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k (zeroMiddle_first_unitRayEquivalent S D)]
    exact (spine.long_outer_composites_full_spans S hfinite).2
  let selectedPrefix := finsetProjectiveHom S (selectedVertices S spine)
    (rightInner_mem_selectedVertices S spine)
    (initial_mem_selectedVertices S spine)
    (zeroMiddle S D ≫ zeroFirst S D)
  have hselectedPrefixEq : selectedPrefix =
      selectedZeroMiddle S D ≫ selectedZeroFirst S D := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp only [selectedPrefix]
    simp only [ProjectiveCategory.comp_val, finsetProjectiveHom_val_val]
    change (zeroFirst S D).1 * (zeroMiddle S D).1 =
      (selectedZeroFirst S D).1.1 * (selectedZeroMiddle S D).1.1
    simp only [finsetProjectiveHom_val_val]
  have hselectedPrefixSpan : twoSidedEndomorphismSpan k
      (selectedZeroMiddle S D ≫ selectedZeroFirst S D) = ⊤ := by
    rw [← hselectedPrefixEq]
    exact finsetProjectiveHom_span_eq_top (k := k) S
      (selectedVertices S spine)
      (rightInner_mem_selectedVertices S spine)
      (initial_mem_selectedVertices S spine)
      (zeroMiddle S D ≫ zeroFirst S D) hprefixAmbient
  have hprefixSpan : twoSidedEndomorphismSpan k
      (middle ≫ first) = ⊤ := by
    change twoSidedEndomorphismSpan k
      (F.map (selectedZeroMiddle S D) ≫
        F.map (selectedZeroFirst S D)) = ⊤
    rw [← F.map_comp]
    exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
      F (selectedZeroMiddle S D ≫ selectedZeroFirst S D)
      hselectedPrefixSpan
  have hprefixCotransit : LargeIndecomposable.AllowsCotransit
      (middle ≫ first) :=
    (quotientZeroMiddle_allowsBitransit S hfinite D Q).2.comp
      (quotientZeroFirst_allowsCotransit S D Q)
  have hPrefixPre (g : Dbar ⟶ Bbar) :
      ∃ a : End Dbar, g = a.asHom ≫ (middle ≫ first) := by
    have hg : g ∈ twoSidedEndomorphismSpan k (middle ≫ first) := by
      rw [hprefixSpan]
      exact Submodule.mem_top
    exact LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      (k := k) hprefixCotransit hg
  have hsuffixAmbient : twoSidedEndomorphismSpan k
      (zeroLast S D ≫ zeroMiddle S D) = ⊤ := by
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k (zeroLast_middle_unitRayEquivalent S D)]
    exact (spine.long_outer_composites_full_spans S hfinite).1
  let selectedSuffix := finsetProjectiveHom S (selectedVertices S spine)
    (terminal_mem_selectedVertices S spine)
    (leftInner_mem_selectedVertices S spine)
    (zeroLast S D ≫ zeroMiddle S D)
  have hselectedSuffixEq : selectedSuffix =
      selectedZeroLast S D ≫ selectedZeroMiddle S D := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp only [selectedSuffix]
    simp only [ProjectiveCategory.comp_val, finsetProjectiveHom_val_val]
    change (zeroMiddle S D).1 * (zeroLast S D).1 =
      (selectedZeroMiddle S D).1.1 * (selectedZeroLast S D).1.1
    simp only [finsetProjectiveHom_val_val]
  have hselectedSuffixSpan : twoSidedEndomorphismSpan k
      (selectedZeroLast S D ≫ selectedZeroMiddle S D) = ⊤ := by
    rw [← hselectedSuffixEq]
    exact finsetProjectiveHom_span_eq_top (k := k) S
      (selectedVertices S spine)
      (terminal_mem_selectedVertices S spine)
      (leftInner_mem_selectedVertices S spine)
      (zeroLast S D ≫ zeroMiddle S D) hsuffixAmbient
  have hsuffixSpan : twoSidedEndomorphismSpan k
      (last ≫ middle) = ⊤ := by
    change twoSidedEndomorphismSpan k
      (F.map (selectedZeroLast S D) ≫
        F.map (selectedZeroMiddle S D)) = ⊤
    rw [← F.map_comp]
    exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
      F (selectedZeroLast S D ≫ selectedZeroMiddle S D)
      hselectedSuffixSpan
  have hsuffixTransit : LargeIndecomposable.AllowsTransit
      (last ≫ middle) :=
    (quotientZeroLast_allowsTransit S D Q).comp
      (quotientZeroMiddle_allowsBitransit S hfinite D Q).1
  have hSuffixPost (g : Abar ⟶ Cbar) :
      ∃ a : End Cbar, g = (last ≫ middle) ≫ a.asHom := by
    have hg : g ∈ twoSidedEndomorphismSpan k (last ≫ middle) := by
      rw [hsuffixSpan]
      exact Submodule.mem_top
    exact LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hsuffixTransit hg
  have hrelation : Qbar.tau.asHom ≫ middle = 0 := by
    change F.map (selectedRightTau S spine Q) ≫
      F.map (selectedZeroMiddle S D) = 0
    simpa only [← F.map_comp] using
      quotientFunctor_map_rightTau_middle_eq_zero S D Q
  have hresiduePtau : residueC Pbar.tau = 0 :=
    (hresidueC Pbar.tau).2 Pbar.mem_jacobson
  have hresidueQtau : residueD Qbar.tau = 0 :=
    (hresidueD Qbar.tau).2 Qbar.mem_jacobson
  have hUpperOuterZero (a : End Bbar) :
      upperSupplement.coefficient (first ≫ a.asHom) = 0 := by
    apply upperSupplement.coefficient_eq_zero_of_mem
    apply (show LargeIndecomposable.RoiterFigure13E.rightOuterActionSubmodule
        (k := k) first ≤
      LargeIndecomposable.RoiterFigure13E.rightArmSupplementObstruction
        (k := k) first Pbar.tau from le_sup_right)
    exact ⟨a, rfl⟩
  have hLowerOuterZero (a : End Abar) :
      lowerSupplement.coefficient (a.asHom ≫ last) = 0 := by
    apply lowerSupplement.coefficient_eq_zero_of_mem
    apply (show LargeIndecomposable.RoiterFigure13E.leftOuterActionSubmodule
        (k := k) last ≤
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) last Qbar.tau from le_sup_right)
    exact ⟨a, rfl⟩
  have hmiddleCoefficient :
      terminalArm.betaZero = initialArm.alphaZero :=
    Figure14ArmCoefficientData.betaZero_eq_alphaZero
      terminalArm initialArm
      (quotientZeroMiddle_span_eq_top S hfinite D Q)
      (quotientZeroMiddle_allowsBitransit S hfinite D Q).1
  have hSuffixBeforePtauZero (g : Abar ⟶ Cbar) :
      terminalArm.crossZero (g ≫ Pbar.tau.asHom) = 0 := by
    obtain ⟨a, rfl⟩ := hSuffixPost g
    simp only [Category.assoc]
    rw [terminalArm.crossZero_left]
    change terminalArm.betaZero
      (middle ≫ (Pbar.tau * a).asHom) = 0
    rw [terminalArm.betaZero_post, map_mul, hresiduePtau, zero_mul]
  have hMiddleBeforePtauZero (g : Dbar ⟶ Cbar) :
      initialArm.alphaZero (g ≫ Pbar.tau.asHom) = 0 := by
    obtain ⟨a, rfl⟩ := hMiddlePost g
    simp only [Category.assoc]
    change initialArm.alphaZero
      (middle ≫ (Pbar.tau * a).asHom) = 0
    rw [initialArm.alphaZero_post, map_mul, hresiduePtau, zero_mul]
  have hResidueBeforePtauZero (g : End Cbar) :
      residueC (End.of (g.asHom ≫ Pbar.tau.asHom)) = 0 := by
    change residueC (Pbar.tau * g) = 0
    rw [map_mul, hresiduePtau, zero_mul]
  have hLeftCoefficientBeforePtau (g : End Cbar) :
      leftRadical.coefficientOne
          (End.of (g.asHom ≫ Pbar.tau.asHom)) =
        residueC g := by
    have hEnd : End.of (g.asHom ≫ Pbar.tau.asHom) =
        g * Pbar.tau := by
      change Pbar.tau * g = g * Pbar.tau
      exact Pbar.mul_comm Pbar.tau g
    rw [hEnd, leftRadical.coefficientOne_mul_tau]
  have hLowerBeforeQtau (g : Abar ⟶ Dbar) :
      lowerSupplement.coefficient (g ≫ Qbar.tau.asHom) =
        terminalArm.alphaZero g := by
    obtain ⟨a, rfl⟩ := hLastPost g
    simp only [Category.assoc]
    change lowerSupplement.coefficient
        (last ≫ (Qbar.tau * a).asHom) =
      terminalArm.alphaZero (last ≫ a.asHom)
    rw [Qbar.mul_comm Qbar.tau a, hLowerBridge,
      rightRadical.coefficientOne_mul_tau,
      terminalArm.alphaZero_post]
  have hRightCoefficientBeforeQtau (g : End Dbar) :
      rightRadical.coefficientOne
          (End.of (g.asHom ≫ Qbar.tau.asHom)) =
        residueD g := by
    have hEnd : End.of (g.asHom ≫ Qbar.tau.asHom) =
        g * Qbar.tau := by
      change Qbar.tau * g = g * Qbar.tau
      exact Qbar.mul_comm Qbar.tau g
    rw [hEnd, rightRadical.coefficientOne_mul_tau]
  have hResidueBeforeQtauZero (g : End Dbar) :
      residueD (End.of (g.asHom ≫ Qbar.tau.asHom)) = 0 := by
    change residueD (Qbar.tau * g) = 0
    rw [map_mul, hresidueQtau, zero_mul]
  have hLastBeforeQtauZero (g : Abar ⟶ Dbar) :
      terminalArm.alphaZero (g ≫ Qbar.tau.asHom) = 0 := by
    obtain ⟨a, rfl⟩ := hLastPost g
    simp only [Category.assoc]
    change terminalArm.alphaZero
      (last ≫ (Qbar.tau * a).asHom) = 0
    rw [terminalArm.alphaZero_post, map_mul, hresidueQtau, zero_mul]
  let table :
      LargeIndecomposable.CriticalSingularFigure15.LiteralEndpointTable
        (k := k) G := {
    residue := quotientVertexResidue S D P Q
    alphaLeftZero := terminalArm.alphaZero
    mainSuffix := terminalArm.crossZero
    lowerComposite := lowerSupplement.coefficient
    deltaZero := initialArm.alphaZero
    mainPrefix := initialArm.crossZero
    sigmaOne := rightRadical.coefficientOne
    alphaRightZero := initialArm.betaZero
    rhoOne := leftRadical.coefficientOne
    upperComposite := upperSupplement.coefficient
    alphaUpperZero := initialArm.betaZero
    alphaLowerZero := terminalArm.alphaZero }
  refine ⟨{
    table := table
    left_arrow := ?_
    right_arrow := ?_ }⟩
  · intro a' a e b hnot g
    cases e <;> cases b <;>
      dsimp only [table, LiteralEndpointTable.coefficient] <;> try rfl
    case alphaLeft.leftEndpoint =>
      change residueA (End.of (last ≫ g)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hAD last g
    case alphaLeft.leftCenter =>
      change terminalArm.alphaZero (last ≫ g) = residueD (End.of g)
      exact terminalArm.alphaZero_post (End.of g)
    case alphaLeft.rightCenter =>
      change terminalArm.crossZero (last ≫ g) = initialArm.alphaZero g
      rw [terminalArm.crossZero_left, hmiddleCoefficient]
    case alphaLeft.rightEndpoint =>
      exact False.elim (hnot ⟨rfl, rfl⟩)
    case alphaLeft.lowerCenter =>
      change lowerSupplement.coefficient (last ≫ g) =
        rightRadical.coefficientOne (End.of g)
      exact hLowerBridge (End.of g)
    case delta.leftCenter =>
      change residueD (End.of (middle ≫ g)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hDC middle g
    case delta.rightCenter =>
      change initialArm.alphaZero (middle ≫ g) = residueC (End.of g)
      exact initialArm.alphaZero_post (End.of g)
    case delta.rightEndpoint =>
      change initialArm.crossZero (middle ≫ g) = initialArm.betaZero g
      exact initialArm.crossZero_left g
    case delta.lowerCenter =>
      change rightRadical.coefficientOne (End.of (middle ≫ g)) = 0
      exact hRightThroughCZero middle g
    case alphaRight.rightCenter =>
      change residueC (End.of (first ≫ g)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hCB first g
    case alphaRight.rightEndpoint =>
      change initialArm.betaZero (first ≫ g) = residueB (End.of g)
      exact initialArm.betaZero_post (End.of g)
    case rho.rightCenter =>
      change leftRadical.coefficientOne
        (End.of (Pbar.tau.asHom ≫ g)) = residueC (End.of g)
      rw [show End.of (Pbar.tau.asHom ≫ g) =
        (End.of g : End Cbar) * Pbar.tau by rfl,
        leftRadical.coefficientOne_mul_tau]
    case rho.rightEndpoint =>
      change upperSupplement.coefficient (Pbar.tau.asHom ≫ g) =
        initialArm.betaZero g
      obtain ⟨a, rfl⟩ := hFirstPre g
      rw [← Category.assoc]
      change upperSupplement.coefficient ((a * Pbar.tau).asHom ≫ first) = _
      rw [hUpperBridge, leftRadical.coefficientOne_mul_tau,
        initialArm.betaZero_pre]
    case rho.upperCenter =>
      change residueC (End.of (Pbar.tau.asHom ≫ g)) = 0
      rw [show End.of (Pbar.tau.asHom ≫ g) =
        (End.of g : End Cbar) * Pbar.tau by rfl,
        map_mul, hresiduePtau, mul_zero]
    case rho.upperEndpoint =>
      change initialArm.betaZero (Pbar.tau.asHom ≫ g) = 0
      obtain ⟨a, rfl⟩ := hFirstPre g
      rw [← Category.assoc]
      change initialArm.betaZero ((a * Pbar.tau).asHom ≫ first) = 0
      rw [initialArm.betaZero_pre, map_mul, hresiduePtau, mul_zero]
    case alphaUpper.rightCenter =>
      change leftRadical.coefficientOne (End.of (first ≫ g)) = 0
      exact hLeftThroughBZero first g
    case alphaUpper.rightEndpoint =>
      change upperSupplement.coefficient (first ≫ g) = 0
      exact hUpperOuterZero (End.of g)
    case alphaUpper.upperCenter =>
      change residueC (End.of (first ≫ g)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hCB first g
    case alphaUpper.upperEndpoint =>
      change initialArm.betaZero (first ≫ g) = residueB (End.of g)
      exact initialArm.betaZero_post (End.of g)
    case sigma.leftCenter =>
      change residueD (End.of (Qbar.tau.asHom ≫ g)) = 0
      rw [show End.of (Qbar.tau.asHom ≫ g) =
        (End.of g : End Dbar) * Qbar.tau by rfl,
        map_mul, hresidueQtau, mul_zero]
    case sigma.rightCenter =>
      change initialArm.alphaZero (Qbar.tau.asHom ≫ g) = 0
      obtain ⟨a, rfl⟩ := hMiddlePost g
      rw [← Category.assoc, hrelation, Limits.zero_comp,
        initialArm.alphaZero.map_zero]
    case sigma.rightEndpoint =>
      change initialArm.crossZero (Qbar.tau.asHom ≫ g) = 0
      obtain ⟨a, rfl⟩ := hPrefixPre g
      have hcomm : Qbar.tau.asHom ≫ a.asHom =
          a.asHom ≫ Qbar.tau.asHom := by
        have h := congrArg End.asHom (Qbar.mul_comm Qbar.tau a)
        simpa only [End.mul_def] using h.symm
      have hzero : Qbar.tau.asHom ≫
          (a.asHom ≫ (middle ≫ first)) = 0 := by
        rw [← Category.assoc, hcomm, Category.assoc,
          ← Category.assoc Qbar.tau.asHom middle first,
          hrelation, Limits.zero_comp, Limits.comp_zero]
      rw [hzero, initialArm.crossZero.map_zero]
    case sigma.lowerCenter =>
      change rightRadical.coefficientOne
        (End.of (Qbar.tau.asHom ≫ g)) = residueD (End.of g)
      rw [show End.of (Qbar.tau.asHom ≫ g) =
        (End.of g : End Dbar) * Qbar.tau by rfl,
        rightRadical.coefficientOne_mul_tau]
    case alphaLower.lowerCenter =>
      change terminalArm.alphaZero (last ≫ g) = residueD (End.of g)
      exact terminalArm.alphaZero_post (End.of g)
    case alphaLower.lowerEndpoint =>
      change residueA (End.of (last ≫ g)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hAD last g
  · intro a b b' e hnot g
    cases e <;> cases a <;>
      dsimp only [table, LiteralEndpointTable.coefficient] <;> try rfl
    case alphaLeft.leftEndpoint =>
      change terminalArm.alphaZero (g ≫ last) = residueA (End.of g)
      exact terminalArm.alphaZero_pre (End.of g)
    case alphaLeft.leftCenter =>
      change residueD (End.of (g ≫ last)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hAD.symm g last
    case delta.leftEndpoint =>
      change terminalArm.crossZero (g ≫ middle) = terminalArm.alphaZero g
      exact terminalArm.crossZero_right g
    case delta.leftCenter =>
      change initialArm.alphaZero (g ≫ middle) = residueD (End.of g)
      exact initialArm.alphaZero_pre (End.of g)
    case delta.rightCenter =>
      change residueC (End.of (g ≫ middle)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hDC.symm g middle
    case delta.upperCenter =>
      change leftRadical.coefficientOne (End.of (g ≫ middle)) = 0
      exact hLeftThroughDZero g middle
    case alphaRight.leftEndpoint =>
      exact False.elim (hnot ⟨rfl, rfl⟩)
    case alphaRight.leftCenter =>
      change initialArm.crossZero (g ≫ first) = initialArm.alphaZero g
      exact initialArm.crossZero_right g
    case alphaRight.rightCenter =>
      change initialArm.betaZero (g ≫ first) = residueC (End.of g)
      exact initialArm.betaZero_pre (End.of g)
    case alphaRight.rightEndpoint =>
      change residueB (End.of (g ≫ first)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hCB.symm g first
    case alphaRight.upperCenter =>
      change upperSupplement.coefficient (g ≫ first) =
        leftRadical.coefficientOne (End.of g)
      exact hUpperBridge (End.of g)
    case rho.leftEndpoint =>
      change terminalArm.crossZero (g ≫ Pbar.tau.asHom) = 0
      exact hSuffixBeforePtauZero g
    case rho.leftCenter =>
      change initialArm.alphaZero (g ≫ Pbar.tau.asHom) = 0
      exact hMiddleBeforePtauZero g
    case rho.rightCenter =>
      change residueC (End.of (g ≫ Pbar.tau.asHom)) = 0
      exact hResidueBeforePtauZero (End.of g)
    case rho.upperCenter =>
      change leftRadical.coefficientOne
        (End.of (g ≫ Pbar.tau.asHom)) = residueC (End.of g)
      exact hLeftCoefficientBeforePtau (End.of g)
    case alphaUpper.upperCenter =>
      change initialArm.betaZero (g ≫ first) = residueC (End.of g)
      exact initialArm.betaZero_pre (End.of g)
    case alphaUpper.upperEndpoint =>
      change residueB (End.of (g ≫ first)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hCB.symm g first
    case sigma.leftEndpoint =>
      change lowerSupplement.coefficient (g ≫ Qbar.tau.asHom) =
        terminalArm.alphaZero g
      exact hLowerBeforeQtau g
    case sigma.leftCenter =>
      change rightRadical.coefficientOne
        (End.of (g ≫ Qbar.tau.asHom)) = residueD (End.of g)
      exact hRightCoefficientBeforeQtau (End.of g)
    case sigma.lowerCenter =>
      change residueD (End.of (g ≫ Qbar.tau.asHom)) = 0
      exact hResidueBeforeQtauZero (End.of g)
    case sigma.lowerEndpoint =>
      change terminalArm.alphaZero (g ≫ Qbar.tau.asHom) = 0
      exact hLastBeforeQtauZero g
    case alphaLower.leftEndpoint =>
      change lowerSupplement.coefficient (g ≫ last) = 0
      exact hLowerOuterZero (End.of g)
    case alphaLower.leftCenter =>
      change rightRadical.coefficientOne (End.of (g ≫ last)) = 0
      exact hRightThroughAZero g last
    case alphaLower.lowerCenter =>
      change residueD (End.of (g ≫ last)) = 0
      exact projectiveEndResidue_comp_eq_zero_of_ne T hAD.symm g last
    case alphaLower.lowerEndpoint =>
      change terminalArm.alphaZero (g ≫ last) = residueA (End.of g)
      exact terminalArm.alphaZero_pre (End.of g)

/-- The compatible literal table gives the complete endpoint coefficient
package consumed by the generic Figure-15 retraction compiler. -/
theorem nonempty_quotientEndpointCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    Nonempty
      (LargeIndecomposable.CriticalSingularFigure15.EndpointCoefficientData
        (k := k) (localQuotientCandidate S D P Q).quotientDiagram) := by
  obtain ⟨table⟩ :=
    nonempty_quotientCompatibleLiteralEndpointTable S hfinite D P Q
  exact ⟨table.toEndpointCoefficientData⟩

/-- The exact quotient attached to a critical spine is a cleaving Figure-15
quotient. -/
theorem localQuotientCandidate_isCleaving
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    {spine : LargeIndecomposable.BGRSCriticalPathSpine p}
    (D : InitialZeroCut (S := S) spine)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (localQuotientCandidate S D P Q).IsCleaving := by
  obtain ⟨coeff⟩ := nonempty_quotientEndpointCoefficientData
    S hfinite D P Q
  exact ⟨coeff.homBifunctorRetraction⟩

/-- Under representation-finiteness, every hypothetical critical path of
length at least three supplies the cleaving local Figure-15 quotient required
by the BGRS critical-figure reduction. -/
theorem hasCriticalLongPathLocalQuotientFigureExtraction
    (hfinite : LargeIndecomposable.MildAlg k A) :
    LargeIndecomposable.CriticalSingularLocalQuotientExtraction.HasCriticalLongPathLocalQuotientFigureExtraction S := by
  intro i j p hp hthree
  obtain ⟨spine⟩ := hp.exists_spine hthree
  obtain ⟨D⟩ := nonempty_initialZeroCut S spine
  obtain ⟨P⟩ := (spine.nonempty_middle_radicalPowerParameters S).1
  obtain ⟨Q⟩ := (spine.nonempty_middle_radicalPowerParameters S).2
  right
  exact ⟨localQuotientCandidate S D P Q,
    localQuotientCandidate_isCleaving S hfinite D P Q⟩

/-- BGRS 4.3: a representation-finite split-basic distributive algebra has
no critical lift-singular path of length at least three. -/
theorem no_long_critical
    (hfinite : LargeIndecomposable.MildAlg k A) :
    ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory}
      (p : Quiver.Path i j),
      LargeIndecomposable.IsCriticalBGRSLiftSingularPath p →
        ¬3 ≤ p.length := by
  intro i j p hp hthree
  obtain ⟨spine⟩ := hp.exists_spine hthree
  obtain ⟨D⟩ := nonempty_initialZeroCut S spine
  obtain ⟨P⟩ := (spine.nonempty_middle_radicalPowerParameters S).1
  obtain ⟨Q⟩ := (spine.nonempty_middle_radicalPowerParameters S).2
  exact LargeIndecomposable.CriticalSingularLocalQuotientExtraction.false_of_figure15LocalQuotient_mild S
    (localQuotientCandidate S D P Q) (localQuotientCandidate_isCleaving S hfinite D P Q) hfinite
    (relationIdeal_ne_bot S hfinite D Q)

end LargeIndecomposable.CriticalFigure15Quotient
