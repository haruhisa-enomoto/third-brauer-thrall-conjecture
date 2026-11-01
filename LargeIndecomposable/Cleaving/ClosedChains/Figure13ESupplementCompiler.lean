module

public import LargeIndecomposable.Cleaving.ClosedChains.Figure13EBoundCoefficientCompiler
public import LargeIndecomposable.Cleaving.ClosedChains.SupplementRetraction

@[expose] public section

/-!
# Supplement compiler for the bound BGRS Figure 13E diagram

The three nonmembership statements printed after Figure 13 in BGRS are
supplement statements at the paths `alpha tau`, `tau^2`, and `tau beta`.
This file turns exactly those statements into the coherent coefficient data
used by `Figure13EBoundCoefficientCompiler`.

The middle supplement also kills the line through `tau`.  This chooses the
degree-two functional with zero degree-one value.  Its translate by
multiplication with `tau` is then the coherent degree-one functional.  The
two arm supplements kill the duplicated outer occurrences.  All remaining
whiskering equations follow from endpoint-radical covariance and the local
factorization `ker(residue) = (-) * tau`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.RoiterFigure13E

open LargeIndecomposable.ClosedZigzagCrossUniverse
open LargeIndecomposable.ClosedZigzagTransfer

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- The span of all endomorphisms of `Y` factoring through `X`. -/
def throughObjectSubmodule (X Y : C) : Submodule k (Y ⟶ Y) :=
  Submodule.span k {q | ∃ (l : Y ⟶ X) (r : X ⟶ Y),
    q = l ≫ r}

/-- Endomorphisms factoring through a fixed object form a genuine Hom
subbimodule of the middle endomorphism space. -/
theorem isHomSubbimodule_throughObjectSubmodule (X Y : C) :
    LargeIndecomposable.IsHomSubbimodule
      (throughObjectSubmodule (k := k) X Y) := by
  constructor
  · intro a q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
        rcases hq with ⟨l, r, rfl⟩
        apply Submodule.subset_span
        exact ⟨a.asHom ≫ l, r, by simp [Category.assoc]⟩
    | zero => simp
    | add q r _ _ hq hr =>
        simpa using
          (throughObjectSubmodule (k := k) X Y).add_mem hq hr
    | smul c q _ hq =>
        simpa using
          (throughObjectSubmodule (k := k) X Y).smul_mem c hq
  · intro b q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
        rcases hq with ⟨l, r, rfl⟩
        apply Submodule.subset_span
        exact ⟨l, r ≫ b.asHom, by simp [Category.assoc]⟩
    | zero => simp
    | add q r _ _ hq hr =>
        simpa using
          (throughObjectSubmodule (k := k) X Y).add_mem hq hr
    | smul c q _ hq =>
        simpa using
          (throughObjectSubmodule (k := k) X Y).smul_mem c hq

/-- The source-endomorphism copies of the left arm. -/
def leftOuterActionSubmodule {X Y : C} (alpha : X ⟶ Y) :
    Submodule k (X ⟶ Y) :=
  LinearMap.range (preEndomorphismLinearMap (k := k) alpha)

/-- The target-endomorphism copies of the right arm. -/
def rightOuterActionSubmodule {Y Z : C} (beta : Y ⟶ Z) :
    Submodule k (Y ⟶ Z) :=
  LinearMap.range (postEndomorphismLinearMap (k := k) beta)

/-- The obstruction which the coefficient at `alpha tau` must kill. -/
def leftArmSupplementObstruction {X Y : C}
    (alpha : X ⟶ Y) (tau : End Y) : Submodule k (X ⟶ Y) :=
  endpointRadicalSubmodule (k := k) (alpha ≫ tau.asHom) ⊔
    leftOuterActionSubmodule (k := k) alpha

/-- The obstruction which the coefficient at `tau beta` must kill. -/
def rightArmSupplementObstruction {Y Z : C}
    (beta : Y ⟶ Z) (tau : End Y) : Submodule k (Y ⟶ Z) :=
  endpointRadicalSubmodule (k := k) (tau.asHom ≫ beta) ⊔
    rightOuterActionSubmodule (k := k) beta

/-- The one-sided middle obstruction printed in Figure 13E: the endpoint
radical of `tau^2`, the degree-one line, and all cycles through one selected
outer object. -/
def middleSquareSideSupplementObstruction
    (X Y : C) (tau : End Y) : Submodule k (End Y) :=
  endpointRadicalSubmodule (k := k) (tau ^ 2).asHom ⊔
    Submodule.span k ({tau} : Set (End Y)) ⊔
    throughObjectSubmodule (k := k) X Y

/-- The obstruction which the coefficient at `tau^2` must kill.  Besides
the endpoint radical of `tau^2`, it contains the degree-one line and all
cycles through either outer object. -/
def middleSquareSupplementObstruction
    (X Y Z : C) (tau : End Y) : Submodule k (End Y) :=
  middleSquareSideSupplementObstruction (k := k) X Y tau ⊔
    throughObjectSubmodule (k := k) Z Y

/-- The three exact linear supplements needed for Figure 13E. -/
structure Figure13ESupplementData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y) : Prop where
  left_separated : alpha ≫ tau.asHom ∉
    leftArmSupplementObstruction (k := k) alpha tau
  middle_separated : (tau ^ 2).asHom ∉
    middleSquareSupplementObstruction (k := k) X Y Z tau
  right_separated : tau.asHom ≫ beta ∉
    rightArmSupplementObstruction (k := k) beta tau

/-- The four supplement statements appearing after BGRS Figure 13: the two
arm statements and one middle statement through each outer object. -/
structure Figure13EPrintedSupplementData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y) : Prop where
  left_separated : alpha ≫ tau.asHom ∉
    leftArmSupplementObstruction (k := k) alpha tau
  middle_left_separated : (tau ^ 2).asHom ∉
    middleSquareSideSupplementObstruction (k := k) X Y tau
  middle_right_separated : (tau ^ 2).asHom ∉
    middleSquareSideSupplementObstruction (k := k) Z Y tau
  right_separated : tau.asHom ≫ beta ∉
    rightArmSupplementObstruction (k := k) beta tau

/-- Distributivity makes the two factor-through subbimodules comparable, so
the two printed middle nonmemberships combine into the single middle
supplement used by the coefficient compiler. -/
theorem Figure13EPrintedSupplementData.toFigure13ESupplementData
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} {alpha : X ⟶ Y} {beta : Y ⟶ Z} {tau : End Y}
    (h : Figure13EPrintedSupplementData (k := k) alpha beta tau) :
    Figure13ESupplementData (k := k) alpha beta tau := by
  refine ⟨h.left_separated, ?_, h.right_separated⟩
  have hcomp :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.homSubbimodule_comparable
      (k := k)
      (throughObjectSubmodule (k := k) X Y)
      (throughObjectSubmodule (k := k) Z Y)
      (isHomSubbimodule_throughObjectSubmodule (k := k) X Y)
      (isHomSubbimodule_throughObjectSubmodule (k := k) Z Y)
  rcases hcomp with hXZ | hZX
  · intro htau
    apply h.middle_right_separated
    apply (show middleSquareSupplementObstruction (k := k) X Y Z tau ≤
        middleSquareSideSupplementObstruction (k := k) Z Y tau from ?_)
      htau
    exact sup_le
      (sup_le le_sup_left (hXZ.trans le_sup_right)) le_sup_right
  · intro htau
    apply h.middle_left_separated
    apply (show middleSquareSupplementObstruction (k := k) X Y Z tau ≤
        middleSquareSideSupplementObstruction (k := k) X Y tau from ?_)
      htau
    exact sup_le le_rfl (hZX.trans le_sup_right)

private theorem alpha_mem_leftOuterActionSubmodule
    {X Y : C} (alpha : X ⟶ Y) :
    alpha ∈ leftOuterActionSubmodule (k := k) alpha := by
  refine ⟨1, ?_⟩
  simp [preEndomorphismLinearMap]

private theorem beta_mem_rightOuterActionSubmodule
    {Y Z : C} (beta : Y ⟶ Z) :
    beta ∈ rightOuterActionSubmodule (k := k) beta := by
  refine ⟨1, ?_⟩
  simp [postEndomorphismLinearMap]

private theorem throughObject_mem
    {X Y : C} (l : Y ⟶ X) (r : X ⟶ Y) :
    End.of (l ≫ r) ∈ throughObjectSubmodule (k := k) X Y := by
  apply Submodule.subset_span
  exact ⟨l, r, rfl⟩

private theorem throughObject_mul_tau_mem
    {X Y : C} (tau : End Y) (l : Y ⟶ X) (r : X ⟶ Y) :
    End.of (l ≫ r) * tau ∈ throughObjectSubmodule (k := k) X Y := by
  apply Submodule.subset_span
  refine ⟨tau.asHom ≫ l, r, ?_⟩
  apply End.ext
  simp only [End.mul_def, Category.assoc]

private theorem middleSquare_endpoint_le
    {X Y Z : C} (tau : End Y) :
    endpointRadicalSubmodule (k := k) (tau ^ 2).asHom ≤
      middleSquareSupplementObstruction (k := k) X Y Z tau := by
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_left))

private theorem middleSquare_tau_mem
    {X Y Z : C} (tau : End Y) :
    tau ∈ middleSquareSupplementObstruction (k := k) X Y Z tau := by
  have hle : Submodule.span k ({tau} : Set (End Y)) ≤
      middleSquareSupplementObstruction (k := k) X Y Z tau :=
    le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  apply hle
  exact Submodule.subset_span (Set.mem_singleton tau)

private theorem middleSquare_through_left_le
    {X Y Z : C} (tau : End Y) :
    throughObjectSubmodule (k := k) X Y ≤
      middleSquareSupplementObstruction (k := k) X Y Z tau := by
  exact le_sup_of_le_left le_sup_right

private theorem middleSquare_through_right_le
    {X Y Z : C} (tau : End Y) :
    throughObjectSubmodule (k := k) Z Y ≤
      middleSquareSupplementObstruction (k := k) X Y Z tau := by
  exact le_sup_right

private theorem leftArm_endpoint_le
    {X Y : C} (alpha : X ⟶ Y) (tau : End Y) :
    endpointRadicalSubmodule (k := k) (alpha ≫ tau.asHom) ≤
      leftArmSupplementObstruction (k := k) alpha tau :=
  le_sup_left

private theorem leftArm_outer_le
    {X Y : C} (alpha : X ⟶ Y) (tau : End Y) :
    leftOuterActionSubmodule (k := k) alpha ≤
      leftArmSupplementObstruction (k := k) alpha tau :=
  le_sup_right

private theorem rightArm_endpoint_le
    {Y Z : C} (beta : Y ⟶ Z) (tau : End Y) :
    endpointRadicalSubmodule (k := k) (tau.asHom ≫ beta) ≤
      rightArmSupplementObstruction (k := k) beta tau :=
  le_sup_left

private theorem rightArm_outer_le
    {Y Z : C} (beta : Y ⟶ Z) (tau : End Y) :
    rightOuterActionSubmodule (k := k) beta ≤
      rightArmSupplementObstruction (k := k) beta tau :=
  le_sup_right

/-- Three BGRS supplement nonmemberships construct every coherent
coefficient required by the bound Figure-13E retraction compiler. -/
theorem exists_repeatedMiddleThinQuotientPathCoefficientData_of_supplements
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (hresidue : ∀ a : End Y,
      residue a = 0 ↔ a ∈ Ring.jacobson (End Y))
    (htauJ : tau ∈ Ring.jacobson (End Y))
    (hfactor : ∀ a : End Y, residue a = 0 →
      ∃ q : End Y, a = q * tau)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (supplement : Figure13ESupplementData
      (k := k) alpha beta tau) :
    Nonempty (ThinQuotientPathCoefficientData (k := k)
      (relationIdeal (k := k))
      ((repeatedMiddleDiagram alpha beta tau hspecial).functor (k := k))) := by
  have hAlphaTau : alpha ≫ tau.asHom ≠ 0 := by
    intro hzero
    apply supplement.left_separated
    rw [hzero]
    exact Submodule.zero_mem _
  have hTauSq : tau ^ 2 ≠ 0 := by
    intro hzero
    apply supplement.middle_separated
    rw [hzero]
    exact Submodule.zero_mem _
  have hTauBeta : tau.asHom ≫ beta ≠ 0 := by
    intro hzero
    apply supplement.right_separated
    rw [hzero]
    exact Submodule.zero_mem _
  have hAlpha : alpha ≠ 0 := by
    intro hzero
    apply hAlphaTau
    rw [hzero]
    simp
  have hBeta : beta ≠ 0 := by
    intro hzero
    apply hTauBeta
    rw [hzero]
    simp

  obtain ⟨middleTwo, hMiddleTwoNorm, hMiddleTwoKill⟩ :=
    exists_normalized_coefficient_killing
      (middleSquareSupplementObstruction (k := k) X Y Z tau)
      (tau ^ 2).asHom supplement.middle_separated
  let mulTau : End Y →ₗ[k] End Y :=
    { toFun := fun a ↦ a * tau
      map_add' := fun a b ↦ add_mul a b tau
      map_smul' := by
        intro c a
        rw [Algebra.smul_mul_assoc, RingHom.id_apply] }
  let middleOne : End Y →ₗ[k] k := middleTwo.comp mulTau
  have hMiddleEndpoint : endpointRadicalSubmodule (k := k)
      (tau ^ 2).asHom ≤ LinearMap.ker middleTwo :=
    (middleSquare_endpoint_le (k := k) (X := X) (Z := Z) tau).trans
      hMiddleTwoKill
  have hMiddleTransform (a : End Y) :
      middleTwo (a * tau ^ 2) = residue a := by
    have h := endpointRadicalCoefficient_comp_right
      (k := k) (tau ^ 2).asHom residue hresidue middleTwo
      hMiddleTwoNorm hMiddleEndpoint a
    have heq : a * tau ^ 2 =
        End.of ((tau ^ 2).asHom ≫ a.asHom) := by
      apply End.ext
      simp only [End.mul_def]
    rw [heq]
    exact h
  have hMiddleTau : middleTwo tau = 0 := by
    exact LinearMap.mem_ker.mp
      (hMiddleTwoKill (middleSquare_tau_mem
        (k := k) (X := X) (Z := Z) tau))
  have hMiddleOneOne : middleOne 1 = 0 := by
    change middleTwo (1 * tau) = 0
    simpa using hMiddleTau
  let middle : RadicalSquareCoefficientData residue tau :=
    { coefficientOne := middleOne
      coefficientTwo := middleTwo
      coefficientOne_mul_tau := by
        intro a
        change middleTwo ((a * tau) * tau) = residue a
        rw [mul_assoc, ← pow_two]
        exact hMiddleTransform a
      coefficientTwo_mul_tau := by
        intro a
        rfl }

  obtain ⟨alphaZero, hAlphaZeroNorm, hAlphaZeroKill⟩ :=
    exists_normalized_endpointRadicalCoefficient (k := k) alpha hAlpha
  obtain ⟨betaZero, hBetaZeroNorm, hBetaZeroKill⟩ :=
    exists_normalized_endpointRadicalCoefficient (k := k) beta hBeta
  obtain ⟨alphaOne, hAlphaOneNorm, hAlphaOneKill⟩ :=
    exists_normalized_coefficient_killing
      (leftArmSupplementObstruction (k := k) alpha tau)
      (alpha ≫ tau.asHom) supplement.left_separated
  obtain ⟨betaOne, hBetaOneNorm, hBetaOneKill⟩ :=
    exists_normalized_coefficient_killing
      (rightArmSupplementObstruction (k := k) beta tau)
      (tau.asHom ≫ beta) supplement.right_separated
  have hAlphaOneEndpoint : endpointRadicalSubmodule (k := k)
      (alpha ≫ tau.asHom) ≤ LinearMap.ker alphaOne :=
    (leftArm_endpoint_le (k := k) alpha tau).trans hAlphaOneKill
  have hBetaOneEndpoint : endpointRadicalSubmodule (k := k)
      (tau.asHom ≫ beta) ≤ LinearMap.ker betaOne :=
    (rightArm_endpoint_le (k := k) beta tau).trans hBetaOneKill
  have hAlphaOneTransform (a : End Y) :
      alphaOne ((alpha ≫ tau.asHom) ≫ a.asHom) = residue a :=
    endpointRadicalCoefficient_comp_right
      (k := k) (alpha ≫ tau.asHom) residue hresidue alphaOne
      hAlphaOneNorm hAlphaOneEndpoint a
  have hBetaOneTransform (a : End Y) :
      betaOne (a.asHom ≫ (tau.asHom ≫ beta)) = residue a :=
    endpointRadicalCoefficient_comp_left
      (k := k) (tau.asHom ≫ beta) residue hresidue betaOne
      hBetaOneNorm hBetaOneEndpoint a
  have hAlphaOneAlpha : alphaOne alpha = 0 := by
    apply LinearMap.mem_ker.mp
    apply hAlphaOneKill
    apply leftArm_outer_le (k := k) alpha tau
    exact alpha_mem_leftOuterActionSubmodule (k := k) alpha
  have hBetaOneBeta : betaOne beta = 0 := by
    apply LinearMap.mem_ker.mp
    apply hBetaOneKill
    apply rightArm_outer_le (k := k) beta tau
    exact beta_mem_rightOuterActionSubmodule (k := k) beta

  have hMiddleOne_of_factor (a q : End Y)
      (ha : a = q * tau + algebraMap k (End Y) (residue a)) :
      middleOne a = residue q := by
    change middleTwo (a * tau) = _
    rw [ha, add_mul, middleTwo.map_add]
    have hscalar :
        algebraMap k (End Y) (residue a) * tau = residue a • tau := by
      rw [Algebra.smul_def]
    rw [mul_assoc, ← pow_two, hMiddleTransform, hscalar,
      middleTwo.map_smul, hMiddleTau, smul_zero, add_zero]

  let arm : Figure13ArmCoefficientData alpha beta residue tau middle :=
    { alphaZero := alphaZero
      alphaOne := alphaOne
      betaZero := betaZero
      betaOne := betaOne
      alphaZero_post := by
        intro a
        exact endpointRadicalCoefficient_comp_right
          (k := k) alpha residue hresidue alphaZero hAlphaZeroNorm
          hAlphaZeroKill a
      alphaOne_post := by
        intro a
        let r : End Y := a - algebraMap k (End Y) (residue a)
        have hr : residue r = 0 := by
          dsimp [r]
          rw [map_sub, residue.commutes]
          simp
        obtain ⟨q, hq⟩ := hfactor r hr
        have ha : a = q * tau + algebraMap k (End Y) (residue a) := by
          calc
            a = r + algebraMap k (End Y) (residue a) := by
              dsimp [r]
              abel
            _ = q * tau + algebraMap k (End Y) (residue a) := by rw [hq]
        have hscalar :
            alpha ≫ (algebraMap k (End Y) (residue a)).asHom =
              residue a • alpha := by
          change alpha ≫ (residue a • (𝟙 Y)) = residue a • alpha
          rw [Linear.comp_smul, Category.comp_id]
        have hcomp : alpha ≫ a.asHom =
            (alpha ≫ tau.asHom) ≫ q.asHom + residue a • alpha := by
          conv_lhs => rw [ha]
          change alpha ≫ ((q * tau).asHom +
              (algebraMap k (End Y) (residue a)).asHom) = _
          rw [Preadditive.comp_add, End.mul_def, Category.assoc, hscalar]
        calc
          alphaOne (alpha ≫ a.asHom) =
              alphaOne ((alpha ≫ tau.asHom) ≫ q.asHom +
                residue a • alpha) := by rw [hcomp]
          _ = alphaOne ((alpha ≫ tau.asHom) ≫ q.asHom) +
                alphaOne (residue a • alpha) := alphaOne.map_add _ _
          _ = residue q := by
            rw [hAlphaOneTransform, alphaOne.map_smul,
              hAlphaOneAlpha, smul_zero, add_zero]
          _ = middleOne a := (hMiddleOne_of_factor a q ha).symm
      betaZero_pre := by
        intro a
        exact endpointRadicalCoefficient_comp_left
          (k := k) beta residue hresidue betaZero hBetaZeroNorm
          hBetaZeroKill a
      betaOne_pre := by
        intro a
        let r : End Y := a - algebraMap k (End Y) (residue a)
        have hr : residue r = 0 := by
          dsimp [r]
          rw [map_sub, residue.commutes]
          simp
        obtain ⟨q, hq⟩ := hfactor r hr
        have ha : a = q * tau + algebraMap k (End Y) (residue a) := by
          calc
            a = r + algebraMap k (End Y) (residue a) := by
              dsimp [r]
              abel
            _ = q * tau + algebraMap k (End Y) (residue a) := by rw [hq]
        have hscalar :
            (algebraMap k (End Y) (residue a)).asHom ≫ beta =
              residue a • beta := by
          change (residue a • (𝟙 Y)) ≫ beta = residue a • beta
          rw [Linear.smul_comp, Category.id_comp]
        have hcomp : a.asHom ≫ beta =
            q.asHom ≫ (tau.asHom ≫ beta) + residue a • beta := by
          conv_lhs => rw [ha]
          rw [hcomm q]
          change ((tau * q).asHom +
              (algebraMap k (End Y) (residue a)).asHom) ≫ beta = _
          rw [Preadditive.add_comp, End.mul_def, Category.assoc, hscalar]
        calc
          betaOne (a.asHom ≫ beta) =
              betaOne (q.asHom ≫ (tau.asHom ≫ beta) +
                residue a • beta) := by rw [hcomp]
          _ = betaOne (q.asHom ≫ (tau.asHom ≫ beta)) +
                betaOne (residue a • beta) := betaOne.map_add _ _
          _ = residue q := by
            rw [hBetaOneTransform, betaOne.map_smul,
              hBetaOneBeta, smul_zero, add_zero]
          _ = middleOne a := (hMiddleOne_of_factor a q ha).symm }

  have hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0 := by
    intro l r
    change middleTwo (End.of (l ≫ r) * tau) = 0
    apply LinearMap.mem_ker.mp
    apply hMiddleTwoKill
    apply middleSquare_through_left_le (k := k) (Z := Z) tau
    exact throughObject_mul_tau_mem (k := k) tau l r
  have hThroughXTwo : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0 := by
    intro l r
    apply LinearMap.mem_ker.mp
    apply hMiddleTwoKill
    apply middleSquare_through_left_le (k := k) (Z := Z) tau
    exact throughObject_mem (k := k) l r
  have hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0 := by
    intro l r
    change middleTwo (End.of (l ≫ r) * tau) = 0
    apply LinearMap.mem_ker.mp
    apply hMiddleTwoKill
    apply middleSquare_through_right_le (k := k) (X := X) tau
    exact throughObject_mul_tau_mem (k := k) tau l r
  have hThroughZTwo : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0 := by
    intro l r
    apply LinearMap.mem_ker.mp
    apply hMiddleTwoKill
    apply middleSquare_through_right_le (k := k) (X := X) tau
    exact throughObject_mem (k := k) l r
  have hOuterXOne : ∀ g : End X,
      arm.alphaOne (g.asHom ≫ alpha) = 0 := by
    intro g
    apply LinearMap.mem_ker.mp
    apply hAlphaOneKill
    apply leftArm_outer_le (k := k) alpha tau
    exact ⟨g, rfl⟩
  have hOuterZOne : ∀ g : End Z,
      arm.betaOne (beta ≫ g.asHom) = 0 := by
    intro g
    apply LinearMap.mem_ker.mp
    apply hBetaOneKill
    apply rightArm_outer_le (k := k) beta tau
    exact ⟨g, rfl⟩
  have hresTau : residue tau = 0 := (hresidue tau).2 htauJ
  exact ⟨repeatedMiddleThinQuotientPathCoefficientData
    alpha beta tau hspecial residue middle arm hresTau hcomm
    hAlphaFactor hBetaFactor hThroughXZero hThroughXOne hThroughXTwo
    hThroughZZero hThroughZOne hThroughZTwo hOuterXOne hOuterZOne⟩

end LargeIndecomposable.RoiterFigure13E
