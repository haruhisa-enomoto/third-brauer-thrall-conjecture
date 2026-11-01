module

public import LargeIndecomposable.Cleaving.ClosedChains.ArrowCoefficient
public import LargeIndecomposable.Cleaving.ClosedChains.Figure13Coefficient
public import LargeIndecomposable.Cleaving.ClosedChains.RadicalPowerParameter

@[expose] public section

/-!
# Coherent coefficients for the central Figure-14 chain

The repeated-object core of Figure 14 is

`D --delta--> C --lambda--> D --delta--> C`.

If `sigma = lambda * delta` is a local radical parameter and the threefold
composite survives, the five path lines `delta`, `lambda`, `sigma`,
`rho = delta * lambda`, and `delta * lambda * delta` admit compatible scalar
coefficients.  This is the degree-one analogue of the Figure-13 coefficient
construction; importantly, it does not require `sigma^2` to survive.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- The coherent coefficient package on the alternating three-arrow core of
Figure 14. -/
structure Figure14CentralCoefficientData
    {X Y : C} (delta : X ⟶ Y) (lambda : Y ⟶ X)
    (residueX : End X →ₐ[k] k) (residueY : End Y →ₐ[k] k)
    (sigma : End Y) where
  deltaZero : (X ⟶ Y) →ₗ[k] k
  lambdaZero : (Y ⟶ X) →ₗ[k] k
  sigmaOne : End Y →ₗ[k] k
  rhoOne : End X →ₗ[k] k
  deltaOne : (X ⟶ Y) →ₗ[k] k
  deltaZero_pre : ∀ a : End X,
    deltaZero (a.asHom ≫ delta) = residueX a
  deltaZero_post : ∀ b : End Y,
    deltaZero (delta ≫ b.asHom) = residueY b
  lambdaZero_pre : ∀ b : End Y,
    lambdaZero (b.asHom ≫ lambda) = residueY b
  lambdaZero_post : ∀ a : End X,
    lambdaZero (lambda ≫ a.asHom) = residueX a
  sigmaOne_mul_sigma : ∀ b : End Y,
    sigmaOne (b * sigma) = residueY b
  sigmaOne_one : sigmaOne 1 = 0
  rhoOne_mul_rho : ∀ a : End X,
    rhoOne (a * End.of (delta ≫ lambda)) = residueX a
  rhoOne_one : rhoOne 1 = 0
  deltaOne_post : ∀ b : End Y,
    deltaOne (delta ≫ b.asHom) = sigmaOne b
  deltaOne_pre : ∀ a : End X,
    deltaOne (a.asHom ≫ delta) = rhoOne a

namespace Figure14CentralCoefficientData

variable {X Y : C} {delta : X ⟶ Y} {lambda : Y ⟶ X}
variable {residueX : End X →ₐ[k] k} {residueY : End Y →ₐ[k] k}
variable {sigma : End Y}

/-- Compatibility at the path `lambda * delta`: left whiskering `lambda`
turns the ordinary `delta` coefficient into the first `sigma` coefficient. -/
theorem sigmaOne_lambda
    (h : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (g : X ⟶ Y) :
    h.sigmaOne (End.of (lambda ≫ g)) = h.deltaZero g := by
  have hg : g ∈ twoSidedEndomorphismSpan k delta := by
    rw [hdeltaSpan]
    exact Submodule.mem_top
  obtain ⟨b, hgb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hdeltaTransit hg
  rw [hgb]
  have hend : End.of (lambda ≫ (delta ≫ b.asHom)) = b * sigma := by
    have hmorph : lambda ≫ (delta ≫ b.asHom) =
        sigma.asHom ≫ b.asHom := by
      rw [hsigma]
      simp only [Category.assoc]
    exact hmorph
  rw [hend, h.sigmaOne_mul_sigma, h.deltaZero_post]

/-- Compatibility at `delta * lambda`: left whiskering `delta` turns the
ordinary `lambda` coefficient into the first opposite-cycle coefficient. -/
theorem rhoOne_delta
    (h : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (g : Y ⟶ X) :
    h.rhoOne (End.of (delta ≫ g)) = h.lambdaZero g := by
  have hg : g ∈ twoSidedEndomorphismSpan k lambda := by
    rw [hlambdaSpan]
    exact Submodule.mem_top
  obtain ⟨a, hga⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hlambdaTransit hg
  rw [hga]
  have hend : End.of (delta ≫ (lambda ≫ a.asHom)) =
      a * End.of (delta ≫ lambda) := by
    apply End.ext
    simp only [End.mul_def, Category.assoc]
  rw [hend, h.rhoOne_mul_rho, h.lambdaZero_post]

/-- The other endpoint equation on `delta * lambda`. -/
theorem rhoOne_comp_lambda
    (h : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (g : X ⟶ Y) :
    h.rhoOne (End.of (g ≫ lambda)) = h.deltaZero g := by
  have hg : g ∈ twoSidedEndomorphismSpan k delta := by
    rw [hdeltaSpan]
    exact Submodule.mem_top
  obtain ⟨b, hgb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hdeltaTransit hg
  rw [hgb]
  obtain ⟨a, hba⟩ := hlambdaTransit b
  have hend : End.of ((delta ≫ b.asHom) ≫ lambda) =
      a * End.of (delta ≫ lambda) := by
    have hmorph : (delta ≫ b.asHom) ≫ lambda =
        (delta ≫ lambda) ≫ a.asHom := by
      simp only [Category.assoc]
      rw [hba]
    exact hmorph
  rw [hend, h.rhoOne_mul_rho, h.deltaZero_post]
  calc
    residueX a = h.lambdaZero (lambda ≫ a.asHom) :=
      (h.lambdaZero_post a).symm
    _ = h.lambdaZero (b.asHom ≫ lambda) := by rw [hba]
    _ = residueY b := h.lambdaZero_pre b

/-- The other endpoint equation on `lambda * delta`. -/
theorem sigmaOne_comp_delta
    (h : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (g : Y ⟶ X) :
    h.sigmaOne (End.of (g ≫ delta)) = h.lambdaZero g := by
  have hg : g ∈ twoSidedEndomorphismSpan k lambda := by
    rw [hlambdaSpan]
    exact Submodule.mem_top
  obtain ⟨a, hga⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hlambdaTransit hg
  rw [hga]
  obtain ⟨b, hab⟩ := hdeltaTransit a
  have hend : End.of ((lambda ≫ a.asHom) ≫ delta) = b * sigma := by
    have hmorph : (lambda ≫ a.asHom) ≫ delta =
        sigma.asHom ≫ b.asHom := by
      simp only [Category.assoc]
      rw [hab, hsigma]
      simp only [Category.assoc]
    exact hmorph
  rw [hend, h.sigmaOne_mul_sigma, h.lambdaZero_post]
  calc
    residueY b = h.deltaZero (delta ≫ b.asHom) :=
      (h.deltaZero_post b).symm
    _ = h.deltaZero (a.asHom ≫ delta) := by rw [hab]
    _ = residueX a := h.deltaZero_pre a

end Figure14CentralCoefficientData

/-- A surviving Figure-14 central chain carries coherent coefficients.  The
middle arrow needs transit only for transporting the opposite cycle; its
ordinary endpoint coefficient is automatically compatible with both split
residue maps. -/
theorem exists_figure14CentralCoefficientData
    [IsAlgClosed k]
    [∀ T : C, Module.Finite k (End T)]
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {X Y : C} (delta : X ⟶ Y) (lambda : Y ⟶ X)
    (residueX : End X →ₐ[k] k) (residueY : End Y →ₐ[k] k)
    (hresidueX : ∀ a : End X,
      residueX a = 0 ↔ a ∈ Ring.jacobson (End X))
    (hresidueY : ∀ b : End Y,
      residueY b = 0 ↔ b ∈ Ring.jacobson (End Y))
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hsigma : P.tau.asHom = lambda ≫ delta)
    (hthree : delta ≫ lambda ≫ delta ≠ 0)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta) :
    Nonempty (Figure14CentralCoefficientData
      delta lambda residueX residueY P.tau) := by
  have hdelta0 : delta ≠ 0 := by
    intro hzero
    apply hthree
    simp [hzero]
  have hlambda0 : lambda ≠ 0 := by
    intro hzero
    apply hthree
    simp [hzero]
  obtain ⟨deltaZero, hdeltaNormalized, hdeltaKernel⟩ :=
    exists_normalized_endpointRadicalCoefficient
      (k := k) delta hdelta0
  obtain ⟨lambdaZero, hlambdaNormalized, hlambdaKernel⟩ :=
    exists_normalized_endpointRadicalCoefficient
      (k := k) lambda hlambda0
  have hdeltaZeroPre (a : End X) :
      deltaZero (a.asHom ≫ delta) = residueX a :=
    endpointRadicalCoefficient_comp_left delta residueX hresidueX
      deltaZero hdeltaNormalized hdeltaKernel a
  have hdeltaZeroPost (b : End Y) :
      deltaZero (delta ≫ b.asHom) = residueY b :=
    endpointRadicalCoefficient_comp_right delta residueY hresidueY
      deltaZero hdeltaNormalized hdeltaKernel b
  have hlambdaZeroPre (b : End Y) :
      lambdaZero (b.asHom ≫ lambda) = residueY b :=
    endpointRadicalCoefficient_comp_left lambda residueY hresidueY
      lambdaZero hlambdaNormalized hlambdaKernel b
  have hlambdaZeroPost (a : End X) :
      lambdaZero (lambda ≫ a.asHom) = residueX a :=
    endpointRadicalCoefficient_comp_right lambda residueX hresidueX
      lambdaZero hlambdaNormalized hlambdaKernel a
  have hresTau : residueY P.tau = 0 :=
    (hresidueY P.tau).2 P.mem_jacobson
  have hunitY : ∀ b : End Y, IsUnit b ↔ residueY b ≠ 0 := by
    intro b
    constructor
    · intro hb hzero
      exact ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End Y) b).1 ((hresidueY b).1 hzero)) hb
    · intro hne
      by_contra hnot
      exact hne ((hresidueY b).2
        ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
          (End Y) b).2 hnot))
  let sigmaData : RadicalCoefficientData residueY P.tau :=
    Classical.choice
      (exists_radicalCoefficientData residueY P.tau P.ne_zero
        hresTau hunitY)
  let deltaAction := postEndomorphismLinearMap (k := k) delta
  have hfactorY : ∀ b : End Y, residueY b = 0 →
      ∃ q : End Y, b = q * P.tau := by
    intro b hb
    have hbJ : b ∈ Ring.jacobson (End Y) := (hresidueY b).1 hb
    have hbSpan : b ∈ twoSidedEndomorphismSpan k P.tau := by
      rw [P.span_eq]
      exact hbJ
    obtain ⟨q, hbq⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
        P.tau_allowsTransit hbSpan
    refine ⟨q, ?_⟩
    apply End.ext
    simpa only [End.mul_def] using hbq
  have hdeltaKerOne : LinearMap.ker deltaAction ≤
      LinearMap.ker sigmaData.coefficientOne := by
    intro b hb
    rw [LinearMap.mem_ker] at hb ⊢
    change delta ≫ b.asHom = 0 at hb
    have hres : residueY b = 0 := by
      by_contra hres
      have hbUnit : IsUnit b := (hunitY b).2 hres
      letI : IsIso b.asHom := (isUnit_iff_isIso b).1 hbUnit
      apply hdelta0
      apply (cancel_mono b.asHom).1
      simpa using hb
    obtain ⟨q, hq⟩ := hfactorY b hres
    rw [hq, sigmaData.coefficientOne_mul_tau]
    by_contra hqres
    have hqUnit : IsUnit q := (hunitY q).2 hqres
    letI : IsIso q.asHom := (isUnit_iff_isIso q).1 hqUnit
    apply hthree
    apply (cancel_mono q.asHom).1
    have hzero : (delta ≫ lambda ≫ delta) ≫ q.asHom = 0 := by
      calc
        (delta ≫ lambda ≫ delta) ≫ q.asHom =
            delta ≫ (q * P.tau).asHom := by
          rw [← hsigma]
          simp only [End.mul_def, Category.assoc]
        _ = delta ≫ b.asHom := by rw [← hq]
        _ = 0 := hb
    simpa using hzero
  obtain ⟨deltaOne, hdeltaOne⟩ :=
    exists_linearMap_comp_eq_of_ker_le deltaAction
      sigmaData.coefficientOne hdeltaKerOne
  have hdeltaOnePost (b : End Y) :
      deltaOne (delta ≫ b.asHom) = sigmaData.coefficientOne b := by
    exact DFunLike.congr_fun hdeltaOne b
  let rhoOne : End X →ₗ[k] k :=
    deltaOne.comp (preEndomorphismLinearMap (k := k) delta)
  have hrhoShift (a : End X) :
      rhoOne (a * End.of (delta ≫ lambda)) = residueX a := by
    obtain ⟨c, hac⟩ := hdeltaTransit a
    have hcomp :
        (a * End.of (delta ≫ lambda)).asHom ≫ delta =
          delta ≫ (c * P.tau).asHom := by
      change ((delta ≫ lambda) ≫ a.asHom) ≫ delta =
        delta ≫ (P.tau.asHom ≫ c.asHom)
      simp only [Category.assoc]
      rw [hac, hsigma]
      simp only [Category.assoc]
    change deltaOne
        ((a * End.of (delta ≫ lambda)).asHom ≫ delta) = residueX a
    rw [hcomp, hdeltaOnePost, sigmaData.coefficientOne_mul_tau]
    calc
      residueY c = deltaZero (delta ≫ c.asHom) :=
        (hdeltaZeroPost c).symm
      _ = deltaZero (a.asHom ≫ delta) := by rw [hac]
      _ = residueX a := hdeltaZeroPre a
  have hrhoOne : rhoOne 1 = 0 := by
    change deltaOne ((𝟙 X) ≫ delta) = 0
    rw [Category.id_comp]
    calc
      deltaOne delta = sigmaData.coefficientOne (1 : End Y) := by
        simpa using hdeltaOnePost (1 : End Y)
      _ = 0 := sigmaData.coefficientOne_one
  refine ⟨⟨deltaZero, lambdaZero, sigmaData.coefficientOne,
    rhoOne, deltaOne, hdeltaZeroPre, hdeltaZeroPost,
    hlambdaZeroPre, hlambdaZeroPost,
    sigmaData.coefficientOne_mul_tau, sigmaData.coefficientOne_one,
    hrhoShift, hrhoOne, hdeltaOnePost, ?_⟩⟩
  intro a
  rfl

/-- Coherent coefficients on a directed length-two arm.  The two last fields
are the generator equations needed to extend naturality from the two arrows
to their composite. -/
structure Figure14ArmCoefficientData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z)
    (residueX : End X →ₐ[k] k) (residueY : End Y →ₐ[k] k)
    (residueZ : End Z →ₐ[k] k) where
  alphaZero : (X ⟶ Y) →ₗ[k] k
  betaZero : (Y ⟶ Z) →ₗ[k] k
  crossZero : (X ⟶ Z) →ₗ[k] k
  alphaZero_pre : ∀ a : End X,
    alphaZero (a.asHom ≫ alpha) = residueX a
  alphaZero_post : ∀ b : End Y,
    alphaZero (alpha ≫ b.asHom) = residueY b
  betaZero_pre : ∀ b : End Y,
    betaZero (b.asHom ≫ beta) = residueY b
  betaZero_post : ∀ c : End Z,
    betaZero (beta ≫ c.asHom) = residueZ c
  crossZero_left : ∀ g : Y ⟶ Z,
    crossZero (alpha ≫ g) = betaZero g
  crossZero_right : ∀ g : X ⟶ Y,
    crossZero (g ≫ beta) = alphaZero g

namespace Figure14ArmCoefficientData

/-- Two directed arm packages which share a full transit arrow have
literally the same normalized coefficient on that arrow. -/
theorem betaZero_eq_alphaZero
    {W X Y Z : C} {alpha : W ⟶ X} {beta : X ⟶ Y}
    {gamma : Y ⟶ Z}
    {residueW : End W →ₐ[k] k} {residueX : End X →ₐ[k] k}
    {residueY : End Y →ₐ[k] k} {residueZ : End Z →ₐ[k] k}
    (left : Figure14ArmCoefficientData
      alpha beta residueW residueX residueY)
    (right : Figure14ArmCoefficientData
      beta gamma residueX residueY residueZ)
    (hspan : twoSidedEndomorphismSpan k beta = ⊤)
    (htransit : LargeIndecomposable.AllowsTransit beta) :
    left.betaZero = right.alphaZero := by
  apply LinearMap.ext
  intro g
  have hg : g ∈ twoSidedEndomorphismSpan k beta := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨b, rfl⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) htransit hg
  rw [left.betaZero_post, right.alphaZero_post]

end Figure14ArmCoefficientData

/-- Extend prescribed, already normalized arrow coefficients across a directed
length-two arm.  This form is needed in Figure 14 because the two arms share
their occurrence of `delta` with the central alternating chain, so the arrow
coefficient must be literally the same functional in all three places. -/
theorem exists_figure14ArmCoefficientData_of_coefficients
    {X Y Z : C} [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    (alpha : X ⟶ Y) (beta : Y ⟶ Z)
    (residueX : End X →ₐ[k] k) (residueY : End Y →ₐ[k] k)
    (residueZ : End Z →ₐ[k] k)
    (alphaZero : (X ⟶ Y) →ₗ[k] k)
    (betaZero : (Y ⟶ Z) →ₗ[k] k)
    (halphaZeroPre : ∀ a : End X,
      alphaZero (a.asHom ≫ alpha) = residueX a)
    (halphaZeroPost : ∀ b : End Y,
      alphaZero (alpha ≫ b.asHom) = residueY b)
    (hbetaZeroPre : ∀ b : End Y,
      betaZero (b.asHom ≫ beta) = residueY b)
    (hbetaZeroPost : ∀ c : End Z,
      betaZero (beta ≫ c.asHom) = residueZ c)
    (hresidueY : ∀ b : End Y,
      residueY b = 0 ↔ b ∈ Ring.jacobson (End Y))
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hcrossUnit : ∀ a : End Y, IsUnit a →
      (alpha ≫ a.asHom) ≫ beta ≠ 0) :
    Nonempty (Figure14ArmCoefficientData
      alpha beta residueX residueY residueZ) := by
  let crossAction := LargeIndecomposable.middleEndomorphismSandwich
    (k := k) alpha beta
  have hcrossKer : LinearMap.ker crossAction ≤
      LinearMap.ker residueY.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change (alpha ≫ a.asHom) ≫ beta = 0 at ha
    by_contra hres
    have haUnit : IsUnit a := by
      by_contra hnot
      exact hres ((hresidueY a).2
        ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
          (End Y) a).2 hnot))
    exact hcrossUnit a haUnit ha
  obtain ⟨crossZero, hcrossZero⟩ :=
    exists_linearMap_comp_eq_of_ker_le crossAction
      residueY.toLinearMap hcrossKer
  have hcrossSandwich (a : End Y) :
      crossZero ((alpha ≫ a.asHom) ≫ beta) = residueY a :=
    DFunLike.congr_fun hcrossZero a
  refine ⟨⟨alphaZero, betaZero, crossZero,
    halphaZeroPre, halphaZeroPost, hbetaZeroPre, hbetaZeroPost,
    ?_, ?_⟩⟩
  · intro g
    obtain ⟨a, rfl⟩ := hBetaFactor g
    rw [← Category.assoc, hcrossSandwich, hbetaZeroPre]
  · intro g
    obtain ⟨a, rfl⟩ := hAlphaFactor g
    rw [hcrossSandwich, halphaZeroPost]

/-- Full, correctly oriented arms admit coherent coefficients as soon as no
invertible twist kills the displayed length-two composite. -/
theorem exists_figure14ArmCoefficientData
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z)
    (residueX : End X →ₐ[k] k) (residueY : End Y →ₐ[k] k)
    (residueZ : End Z →ₐ[k] k)
    (hresidueX : ∀ a : End X,
      residueX a = 0 ↔ a ∈ Ring.jacobson (End X))
    (hresidueY : ∀ b : End Y,
      residueY b = 0 ↔ b ∈ Ring.jacobson (End Y))
    (hresidueZ : ∀ c : End Z,
      residueZ c = 0 ↔ c ∈ Ring.jacobson (End Z))
    (halphaSpan : twoSidedEndomorphismSpan k alpha = ⊤)
    (hbetaSpan : twoSidedEndomorphismSpan k beta = ⊤)
    (halphaTransit : LargeIndecomposable.AllowsTransit alpha)
    (hbetaCotransit : LargeIndecomposable.AllowsCotransit beta)
    (hcrossUnit : ∀ a : End Y, IsUnit a →
      (alpha ≫ a.asHom) ≫ beta ≠ 0) :
    Nonempty (Figure14ArmCoefficientData
      alpha beta residueX residueY residueZ) := by
  have hcross0 := hcrossUnit (1 : End Y) isUnit_one
  have halpha0 : alpha ≠ 0 := by
    intro hzero
    apply hcross0
    simp [hzero]
  have hbeta0 : beta ≠ 0 := by
    intro hzero
    apply hcross0
    simp [hzero]
  obtain ⟨alphaZero, halphaNormalized, halphaKernel⟩ :=
    exists_normalized_endpointRadicalCoefficient
      (k := k) alpha halpha0
  obtain ⟨betaZero, hbetaNormalized, hbetaKernel⟩ :=
    exists_normalized_endpointRadicalCoefficient
      (k := k) beta hbeta0
  have halphaZeroPre (a : End X) :
      alphaZero (a.asHom ≫ alpha) = residueX a :=
    endpointRadicalCoefficient_comp_left alpha residueX hresidueX
      alphaZero halphaNormalized halphaKernel a
  have halphaZeroPost (b : End Y) :
      alphaZero (alpha ≫ b.asHom) = residueY b :=
    endpointRadicalCoefficient_comp_right alpha residueY hresidueY
      alphaZero halphaNormalized halphaKernel b
  have hbetaZeroPre (b : End Y) :
      betaZero (b.asHom ≫ beta) = residueY b :=
    endpointRadicalCoefficient_comp_left beta residueY hresidueY
      betaZero hbetaNormalized hbetaKernel b
  have hbetaZeroPost (c : End Z) :
      betaZero (beta ≫ c.asHom) = residueZ c :=
    endpointRadicalCoefficient_comp_right beta residueZ hresidueZ
      betaZero hbetaNormalized hbetaKernel c
  have hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom := by
    intro g
    apply LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k)
      halphaTransit
    rw [halphaSpan]
    exact Submodule.mem_top
  have hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta := by
    intro g
    apply LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      (k := k)
      hbetaCotransit
    rw [hbetaSpan]
    exact Submodule.mem_top
  let crossAction := LargeIndecomposable.middleEndomorphismSandwich
    (k := k) alpha beta
  have hcrossKer : LinearMap.ker crossAction ≤
      LinearMap.ker residueY.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change (alpha ≫ a.asHom) ≫ beta = 0 at ha
    by_contra hres
    have haUnit : IsUnit a := by
      by_contra hnot
      exact hres ((hresidueY a).2
        ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
          (End Y) a).2 hnot))
    exact hcrossUnit a haUnit ha
  obtain ⟨crossZero, hcrossZero⟩ :=
    exists_linearMap_comp_eq_of_ker_le crossAction
      residueY.toLinearMap hcrossKer
  have hcrossSandwich (a : End Y) :
      crossZero ((alpha ≫ a.asHom) ≫ beta) = residueY a :=
    DFunLike.congr_fun hcrossZero a
  refine ⟨⟨alphaZero, betaZero, crossZero,
    halphaZeroPre, halphaZeroPost, hbetaZeroPre, hbetaZeroPost,
    ?_, ?_⟩⟩
  · intro g
    obtain ⟨a, rfl⟩ := hBetaFactor g
    rw [← Category.assoc, hcrossSandwich, hbetaZeroPre]
  · intro g
    obtain ⟨a, rfl⟩ := hAlphaFactor g
    rw [hcrossSandwich, halphaZeroPost]

end LargeIndecomposable.ClosedZigzagTransfer
