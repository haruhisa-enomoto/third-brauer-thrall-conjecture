module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RoiterTransit
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

/-!
# Coherent coefficients for the repeated middle of Figure 13

This file constructs the scalar coefficient maps needed on the middle chain
`1, tau, tau^2` and extends them coherently to the two arms and outer
composite of the Figure-13 shape.  The construction is pure linear algebra:
a functional descends through a linear map when the latter's kernel is
contained in the former's kernel, and a functional on a subspace extends over
a field.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w x z

variable {k : Type u} [Field k]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- A scalar linear functional descends through a linear map precisely when
the map's kernel is contained in the functional's kernel.  Over a field, the
resulting functional on the range extends to the whole codomain. -/
theorem exists_linearMap_comp_eq_of_ker_le
    (F : V →ₗ[k] W) (ell : V →ₗ[k] k)
    (hker : LinearMap.ker F ≤ LinearMap.ker ell) :
    ∃ L : W →ₗ[k] k, L.comp F = ell := by
  let onRange : LinearMap.range F →ₗ[k] k :=
    (LinearMap.ker F).liftQ ell hker |>.comp
      F.quotKerEquivRange.symm.toLinearMap
  obtain ⟨L, hL⟩ := LinearMap.exists_extend onRange
  refine ⟨L, ?_⟩
  apply LinearMap.ext
  intro a
  have haRange : F a ∈ LinearMap.range F := ⟨a, rfl⟩
  have hEval := DFunLike.congr_fun hL ⟨F a, haRange⟩
  simpa [onRange] using hEval

variable {R : Type z} [Ring R] [Algebra k R]

/-- The first three coherent coefficients along a nonzero radical parameter.
The two displayed shift identities are the exact equations needed along a
source chain `1, tau, tau^2`. -/
structure RadicalSquareCoefficientData
    (residue : R →ₐ[k] k) (tau : R) where
  coefficientOne : R →ₗ[k] k
  coefficientTwo : R →ₗ[k] k
  coefficientOne_mul_tau : ∀ a : R,
    coefficientOne (a * tau) = residue a
  coefficientTwo_mul_tau : ∀ a : R,
    coefficientTwo (a * tau) = coefficientOne a

/-- The constant and first-order coherent coefficients along a radical
parameter.  The normalization on `1` is useful when the same ambient object
occurs at distinct source vertices: it makes the coefficient of the
positive-length path vanish on the ambient identity. -/
structure RadicalCoefficientData
    (residue : R →ₐ[k] k) (tau : R) where
  coefficientOne : R →ₗ[k] k
  coefficientOne_mul_tau : ∀ a : R,
    coefficientOne (a * tau) = residue a
  coefficientOne_one : coefficientOne 1 = 0

/-- A coherent first-order coefficient exists for every nonzero radical
parameter.  Unlike `exists_radicalSquareCoefficientData`, no nonvanishing of
`tau²` is needed. -/
theorem exists_radicalCoefficientData
    (residue : R →ₐ[k] k) (tau : R)
    (htau0 : tau ≠ 0) (hresTau : residue tau = 0)
    (hunit : ∀ a : R, IsUnit a ↔ residue a ≠ 0) :
    Nonempty (RadicalCoefficientData residue tau) := by
  let mulTau : R →ₗ[k] R :=
    { toFun := fun a ↦ a * tau
      map_add' := fun a b ↦ add_mul a b tau
      map_smul' := by
        intro c a
        rw [Algebra.smul_mul_assoc, RingHom.id_apply] }
  have hkerResidue : LinearMap.ker mulTau ≤
      LinearMap.ker residue.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change a * tau = 0 at ha
    by_contra hres
    have haUnit : IsUnit a := (hunit a).2 hres
    apply htau0
    apply haUnit.mul_left_cancel
    simpa only [mul_zero] using ha
  obtain ⟨raw, hraw⟩ :=
    exists_linearMap_comp_eq_of_ker_le mulTau residue.toLinearMap
      hkerResidue
  have hrawShift (a : R) : raw (a * tau) = residue a := by
    exact DFunLike.congr_fun hraw a
  let coefficientOne : R →ₗ[k] k :=
    raw - raw 1 • residue.toLinearMap
  refine ⟨⟨coefficientOne, ?_, ?_⟩⟩
  · intro a
    change raw (a * tau) - raw 1 * residue (a * tau) = residue a
    rw [hrawShift, map_mul, hresTau, mul_zero, mul_zero, sub_zero]
  · change raw 1 - raw 1 * residue 1 = 0
    rw [show residue 1 = 1 from map_one residue, mul_one, sub_self]

/-- Residue coefficients can be divided coherently by a radical parameter
through degree two, provided the parameter and its square are nonzero and
every residue-zero element is divisible by the parameter. -/
theorem exists_radicalSquareCoefficientData
    (residue : R →ₐ[k] k) (tau : R)
    (htau0 : tau ≠ 0) (htauSq0 : tau * tau ≠ 0)
    (hunit : ∀ a : R, IsUnit a ↔ residue a ≠ 0)
    (hfactor : ∀ a : R, residue a = 0 → ∃ q : R, a = q * tau) :
    Nonempty (RadicalSquareCoefficientData residue tau) := by
  let mulTau : R →ₗ[k] R :=
    { toFun := fun a ↦ a * tau
      map_add' := fun a b ↦ add_mul a b tau
      map_smul' := by
        intro c a
        rw [Algebra.smul_mul_assoc, RingHom.id_apply] }
  have hkerResidue : LinearMap.ker mulTau ≤
      LinearMap.ker residue.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change a * tau = 0 at ha
    by_contra hres
    have haUnit : IsUnit a := (hunit a).2 hres
    apply htau0
    apply haUnit.mul_left_cancel
    simpa only [mul_zero] using ha
  obtain ⟨coefficientOne, hOne⟩ :=
    exists_linearMap_comp_eq_of_ker_le mulTau residue.toLinearMap
      hkerResidue
  have hOneShift (a : R) : coefficientOne (a * tau) = residue a := by
    exact DFunLike.congr_fun hOne a
  have hkerOne : LinearMap.ker mulTau ≤
      LinearMap.ker coefficientOne := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change a * tau = 0 at ha
    have hres : residue a = 0 :=
      LinearMap.mem_ker.mp (hkerResidue (LinearMap.mem_ker.mpr ha))
    obtain ⟨q, hq⟩ := hfactor a hres
    rw [hq, hOneShift]
    by_contra hqres
    have hqUnit : IsUnit q := (hunit q).2 hqres
    apply htauSq0
    apply hqUnit.mul_left_cancel
    rw [mul_zero]
    calc
      q * (tau * tau) = (q * tau) * tau := (mul_assoc q tau tau).symm
      _ = a * tau := by rw [← hq]
      _ = 0 := ha
  obtain ⟨coefficientTwo, hTwo⟩ :=
    exists_linearMap_comp_eq_of_ker_le mulTau coefficientOne hkerOne
  refine ⟨⟨coefficientOne, coefficientTwo, hOneShift, ?_⟩⟩
  intro a
  exact DFunLike.congr_fun hTwo a

variable {C : Type x} [Category C] [Preadditive C] [Linear k C]

/-- Postcomposition by an endomorphism, as a linear map in that
endomorphism. -/
def postEndomorphismLinearMap {X Y : C} (alpha : X ⟶ Y) :
    End Y →ₗ[k] (X ⟶ Y) where
  toFun a := alpha ≫ a.asHom
  map_add' a b := by
    change alpha ≫ (a.asHom + b.asHom) = _
    rw [Preadditive.comp_add]
  map_smul' c a := by
    change alpha ≫ (c • a.asHom) = c • (alpha ≫ a.asHom)
    rw [Linear.comp_smul]

/-- Precomposition by an endomorphism, as a linear map in that
endomorphism. -/
def preEndomorphismLinearMap {Y Z : C} (beta : Y ⟶ Z) :
    End Y →ₗ[k] (Y ⟶ Z) where
  toFun a := a.asHom ≫ beta
  map_add' a b := by
    change (a.asHom + b.asHom) ≫ beta = _
    rw [Preadditive.add_comp]
  map_smul' c a := by
    change (c • a.asHom) ≫ beta = c • (a.asHom ≫ beta)
    rw [Linear.smul_comp]

/-- Compatible extensions of the middle coefficients to the two arms and
the outer composite of the Figure-13 shape. -/
structure Figure13CoefficientExtensionData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z)
    (residue : End Y →ₐ[k] k) (tau : End Y)
    (middle : RadicalSquareCoefficientData residue tau) where
  alphaZero : (X ⟶ Y) →ₗ[k] k
  alphaOne : (X ⟶ Y) →ₗ[k] k
  betaZero : (Y ⟶ Z) →ₗ[k] k
  betaOne : (Y ⟶ Z) →ₗ[k] k
  crossZero : (X ⟶ Z) →ₗ[k] k
  alphaZero_post : ∀ a : End Y,
    alphaZero (alpha ≫ a.asHom) = residue a
  alphaOne_post : ∀ a : End Y,
    alphaOne (alpha ≫ a.asHom) = middle.coefficientOne a
  betaZero_pre : ∀ a : End Y,
    betaZero (a.asHom ≫ beta) = residue a
  betaOne_pre : ∀ a : End Y,
    betaOne (a.asHom ≫ beta) = middle.coefficientOne a
  crossZero_sandwich : ∀ a : End Y,
    crossZero ((alpha ≫ a.asHom) ≫ beta) = residue a

/-- The coherent middle coefficients extend to both Figure-13 arms and the
outer composite whenever the four displayed paths survive and every
invertible middle twist of the outer composite is nonzero. -/
theorem exists_figure13CoefficientExtensionData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z)
    (residue : End Y →ₐ[k] k) (tau : End Y)
    (middle : RadicalSquareCoefficientData residue tau)
    (hunit : ∀ a : End Y, IsUnit a ↔ residue a ≠ 0)
    (hfactor : ∀ a : End Y, residue a = 0 →
      ∃ q : End Y, a = q * tau)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (halpha : alpha ≠ 0) (halphaTau : alpha ≫ tau.asHom ≠ 0)
    (hbeta : beta ≠ 0) (htauBeta : tau.asHom ≫ beta ≠ 0)
    (hcrossUnit : ∀ a : End Y, IsUnit a →
      (alpha ≫ a.asHom) ≫ beta ≠ 0) :
    Nonempty (Figure13CoefficientExtensionData
      alpha beta residue tau middle) := by
  let alphaAction := postEndomorphismLinearMap (k := k) alpha
  let betaAction := preEndomorphismLinearMap (k := k) beta
  let crossAction := LargeIndecomposable.middleEndomorphismSandwich
    (k := k) alpha beta
  have alphaKerResidue : LinearMap.ker alphaAction ≤
      LinearMap.ker residue.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change alpha ≫ a.asHom = 0 at ha
    by_contra hres
    have haUnit : IsUnit a := (hunit a).2 hres
    letI : IsIso a.asHom := (isUnit_iff_isIso a).1 haUnit
    apply halpha
    apply (cancel_mono a.asHom).1
    simpa using ha
  have alphaKerOne : LinearMap.ker alphaAction ≤
      LinearMap.ker middle.coefficientOne := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change alpha ≫ a.asHom = 0 at ha
    have hres : residue a = 0 :=
      LinearMap.mem_ker.mp
        (alphaKerResidue (LinearMap.mem_ker.mpr ha))
    obtain ⟨q, hq⟩ := hfactor a hres
    rw [hq, middle.coefficientOne_mul_tau]
    by_contra hqres
    have hqUnit : IsUnit q := (hunit q).2 hqres
    letI : IsIso q.asHom := (isUnit_iff_isIso q).1 hqUnit
    apply halphaTau
    apply (cancel_mono q.asHom).1
    have hzero : (alpha ≫ tau.asHom) ≫ q.asHom = 0 := by
      calc
        (alpha ≫ tau.asHom) ≫ q.asHom =
            alpha ≫ (q * tau).asHom := by
              rw [End.mul_def, Category.assoc]
        _ = alpha ≫ a.asHom := by rw [← hq]
        _ = 0 := ha
    simpa using hzero
  have betaKerResidue : LinearMap.ker betaAction ≤
      LinearMap.ker residue.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change a.asHom ≫ beta = 0 at ha
    by_contra hres
    have haUnit : IsUnit a := (hunit a).2 hres
    letI : IsIso a.asHom := (isUnit_iff_isIso a).1 haUnit
    apply hbeta
    apply (cancel_epi a.asHom).1
    simpa using ha
  have betaKerOne : LinearMap.ker betaAction ≤
      LinearMap.ker middle.coefficientOne := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change a.asHom ≫ beta = 0 at ha
    have hres : residue a = 0 :=
      LinearMap.mem_ker.mp
        (betaKerResidue (LinearMap.mem_ker.mpr ha))
    obtain ⟨q, hq⟩ := hfactor a hres
    rw [hq, middle.coefficientOne_mul_tau]
    by_contra hqres
    have hqUnit : IsUnit q := (hunit q).2 hqres
    letI : IsIso q.asHom := (isUnit_iff_isIso q).1 hqUnit
    apply htauBeta
    apply (cancel_epi q.asHom).1
    have hzero : q.asHom ≫ (tau.asHom ≫ beta) = 0 := by
      calc
        q.asHom ≫ (tau.asHom ≫ beta) =
            (tau * q).asHom ≫ beta := by
              rw [End.mul_def, Category.assoc]
        _ = (q * tau).asHom ≫ beta := by rw [← hcomm q]
        _ = a.asHom ≫ beta := by rw [← hq]
        _ = 0 := ha
    simpa using hzero
  have crossKerResidue : LinearMap.ker crossAction ≤
      LinearMap.ker residue.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change (alpha ≫ a.asHom) ≫ beta = 0 at ha
    by_contra hres
    exact hcrossUnit a ((hunit a).2 hres) ha
  obtain ⟨alphaZero, hAlphaZero⟩ :=
    exists_linearMap_comp_eq_of_ker_le alphaAction residue.toLinearMap
      alphaKerResidue
  obtain ⟨alphaOne, hAlphaOne⟩ :=
    exists_linearMap_comp_eq_of_ker_le alphaAction middle.coefficientOne
      alphaKerOne
  obtain ⟨betaZero, hBetaZero⟩ :=
    exists_linearMap_comp_eq_of_ker_le betaAction residue.toLinearMap
      betaKerResidue
  obtain ⟨betaOne, hBetaOne⟩ :=
    exists_linearMap_comp_eq_of_ker_le betaAction middle.coefficientOne
      betaKerOne
  obtain ⟨crossZero, hCrossZero⟩ :=
    exists_linearMap_comp_eq_of_ker_le crossAction residue.toLinearMap
      crossKerResidue
  refine ⟨⟨alphaZero, alphaOne, betaZero, betaOne, crossZero,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals intro a
  · exact DFunLike.congr_fun hAlphaZero a
  · exact DFunLike.congr_fun hAlphaOne a
  · exact DFunLike.congr_fun hBetaZero a
  · exact DFunLike.congr_fun hBetaOne a
  · exact DFunLike.congr_fun hCrossZero a

end LargeIndecomposable.ClosedZigzagTransfer
