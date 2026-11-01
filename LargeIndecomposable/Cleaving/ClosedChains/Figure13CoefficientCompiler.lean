module

public import LargeIndecomposable.Cleaving.ClosedChains.Figure13Coefficient
public import LargeIndecomposable.Cleaving.ClosedChains.CrossUniverseThinPathRetraction
public import LargeIndecomposable.Cleaving.ClosedChains.RadicalPowerParameter
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.RoiterFigure13D

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.RoiterFigure13D

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u v w z t

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- A linear functor carries a principal two-sided endomorphism span into
the span of the mapped generator. -/
theorem linearFunctor_map_mem_twoSidedEndomorphismSpan
    {D : Type z} [Category.{t} D] [Preadditive D] [Linear k D]
    (F : C ⥤ D) [F.Additive] [F.Linear k]
    {X Y : C} {a generator : X ⟶ Y}
    (ha : a ∈ twoSidedEndomorphismSpan k generator) :
    F.map a ∈ twoSidedEndomorphismSpan k (F.map generator) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      rcases ha with ⟨c, d, rfl⟩
      apply Submodule.subset_span
      refine ⟨End.of (F.map c.asHom), End.of (F.map d.asHom), ?_⟩
      simp only [Functor.map_comp]
  | zero => simp
  | add a b _ _ ha hb =>
      rw [F.map_add]
      exact (twoSidedEndomorphismSpan k (F.map generator)).add_mem ha hb
  | smul c a _ ha =>
      rw [F.map_smul]
      exact (twoSidedEndomorphismSpan k
        (F.map generator)).smul_mem c ha

/-- The first coherent middle coefficient vanishes on the square of the
local radical. -/
theorem RadicalSquareCoefficientData.coefficientOne_eq_zero_of_mem_jacobson_sq
    [IsAlgClosed k] {Y : C} [Module.Finite k (End Y)]
    [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue P.tau)
    (hresTau : residue P.tau = 0)
    (a : End Y) (haSq : a ∈ (Ring.jacobson (End Y)) ^ 2) :
    middle.coefficientOne a = 0 := by
  by_cases ha0 : a = 0
  · subst a
    exact middle.coefficientOne.map_zero
  have haJ : a ∈ Ring.jacobson (End Y) :=
    (Ideal.pow_le_self (R := End Y) (by omega)) haSq
  obtain ⟨n, hn, e, he, hae⟩ := P.transitData.factors a haJ ha0
  have hn2 : 2 ≤ n :=
    P.two_le_transitExponent_of_mem_sq haSq ha0 n hn e he hae
  have haRing : a = e * P.tau ^ n := by
    apply End.ext
    simpa only [End.mul_def] using hae
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hpow : P.tau ^ n = P.tau ^ (n - 1) * P.tau := by
    conv_lhs => rw [← hnEq]
    exact pow_succ P.tau (n - 1)
  have haFactor : a = (e * P.tau ^ (n - 1)) * P.tau := by
    rw [haRing, hpow, mul_assoc]
  have hnsub : n - 1 ≠ 0 := by omega
  rw [haFactor, middle.coefficientOne_mul_tau, map_mul, map_pow,
    hresTau, zero_pow hnsub, mul_zero]

/-- A Figure-13 diagram whose three middle occurrences are realized by one
object and whose two vertical arrows are realized by one endomorphism. -/
def repeatedMiddleDiagram
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y) :
    DiagramData (C := C) where
  center := Y
  leftLeaf := X
  upperLeaf := Y
  lowerLeaf := Y
  rightLeaf := Z
  alpha := alpha
  tauUpper := tau.asHom
  tauLower := tau.asHom
  beta := beta

def leftIdentityCoefficient
    {X Y Z : C} {alpha : X ⟶ Y} {beta : Y ⟶ Z} {tau : End Y}
    {residue : End Y →ₐ[k] k}
    {middle : RadicalSquareCoefficientData residue tau}
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle) :
    End X →ₗ[k] k :=
  extension.alphaZero.comp (preEndomorphismLinearMap (k := k) alpha)

def rightIdentityCoefficient
    {X Y Z : C} {alpha : X ⟶ Y} {beta : Y ⟶ Z} {tau : End Y}
    {residue : End Y →ₐ[k] k}
    {middle : RadicalSquareCoefficientData residue tau}
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle) :
    End Z →ₗ[k] k :=
  extension.betaZero.comp (postEndomorphismLinearMap (k := k) beta)

/-- The coefficient map attached to every ordered pair of Figure-13
vertices.  Pairs not joined by a source path receive zero. -/
def repeatedMiddleEndpointCoefficient
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    (a b : Vertex) :
    ((repeatedMiddleDiagram alpha beta tau).object a ⟶
      (repeatedMiddleDiagram alpha beta tau).object b) →ₗ[k] k := by
  cases a <;> cases b
  · exact residue.toLinearMap
  · exact 0
  · exact 0
  · exact middle.coefficientOne
  · exact extension.betaZero
  · exact extension.alphaZero
  · exact leftIdentityCoefficient extension
  · exact 0
  · exact extension.alphaOne
  · exact extension.crossZero
  · exact middle.coefficientOne
  · exact 0
  · exact residue.toLinearMap
  · exact middle.coefficientTwo
  · exact extension.betaOne
  · exact 0
  · exact 0
  · exact 0
  · exact residue.toLinearMap
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact rightIdentityCoefficient extension

/-- Path-indexed form of `repeatedMiddleEndpointCoefficient`. -/
def repeatedMiddleVertexCoefficient
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    {a b : Vertexᵒᵖ} (_p : Quiver.Path b a) :
    ((repeatedMiddleDiagram alpha beta tau).object a.unop ⟶
      (repeatedMiddleDiagram alpha beta tau).object b.unop) →ₗ[k] k :=
  repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
    a.unop b.unop

omit [Preadditive C] in
@[simp]
theorem repeatedMiddle_pathMap_toPath
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    {a b : Vertex} (e : a ⟶ b) :
    LinearPathCategory.pathMap
        (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
        (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop)
        (Quiver.Hom.toPath (Quiver.Hom.op e)) =
      (repeatedMiddleDiagram alpha beta tau).arrow e := by
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

/-- Left whiskering by any Figure-13 generator preserves the endpoint
coefficient, including the zero coefficients on impossible source pairs. -/
theorem repeatedMiddleEndpointCoefficient_left_arrow
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    {a' a : Vertex} (e : a' ⟶ a) (b : Vertex)
    (g : (repeatedMiddleDiagram alpha beta tau).object a ⟶
      (repeatedMiddleDiagram alpha beta tau).object b) :
    repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a' b ((repeatedMiddleDiagram alpha beta tau).arrow e ≫ g) =
      repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a b g := by
  cases e <;> cases b
  · change extension.alphaZero (alpha ≫ g) = residue (End.of g)
    exact extension.alphaZero_post (End.of g)
  · change leftIdentityCoefficient extension (alpha ≫ g) = 0
    change extension.alphaZero ((alpha ≫ g) ≫ alpha) = 0
    calc
      extension.alphaZero ((alpha ≫ g) ≫ alpha) =
          residue (End.of (g ≫ alpha)) := by
        rw [Category.assoc]
        exact extension.alphaZero_post (End.of (g ≫ alpha))
      _ = 0 := hThroughXZero g alpha
  · rfl
  · change extension.alphaOne (alpha ≫ g) = middle.coefficientOne (End.of g)
    exact extension.alphaOne_post (End.of g)
  · rcases hBetaFactor g with ⟨q, hq⟩
    rw [hq]
    change extension.crossZero (alpha ≫ (q.asHom ≫ beta)) =
      extension.betaZero (q.asHom ≫ beta)
    rw [← Category.assoc, extension.crossZero_sandwich,
      extension.betaZero_pre]
  · change middle.coefficientOne (End.of (tau.asHom ≫ g)) = residue (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientOne (End.of g * tau) = residue (End.of g)
    exact middle.coefficientOne_mul_tau (End.of g)
  · rfl
  · change residue (End.of (tau.asHom ≫ g)) = 0
    change Y ⟶ Y at g
    change residue (End.of g * tau) = 0
    rw [map_mul, hresTau, mul_zero]
  · change middle.coefficientTwo (End.of (tau.asHom ≫ g)) =
      middle.coefficientOne (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientTwo (End.of g * tau) =
      middle.coefficientOne (End.of g)
    exact middle.coefficientTwo_mul_tau (End.of g)
  · rcases hBetaFactor g with ⟨q, hq⟩
    rw [hq]
    change extension.betaOne (tau.asHom ≫ (q.asHom ≫ beta)) =
      extension.betaZero (q.asHom ≫ beta)
    rw [← Category.assoc]
    change extension.betaOne ((q * tau).asHom ≫ beta) =
      extension.betaZero (q.asHom ≫ beta)
    rw [extension.betaOne_pre, extension.betaZero_pre,
      middle.coefficientOne_mul_tau]
  · change residue (End.of (tau.asHom ≫ g)) = 0
    change Y ⟶ Y at g
    change residue (End.of g * tau) = 0
    rw [map_mul, hresTau, mul_zero]
  · rfl
  · rfl
  · change middle.coefficientOne (End.of (tau.asHom ≫ g)) = residue (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientOne (End.of g * tau) = residue (End.of g)
    exact middle.coefficientOne_mul_tau (End.of g)
  · rcases hBetaFactor g with ⟨q, hq⟩
    rw [hq]
    change extension.betaZero (tau.asHom ≫ (q.asHom ≫ beta)) = 0
    rw [← Category.assoc]
    change extension.betaZero ((q * tau).asHom ≫ beta) = 0
    rw [extension.betaZero_pre, map_mul, hresTau, mul_zero]
  · change residue (End.of (beta ≫ g)) = 0
    exact hThroughZZero beta g
  · rfl
  · rfl
  · change middle.coefficientOne (End.of (beta ≫ g)) = 0
    exact hThroughZOne beta g
  · rfl

/-- Right whiskering by any Figure-13 generator preserves the endpoint
coefficient, again including impossible source pairs. -/
theorem repeatedMiddleEndpointCoefficient_right_arrow
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (a : Vertex) {b b' : Vertex} (e : b ⟶ b')
    (g : (repeatedMiddleDiagram alpha beta tau).object a ⟶
      (repeatedMiddleDiagram alpha beta tau).object b) :
    repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a b' (g ≫ (repeatedMiddleDiagram alpha beta tau).arrow e) =
      repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a b g := by
  cases e <;> cases a
  · change residue (End.of (g ≫ alpha)) = 0
    exact hThroughXZero g alpha
  · rfl
  · change middle.coefficientOne (End.of (g ≫ alpha)) = 0
    exact hThroughXOne g alpha
  · rfl
  · rfl
  · change residue (End.of (g ≫ tau.asHom)) = 0
    change Y ⟶ Y at g
    change residue (tau * End.of g) = 0
    rw [← hcomm (End.of g), map_mul, hresTau, mul_zero]
  · rcases hAlphaFactor g with ⟨q, hq⟩
    rw [hq]
    change extension.alphaZero ((alpha ≫ q.asHom) ≫ tau.asHom) = 0
    rw [Category.assoc]
    change extension.alphaZero (alpha ≫ (tau * q).asHom) = 0
    rw [← hcomm q, extension.alphaZero_post, map_mul, hresTau, mul_zero]
  · change middle.coefficientOne (End.of (g ≫ tau.asHom)) = residue (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientOne (tau * End.of g) = residue (End.of g)
    rw [← hcomm (End.of g)]
    exact middle.coefficientOne_mul_tau (End.of g)
  · rfl
  · rfl
  · change middle.coefficientOne (End.of (g ≫ tau.asHom)) = residue (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientOne (tau * End.of g) = residue (End.of g)
    rw [← hcomm (End.of g)]
    exact middle.coefficientOne_mul_tau (End.of g)
  · rcases hAlphaFactor g with ⟨q, hq⟩
    rw [hq]
    change extension.alphaOne ((alpha ≫ q.asHom) ≫ tau.asHom) =
      extension.alphaZero (alpha ≫ q.asHom)
    rw [Category.assoc]
    change extension.alphaOne (alpha ≫ (tau * q).asHom) =
      extension.alphaZero (alpha ≫ q.asHom)
    rw [← hcomm q, extension.alphaOne_post,
      extension.alphaZero_post, middle.coefficientOne_mul_tau]
  · change middle.coefficientTwo (End.of (g ≫ tau.asHom)) =
      middle.coefficientOne (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientTwo (tau * End.of g) =
      middle.coefficientOne (End.of g)
    rw [← hcomm (End.of g)]
    exact middle.coefficientTwo_mul_tau (End.of g)
  · change residue (End.of (g ≫ tau.asHom)) = 0
    change Y ⟶ Y at g
    change residue (tau * End.of g) = 0
    rw [← hcomm (End.of g), map_mul, hresTau, mul_zero]
  · rfl
  · change extension.betaZero (g ≫ beta) = residue (End.of g)
    exact extension.betaZero_pre (End.of g)
  · rcases hAlphaFactor g with ⟨q, hq⟩
    rw [hq]
    change extension.crossZero ((alpha ≫ q.asHom) ≫ beta) =
      extension.alphaZero (alpha ≫ q.asHom)
    rw [extension.crossZero_sandwich, extension.alphaZero_post]
  · change extension.betaOne (g ≫ beta) = middle.coefficientOne (End.of g)
    exact extension.betaOne_pre (End.of g)
  · rfl
  · change rightIdentityCoefficient extension (g ≫ beta) = 0
    change extension.betaZero (beta ≫ (g ≫ beta)) = 0
    rw [← Category.assoc]
    calc
      extension.betaZero ((beta ≫ g) ≫ beta) =
          residue (End.of (beta ≫ g)) := by
        exact extension.betaZero_pre (End.of (beta ≫ g))
      _ = 0 := hThroughZZero beta g

/-- Iterating the left-generator table along an arbitrary source path. -/
theorem repeatedMiddleEndpointCoefficient_left_path
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    {a a' : Vertexᵒᵖ} (p : Quiver.Path a a')
    (b : Vertex)
    (g : (repeatedMiddleDiagram alpha beta tau).object a.unop ⟶
      (repeatedMiddleDiagram alpha beta tau).object b) :
    repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a'.unop b
        (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) p ≫ g) =
      repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a.unop b g := by
  induction p with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.id_comp]
  | cons p e ih =>
      rw [LinearPathCategory.pathMap_cons, Category.assoc]
      exact (repeatedMiddleEndpointCoefficient_left_arrow
        alpha beta tau residue middle extension hresTau hBetaFactor
        hThroughXZero hThroughZZero hThroughZOne e.unop b _).trans
          ih

/-- Iterating the right-generator table along an arbitrary source path. -/
theorem repeatedMiddleEndpointCoefficient_right_path
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (a : Vertex) {b' b : Vertexᵒᵖ}
    (q : Quiver.Path b' b)
    (g : (repeatedMiddleDiagram alpha beta tau).object a ⟶
      (repeatedMiddleDiagram alpha beta tau).object b.unop) :
    repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a b'.unop
        (g ≫ LinearPathCategory.pathMap
          (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
          (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) q) =
      repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a b.unop g := by
  induction q with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.comp_id]
  | cons q e ih =>
      rw [LinearPathCategory.pathMap_cons, ← Category.assoc]
      exact (ih (g ≫
        (repeatedMiddleDiagram alpha beta tau).arrow e.unop)).trans
          (repeatedMiddleEndpointCoefficient_right_arrow
            alpha beta tau residue middle extension hresTau hcomm
            hAlphaFactor hThroughXZero hThroughXOne hThroughZZero
            _ e.unop g)

/-- Two-sided path whiskering preserves the endpoint coefficient. -/
theorem repeatedMiddleEndpointCoefficient_whisker
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    {a' a b b' : Vertexᵒᵖ}
    (p : Quiver.Path a a')
    (g : (repeatedMiddleDiagram alpha beta tau).object a.unop ⟶
      (repeatedMiddleDiagram alpha beta tau).object b.unop)
    (q : Quiver.Path b' b) :
    repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a'.unop b'.unop
        (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) q) =
      repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a.unop b.unop g := by
  rw [← Category.assoc]
  calc
    _ = repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a'.unop b.unop
        (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) p ≫
          g) := repeatedMiddleEndpointCoefficient_right_path
            alpha beta tau residue middle extension hresTau hcomm
            hAlphaFactor hThroughXZero hThroughXOne hThroughZZero a'.unop q _
    _ = _ := repeatedMiddleEndpointCoefficient_left_path
      alpha beta tau residue middle extension hresTau hBetaFactor
      hThroughXZero hThroughZZero hThroughZOne p b.unop g

/-- The endpoint coefficient is zero whenever the corresponding Figure-13
source path type is empty. -/
theorem repeatedMiddleEndpointCoefficient_eq_zero_of_isEmpty
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    {a b : Vertex}
    (hp : IsEmpty (Quiver.Path (Opposite.op b) (Opposite.op a)))
    (g : (repeatedMiddleDiagram alpha beta tau).object a ⟶
      (repeatedMiddleDiagram alpha beta tau).object b) :
    repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
      a b g = 0 := by
  cases a <;> cases b
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower))).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.beta))).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alpha))).elim
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alpha)))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.beta)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alpha)))).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper))).elim
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper)))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.beta)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper)))).elim
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim

/-- `coefficientOrZero` for the path-indexed family is exactly the endpoint
coefficient, whether or not a source path exists. -/
theorem coefficientOrZero_repeatedMiddleVertexCoefficient
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    (a b : Vertex)
    (g : (repeatedMiddleDiagram alpha beta tau).object a ⟶
      (repeatedMiddleDiagram alpha beta tau).object b) :
    ClosedZigzagTransfer.coefficientOrZero
        (fun p : Quiver.Path (Opposite.op b) (Opposite.op a) ↦
          repeatedMiddleVertexCoefficient alpha beta tau residue middle
            extension p) g =
      repeatedMiddleEndpointCoefficient alpha beta tau residue middle extension
        a b g := by
  classical
  by_cases hp : Nonempty
      (Quiver.Path (Opposite.op b) (Opposite.op a))
  · rw [ClosedZigzagTransfer.coefficientOrZero_of_nonempty _ _ hp]
    rfl
  · have hp' : IsEmpty
        (Quiver.Path (Opposite.op b) (Opposite.op a)) :=
      not_nonempty_iff.mp hp
    rw [ClosedZigzagTransfer.coefficientOrZero_of_isEmpty _ _ hp']
    exact (repeatedMiddleEndpointCoefficient_eq_zero_of_isEmpty
      alpha beta tau residue middle extension hp' g).symm

private theorem false_of_path_length_zero
    {a b : Vertexᵒᵖ} (p : Quiver.Path a b) (h : p.length = 0)
    (hne : a ≠ b) : False :=
  hne (p.eq_of_length_zero h)

/-- The vertex-indexed coefficient is normalized on every Figure-13 path. -/
theorem repeatedMiddleVertexCoefficient_normalized
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    {a b : Vertexᵒᵖ} (p : Quiver.Path b a) :
    repeatedMiddleVertexCoefficient alpha beta tau residue middle extension p
      (LinearPathCategory.pathMap
        (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
        (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) p) = 1 := by
  induction a using Opposite.rec
  rename_i a
  induction b using Opposite.rec
  rename_i b
  cases a <;> cases b
  · rw [(path_subsingleton _ _).elim p Quiver.Path.nil]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_nil]
    change residue (1 : End Y) = 1
    exact map_one residue
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_source_left p) (by simp))
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_source_upper p) (by simp))
  · rw [(path_subsingleton _ _).elim p
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower))]
    simp only [repeatedMiddleVertexCoefficient,
      repeatedMiddle_pathMap_toPath]
    change middle.coefficientOne tau = 1
    calc
      middle.coefficientOne tau = residue 1 := by
        simpa using middle.coefficientOne_mul_tau 1
      _ = 1 := map_one residue
  · rw [(path_subsingleton _ _).elim p
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.beta))]
    simp only [repeatedMiddleVertexCoefficient,
      repeatedMiddle_pathMap_toPath]
    change extension.betaZero beta = 1
    calc
      extension.betaZero beta = residue 1 := by
        simpa using extension.betaZero_pre 1
      _ = 1 := map_one residue
  · rw [(path_subsingleton _ _).elim p
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alpha))]
    simp only [repeatedMiddleVertexCoefficient,
      repeatedMiddle_pathMap_toPath]
    change extension.alphaZero alpha = 1
    calc
      extension.alphaZero alpha = residue 1 := by
        simpa using extension.alphaZero_post 1
      _ = 1 := map_one residue
  · rw [(path_subsingleton _ _).elim p Quiver.Path.nil]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_nil]
    change extension.alphaZero ((1 : End X).asHom ≫ alpha) = 1
    calc
      extension.alphaZero ((1 : End X).asHom ≫ alpha) =
          residue 1 := by simpa using extension.alphaZero_post 1
      _ = 1 := map_one residue
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_source_upper p) (by simp))
  · rw [(path_subsingleton _ _).elim p
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alpha)))]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_comp, repeatedMiddle_pathMap_toPath]
    change extension.alphaOne (alpha ≫ tau.asHom) = 1
    calc
      extension.alphaOne (alpha ≫ tau.asHom) =
          middle.coefficientOne tau := extension.alphaOne_post tau
      _ = residue 1 := by
        simpa using middle.coefficientOne_mul_tau 1
      _ = 1 := map_one residue
  · rw [(path_subsingleton _ _).elim p
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.beta)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alpha)))]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_comp, repeatedMiddle_pathMap_toPath]
    change extension.crossZero (alpha ≫ beta) = 1
    calc
      extension.crossZero (alpha ≫ beta) = residue 1 := by
        simpa using extension.crossZero_sandwich 1
      _ = 1 := map_one residue
  · rw [(path_subsingleton _ _).elim p
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper))]
    simp only [repeatedMiddleVertexCoefficient,
      repeatedMiddle_pathMap_toPath]
    change middle.coefficientOne tau = 1
    calc
      middle.coefficientOne tau = residue 1 := by
        simpa using middle.coefficientOne_mul_tau 1
      _ = 1 := map_one residue
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_source_left p) (by simp))
  · rw [(path_subsingleton _ _).elim p Quiver.Path.nil]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_nil]
    change residue (1 : End Y) = 1
    exact map_one residue
  · rw [(path_subsingleton _ _).elim p
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper)))]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_comp, repeatedMiddle_pathMap_toPath]
    change middle.coefficientTwo (tau * tau) = 1
    calc
      middle.coefficientTwo (tau * tau) = middle.coefficientOne tau :=
        middle.coefficientTwo_mul_tau tau
      _ = residue 1 := by
        simpa using middle.coefficientOne_mul_tau 1
      _ = 1 := map_one residue
  · rw [(path_subsingleton _ _).elim p
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.beta)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper)))]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_comp, repeatedMiddle_pathMap_toPath]
    change extension.betaOne (tau.asHom ≫ beta) = 1
    calc
      extension.betaOne (tau.asHom ≫ beta) =
          middle.coefficientOne tau := extension.betaOne_pre tau
      _ = residue 1 := by
        simpa using middle.coefficientOne_mul_tau 1
      _ = 1 := map_one residue
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_target_lower p) (by simp))
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_target_lower p) (by simp))
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_target_lower p) (by simp))
  · rw [(path_subsingleton _ _).elim p Quiver.Path.nil]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_nil]
    change residue (1 : End Y) = 1
    exact map_one residue
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_target_lower p) (by simp))
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_target_right p) (by simp))
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_target_right p) (by simp))
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_target_right p) (by simp))
  · exact False.elim (false_of_path_length_zero p
      (path_length_zero_of_target_right p) (by simp))
  · rw [(path_subsingleton _ _).elim p Quiver.Path.nil]
    simp only [repeatedMiddleVertexCoefficient,
      LinearPathCategory.pathMap_nil]
    change extension.betaZero (beta ≫ (1 : End Z).asHom) = 1
    calc
      extension.betaZero (beta ≫ (1 : End Z).asHom) = residue 1 := by
        simpa using extension.betaZero_pre 1
      _ = 1 := map_one residue

/-- The coherent endpoint functionals compile into the complete thin-path
coefficient package for the repeated-middle Figure-13 source. -/
def repeatedMiddleThinPathCoefficientData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (extension : Figure13CoefficientExtensionData
      alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0) :
    ThinPathCoefficientData (k := k)
      ((repeatedMiddleDiagram alpha beta tau).functor (k := k)) where
  path_subsingleton := path_subsingleton
  coefficient := fun p ↦
    repeatedMiddleVertexCoefficient alpha beta tau residue middle extension p
  normalized := by
    intro U V p
    unfold DiagramData.functor
    rw [LinearPathCategory.lift_map_pathHom]
    change repeatedMiddleVertexCoefficient alpha beta tau residue middle
      extension p
      (LinearPathCategory.pathMap
        (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
        (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) p) = 1
    exact repeatedMiddleVertexCoefficient_normalized
      alpha beta tau residue middle extension p
  whisker_coefficient := by
    intro U' U V V' p g q r
    unfold DiagramData.functor at g ⊢
    change (repeatedMiddleDiagram alpha beta tau).object
        (LinearPathCategory.vertex U).unop ⟶
      (repeatedMiddleDiagram alpha beta tau).object
        (LinearPathCategory.vertex V).unop at g
    rw [LinearPathCategory.lift_map_pathHom,
      LinearPathCategory.lift_map_pathHom]
    change repeatedMiddleEndpointCoefficient
        alpha beta tau residue middle extension
        (LinearPathCategory.vertex U').unop
        (LinearPathCategory.vertex V').unop
        (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau).arrow e.unop) q) =
      ClosedZigzagTransfer.coefficientOrZero
        (fun s : Quiver.Path (LinearPathCategory.vertex V)
            (LinearPathCategory.vertex U) ↦
          repeatedMiddleVertexCoefficient alpha beta tau residue middle
            extension s) g
    calc
      _ = repeatedMiddleEndpointCoefficient
          alpha beta tau residue middle extension
          (LinearPathCategory.vertex U).unop
          (LinearPathCategory.vertex V).unop g :=
        repeatedMiddleEndpointCoefficient_whisker
          alpha beta tau residue middle extension hresTau hcomm
          hAlphaFactor hBetaFactor hThroughXZero hThroughXOne
          hThroughZZero hThroughZOne p g q
      _ = _ := (coefficientOrZero_repeatedMiddleVertexCoefficient
        alpha beta tau residue middle extension
        (LinearPathCategory.vertex U).unop
        (LinearPathCategory.vertex V).unop g).symm

end LargeIndecomposable.RoiterFigure13D
