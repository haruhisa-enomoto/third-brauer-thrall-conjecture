module

public import LargeIndecomposable.Cleaving.ClosedChains.Figure14CentralCoefficient
public import LargeIndecomposable.Cleaving.ClosedChains.CrossUniverseThinPathRetraction
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure14

@[expose] public section

/-!
# Compiling Figure-14 coefficients into a Hom-bifunctor retraction

The literal Figure-14 source is realized on four ambient objects by repeating
the two central objects at the left and right leaves:

`X --delta--> Y --lambda--> X --delta--> Y`,

with the remaining arrows `Y --first--> L` and `U --last--> X`.  Coherent
central and arm coefficients, together with the explicit off-path vanishing
conditions, give a coefficient for every ordered pair of source vertices.
The generator tables below compile these coefficients into the thin-path
retraction used by the cleaving argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalSingularFigure14

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- The repeated-center ambient realization of Figure 14. -/
def repeatedCenterDiagram
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X) :
    DiagramData (C := C) where
  c := Y
  d := X
  b := X
  cUpper := U
  dLower := L
  a := Y
  lambda := lambda
  alphaLeft := delta
  deltaUpper := last
  deltaLower := first
  alphaRight := delta

/-- The scalar coefficient attached to each ordered pair of Figure-14
vertices.  Its nonzero entries are exactly the identities, the five arrows,
the four length-two paths, and the central length-three path. -/
def repeatedCenterEndpointCoefficient
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (a b : Vertex) :
    ((repeatedCenterDiagram first delta lambda last).object a ⟶
      (repeatedCenterDiagram first delta lambda last).object b) →ₗ[k] k := by
  cases a <;> cases b
  · exact residueY.toLinearMap
  · exact central.lambdaZero
  · exact 0
  · exact 0
  · exact initialArm.betaZero
  · exact central.sigmaOne
  · exact 0
  · exact residueX.toLinearMap
  · exact 0
  · exact 0
  · exact 0
  · exact central.deltaZero
  · exact central.deltaZero
  · exact central.rhoOne
  · exact residueX.toLinearMap
  · exact 0
  · exact initialArm.crossZero
  · exact central.deltaOne
  · exact 0
  · exact suffix.alphaZero
  · exact 0
  · exact residueU.toLinearMap
  · exact 0
  · exact suffix.crossZero
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact residueL.toLinearMap
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact residueY.toLinearMap

/-- Path-indexed form of `repeatedCenterEndpointCoefficient`. -/
def repeatedCenterVertexCoefficient
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    {a b : Vertexᵒᵖ} (_p : Quiver.Path b a) :
    ((repeatedCenterDiagram first delta lambda last).object a.unop ⟶
      (repeatedCenterDiagram first delta lambda last).object b.unop) →ₗ[k] k :=
  repeatedCenterEndpointCoefficient first delta lambda last
    residueU residueX residueY residueL central initialArm suffix a.unop b.unop

omit [Preadditive C] in
@[simp]
theorem repeatedCenter_pathMap_toPath
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    {a b : Vertex} (e : a ⟶ b) :
    LinearPathCategory.pathMap
        (fun x ↦ (repeatedCenterDiagram first delta lambda last).object x.unop)
        (fun e ↦ (repeatedCenterDiagram first delta lambda last).arrow e.unop)
        (Quiver.Hom.toPath (Quiver.Hom.op e)) =
      (repeatedCenterDiagram first delta lambda last).arrow e := by
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

/-- Left whiskering by any Figure-14 generator preserves the endpoint
coefficient. -/
theorem repeatedCenterEndpointCoefficient_left_arrow
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (hsuffixDelta : suffix.betaZero = central.deltaZero)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (hYThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hXThroughYZero : ∀ (l : X ⟶ Y) (r : Y ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hUThroughXZero : ∀ (l : U ⟶ X) (r : X ⟶ U),
      residueU (End.of (l ≫ r)) = 0)
    (hYThroughLZero : ∀ (l : Y ⟶ L) (r : L ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hFirstAfterLambdaZero : ∀ g : X ⟶ L,
      initialArm.betaZero (lambda ≫ g) = 0)
    (hLambdaAfterFirstZero : ∀ g : L ⟶ X,
      central.lambdaZero (first ≫ g) = 0)
    (hSigmaThroughLZero : ∀ g : L ⟶ Y,
      central.sigmaOne (End.of (first ≫ g)) = 0)
    {a' a : Vertex} (e : a' ⟶ a) (b : Vertex)
    (g : (repeatedCenterDiagram first delta lambda last).object a ⟶
      (repeatedCenterDiagram first delta lambda last).object b) :
    repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix a' b
        ((repeatedCenterDiagram first delta lambda last).arrow e ≫ g) =
      repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix a b g := by
  cases e <;> cases b
  · change residueY (End.of (lambda ≫ g)) = 0
    exact hYThroughXZero lambda g
  · change central.lambdaZero (lambda ≫ g) = residueX (End.of g)
    exact central.lambdaZero_post (End.of g)
  · rfl
  · rfl
  · exact hFirstAfterLambdaZero g
  · change central.sigmaOne (End.of (lambda ≫ g)) = central.deltaZero g
    exact central.sigmaOne_lambda hsigma hdeltaSpan hdeltaTransit g
  · change central.deltaZero (delta ≫ g) = residueY (End.of g)
    exact central.deltaZero_post (End.of g)
  · change central.rhoOne (End.of (delta ≫ g)) = central.lambdaZero g
    exact central.rhoOne_delta hlambdaSpan hlambdaTransit g
  · change residueX (End.of (delta ≫ g)) = 0
    exact hXThroughYZero delta g
  · rfl
  · change initialArm.crossZero (delta ≫ g) = initialArm.betaZero g
    exact initialArm.crossZero_left g
  · change central.deltaOne (delta ≫ g) = central.sigmaOne (End.of g)
    exact central.deltaOne_post (End.of g)
  · rfl
  · change suffix.alphaZero (last ≫ g) = residueX (End.of g)
    exact suffix.alphaZero_post (End.of g)
  · rfl
  · change residueU (End.of (last ≫ g)) = 0
    exact hUThroughXZero last g
  · rfl
  · change suffix.crossZero (last ≫ g) = central.deltaZero g
    rw [suffix.crossZero_left, hsuffixDelta]
  · change residueY (End.of (first ≫ g)) = 0
    exact hYThroughLZero first g
  · exact hLambdaAfterFirstZero g
  · rfl
  · rfl
  · change initialArm.betaZero (first ≫ g) = residueL (End.of g)
    exact initialArm.betaZero_post (End.of g)
  · exact hSigmaThroughLZero g
  · rfl
  · change residueX (End.of (delta ≫ g)) = 0
    exact hXThroughYZero delta g
  · rfl
  · rfl
  · rfl
  · change central.deltaZero (delta ≫ g) = residueY (End.of g)
    exact central.deltaZero_post (End.of g)

/-- Right whiskering by any Figure-14 generator preserves the endpoint
coefficient. -/
theorem repeatedCenterEndpointCoefficient_right_arrow
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (hinitialDelta : initialArm.alphaZero = central.deltaZero)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (hYThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hXThroughYZero : ∀ (l : X ⟶ Y) (r : Y ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hXThroughUZero : ∀ (l : X ⟶ U) (r : U ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hLThroughYZero : ∀ (l : L ⟶ Y) (r : Y ⟶ L),
      residueL (End.of (l ≫ r)) = 0)
    (hLastBeforeLambdaZero : ∀ g : U ⟶ Y,
      suffix.alphaZero (g ≫ lambda) = 0)
    (hLambdaBeforeLastZero : ∀ g : Y ⟶ U,
      central.lambdaZero (g ≫ last) = 0)
    (hRhoThroughUZero : ∀ g : X ⟶ U,
      central.rhoOne (End.of (g ≫ last)) = 0)
    (a : Vertex) {b b' : Vertex} (e : b ⟶ b')
    (g : (repeatedCenterDiagram first delta lambda last).object a ⟶
      (repeatedCenterDiagram first delta lambda last).object b) :
    repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix a b'
        (g ≫ (repeatedCenterDiagram first delta lambda last).arrow e) =
      repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix a b g := by
  cases e <;> cases a
  · change central.lambdaZero (g ≫ lambda) = residueY (End.of g)
    exact central.lambdaZero_pre (End.of g)
  · change residueX (End.of (g ≫ lambda)) = 0
    exact hXThroughYZero g lambda
  · change central.rhoOne (End.of (g ≫ lambda)) = central.deltaZero g
    exact central.rhoOne_comp_lambda hdeltaSpan hdeltaTransit hlambdaTransit g
  · exact hLastBeforeLambdaZero g
  · rfl
  · rfl
  · change residueY (End.of (g ≫ delta)) = 0
    exact hYThroughXZero g delta
  · rfl
  · change central.deltaZero (g ≫ delta) = residueX (End.of g)
    exact central.deltaZero_pre (End.of g)
  · rfl
  · rfl
  · rfl
  · exact hLambdaBeforeLastZero g
  · change residueX (End.of (g ≫ last)) = 0
    exact hXThroughUZero g last
  · exact hRhoThroughUZero g
  · change suffix.alphaZero (g ≫ last) = residueU (End.of g)
    exact suffix.alphaZero_pre (End.of g)
  · rfl
  · rfl
  · change initialArm.betaZero (g ≫ first) = residueY (End.of g)
    exact initialArm.betaZero_pre (End.of g)
  · rfl
  · change initialArm.crossZero (g ≫ first) = central.deltaZero g
    dsimp [repeatedCenterDiagram] at g ⊢
    calc
      initialArm.crossZero (g ≫ first) = initialArm.alphaZero g :=
        initialArm.crossZero_right g
      _ = central.deltaZero g := DFunLike.congr_fun hinitialDelta g
  · rfl
  · change residueL (End.of (g ≫ first)) = 0
    exact hLThroughYZero g first
  · rfl
  · change central.sigmaOne (End.of (g ≫ delta)) = central.lambdaZero g
    exact central.sigmaOne_comp_delta hsigma hlambdaSpan
      hlambdaTransit hdeltaTransit g
  · change central.deltaZero (g ≫ delta) = residueX (End.of g)
    exact central.deltaZero_pre (End.of g)
  · change central.deltaOne (g ≫ delta) = central.rhoOne (End.of g)
    exact central.deltaOne_pre (End.of g)
  · change suffix.crossZero (g ≫ delta) = suffix.alphaZero g
    exact suffix.crossZero_right g
  · rfl
  · change residueY (End.of (g ≫ delta)) = 0
    exact hYThroughXZero g delta

/-- Iterating the left-generator table along an arbitrary Figure-14 path. -/
theorem repeatedCenterEndpointCoefficient_left_path
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (hsuffixDelta : suffix.betaZero = central.deltaZero)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (hYThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hXThroughYZero : ∀ (l : X ⟶ Y) (r : Y ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hUThroughXZero : ∀ (l : U ⟶ X) (r : X ⟶ U),
      residueU (End.of (l ≫ r)) = 0)
    (hYThroughLZero : ∀ (l : Y ⟶ L) (r : L ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hFirstAfterLambdaZero : ∀ g : X ⟶ L,
      initialArm.betaZero (lambda ≫ g) = 0)
    (hLambdaAfterFirstZero : ∀ g : L ⟶ X,
      central.lambdaZero (first ≫ g) = 0)
    (hSigmaThroughLZero : ∀ g : L ⟶ Y,
      central.sigmaOne (End.of (first ≫ g)) = 0)
    {a a' : Vertexᵒᵖ} (p : Quiver.Path a a') (b : Vertex)
    (g : (repeatedCenterDiagram first delta lambda last).object a.unop ⟶
      (repeatedCenterDiagram first delta lambda last).object b) :
    repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix
        a'.unop b
        (LinearPathCategory.pathMap
            (fun x ↦
              (repeatedCenterDiagram first delta lambda last).object x.unop)
            (fun e ↦
              (repeatedCenterDiagram first delta lambda last).arrow e.unop) p ≫ g) =
      repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix
        a.unop b g := by
  induction p with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.id_comp]
  | cons p e ih =>
      rw [LinearPathCategory.pathMap_cons, Category.assoc]
      exact (repeatedCenterEndpointCoefficient_left_arrow
        first delta lambda last residueU residueX residueY residueL
        central initialArm suffix hsuffixDelta hsigma hdeltaSpan hlambdaSpan
        hdeltaTransit hlambdaTransit hYThroughXZero hXThroughYZero
        hUThroughXZero hYThroughLZero hFirstAfterLambdaZero
        hLambdaAfterFirstZero hSigmaThroughLZero e.unop b _).trans ih

/-- Iterating the right-generator table along an arbitrary Figure-14 path. -/
theorem repeatedCenterEndpointCoefficient_right_path
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (hinitialDelta : initialArm.alphaZero = central.deltaZero)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (hYThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hXThroughYZero : ∀ (l : X ⟶ Y) (r : Y ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hXThroughUZero : ∀ (l : X ⟶ U) (r : U ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hLThroughYZero : ∀ (l : L ⟶ Y) (r : Y ⟶ L),
      residueL (End.of (l ≫ r)) = 0)
    (hLastBeforeLambdaZero : ∀ g : U ⟶ Y,
      suffix.alphaZero (g ≫ lambda) = 0)
    (hLambdaBeforeLastZero : ∀ g : Y ⟶ U,
      central.lambdaZero (g ≫ last) = 0)
    (hRhoThroughUZero : ∀ g : X ⟶ U,
      central.rhoOne (End.of (g ≫ last)) = 0)
    (a : Vertex) {b' b : Vertexᵒᵖ} (q : Quiver.Path b' b)
    (g : (repeatedCenterDiagram first delta lambda last).object a ⟶
      (repeatedCenterDiagram first delta lambda last).object b.unop) :
    repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix
        a b'.unop
        (g ≫ LinearPathCategory.pathMap
          (fun x ↦
            (repeatedCenterDiagram first delta lambda last).object x.unop)
          (fun e ↦
            (repeatedCenterDiagram first delta lambda last).arrow e.unop) q) =
      repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix
        a b.unop g := by
  induction q with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.comp_id]
  | cons q e ih =>
      rw [LinearPathCategory.pathMap_cons, ← Category.assoc]
      exact (ih (g ≫
        (repeatedCenterDiagram first delta lambda last).arrow e.unop)).trans
          (repeatedCenterEndpointCoefficient_right_arrow
            first delta lambda last residueU residueX residueY residueL
            central initialArm suffix hinitialDelta hsigma hdeltaSpan
            hlambdaSpan hdeltaTransit hlambdaTransit hYThroughXZero
            hXThroughYZero hXThroughUZero hLThroughYZero
            hLastBeforeLambdaZero hLambdaBeforeLastZero hRhoThroughUZero
            _ e.unop g)

/-- Two-sided path whiskering preserves the Figure-14 endpoint coefficient. -/
theorem repeatedCenterEndpointCoefficient_whisker
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (hinitialDelta : initialArm.alphaZero = central.deltaZero)
    (hsuffixDelta : suffix.betaZero = central.deltaZero)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (hYThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hXThroughYZero : ∀ (l : X ⟶ Y) (r : Y ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hUThroughXZero : ∀ (l : U ⟶ X) (r : X ⟶ U),
      residueU (End.of (l ≫ r)) = 0)
    (hXThroughUZero : ∀ (l : X ⟶ U) (r : U ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hYThroughLZero : ∀ (l : Y ⟶ L) (r : L ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hLThroughYZero : ∀ (l : L ⟶ Y) (r : Y ⟶ L),
      residueL (End.of (l ≫ r)) = 0)
    (hFirstAfterLambdaZero : ∀ g : X ⟶ L,
      initialArm.betaZero (lambda ≫ g) = 0)
    (hLambdaAfterFirstZero : ∀ g : L ⟶ X,
      central.lambdaZero (first ≫ g) = 0)
    (hSigmaThroughLZero : ∀ g : L ⟶ Y,
      central.sigmaOne (End.of (first ≫ g)) = 0)
    (hLastBeforeLambdaZero : ∀ g : U ⟶ Y,
      suffix.alphaZero (g ≫ lambda) = 0)
    (hLambdaBeforeLastZero : ∀ g : Y ⟶ U,
      central.lambdaZero (g ≫ last) = 0)
    (hRhoThroughUZero : ∀ g : X ⟶ U,
      central.rhoOne (End.of (g ≫ last)) = 0)
    {a' a b b' : Vertexᵒᵖ} (p : Quiver.Path a a')
    (g : (repeatedCenterDiagram first delta lambda last).object a.unop ⟶
      (repeatedCenterDiagram first delta lambda last).object b.unop)
    (q : Quiver.Path b' b) :
    repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix
        a'.unop b'.unop
        (LinearPathCategory.pathMap
            (fun x ↦
              (repeatedCenterDiagram first delta lambda last).object x.unop)
            (fun e ↦
              (repeatedCenterDiagram first delta lambda last).arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦
              (repeatedCenterDiagram first delta lambda last).object x.unop)
            (fun e ↦
              (repeatedCenterDiagram first delta lambda last).arrow e.unop) q) =
      repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix
        a.unop b.unop g := by
  rw [← Category.assoc]
  calc
    _ = repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix
        a'.unop b.unop
        (LinearPathCategory.pathMap
            (fun x ↦
              (repeatedCenterDiagram first delta lambda last).object x.unop)
            (fun e ↦
              (repeatedCenterDiagram first delta lambda last).arrow e.unop) p ≫
          g) := repeatedCenterEndpointCoefficient_right_path
            first delta lambda last residueU residueX residueY residueL
            central initialArm suffix hinitialDelta hsigma hdeltaSpan
            hlambdaSpan hdeltaTransit hlambdaTransit hYThroughXZero
            hXThroughYZero hXThroughUZero hLThroughYZero
            hLastBeforeLambdaZero hLambdaBeforeLastZero hRhoThroughUZero
            a'.unop q _
    _ = _ := repeatedCenterEndpointCoefficient_left_path
      first delta lambda last residueU residueX residueY residueL
      central initialArm suffix hsuffixDelta hsigma hdeltaSpan hlambdaSpan
      hdeltaTransit hlambdaTransit hYThroughXZero hXThroughYZero
      hUThroughXZero hYThroughLZero hFirstAfterLambdaZero
      hLambdaAfterFirstZero hSigmaThroughLZero p b.unop g

/-- The endpoint coefficient is zero whenever the corresponding Figure-14
source path type is empty. -/
theorem repeatedCenterEndpointCoefficient_eq_zero_of_isEmpty
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    {a b : Vertex}
    (hp : IsEmpty (Quiver.Path (Opposite.op b) (Opposite.op a)))
    (g : (repeatedCenterDiagram first delta lambda last).object a ⟶
      (repeatedCenterDiagram first delta lambda last).object b) :
    repeatedCenterEndpointCoefficient first delta lambda last
      residueU residueX residueY residueL central initialArm suffix a b g = 0 := by
  cases a <;> cases b
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.lambda))).elim
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.deltaLower))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.lambda)))).elim
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight))).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.lambda)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft)))).elim
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.deltaLower)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft)))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight)).comp
        ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.lambda)).comp
          (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft))))).elim
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.deltaUpper))).elim
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.deltaUpper)))).elim
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim

/-- `coefficientOrZero` for the path-indexed Figure-14 family is exactly the
endpoint coefficient. -/
theorem coefficientOrZero_repeatedCenterVertexCoefficient
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (a b : Vertex)
    (g : (repeatedCenterDiagram first delta lambda last).object a ⟶
      (repeatedCenterDiagram first delta lambda last).object b) :
    ClosedZigzagTransfer.coefficientOrZero
        (fun p : Quiver.Path (Opposite.op b) (Opposite.op a) ↦
          repeatedCenterVertexCoefficient first delta lambda last
            residueU residueX residueY residueL central initialArm suffix p) g =
      repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix a b g := by
  classical
  by_cases hp : Nonempty
      (Quiver.Path (Opposite.op b) (Opposite.op a))
  · rw [ClosedZigzagTransfer.coefficientOrZero_of_nonempty _ _ hp]
    rfl
  · have hp' : IsEmpty
        (Quiver.Path (Opposite.op b) (Opposite.op a)) :=
      not_nonempty_iff.mp hp
    rw [ClosedZigzagTransfer.coefficientOrZero_of_isEmpty _ _ hp']
    exact (repeatedCenterEndpointCoefficient_eq_zero_of_isEmpty
      first delta lambda last residueU residueX residueY residueL
      central initialArm suffix hp' g).symm

/-- Every diagonal endpoint coefficient sends the identity to one. -/
theorem repeatedCenterEndpointCoefficient_identity
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (a : Vertex) :
    repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix a a
        (𝟙 ((repeatedCenterDiagram first delta lambda last).object a)) = 1 := by
  cases a
  · change residueY (1 : End Y) = 1
    exact map_one residueY
  · change residueX (1 : End X) = 1
    exact map_one residueX
  · change residueX (1 : End X) = 1
    exact map_one residueX
  · change residueU (1 : End U) = 1
    exact map_one residueU
  · change residueL (1 : End L) = 1
    exact map_one residueL
  · change residueY (1 : End Y) = 1
    exact map_one residueY

/-- Normalization of every path follows from the left-generator table and
the six diagonal identity coefficients. -/
theorem repeatedCenterVertexCoefficient_normalized
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (hsuffixDelta : suffix.betaZero = central.deltaZero)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (hYThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hXThroughYZero : ∀ (l : X ⟶ Y) (r : Y ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hUThroughXZero : ∀ (l : U ⟶ X) (r : X ⟶ U),
      residueU (End.of (l ≫ r)) = 0)
    (hYThroughLZero : ∀ (l : Y ⟶ L) (r : L ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hFirstAfterLambdaZero : ∀ g : X ⟶ L,
      initialArm.betaZero (lambda ≫ g) = 0)
    (hLambdaAfterFirstZero : ∀ g : L ⟶ X,
      central.lambdaZero (first ≫ g) = 0)
    (hSigmaThroughLZero : ∀ g : L ⟶ Y,
      central.sigmaOne (End.of (first ≫ g)) = 0)
    {a b : Vertexᵒᵖ} (p : Quiver.Path b a) :
    repeatedCenterVertexCoefficient first delta lambda last
      residueU residueX residueY residueL central initialArm suffix p
      (LinearPathCategory.pathMap
        (fun x ↦
          (repeatedCenterDiagram first delta lambda last).object x.unop)
        (fun e ↦
          (repeatedCenterDiagram first delta lambda last).arrow e.unop) p) = 1 := by
  have hpath := repeatedCenterEndpointCoefficient_left_path
    first delta lambda last residueU residueX residueY residueL
    central initialArm suffix hsuffixDelta hsigma hdeltaSpan hlambdaSpan
    hdeltaTransit hlambdaTransit hYThroughXZero hXThroughYZero
    hUThroughXZero hYThroughLZero hFirstAfterLambdaZero
    hLambdaAfterFirstZero hSigmaThroughLZero p b.unop
    (𝟙 ((repeatedCenterDiagram first delta lambda last).object b.unop))
  exact (by
    simpa only [repeatedCenterVertexCoefficient, Category.comp_id] using
      hpath.trans (repeatedCenterEndpointCoefficient_identity
        first delta lambda last residueU residueX residueY residueL
        central initialArm suffix b.unop))

/-- The coherent endpoint functionals compile into the complete thin-path
coefficient package for the repeated-center Figure-14 source. -/
def repeatedCenterThinPathCoefficientData
    {U X Y L : C} (first : Y ⟶ L) (delta : X ⟶ Y)
    (lambda : Y ⟶ X) (last : U ⟶ X)
    (residueU : End U →ₐ[k] k) (residueX : End X →ₐ[k] k)
    (residueY : End Y →ₐ[k] k) (residueL : End L →ₐ[k] k)
    {sigma : End Y}
    (central : Figure14CentralCoefficientData
      delta lambda residueX residueY sigma)
    (initialArm : Figure14ArmCoefficientData
      delta first residueX residueY residueL)
    (suffix : Figure14ArmCoefficientData
      last delta residueU residueX residueY)
    (hinitialDelta : initialArm.alphaZero = central.deltaZero)
    (hsuffixDelta : suffix.betaZero = central.deltaZero)
    (hsigma : sigma.asHom = lambda ≫ delta)
    (hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤)
    (hlambdaSpan : twoSidedEndomorphismSpan k lambda = ⊤)
    (hdeltaTransit : LargeIndecomposable.AllowsTransit delta)
    (hlambdaTransit : LargeIndecomposable.AllowsTransit lambda)
    (hYThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hXThroughYZero : ∀ (l : X ⟶ Y) (r : Y ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hUThroughXZero : ∀ (l : U ⟶ X) (r : X ⟶ U),
      residueU (End.of (l ≫ r)) = 0)
    (hXThroughUZero : ∀ (l : X ⟶ U) (r : U ⟶ X),
      residueX (End.of (l ≫ r)) = 0)
    (hYThroughLZero : ∀ (l : Y ⟶ L) (r : L ⟶ Y),
      residueY (End.of (l ≫ r)) = 0)
    (hLThroughYZero : ∀ (l : L ⟶ Y) (r : Y ⟶ L),
      residueL (End.of (l ≫ r)) = 0)
    (hFirstAfterLambdaZero : ∀ g : X ⟶ L,
      initialArm.betaZero (lambda ≫ g) = 0)
    (hLambdaAfterFirstZero : ∀ g : L ⟶ X,
      central.lambdaZero (first ≫ g) = 0)
    (hSigmaThroughLZero : ∀ g : L ⟶ Y,
      central.sigmaOne (End.of (first ≫ g)) = 0)
    (hLastBeforeLambdaZero : ∀ g : U ⟶ Y,
      suffix.alphaZero (g ≫ lambda) = 0)
    (hLambdaBeforeLastZero : ∀ g : Y ⟶ U,
      central.lambdaZero (g ≫ last) = 0)
    (hRhoThroughUZero : ∀ g : X ⟶ U,
      central.rhoOne (End.of (g ≫ last)) = 0) :
    ThinPathCoefficientData (k := k)
      ((repeatedCenterDiagram first delta lambda last).functor (k := k)) where
  path_subsingleton := path_subsingleton
  coefficient := fun p ↦
    repeatedCenterVertexCoefficient first delta lambda last
      residueU residueX residueY residueL central initialArm suffix p
  normalized := by
    intro A B p
    unfold DiagramData.functor
    rw [LinearPathCategory.lift_map_pathHom]
    change repeatedCenterVertexCoefficient first delta lambda last
      residueU residueX residueY residueL central initialArm suffix p
      (LinearPathCategory.pathMap
        (fun x ↦
          (repeatedCenterDiagram first delta lambda last).object x.unop)
        (fun e ↦
          (repeatedCenterDiagram first delta lambda last).arrow e.unop) p) = 1
    exact repeatedCenterVertexCoefficient_normalized
      first delta lambda last residueU residueX residueY residueL
      central initialArm suffix hsuffixDelta hsigma hdeltaSpan hlambdaSpan
      hdeltaTransit hlambdaTransit hYThroughXZero hXThroughYZero
      hUThroughXZero hYThroughLZero hFirstAfterLambdaZero
      hLambdaAfterFirstZero hSigmaThroughLZero p
  whisker_coefficient := by
    intro A' A B B' p g q r
    unfold DiagramData.functor at g ⊢
    change (repeatedCenterDiagram first delta lambda last).object
        (LinearPathCategory.vertex A).unop ⟶
      (repeatedCenterDiagram first delta lambda last).object
        (LinearPathCategory.vertex B).unop at g
    rw [LinearPathCategory.lift_map_pathHom,
      LinearPathCategory.lift_map_pathHom]
    change repeatedCenterEndpointCoefficient first delta lambda last
        residueU residueX residueY residueL central initialArm suffix
        (LinearPathCategory.vertex A').unop
        (LinearPathCategory.vertex B').unop
        (LinearPathCategory.pathMap
            (fun x ↦
              (repeatedCenterDiagram first delta lambda last).object x.unop)
            (fun e ↦
              (repeatedCenterDiagram first delta lambda last).arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦
              (repeatedCenterDiagram first delta lambda last).object x.unop)
            (fun e ↦
              (repeatedCenterDiagram first delta lambda last).arrow e.unop) q) =
      ClosedZigzagTransfer.coefficientOrZero
        (fun s : Quiver.Path (LinearPathCategory.vertex B)
            (LinearPathCategory.vertex A) ↦
          repeatedCenterVertexCoefficient first delta lambda last
            residueU residueX residueY residueL central initialArm suffix s) g
    calc
      _ = repeatedCenterEndpointCoefficient first delta lambda last
          residueU residueX residueY residueL central initialArm suffix
          (LinearPathCategory.vertex A).unop
          (LinearPathCategory.vertex B).unop g :=
        repeatedCenterEndpointCoefficient_whisker
          first delta lambda last residueU residueX residueY residueL
          central initialArm suffix hinitialDelta hsuffixDelta hsigma
          hdeltaSpan hlambdaSpan hdeltaTransit hlambdaTransit
          hYThroughXZero hXThroughYZero hUThroughXZero hXThroughUZero
          hYThroughLZero hLThroughYZero hFirstAfterLambdaZero
          hLambdaAfterFirstZero hSigmaThroughLZero hLastBeforeLambdaZero
          hLambdaBeforeLastZero hRhoThroughUZero p g q
      _ = _ := (coefficientOrZero_repeatedCenterVertexCoefficient
        first delta lambda last residueU residueX residueY residueL
        central initialArm suffix (LinearPathCategory.vertex A).unop
        (LinearPathCategory.vertex B).unop g).symm

end LargeIndecomposable.CriticalSingularFigure14
