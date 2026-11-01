module

public import LargeIndecomposable.Cleaving.ClosedChains.CrossUniverseThinPathRetraction
public import LargeIndecomposable.Cleaving.ClosedChains.Figure13ESupplementCompiler
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure16

@[expose] public section

/-!
# Endpoint coefficient compiler for BGRS Figure 16

The literal Figure-16 source has six occurrences but may be realized on only
three ambient objects.  Consequently its scalar projection must remember
source occurrences, not merely ambient endpoints.  This file records the
thirteen supported entries of that projection: six identities, five arrows,
and the two lower-branch paths through the central arrow.

Once the finite table is compatible with left and right whiskering by the
five displayed arrows, thinness extends those equations to arbitrary paths
and produces the Hom-bifunctor retraction used by the cleaving argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalSingularFigure16

open LargeIndecomposable.ClosedZigzagCrossUniverse
open LargeIndecomposable.ClosedZigzagTransfer

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- A normalized coefficient on one branch--`tau` path which kills the full
left-arm supplement obstruction. -/
structure SupplementCoefficientData
    {B M : C} (branch : B ⟶ M) (tau : End M) where
  coefficient : (B ⟶ M) →ₗ[k] k
  normalized : coefficient (branch ≫ tau.asHom) = 1
  obstruction_le_ker :
    LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) branch tau ≤
      LinearMap.ker coefficient

/-- Linear separation constructs a normalized branch--`tau` coefficient
from the exact left-arm supplement nonmembership. -/
theorem nonempty_supplementCoefficientData
    {B M : C} (branch : B ⟶ M) (tau : End M)
    (hlanding : branch ≫ tau.asHom ∉
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) branch tau) :
    Nonempty (SupplementCoefficientData (k := k) branch tau) := by
  obtain ⟨coefficient, hnormalized, hker⟩ :=
    LargeIndecomposable.ClosedZigzagTransfer.exists_normalized_coefficient_killing
      _ _ hlanding
  exact ⟨⟨coefficient, hnormalized, hker⟩⟩

namespace SupplementCoefficientData

variable {B M : C} {branch : B ⟶ M} {tau : End M}

/-- A branch supplement coefficient vanishes on every prescribed
obstruction term. -/
theorem coefficient_eq_zero_of_mem
    (h : SupplementCoefficientData (k := k) branch tau)
    {g : B ⟶ M}
    (hg : g ∈
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) branch tau) :
    h.coefficient g = 0 := h.obstruction_le_ker hg

/-- Its kernel contains the endpoint-radical submodule of the landing
branch--`tau` path. -/
theorem endpointRadical_le_ker
    (h : SupplementCoefficientData (k := k) branch tau) :
    LargeIndecomposable.ClosedZigzagTransfer.endpointRadicalSubmodule
        (k := k) (branch ≫ tau.asHom) ≤
      LinearMap.ker h.coefficient :=
  (show LargeIndecomposable.ClosedZigzagTransfer.endpointRadicalSubmodule
      (k := k) (branch ≫ tau.asHom) ≤
        LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
          (k := k) branch tau from le_sup_left).trans
    h.obstruction_le_ker

/-- Its kernel also contains the entire source-endomorphism action on the
outer branch arrow. -/
theorem outer_le_ker
    (h : SupplementCoefficientData (k := k) branch tau) :
    LargeIndecomposable.RoiterFigure13E.leftOuterActionSubmodule
        (k := k) branch ≤
      LinearMap.ker h.coefficient :=
  (show LargeIndecomposable.RoiterFigure13E.leftOuterActionSubmodule
      (k := k) branch ≤
        LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
          (k := k) branch tau from le_sup_right).trans
    h.obstruction_le_ker

end SupplementCoefficientData

/-- The two branch--`tau` supplement coefficients together with the only
cross-branch vanishings not already contained in their separate left-arm
obstructions. -/
structure BranchTauCrossCoefficientData
    {M B H : C} (tau : End M) (beta : B ⟶ M) (gamma : H ⟶ M) where
  betaSupplement : SupplementCoefficientData (k := k) beta tau
  gammaSupplement : SupplementCoefficientData (k := k) gamma tau
  beta_cross : ∀ g : B ⟶ H,
    betaSupplement.coefficient (g ≫ gamma) = 0
  gamma_cross : ∀ g : H ⟶ B,
    gammaSupplement.coefficient (g ≫ beta) = 0

/-- Postcomposition with a fixed opposite branch.  Its range is precisely
the family of cross-branch composites which a branch--`tau` coefficient
must kill. -/
def branchCrossLinearMap {B H M : C} (gamma : H ⟶ M) :
    (B ⟶ H) →ₗ[k] (B ⟶ M) where
  toFun g := g ≫ gamma
  map_add' g h := by rw [Preadditive.add_comp]
  map_smul' c g := by
    change (c • g) ≫ gamma = c • (g ≫ gamma)
    rw [Linear.smul_comp]

/-- The full Figure-16 obstruction at `beta * tau`: the ordinary left-arm
supplement together with all composites through the opposite displayed
branch `gamma`. -/
def branchTauCrossObstruction
    {M B H : C} (tau : End M) (beta : B ⟶ M) (gamma : H ⟶ M) :
    Submodule k (B ⟶ M) :=
  LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
      (k := k) beta tau ⊔
    LinearMap.range (branchCrossLinearMap (k := k) gamma)

/-- Simultaneous separation of the two branch--`tau` paths from their full
cross obstructions constructs exactly the remaining coefficient package. -/
theorem nonempty_branchTauCrossCoefficientData
    {M B H : C} (tau : End M) (beta : B ⟶ M) (gamma : H ⟶ M)
    (hbeta : beta ≫ tau.asHom ∉
      branchTauCrossObstruction (k := k) tau beta gamma)
    (hgamma : gamma ≫ tau.asHom ∉
      branchTauCrossObstruction (k := k) tau gamma beta) :
    Nonempty (BranchTauCrossCoefficientData (k := k) tau beta gamma) := by
  obtain ⟨betaCoefficient, hbetaOne, hbetaKer⟩ :=
    LargeIndecomposable.ClosedZigzagTransfer.exists_normalized_coefficient_killing
      _ _ hbeta
  obtain ⟨gammaCoefficient, hgammaOne, hgammaKer⟩ :=
    LargeIndecomposable.ClosedZigzagTransfer.exists_normalized_coefficient_killing
      _ _ hgamma
  let betaSupplement : SupplementCoefficientData (k := k) beta tau :=
    { coefficient := betaCoefficient
      normalized := hbetaOne
      obstruction_le_ker := le_sup_left.trans hbetaKer }
  let gammaSupplement : SupplementCoefficientData (k := k) gamma tau :=
    { coefficient := gammaCoefficient
      normalized := hgammaOne
      obstruction_le_ker := le_sup_left.trans hgammaKer }
  refine ⟨{
    betaSupplement := betaSupplement
    gammaSupplement := gammaSupplement
    beta_cross := ?_
    gamma_cross := ?_ }⟩
  · intro g
    apply hbetaKer
    apply (show LinearMap.range (branchCrossLinearMap (k := k) gamma) ≤
      branchTauCrossObstruction (k := k) tau beta gamma from le_sup_right)
    exact ⟨g, rfl⟩
  · intro g
    apply hgammaKer
    apply (show LinearMap.range (branchCrossLinearMap (k := k) beta) ≤
      branchTauCrossObstruction (k := k) tau gamma beta from le_sup_right)
    exact ⟨g, rfl⟩

/-- The occurrence-sensitive thirteen-entry endpoint table for Figure 16.
The seven nondiagonal entries correspond, in order, to the central arrow,
the four branch arrows, and the two lower-branch length-two paths. -/
structure LiteralEndpointTable (G : DiagramData (C := C)) where
  residue : ∀ a : Vertex, End (G.object a) →ₐ[k] k
  tauOne : (G.object .lowerCenter ⟶ G.object .upperCenter) →ₗ[k] k
  betaUpperZero :
    (G.object .upperBeta ⟶ G.object .upperCenter) →ₗ[k] k
  gammaUpperZero :
    (G.object .upperGamma ⟶ G.object .upperCenter) →ₗ[k] k
  betaLowerZero :
    (G.object .lowerBeta ⟶ G.object .lowerCenter) →ₗ[k] k
  gammaLowerZero :
    (G.object .lowerGamma ⟶ G.object .lowerCenter) →ₗ[k] k
  betaTau : (G.object .lowerBeta ⟶ G.object .upperCenter) →ₗ[k] k
  gammaTau : (G.object .lowerGamma ⟶ G.object .upperCenter) →ₗ[k] k

namespace LiteralEndpointTable

variable {G : DiagramData (C := C)}

/-- The coefficient selected by an ordered pair of source occurrences.
Unsupported pairs are assigned the zero functional. -/
def coefficient (t : LiteralEndpointTable (k := k) G)
    (a b : Vertex) : (G.object a ⟶ G.object b) →ₗ[k] k := by
  cases a <;> cases b
  -- upperCenter
  · exact (t.residue .upperCenter).toLinearMap
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  -- lowerCenter
  · exact t.tauOne
  · exact (t.residue .lowerCenter).toLinearMap
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  -- upperBeta
  · exact t.betaUpperZero
  · exact 0
  · exact (t.residue .upperBeta).toLinearMap
  · exact 0
  · exact 0
  · exact 0
  -- upperGamma
  · exact t.gammaUpperZero
  · exact 0
  · exact 0
  · exact (t.residue .upperGamma).toLinearMap
  · exact 0
  · exact 0
  -- lowerBeta
  · exact t.betaTau
  · exact t.betaLowerZero
  · exact 0
  · exact 0
  · exact (t.residue .lowerBeta).toLinearMap
  · exact 0
  -- lowerGamma
  · exact t.gammaTau
  · exact t.gammaLowerZero
  · exact 0
  · exact 0
  · exact 0
  · exact (t.residue .lowerGamma).toLinearMap

/-- Every diagonal entry sends the ambient identity to one. -/
theorem coefficient_identity (t : LiteralEndpointTable (k := k) G)
    (a : Vertex) :
    t.coefficient a a (𝟙 (G.object a)) = 1 := by
  cases a <;> exact map_one (t.residue _)

/-- Every entry unsupported by a path in the free Figure-16 quiver is the
zero functional. -/
theorem coefficient_eq_zero_of_isEmpty
    (t : LiteralEndpointTable (k := k) G) (a b : Vertex)
    (hp : IsEmpty (Quiver.Path (Opposite.op b) (Opposite.op a)))
    (g : G.object a ⟶ G.object b) :
    t.coefficient a b g = 0 := by
  cases a <;> cases b
  -- upperCenter
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  -- lowerCenter
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tau))).elim
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  · rfl
  -- upperBeta
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.betaUpper))).elim
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  -- upperGamma
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.gammaUpper))).elim
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  -- lowerBeta
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.tau)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.betaLower)))).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.betaLower))).elim
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  -- lowerGamma
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.tau)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.gammaLower)))).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.gammaLower))).elim
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim

end LiteralEndpointTable

/-- A literal Figure-16 table compatible with whiskering by every displayed
generator.  These sixty finite equations are the complete algebraic input to
the path compiler. -/
structure CompatibleLiteralEndpointTable (G : DiagramData (C := C)) where
  table : LiteralEndpointTable (k := k) G
  left_arrow : ∀ {a' a : Vertex} (e : a' ⟶ a) (b : Vertex)
      (g : G.object a ⟶ G.object b),
    table.coefficient a' b (G.arrow e ≫ g) =
      table.coefficient a b g
  right_arrow : ∀ (a : Vertex) {b b' : Vertex} (e : b ⟶ b')
      (g : G.object a ⟶ G.object b),
    table.coefficient a b' (g ≫ G.arrow e) =
      table.coefficient a b g

namespace CompatibleLiteralEndpointTable

variable {G : DiagramData (C := C)}

/-- Iterating the left-generator equations along an arbitrary path. -/
theorem left_path (t : CompatibleLiteralEndpointTable (k := k) G)
    {a a' : Vertexᵒᵖ} (p : Quiver.Path a a') (b : Vertex)
    (g : G.object a.unop ⟶ G.object b) :
    t.table.coefficient a'.unop b
        (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫ g) =
      t.table.coefficient a.unop b g := by
  induction p with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.id_comp]
  | cons p e ih =>
      rw [LinearPathCategory.pathMap_cons, Category.assoc]
      exact (t.left_arrow e.unop b _).trans ih

/-- Iterating the right-generator equations along an arbitrary path. -/
theorem right_path (t : CompatibleLiteralEndpointTable (k := k) G)
    (a : Vertex) {b' b : Vertexᵒᵖ} (q : Quiver.Path b' b)
    (g : G.object a ⟶ G.object b.unop) :
    t.table.coefficient a b'.unop
        (g ≫ LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) =
      t.table.coefficient a b.unop g := by
  induction q with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.comp_id]
  | cons q e ih =>
      rw [LinearPathCategory.pathMap_cons, ← Category.assoc]
      exact (ih (g ≫ G.arrow e.unop)).trans (t.right_arrow _ e.unop g)

/-- Two-sided path whiskering preserves the occurrence-sensitive endpoint
coefficient. -/
theorem whisker (t : CompatibleLiteralEndpointTable (k := k) G)
    {a' a b b' : Vertexᵒᵖ}
    (p : Quiver.Path a a') (g : G.object a.unop ⟶ G.object b.unop)
    (q : Quiver.Path b' b) :
    t.table.coefficient a'.unop b'.unop
        (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) =
      t.table.coefficient a.unop b.unop g := by
  rw [← Category.assoc]
  exact (t.right_path a'.unop q _).trans (t.left_path p b.unop g)

/-- Every supported path evaluates to one; compatibility reduces it to the
identity coefficient at the path source. -/
theorem normalized (t : CompatibleLiteralEndpointTable (k := k) G)
    {a b : Vertexᵒᵖ} (p : Quiver.Path b a) :
    t.table.coefficient a.unop b.unop
        (LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p) = 1 := by
  have hcoeff := t.left_path p b.unop (𝟙 (G.object b.unop))
  have hcoeff' : t.table.coefficient a.unop b.unop
        (LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p) =
      t.table.coefficient b.unop b.unop (𝟙 (G.object b.unop)) := by
    rw [← Category.comp_id (LinearPathCategory.pathMap
      (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p)]
    exact hcoeff
  rw [hcoeff', t.table.coefficient_identity]

end CompatibleLiteralEndpointTable

/-- The algebraic identities on five scalar functionals which imply all
sixty generator equations for the repeated-object Figure-16 realization.

The first four groups are the central and endpoint covariance equations.
The return and cross fields are precisely the extra vanishings forced by
distinct source occurrences sharing the ambient objects `M`, `B`, and `H`.
-/
structure RepeatedObjectCoefficientData
    {M B H : C} (tau : End M) (beta : B ⟶ M) (gamma : H ⟶ M) where
  residueM : End M →ₐ[k] k
  residueB : End B →ₐ[k] k
  residueH : End H →ₐ[k] k
  tauOne : End M →ₗ[k] k
  betaZero : (B ⟶ M) →ₗ[k] k
  gammaZero : (H ⟶ M) →ₗ[k] k
  betaTau : (B ⟶ M) →ₗ[k] k
  gammaTau : (H ⟶ M) →ₗ[k] k
  tauOne_post : ∀ a : End M,
    tauOne (End.of (tau.asHom ≫ a.asHom)) = residueM a
  tauOne_pre : ∀ a : End M,
    tauOne (End.of (a.asHom ≫ tau.asHom)) = residueM a
  residueM_tau_post : ∀ a : End M,
    residueM (End.of (tau.asHom ≫ a.asHom)) = 0
  residueM_tau_pre : ∀ a : End M,
    residueM (End.of (a.asHom ≫ tau.asHom)) = 0
  betaZero_post : ∀ a : End M,
    betaZero (beta ≫ a.asHom) = residueM a
  betaZero_pre : ∀ a : End B,
    betaZero (a.asHom ≫ beta) = residueB a
  gammaZero_post : ∀ a : End M,
    gammaZero (gamma ≫ a.asHom) = residueM a
  gammaZero_pre : ∀ a : End H,
    gammaZero (a.asHom ≫ gamma) = residueH a
  residueB_beta_return : ∀ g : M ⟶ B,
    residueB (End.of (beta ≫ g)) = 0
  residueH_gamma_return : ∀ g : M ⟶ H,
    residueH (End.of (gamma ≫ g)) = 0
  residueM_beta_return : ∀ g : M ⟶ B,
    residueM (End.of (g ≫ beta)) = 0
  residueM_gamma_return : ∀ g : M ⟶ H,
    residueM (End.of (g ≫ gamma)) = 0
  tauOne_beta_return : ∀ g : M ⟶ B,
    tauOne (End.of (g ≫ beta)) = 0
  tauOne_gamma_return : ∀ g : M ⟶ H,
    tauOne (End.of (g ≫ gamma)) = 0
  betaZero_tau : ∀ g : B ⟶ M,
    betaZero (g ≫ tau.asHom) = 0
  gammaZero_tau : ∀ g : H ⟶ M,
    gammaZero (g ≫ tau.asHom) = 0
  betaZero_cross : ∀ g : B ⟶ H,
    betaZero (g ≫ gamma) = 0
  gammaZero_cross : ∀ g : H ⟶ B,
    gammaZero (g ≫ beta) = 0
  betaTau_post : ∀ a : End M,
    betaTau (beta ≫ a.asHom) = tauOne a
  gammaTau_post : ∀ a : End M,
    gammaTau (gamma ≫ a.asHom) = tauOne a
  betaTau_tau : ∀ g : B ⟶ M,
    betaTau (g ≫ tau.asHom) = betaZero g
  gammaTau_tau : ∀ g : H ⟶ M,
    gammaTau (g ≫ tau.asHom) = gammaZero g
  betaTau_outer : ∀ a : End B,
    betaTau (a.asHom ≫ beta) = 0
  gammaTau_outer : ∀ a : End H,
    gammaTau (a.asHom ≫ gamma) = 0
  betaTau_cross : ∀ g : B ⟶ H,
    betaTau (g ≫ gamma) = 0
  gammaTau_cross : ∀ g : H ⟶ B,
    gammaTau (g ≫ beta) = 0

namespace RepeatedObjectCoefficientData

variable {M B H : C} {tau : End M} {beta : B ⟶ M} {gamma : H ⟶ M}

/-- Package the eight algebraic functionals as the literal thirteen-entry
occurrence table. -/
def literalEndpointTable
    (h : RepeatedObjectCoefficientData (k := k) tau beta gamma) :
    LiteralEndpointTable (k := k)
      (repeatedObjectDiagram tau beta gamma) where
  residue
    | .upperCenter | .lowerCenter => h.residueM
    | .upperBeta | .lowerBeta => h.residueB
    | .upperGamma | .lowerGamma => h.residueH
  tauOne := h.tauOne
  betaUpperZero := h.betaZero
  gammaUpperZero := h.gammaZero
  betaLowerZero := h.betaZero
  gammaLowerZero := h.gammaZero
  betaTau := h.betaTau
  gammaTau := h.gammaTau

/-- The named algebraic interface discharges the complete finite generator
table by case analysis. -/
def compatibleLiteralEndpointTable
    (h : RepeatedObjectCoefficientData (k := k) tau beta gamma) :
    CompatibleLiteralEndpointTable (k := k)
      (repeatedObjectDiagram tau beta gamma) where
  table := h.literalEndpointTable
  left_arrow := by
    intro a' a e b g
    cases e <;> cases b
    -- tau
    · exact h.tauOne_post (End.of g)
    · exact h.residueM_tau_post (End.of g)
    · rfl
    · rfl
    · rfl
    · rfl
    -- betaUpper
    · exact h.betaZero_post (End.of g)
    · rfl
    · exact h.residueB_beta_return g
    · rfl
    · rfl
    · rfl
    -- gammaUpper
    · exact h.gammaZero_post (End.of g)
    · rfl
    · rfl
    · exact h.residueH_gamma_return g
    · rfl
    · rfl
    -- betaLower
    · exact h.betaTau_post (End.of g)
    · exact h.betaZero_post (End.of g)
    · rfl
    · rfl
    · exact h.residueB_beta_return g
    · rfl
    -- gammaLower
    · exact h.gammaTau_post (End.of g)
    · exact h.gammaZero_post (End.of g)
    · rfl
    · rfl
    · rfl
    · exact h.residueH_gamma_return g
  right_arrow := by
    intro a b b' e g
    cases e <;> cases a
    -- tau
    · exact h.residueM_tau_pre (End.of g)
    · exact h.tauOne_pre (End.of g)
    · exact h.betaZero_tau g
    · exact h.gammaZero_tau g
    · exact h.betaTau_tau g
    · exact h.gammaTau_tau g
    -- betaUpper
    · exact h.residueM_beta_return g
    · exact h.tauOne_beta_return g
    · exact h.betaZero_pre (End.of g)
    · exact h.gammaZero_cross g
    · exact h.betaTau_outer (End.of g)
    · exact h.gammaTau_cross g
    -- gammaUpper
    · exact h.residueM_gamma_return g
    · exact h.tauOne_gamma_return g
    · exact h.betaZero_cross g
    · exact h.gammaZero_pre (End.of g)
    · exact h.betaTau_cross g
    · exact h.gammaTau_outer (End.of g)
    -- betaLower
    · rfl
    · exact h.residueM_beta_return g
    · rfl
    · rfl
    · exact h.betaZero_pre (End.of g)
    · exact h.gammaZero_cross g
    -- gammaLower
    · rfl
    · exact h.residueM_gamma_return g
    · rfl
    · rfl
    · exact h.betaZero_cross g
    · exact h.gammaZero_pre (End.of g)

end RepeatedObjectCoefficientData

/-- A verified endpoint table, in a form independent of the particular
thirteen-field presentation used to construct it. -/
structure EndpointCoefficientData (G : DiagramData (C := C)) where
  coefficient : ∀ a b : Vertex, (G.object a ⟶ G.object b) →ₗ[k] k
  normalized : ∀ {a b : Vertexᵒᵖ} (p : Quiver.Path b a),
    coefficient a.unop b.unop
      (LinearPathCategory.pathMap
        (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p) = 1
  whisker : ∀ {a' a b b' : Vertexᵒᵖ}
      (p : Quiver.Path a a')
      (g : G.object a.unop ⟶ G.object b.unop)
      (q : Quiver.Path b' b),
    coefficient a'.unop b'.unop
        (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) =
      coefficient a.unop b.unop g
  eq_zero_of_isEmpty : ∀ (a b : Vertex),
    IsEmpty (Quiver.Path (Opposite.op b) (Opposite.op a)) →
      ∀ g : G.object a ⟶ G.object b, coefficient a b g = 0

/-- The finite compatible table supplies all fields of the verified endpoint
package. -/
def CompatibleLiteralEndpointTable.toEndpointCoefficientData
    {G : DiagramData (C := C)}
    (t : CompatibleLiteralEndpointTable (k := k) G) :
    EndpointCoefficientData (k := k) G where
  coefficient := t.table.coefficient
  normalized := t.normalized
  whisker := t.whisker
  eq_zero_of_isEmpty := t.table.coefficient_eq_zero_of_isEmpty

namespace EndpointCoefficientData

variable {G : DiagramData (C := C)}

/-- Path-indexed form of an endpoint coefficient table. -/
def vertexCoefficient (h : EndpointCoefficientData (k := k) G)
    {a b : Vertexᵒᵖ} (_p : Quiver.Path b a) :
    (G.object a.unop ⟶ G.object b.unop) →ₗ[k] k :=
  h.coefficient a.unop b.unop

/-- The endpoint compiler produces the complete thin-path coefficient data
for the free Figure-16 source. -/
def toThinPathCoefficientData
    (h : EndpointCoefficientData (k := k) G) :
    ThinPathCoefficientData (k := k) (G.functor (k := k)) where
  path_subsingleton := path_subsingleton
  coefficient := fun p ↦ h.vertexCoefficient p
  normalized := by
    intro U V p
    unfold DiagramData.functor
    rw [LinearPathCategory.lift_map_pathHom]
    exact h.normalized p
  whisker_coefficient := by
    classical
    intro U' U V V' p g q r
    unfold DiagramData.functor at g ⊢
    change G.object (LinearPathCategory.vertex U).unop ⟶
      G.object (LinearPathCategory.vertex V).unop at g
    rw [LinearPathCategory.lift_map_pathHom,
      LinearPathCategory.lift_map_pathHom]
    change h.coefficient
        (LinearPathCategory.vertex U').unop
        (LinearPathCategory.vertex V').unop
        (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) = _
    rw [h.whisker p g q]
    by_cases hmiddle : Nonempty (Quiver.Path
        (LinearPathCategory.vertex V) (LinearPathCategory.vertex U))
    · rw [coefficientOrZero_of_nonempty _ _ hmiddle]
      rfl
    · have hmiddle' : IsEmpty (Quiver.Path
          (LinearPathCategory.vertex V) (LinearPathCategory.vertex U)) :=
        not_nonempty_iff.mp hmiddle
      rw [coefficientOrZero_of_isEmpty _ _ hmiddle']
      exact h.eq_zero_of_isEmpty
        (LinearPathCategory.vertex U).unop
        (LinearPathCategory.vertex V).unop
        (by simpa only [Opposite.op_unop] using hmiddle') g

/-- Endpoint coefficients directly yield the BGRS Hom-bifunctor retraction
for a Figure-16 diagram. -/
def homBifunctorRetraction
    (h : EndpointCoefficientData (k := k) G) :
    HomBifunctorRetraction (k := k) (G.functor (k := k)) :=
  h.toThinPathCoefficientData.homBifunctorRetraction

end EndpointCoefficientData

namespace RepeatedObjectCoefficientData

variable {M B H : C} {tau : End M} {beta : B ⟶ M} {gamma : H ⟶ M}

/-- The algebraic Figure-16 interface compiles directly to a
Hom-bifunctor retraction. -/
def homBifunctorRetraction
    (h : RepeatedObjectCoefficientData (k := k) tau beta gamma) :
    HomBifunctorRetraction (k := k)
      ((repeatedObjectDiagram tau beta gamma).functor (k := k)) :=
  h.compatibleLiteralEndpointTable.toEndpointCoefficientData.homBifunctorRetraction

end RepeatedObjectCoefficientData

end LargeIndecomposable.CriticalSingularFigure16
