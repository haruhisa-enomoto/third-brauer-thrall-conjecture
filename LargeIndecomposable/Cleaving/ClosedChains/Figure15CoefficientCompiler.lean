module

public import LargeIndecomposable.Cleaving.ClosedChains.CrossUniverseThinQuotientRetraction
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure15

@[expose] public section

/-!
# Endpoint coefficient compiler for the bound BGRS Figure 15 source

The free Figure-15 quiver is thin, but its main length-three path is killed
in the bound source.  This file isolates the formal compiler needed after the
finite coefficient table has been constructed.  An endpoint coefficient is
specified for every ordered pair of the eight source occurrences.  Generator
compatibility is stated after scaling by the landing path in the bound source,
so every equation landing on the killed main path is automatic.

The compiler iterates the two generator tables along arbitrary paths and
produces the `ThinQuotientPathCoefficientData` used by the cross-universe
Hom-bifunctor retraction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalSingularFigure15

open LargeIndecomposable.ClosedZigzagCrossUniverse
open LargeIndecomposable.ClosedZigzagTransfer

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- A normalized linear coefficient which kills a specified supplement
obstruction. -/
structure SupplementCoefficientData
    {V : Type*} [AddCommGroup V] [Module k V]
    (obstruction : Submodule k V) (landing : V) where
  coefficient : V →ₗ[k] k
  normalized : coefficient landing = 1
  obstruction_le_ker : obstruction ≤ LinearMap.ker coefficient

/-- Linear separation constructs a normalized coefficient from every
supplement nonmembership. -/
theorem nonempty_supplementCoefficientData
    {V : Type*} [AddCommGroup V] [Module k V]
    (obstruction : Submodule k V) (landing : V)
    (hlanding : landing ∉ obstruction) :
    Nonempty (SupplementCoefficientData
      (k := k) obstruction landing) := by
  obtain ⟨coefficient, hnormalized, hker⟩ :=
    LargeIndecomposable.ClosedZigzagTransfer.exists_normalized_coefficient_killing
      obstruction landing hlanding
  exact ⟨⟨coefficient, hnormalized, hker⟩⟩

namespace SupplementCoefficientData

variable {V : Type*} [AddCommGroup V] [Module k V]
variable {obstruction : Submodule k V} {landing : V}

/-- A supplement coefficient vanishes on every member of its prescribed
obstruction. -/
theorem coefficient_eq_zero_of_mem
    (h : SupplementCoefficientData (k := k) obstruction landing)
    {g : V} (hg : g ∈ obstruction) : h.coefficient g = 0 :=
  h.obstruction_le_ker hg

/-- If the supplement obstruction contains the endpoint radical, its
normalized functional has the usual source-residue covariance. -/
theorem coefficient_comp_left
    {X Y : C} {f : X ⟶ Y}
    {obstruction : Submodule k (X ⟶ Y)}
    (h : SupplementCoefficientData (k := k) obstruction f)
    (hendpoint : endpointRadicalSubmodule (k := k) f ≤ obstruction)
    (residue : End X →ₐ[k] k)
    (hresidue : ∀ a : End X,
      residue a = 0 ↔ a ∈ Ring.jacobson (End X))
    (a : End X) :
    h.coefficient (a.asHom ≫ f) = residue a :=
  endpointRadicalCoefficient_comp_left f residue hresidue
    h.coefficient h.normalized
    (hendpoint.trans h.obstruction_le_ker) a

/-- Target-residue covariance of a supplement coefficient whose
obstruction contains the endpoint radical. -/
theorem coefficient_comp_right
    {X Y : C} {f : X ⟶ Y}
    {obstruction : Submodule k (X ⟶ Y)}
    (h : SupplementCoefficientData (k := k) obstruction f)
    (hendpoint : endpointRadicalSubmodule (k := k) f ≤ obstruction)
    (residue : End Y →ₐ[k] k)
    (hresidue : ∀ b : End Y,
      residue b = 0 ↔ b ∈ Ring.jacobson (End Y))
    (b : End Y) :
    h.coefficient (f ≫ b.asHom) = residue b :=
  endpointRadicalCoefficient_comp_right f residue hresidue
    h.coefficient h.normalized
    (hendpoint.trans h.obstruction_le_ker) b

end SupplementCoefficientData

/-- The repeated-object realization underlying the exact Figure-15
quotient.  The four ambient objects occur as `A,D,C,B,C,B,D,A`. -/
def repeatedObjectDiagram
    {A D C₀ B : C} (alpha : A ⟶ D) (delta : D ⟶ C₀)
    (beta : C₀ ⟶ B) (rho : End C₀) (sigma : End D)
    (hmain : alpha ≫ delta ≫ beta = 0) : DiagramData (C := C) where
  object
    | .leftEndpoint => A
    | .leftCenter => D
    | .rightCenter => C₀
    | .rightEndpoint => B
    | .upperCenter => C₀
    | .upperEndpoint => B
    | .lowerCenter => D
    | .lowerEndpoint => A
  arrow
    | .alphaLeft => alpha
    | .delta => delta
    | .alphaRight => beta
    | .rho => rho.asHom
    | .alphaUpper => beta
    | .sigma => sigma.asHom
    | .alphaLower => alpha
  main_zero := hmain

/-- The literal finite endpoint table for the repeated-object Figure-15
diagram.  Its nonzero entries are exactly the eight identities, seven
arrows, and four surviving length-two paths. -/
def repeatedEndpointCoefficient
    {A D C₀ B : C} (alpha : A ⟶ D) (delta : D ⟶ C₀)
    (beta : C₀ ⟶ B) (rho : End C₀) (sigma : End D)
    (hmain : alpha ≫ delta ≫ beta = 0)
    (residueA : End A →ₐ[k] k) (residueD : End D →ₐ[k] k)
    (residueC : End C₀ →ₐ[k] k) (residueB : End B →ₐ[k] k)
    (alphaZero alphaOne : (A ⟶ D) →ₗ[k] k)
    (deltaZero : (D ⟶ C₀) →ₗ[k] k)
    (betaZero betaOne : (C₀ ⟶ B) →ₗ[k] k)
    (rhoOne : End C₀ →ₗ[k] k) (sigmaOne : End D →ₗ[k] k)
    (suffix : (A ⟶ C₀) →ₗ[k] k)
    (prefixCoefficient : (D ⟶ B) →ₗ[k] k)
    (a b : Vertex) :
    ((repeatedObjectDiagram alpha delta beta rho sigma hmain).object a ⟶
      (repeatedObjectDiagram alpha delta beta rho sigma hmain).object b) →ₗ[k] k := by
  cases a <;> cases b
  -- leftEndpoint
  · exact residueA.toLinearMap
  · exact alphaZero
  · exact suffix
  · exact 0
  · exact 0
  · exact 0
  · exact alphaOne
  · exact 0
  -- leftCenter
  · exact 0
  · exact residueD.toLinearMap
  · exact deltaZero
  · exact prefixCoefficient
  · exact 0
  · exact 0
  · exact sigmaOne
  · exact 0
  -- rightCenter
  · exact 0
  · exact 0
  · exact residueC.toLinearMap
  · exact betaZero
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  -- rightEndpoint
  · exact 0
  · exact 0
  · exact 0
  · exact residueB.toLinearMap
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  -- upperCenter
  · exact 0
  · exact 0
  · exact rhoOne
  · exact betaOne
  · exact residueC.toLinearMap
  · exact betaZero
  · exact 0
  · exact 0
  -- upperEndpoint
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact residueB.toLinearMap
  · exact 0
  · exact 0
  -- lowerCenter
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact residueD.toLinearMap
  · exact 0
  -- lowerEndpoint
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact alphaZero
  · exact residueA.toLinearMap

/-- Every diagonal entry of the repeated Figure-15 table sends the identity
to one. -/
theorem repeatedEndpointCoefficient_identity
    {A D C₀ B : C} (alpha : A ⟶ D) (delta : D ⟶ C₀)
    (beta : C₀ ⟶ B) (rho : End C₀) (sigma : End D)
    (hmain : alpha ≫ delta ≫ beta = 0)
    (residueA : End A →ₐ[k] k) (residueD : End D →ₐ[k] k)
    (residueC : End C₀ →ₐ[k] k) (residueB : End B →ₐ[k] k)
    (alphaZero alphaOne : (A ⟶ D) →ₗ[k] k)
    (deltaZero : (D ⟶ C₀) →ₗ[k] k)
    (betaZero betaOne : (C₀ ⟶ B) →ₗ[k] k)
    (rhoOne : End C₀ →ₗ[k] k) (sigmaOne : End D →ₗ[k] k)
    (suffix : (A ⟶ C₀) →ₗ[k] k)
    (prefixCoefficient : (D ⟶ B) →ₗ[k] k)
    (a : Vertex) :
    repeatedEndpointCoefficient alpha delta beta rho sigma hmain
        residueA residueD residueC residueB alphaZero alphaOne deltaZero
        betaZero betaOne rhoOne sigmaOne suffix prefixCoefficient a a
        (𝟙 ((repeatedObjectDiagram alpha delta beta rho sigma hmain).object a)) = 1 := by
  cases a
  · exact map_one residueA
  · exact map_one residueD
  · exact map_one residueC
  · exact map_one residueB
  · exact map_one residueC
  · exact map_one residueB
  · exact map_one residueD
  · exact map_one residueA

/-- Unsupported endpoint entries of the literal Figure-15 table vanish. -/
theorem repeatedEndpointCoefficient_eq_zero_of_isEmpty
    {A D C₀ B : C} (alpha : A ⟶ D) (delta : D ⟶ C₀)
    (beta : C₀ ⟶ B) (rho : End C₀) (sigma : End D)
    (hmain : alpha ≫ delta ≫ beta = 0)
    (residueA : End A →ₐ[k] k) (residueD : End D →ₐ[k] k)
    (residueC : End C₀ →ₐ[k] k) (residueB : End B →ₐ[k] k)
    (alphaZero alphaOne : (A ⟶ D) →ₗ[k] k)
    (deltaZero : (D ⟶ C₀) →ₗ[k] k)
    (betaZero betaOne : (C₀ ⟶ B) →ₗ[k] k)
    (rhoOne : End C₀ →ₗ[k] k) (sigmaOne : End D →ₗ[k] k)
    (suffix : (A ⟶ C₀) →ₗ[k] k)
    (prefixCoefficient : (D ⟶ B) →ₗ[k] k)
    (a b : Vertex)
    (hp : IsEmpty (Quiver.Path (Opposite.op b) (Opposite.op a)))
    (g : (repeatedObjectDiagram alpha delta beta rho sigma hmain).object a ⟶
      (repeatedObjectDiagram alpha delta beta rho sigma hmain).object b) :
    repeatedEndpointCoefficient alpha delta beta rho sigma hmain
      residueA residueD residueC residueB alphaZero alphaOne deltaZero
      betaZero betaOne rhoOne sigmaOne suffix prefixCoefficient a b g = 0 := by
  cases a <;> cases b
  -- leftEndpoint
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.delta)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft)))).elim
  · rfl
  · rfl
  · rfl
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.sigma)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft)))).elim
  · rfl
  -- leftCenter
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.delta))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.delta)))).elim
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.sigma))).elim
  · rfl
  -- rightCenter
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight))).elim
  · rfl
  · rfl
  · rfl
  · rfl
  -- rightEndpoint
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  · rfl
  -- upperCenter
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.rho))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.rho)))).elim
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaUpper))).elim
  · rfl
  · rfl
  -- upperEndpoint
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  -- lowerCenter
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  -- lowerEndpoint
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLower))).elim
  · exact (hp.false Quiver.Path.nil).elim

/-- The same 19-entry Figure-15 endpoint table, stated directly on an
arbitrary diagram.  This occurrence-sensitive form avoids transporting
coefficient maps across equal ambient objects when the diagram arises from
a structured quotient construction. -/
structure LiteralEndpointTable (G : DiagramData (C := C)) where
  residue : ∀ a : Vertex, End (G.object a) →ₐ[k] k
  alphaLeftZero : (G.object .leftEndpoint ⟶ G.object .leftCenter) →ₗ[k] k
  mainSuffix : (G.object .leftEndpoint ⟶ G.object .rightCenter) →ₗ[k] k
  lowerComposite :
    (G.object .leftEndpoint ⟶ G.object .lowerCenter) →ₗ[k] k
  deltaZero : (G.object .leftCenter ⟶ G.object .rightCenter) →ₗ[k] k
  mainPrefix : (G.object .leftCenter ⟶ G.object .rightEndpoint) →ₗ[k] k
  sigmaOne : (G.object .leftCenter ⟶ G.object .lowerCenter) →ₗ[k] k
  alphaRightZero :
    (G.object .rightCenter ⟶ G.object .rightEndpoint) →ₗ[k] k
  rhoOne : (G.object .upperCenter ⟶ G.object .rightCenter) →ₗ[k] k
  upperComposite :
    (G.object .upperCenter ⟶ G.object .rightEndpoint) →ₗ[k] k
  alphaUpperZero :
    (G.object .upperCenter ⟶ G.object .upperEndpoint) →ₗ[k] k
  alphaLowerZero :
    (G.object .lowerEndpoint ⟶ G.object .lowerCenter) →ₗ[k] k

namespace LiteralEndpointTable

variable {G : DiagramData (C := C)}

/-- The occurrence-sensitive endpoint coefficient selected by a literal
Figure-15 table. -/
def coefficient (t : LiteralEndpointTable (k := k) G) (a b : Vertex) :
    (G.object a ⟶ G.object b) →ₗ[k] k := by
  cases a <;> cases b
  -- leftEndpoint
  · exact (t.residue .leftEndpoint).toLinearMap
  · exact t.alphaLeftZero
  · exact t.mainSuffix
  · exact 0
  · exact 0
  · exact 0
  · exact t.lowerComposite
  · exact 0
  -- leftCenter
  · exact 0
  · exact (t.residue .leftCenter).toLinearMap
  · exact t.deltaZero
  · exact t.mainPrefix
  · exact 0
  · exact 0
  · exact t.sigmaOne
  · exact 0
  -- rightCenter
  · exact 0
  · exact 0
  · exact (t.residue .rightCenter).toLinearMap
  · exact t.alphaRightZero
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  -- rightEndpoint
  · exact 0
  · exact 0
  · exact 0
  · exact (t.residue .rightEndpoint).toLinearMap
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  -- upperCenter
  · exact 0
  · exact 0
  · exact t.rhoOne
  · exact t.upperComposite
  · exact (t.residue .upperCenter).toLinearMap
  · exact t.alphaUpperZero
  · exact 0
  · exact 0
  -- upperEndpoint
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact (t.residue .upperEndpoint).toLinearMap
  · exact 0
  · exact 0
  -- lowerCenter
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact (t.residue .lowerCenter).toLinearMap
  · exact 0
  -- lowerEndpoint
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact t.alphaLowerZero
  · exact (t.residue .lowerEndpoint).toLinearMap

/-- Every diagonal entry of a literal endpoint table sends the identity to
one. -/
theorem coefficient_identity (t : LiteralEndpointTable (k := k) G)
    (a : Vertex) :
    t.coefficient a a (𝟙 (G.object a)) = 1 := by
  cases a <;> exact map_one (t.residue _)

/-- Every endpoint entry unsupported by the free Figure-15 quiver is zero. -/
theorem coefficient_eq_zero_of_isEmpty
    (t : LiteralEndpointTable (k := k) G) (a b : Vertex)
    (hp : IsEmpty (Quiver.Path (Opposite.op b) (Opposite.op a)))
    (g : G.object a ⟶ G.object b) :
    t.coefficient a b g = 0 := by
  cases a <;> cases b
  -- leftEndpoint
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.delta)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft)))).elim
  · rfl
  · rfl
  · rfl
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.sigma)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft)))).elim
  · rfl
  -- leftCenter
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.delta))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.delta)))).elim
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.sigma))).elim
  · rfl
  -- rightCenter
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight))).elim
  · rfl
  · rfl
  · rfl
  · rfl
  -- rightEndpoint
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  · rfl
  -- upperCenter
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.rho))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.rho)))).elim
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaUpper))).elim
  · rfl
  · rfl
  -- upperEndpoint
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  -- lowerCenter
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  -- lowerEndpoint
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLower))).elim
  · exact (hp.false Quiver.Path.nil).elim

end LiteralEndpointTable

/-- A literal Figure-15 endpoint table whose coefficients are compatible
with left and right whiskering by every displayed arrow, away from the
unique endpoint pair on which the defining length-three path is killed. -/
structure CompatibleLiteralEndpointTable (G : DiagramData (C := C)) where
  table : LiteralEndpointTable (k := k) G
  left_arrow : ∀ {a' a : Vertex} (e : a' ⟶ a) (b : Vertex),
    ¬ (a' = .leftEndpoint ∧ b = .rightEndpoint) →
    ∀ g : G.object a ⟶ G.object b,
      table.coefficient a' b (G.arrow e ≫ g) =
        table.coefficient a b g
  right_arrow : ∀ (a : Vertex) {b b' : Vertex} (e : b ⟶ b'),
    ¬ (a = .leftEndpoint ∧ b' = .rightEndpoint) →
    ∀ g : G.object a ⟶ G.object b,
      table.coefficient a b' (g ≫ G.arrow e) =
        table.coefficient a b g

namespace CompatibleLiteralEndpointTable

variable {G : DiagramData (C := C)}

def mainPath : Quiver.Path
    (Opposite.op Vertex.rightEndpoint) (Opposite.op Vertex.leftEndpoint) :=
  (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaRight)).comp
    ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.delta)).comp
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLeft)))

/-- Every free path between the endpoints of the displayed Figure-15
relation vanishes in the bound source. -/
theorem quotient_path_eq_zero_of_leftEndpoint_rightEndpoint
    (r : Quiver.Path (Opposite.op Vertex.rightEndpoint)
      (Opposite.op Vertex.leftEndpoint)) :
    (quotientFunctor (k := k)).map
      (LinearPathCategory.pathHom r) = 0 := by
  rw [(path_subsingleton _ _).elim r mainPath]
  have hpath : LinearPathCategory.pathHom mainPath =
      mainComposite (k := k) := by
    unfold mainPath mainComposite freeGeneratorHom
    rw [← LinearPathCategory.pathHom_comp,
      ← LinearPathCategory.pathHom_comp]
    exact Category.assoc _ _ _
  rw [hpath]
  exact mainComposite_zero (k := k)

private theorem arrow_target_ne_leftEndpoint
    {a b : Vertex} (e : a ⟶ b) : b ≠ Vertex.leftEndpoint := by
  cases e <;> intro h <;> cases h

/-- Iteration of the strict left-generator table away from the killed
landing pair. -/
theorem left_path (t : CompatibleLiteralEndpointTable (k := k) G)
    {a a' : Vertexᵒᵖ} (p : Quiver.Path a a') (b : Vertex)
    (hnot : ¬ (a'.unop = Vertex.leftEndpoint ∧
      b = Vertex.rightEndpoint))
    (g : G.object a.unop ⟶ G.object b) :
    t.table.coefficient a'.unop b
        (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫ g) =
      t.table.coefficient a.unop b g := by
  induction p with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.id_comp]
  | cons p e ih =>
      rw [LinearPathCategory.pathMap_cons, Category.assoc]
      exact (t.left_arrow e.unop b hnot _).trans (ih (by
        intro h
        exact arrow_target_ne_leftEndpoint e.unop h.1))

private theorem path_source_unop_eq_rightEndpoint
    {b' b : Vertexᵒᵖ} (q : Quiver.Path b' b)
    (hb : b.unop = Vertex.rightEndpoint) :
    b'.unop = Vertex.rightEndpoint := by
  have hbOp : b = Opposite.op Vertex.rightEndpoint := by
    simpa only [Opposite.op_unop] using congrArg Opposite.op hb
  subst b
  have hq0 := path_length_zero_of_target_rightEndpoint q
  exact congrArg Opposite.unop (q.eq_of_length_zero hq0)

/-- Iteration of the strict right-generator table away from the killed
landing pair. -/
theorem right_path (t : CompatibleLiteralEndpointTable (k := k) G)
    (a : Vertex) {b' b : Vertexᵒᵖ} (q : Quiver.Path b' b)
    (hnot : ¬ (a = Vertex.leftEndpoint ∧
      b'.unop = Vertex.rightEndpoint))
    (g : G.object a ⟶ G.object b.unop) :
    t.table.coefficient a b'.unop
        (g ≫ LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) =
      t.table.coefficient a b.unop g := by
  induction q with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.comp_id]
  | cons q e ih =>
      rw [LinearPathCategory.pathMap_cons, ← Category.assoc]
      exact (ih (g ≫ G.arrow e.unop)).trans
        (t.right_arrow _ e.unop (by
          intro h
          exact hnot ⟨h.1, path_source_unop_eq_rightEndpoint q h.2⟩) g)

/-- Two-sided path whiskering preserves every literal endpoint coefficient
after scaling by the landing path in the bound source. -/
theorem whisker_scaled
    (t : CompatibleLiteralEndpointTable (k := k) G)
    {a' a b b' : Vertexᵒᵖ}
    (p : Quiver.Path a a') (g : G.object a.unop ⟶ G.object b.unop)
    (q : Quiver.Path b' b) (r : Quiver.Path b' a') :
    t.table.coefficient a'.unop b'.unop
        (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) •
        (quotientFunctor (k := k)).map
          (LinearPathCategory.pathHom r) =
      t.table.coefficient a.unop b.unop g •
        (quotientFunctor (k := k)).map
          (LinearPathCategory.pathHom r) := by
  by_cases hlanding : a'.unop = Vertex.leftEndpoint ∧
      b'.unop = Vertex.rightEndpoint
  · rcases hlanding with ⟨ha, hb⟩
    have haOp : a' = Opposite.op Vertex.leftEndpoint := by
      simpa only [Opposite.op_unop] using congrArg Opposite.op ha
    have hbOp : b' = Opposite.op Vertex.rightEndpoint := by
      simpa only [Opposite.op_unop] using congrArg Opposite.op hb
    subst a'
    subst b'
    rw [quotient_path_eq_zero_of_leftEndpoint_rightEndpoint r]
    simp
  · have hmiddle : ¬ (a'.unop = Vertex.leftEndpoint ∧
        b.unop = Vertex.rightEndpoint) := by
      intro h
      exact hlanding
        ⟨h.1, path_source_unop_eq_rightEndpoint q h.2⟩
    have hcoeff :
        t.table.coefficient a'.unop b'.unop
            (LinearPathCategory.pathMap
                (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫
              g ≫ LinearPathCategory.pathMap
                (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) =
          t.table.coefficient a.unop b.unop g := by
      rw [← Category.assoc]
      calc
        _ = t.table.coefficient a'.unop b.unop
            (LinearPathCategory.pathMap
                (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫ g) :=
          t.right_path a'.unop q hlanding _
        _ = _ := t.left_path p b.unop hmiddle g
    rw [hcoeff]

/-- Every literal path entry is normalized after scaling by its quotient
path.  The killed main path is automatic; every other path reduces to a
diagonal identity coefficient. -/
theorem normalized_scaled
    (t : CompatibleLiteralEndpointTable (k := k) G)
    {a b : Vertexᵒᵖ} (p : Quiver.Path b a) :
    t.table.coefficient a.unop b.unop
        (LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p) •
        (quotientFunctor (k := k)).map
          (LinearPathCategory.pathHom p) =
      (quotientFunctor (k := k)).map
        (LinearPathCategory.pathHom p) := by
  by_cases hlanding : a.unop = Vertex.leftEndpoint ∧
      b.unop = Vertex.rightEndpoint
  · rcases hlanding with ⟨ha, hb⟩
    have haOp : a = Opposite.op Vertex.leftEndpoint := by
      simpa only [Opposite.op_unop] using congrArg Opposite.op ha
    have hbOp : b = Opposite.op Vertex.rightEndpoint := by
      simpa only [Opposite.op_unop] using congrArg Opposite.op hb
    subst a
    subst b
    rw [quotient_path_eq_zero_of_leftEndpoint_rightEndpoint p]
    simp
  · have hcoeff := t.left_path p b.unop hlanding
        (𝟙 (G.object b.unop))
    have hcoeff' : t.table.coefficient a.unop b.unop
          (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p) =
        t.table.coefficient b.unop b.unop (𝟙 (G.object b.unop)) := by
      rw [← Category.comp_id (LinearPathCategory.pathMap
        (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p)]
      exact hcoeff
    rw [hcoeff', t.table.coefficient_identity, one_smul]

end CompatibleLiteralEndpointTable

/-- A complete verified endpoint coefficient table for a Figure-15 diagram.
Normalization and two-sided compatibility are stated after scaling by the
landing path in the bound source, so the killed main path imposes no false
normalization equation. -/
structure EndpointCoefficientData (G : DiagramData (C := C)) where
  coefficient : ∀ a b : Vertex, (G.object a ⟶ G.object b) →ₗ[k] k
  normalized_scaled : ∀ {a b : Vertexᵒᵖ} (p : Quiver.Path b a),
    coefficient a.unop b.unop
        (LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p) =
      (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p)
  whisker_scaled : ∀ {a' a b b' : Vertexᵒᵖ}
      (p : Quiver.Path a a')
      (g : G.object a.unop ⟶ G.object b.unop)
      (q : Quiver.Path b' b) (r : Quiver.Path b' a'),
    coefficient a'.unop b'.unop
        (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) =
      coefficient a.unop b.unop g •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r)
  eq_zero_of_isEmpty : ∀ (a b : Vertex),
      IsEmpty (Quiver.Path (Opposite.op b) (Opposite.op a)) →
      ∀ g : G.object a ⟶ G.object b, coefficient a b g = 0

/-- A compatible literal table is a complete endpoint coefficient package
for the bound Figure-15 source. -/
def CompatibleLiteralEndpointTable.toEndpointCoefficientData
    {G : DiagramData (C := C)}
    (t : CompatibleLiteralEndpointTable (k := k) G) :
    EndpointCoefficientData (k := k) G where
  coefficient := t.table.coefficient
  normalized_scaled := t.normalized_scaled
  whisker_scaled := t.whisker_scaled
  eq_zero_of_isEmpty := t.table.coefficient_eq_zero_of_isEmpty

namespace EndpointCoefficientData

variable {G : DiagramData (C := C)}

/-- Path-indexed form of the endpoint table.  Thinness makes the functional
depend only on the ordered pair of endpoints. -/
def vertexCoefficient (h : EndpointCoefficientData (k := k) G)
    {a b : Vertexᵒᵖ} (_p : Quiver.Path b a) :
    (G.object a.unop ⟶ G.object b.unop) →ₗ[k] k :=
  h.coefficient a.unop b.unop

/-- The endpoint compiler produces the complete thin quotient-path package
for the bound Figure-15 source. -/
def toThinQuotientPathCoefficientData
    (h : EndpointCoefficientData (k := k) G) :
    ThinQuotientPathCoefficientData (k := k) (relationIdeal (k := k))
      (G.functor (k := k)) where
  path_subsingleton := path_subsingleton
  coefficient := fun p ↦ h.vertexCoefficient p
  normalized_scaled := by
    intro U V p
    have hmap : (G.functor (k := k)).map
          ((quotientFunctor (k := k)).map
            (LinearPathCategory.pathHom p)) =
        LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p := by
      unfold DiagramData.functor
      rw [quotientLift_map_quotient]
      unfold DiagramData.freeFunctor
      rw [LinearPathCategory.lift_map_pathHom]
    rw [hmap]
    exact h.normalized_scaled p
  whisker_scaled := by
    classical
    intro U' U V V' p g q r
    change G.object (LinearPathCategory.vertex U).unop ⟶
      G.object (LinearPathCategory.vertex V).unop at g
    have hpmap : (G.functor (k := k)).map
          ((quotientFunctor (k := k)).map
            (LinearPathCategory.pathHom p)) =
        LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p := by
      unfold DiagramData.functor
      rw [quotientLift_map_quotient]
      unfold DiagramData.freeFunctor
      rw [LinearPathCategory.lift_map_pathHom]
    have hqmap : (G.functor (k := k)).map
          ((quotientFunctor (k := k)).map
            (LinearPathCategory.pathHom q)) =
        LinearPathCategory.pathMap
          (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q := by
      unfold DiagramData.functor
      rw [quotientLift_map_quotient]
      unfold DiagramData.freeFunctor
      rw [LinearPathCategory.lift_map_pathHom]
    rw [hpmap, hqmap]
    change h.coefficient
        (LinearPathCategory.vertex U').unop
        (LinearPathCategory.vertex V').unop
        (LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ G.object x.unop) (fun e ↦ G.arrow e.unop) q) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) = _
    have hscaled := h.whisker_scaled p g q r
    rw [hscaled]
    by_cases hmiddle : Nonempty (Quiver.Path
        (LinearPathCategory.vertex V) (LinearPathCategory.vertex U))
    · rw [thinQuotientPathProjection_apply_of_nonempty
          (relationIdeal (k := k)) (G.functor (k := k))
          (fun s ↦ h.vertexCoefficient s) U V hmiddle g]
      let s := Classical.choice hmiddle
      rw [(path_subsingleton _ _).elim (Classical.choice hmiddle) s]
      have hr : r = q.comp (s.comp p) := (path_subsingleton _ _).elim _ _
      subst r
      dsimp only [s, vertexCoefficient]
      have hpath :
          (quotientFunctor (k := k)).map
                (LinearPathCategory.pathHom p) ≫
              (quotientFunctor (k := k)).map
                (LinearPathCategory.pathHom (Classical.choice hmiddle)) ≫
            (quotientFunctor (k := k)).map
              (LinearPathCategory.pathHom q) =
          (quotientFunctor (k := k)).map
            (LinearPathCategory.pathHom
              (q.comp ((Classical.choice hmiddle).comp p))) := by
        rw [← Functor.map_comp, LinearPathCategory.pathHom_comp,
          ← Functor.map_comp, LinearPathCategory.pathHom_comp,
          Quiver.Path.comp_assoc]
      change h.coefficient
            (LinearPathCategory.vertex U).unop
            (LinearPathCategory.vertex V).unop g •
          (quotientFunctor (k := k)).map
            (LinearPathCategory.pathHom
              (q.comp ((Classical.choice hmiddle).comp p))) =
        (quotientFunctor (k := k)).map
              (LinearPathCategory.pathHom p) ≫
            (h.coefficient
                (LinearPathCategory.vertex U).unop
                (LinearPathCategory.vertex V).unop g •
              (quotientFunctor (k := k)).map
                (LinearPathCategory.pathHom (Classical.choice hmiddle))) ≫
          (quotientFunctor (k := k)).map
            (LinearPathCategory.pathHom q)
      simp only [Linear.comp_smul, Linear.smul_comp, hpath]
    · have hmiddle' : IsEmpty (Quiver.Path
          (LinearPathCategory.vertex V) (LinearPathCategory.vertex U)) :=
        not_nonempty_iff.mp hmiddle
      rw [thinQuotientPathProjection_apply_of_isEmpty
          (relationIdeal (k := k)) (G.functor (k := k))
          (fun s ↦ h.vertexCoefficient s) U V hmiddle' g]
      have hzero := h.eq_zero_of_isEmpty
        (LinearPathCategory.vertex U).unop
        (LinearPathCategory.vertex V).unop
        (by simpa only [Opposite.op_unop] using hmiddle') g
      rw [hzero]
      simp

/-- Endpoint coefficients directly yield the BGRS 3.2 Hom-bifunctor
retraction for the bound Figure-15 diagram. -/
def homBifunctorRetraction
    (h : EndpointCoefficientData (k := k) G) :
    HomBifunctorRetraction (k := k) (G.functor (k := k)) :=
  h.toThinQuotientPathCoefficientData.homBifunctorRetraction

end EndpointCoefficientData

end LargeIndecomposable.CriticalSingularFigure15
