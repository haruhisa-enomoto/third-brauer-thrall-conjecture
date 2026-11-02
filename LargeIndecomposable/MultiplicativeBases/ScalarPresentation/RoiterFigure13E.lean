module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalCleavingTransfer
public import LargeIndecomposable.Foundations.CategoryTheory.LinearIdealQuotient
public import LargeIndecomposable.Foundations.PathCategories.LinearPathCategory
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import LargeIndecomposable.Foundations.CategoryTheory.LinearIdealQuotientLift

@[expose] public section

/-!
# The BGRS Figure 13E bound cleaving diagram

This file encodes the seven-vertex bound diagram `E` in the proof of BGRS
Figure 13.  Its source has the single displayed relation
`alphaCenter ≫ betaCenter = 0`.

The explicit one-parameter family has dimension vector
`(2,1,1,3,1,2,1)`.  In the order used below, its two nontrivial middle maps
are

```
  tauUpper(c) = [1 0; 0 1; c 1],
  tauLower    = [1 1 0; 0 0 1].
```

The four outer arrows are coordinate inclusions or projections.  Their flag
conditions force every morphism between parameters `c,d` to be scalar, while
the remaining `tauUpper` equation is `c*r = d*r`.  The calculation uses no
division and is therefore valid in every characteristic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.RoiterFigure13E

open LargeIndecomposable.PreadditiveHomIdeal
open LargeIndecomposable.CriticalSingularCleaving
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u

variable {k : Type u} [Field k]

/-- The seven occurrences in BGRS Figure 13E. -/
inductive Vertex
  | upperMiddle
  | upperRight
  | leftMiddle
  | center
  | rightMiddle
  | lowerMiddle
  | lowerLeft
  deriving DecidableEq

def vertexEquiv : Vertex ≃ Fin 7 where
  toFun
    | .upperMiddle => 0
    | .upperRight => 1
    | .leftMiddle => 2
    | .center => 3
    | .rightMiddle => 4
    | .lowerMiddle => 5
    | .lowerLeft => 6
  invFun
    | ⟨0, _⟩ => .upperMiddle
    | ⟨1, _⟩ => .upperRight
    | ⟨2, _⟩ => .leftMiddle
    | ⟨3, _⟩ => .center
    | ⟨4, _⟩ => .rightMiddle
    | ⟨5, _⟩ => .lowerMiddle
    | ⟨6, _⟩ => .lowerLeft
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Vertex := Fintype.ofEquiv (Fin 7) vertexEquiv.symm

/-- The six arrows in Figure 13E. -/
inductive Arrow : Vertex → Vertex → Type
  | tauUpper : Arrow .upperMiddle .center
  | betaUpper : Arrow .upperMiddle .upperRight
  | alphaCenter : Arrow .leftMiddle .center
  | betaCenter : Arrow .center .rightMiddle
  | tauLower : Arrow .center .lowerMiddle
  | alphaLower : Arrow .lowerLeft .lowerMiddle

instance : Quiver Vertex where Hom := Arrow

abbrev FreeLinearSource (k : Type u) [Field k] :=
  LinearPathCategory.Category k Vertexᵒᵖ

def vertexOppositeEquiv : Vertex ≃ Vertexᵒᵖ where
  toFun := Opposite.op
  invFun := Opposite.unop
  left_inv _ := rfl
  right_inv _ := rfl

instance vertexOppositeFintype : Fintype Vertexᵒᵖ :=
  Fintype.ofEquiv Vertex vertexOppositeEquiv

instance freeLinearSourceFintype : Fintype (FreeLinearSource k) :=
  Fintype.ofEquiv Vertexᵒᵖ (Equiv.refl Vertexᵒᵖ)

def freeVertexObj (a : Vertex) : FreeLinearSource k :=
  LinearPathCategory.obj k Vertexᵒᵖ (Opposite.op a)

def freeGeneratorHom {a b : Vertex} (e : a ⟶ b) :
    freeVertexObj (k := k) a ⟶ freeVertexObj (k := k) b :=
  LinearPathCategory.pathHom (Quiver.Hom.toPath (Quiver.Hom.op e))

/-- The length-two path displayed as zero in Figure 13E. -/
def mainComposite :
    freeVertexObj (k := k) .leftMiddle ⟶
      freeVertexObj (k := k) .rightMiddle :=
  freeGeneratorHom (k := k) Arrow.alphaCenter ≫
    freeGeneratorHom (k := k) Arrow.betaCenter

/-- A transport-stable singleton presentation of the displayed relation. -/
def relation (X Y : FreeLinearSource k) : Set (X ⟶ Y) :=
  {f | ∃ (hX : X = freeVertexObj (k := k) .leftMiddle)
      (hY : Y = freeVertexObj (k := k) .rightMiddle),
    f = eqToHom hX ≫ mainComposite (k := k) ≫ eqToHom hY.symm}

abbrev relationIdeal : HomIdeal (FreeLinearSource k) :=
  HomIdeal.linearSpan k (relation (k := k))

/-- The bound linear source of Figure 13E. -/
abbrev LinearSource := CategoryTheory.Quotient (relationIdeal (k := k)).rel

abbrev quotientFunctor : FreeLinearSource k ⥤ LinearSource (k := k) :=
  CategoryTheory.Quotient.functor (relationIdeal (k := k)).rel

instance linearSourcePreadditive : Preadditive (LinearSource (k := k)) :=
  (relationIdeal (k := k)).quotientPreadditive

instance quotientFunctorAdditive : (quotientFunctor (k := k)).Additive :=
  CategoryTheory.Quotient.functor_additive
    (relationIdeal (k := k)).rel
    (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
      (relationIdeal (k := k)).add_compatible f₁ f₂ g₁ g₂ hf hg)

instance linearSourceLinear : Linear k (LinearSource (k := k)) :=
  (relationIdeal (k := k)).quotientLinear

instance quotientFunctorLinear : (quotientFunctor (k := k)).Linear k :=
  (relationIdeal (k := k)).quotientFunctorLinear

instance linearSourceFintype : Fintype (LinearSource (k := k)) :=
  Fintype.ofEquiv (FreeLinearSource k)
    (CategoryTheory.Quotient.equiv (relationIdeal (k := k)).rel).symm

abbrev vertexObj (a : Vertex) : LinearSource (k := k) :=
  (quotientFunctor (k := k)).obj (freeVertexObj (k := k) a)

abbrev generatorHom {a b : Vertex} (e : a ⟶ b) :
    vertexObj (k := k) a ⟶ vertexObj (k := k) b :=
  (quotientFunctor (k := k)).map (freeGeneratorHom (k := k) e)

theorem mainComposite_zero :
    (quotientFunctor (k := k)).map (mainComposite (k := k)) = 0 := by
  rw [(relationIdeal (k := k)).map_eq_zero_iff]
  apply HomIdeal.relation_mem_linearSpan (relation (k := k))
  exact ⟨rfl, rfl, by simp⟩

section QuotientLift

universe v w

variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (F : FreeLinearSource k ⥤ C) [F.Additive] [F.Linear k]

theorem relationIdeal_isKilledBy
    (hmain : F.map (mainComposite (k := k)) = 0) :
    (relationIdeal (k := k)).IsKilledBy F := by
  apply HomIdeal.linearSpan_le (relation (k := k))
    (HomIdeal.functorKernel (k := k) F)
  intro X Y r hr
  rw [HomIdeal.mem_functorKernel_iff]
  rcases hr with ⟨hX, hY, rfl⟩
  subst X
  subst Y
  simp only [F.map_comp]
  rw [hmain]
  simp

/-- Descend a free diagram which kills the displayed composite. -/
def quotientLift
    (hmain : F.map (mainComposite (k := k)) = 0) :
    LinearSource (k := k) ⥤ C :=
  (relationIdeal (k := k)).quotientLift F
    (relationIdeal_isKilledBy F hmain)

instance quotientLift_additive
    (hmain : F.map (mainComposite (k := k)) = 0) :
    (quotientLift F hmain).Additive := by
  unfold quotientLift
  infer_instance

instance quotientLift_linear
    (hmain : F.map (mainComposite (k := k)) = 0) :
    (quotientLift F hmain).Linear k := by
  unfold quotientLift
  infer_instance

@[simp] theorem quotientLift_map_quotient
    (hmain : F.map (mainComposite (k := k)) = 0)
    {X Y : FreeLinearSource k} (f : X ⟶ Y) :
    (quotientLift F hmain).map ((quotientFunctor (k := k)).map f) = F.map f :=
  rfl

end QuotientLift

abbrev Central := ModuleCat.of k (Fin 3 → k)
abbrev Branch := ModuleCat.of k (Fin 2 → k)
abbrev Leaf := ModuleCat.of k k

abbrev obj : Vertex → ModuleCat k
  | .upperMiddle | .lowerMiddle => Branch (k := k)
  | .center => Central (k := k)
  | .upperRight | .leftMiddle | .rightMiddle | .lowerLeft => Leaf (k := k)

def basis3 (i : Fin 3) : Central (k := k) := Pi.single i 1
def basis2 (i : Fin 2) : Branch (k := k) := Pi.single i 1

@[simp] private theorem basis3_apply (i j : Fin 3) :
    basis3 (k := k) i j = if i = j then 1 else 0 := by
  simp [basis3, Pi.single_apply, eq_comm]

@[simp] private theorem basis2_apply (i j : Fin 2) :
    basis2 (k := k) i j = if i = j then 1 else 0 := by
  simp [basis2, Pi.single_apply, eq_comm]

def tauUpperMap (c : k) : Branch (k := k) ⟶ Central (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦
        if i = 0 then x 0 else if i = 1 then x 1 else c * x 0 + x 1
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [mul_add] <;> abel
      map_smul' := by
        intro a x
        funext i
        fin_cases i <;> simp <;> ring }

def betaUpperMap : Branch (k := k) ⟶ Leaf (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ x 0
      map_add' := by intros; simp
      map_smul' := by intros; simp }

def alphaCenterMap : Leaf (k := k) ⟶ Central (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then x else 0
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro c x; funext i; fin_cases i <;> simp }

def betaCenterMap : Central (k := k) ⟶ Leaf (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ x 1
      map_add' := by intros; simp
      map_smul' := by intros; simp }

def tauLowerMap : Central (k := k) ⟶ Branch (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then x 0 + x 1 else x 2
      map_add' := by intro x y; funext i; fin_cases i <;> simp <;> abel
      map_smul' := by intro c x; funext i; fin_cases i <;> simp <;> ring }

def alphaLowerMap : Leaf (k := k) ⟶ Branch (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then 0 else x
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro c x; funext i; fin_cases i <;> simp }

def arrowMap (c : k) {a b : Vertex} :
    (a ⟶ b) → (obj (k := k) a ⟶ obj (k := k) b)
  | .tauUpper => tauUpperMap (k := k) c
  | .betaUpper => betaUpperMap (k := k)
  | .alphaCenter => alphaCenterMap (k := k)
  | .betaCenter => betaCenterMap (k := k)
  | .tauLower => tauLowerMap (k := k)
  | .alphaLower => alphaLowerMap (k := k)

def freeModule (c : k) : FreeLinearSource k ⥤ ModuleCat k :=
  LinearPathCategory.lift
    (fun a ↦ obj (k := k) a.unop)
    (fun e ↦ arrowMap (k := k) c e.unop)

instance freeModule_additive (c : k) : (freeModule (k := k) c).Additive := by
  unfold freeModule
  infer_instance

instance freeModule_linear (c : k) : (freeModule (k := k) c).Linear k := by
  unfold freeModule
  infer_instance

@[simp] private theorem freeModule_map_generator (c : k)
    {a b : Vertex} (e : a ⟶ b) :
    (freeModule (k := k) c).map (freeGeneratorHom (k := k) e) =
      arrowMap (k := k) c e := by
  unfold freeModule freeGeneratorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

theorem freeModule_mainComposite_zero (c : k) :
    (freeModule (k := k) c).map (mainComposite (k := k)) = 0 := by
  unfold mainComposite
  rw [Functor.map_comp]
  simp only [freeModule_map_generator]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change betaCenterMap (k := k) (alphaCenterMap (k := k) x) = 0
  simp [alphaCenterMap, betaCenterMap]

/-- The explicit Figure-13E module of parameter `c`. -/
def module (c : k) : LinearSource (k := k) ⥤ ModuleCat k :=
  quotientLift (freeModule (k := k) c) (freeModule_mainComposite_zero c)

instance module_additive (c : k) : (module (k := k) c).Additive := by
  unfold module
  infer_instance

instance module_linear (c : k) : (module (k := k) c).Linear k := by
  unfold module
  infer_instance

@[simp] theorem module_obj (c : k) (a : Vertex) :
    (module (k := k) c).obj (vertexObj (k := k) a) = obj (k := k) a := rfl

@[simp] theorem module_map_generator (c : k) {a b : Vertex} (e : a ⟶ b) :
    (module (k := k) c).map (generatorHom (k := k) e) =
      arrowMap (k := k) c e := by
  unfold module generatorHom
  rw [quotientLift_map_quotient]
  exact freeModule_map_generator c e

/-- Every morphism in the explicit family is scalar, and its scalar satisfies
the one parameter equation. -/
def HasScalarControl : Prop :=
  ∀ {c d : k} (f : module (k := k) c ⟶ module d),
    ∃ r : k,
      c * r = d * r ∧
      ∀ (a : Vertex) (x : obj (k := k) a),
        f.app (vertexObj (k := k) a) x = r • x

def upperComponent {c d : k}
    (f : module (k := k) c ⟶ module d) :
    Branch (k := k) ⟶ Branch (k := k) :=
  f.app (vertexObj (k := k) .upperMiddle)

def centerComponent {c d : k}
    (f : module (k := k) c ⟶ module d) :
    Central (k := k) ⟶ Central (k := k) :=
  f.app (vertexObj (k := k) .center)

def lowerComponent {c d : k}
    (f : module (k := k) c ⟶ module d) :
    Branch (k := k) ⟶ Branch (k := k) :=
  f.app (vertexObj (k := k) .lowerMiddle)

def leafComponent {c d : k}
    (f : module (k := k) c ⟶ module d) (a : Vertex) :
    obj (k := k) a ⟶ obj (k := k) a :=
  f.app (vertexObj (k := k) a)

def coeff {c d : k}
    (f : module (k := k) c ⟶ module d) : k :=
  leafComponent f .leftMiddle 1

def upperCoeff {c d : k}
    (f : module (k := k) c ⟶ module d) : k :=
  leafComponent f .upperRight 1

def rightCoeff {c d : k}
    (f : module (k := k) c ⟶ module d) : k :=
  leafComponent f .rightMiddle 1

def lowerCoeff {c d : k}
    (f : module (k := k) c ⟶ module d) : k :=
  leafComponent f .lowerLeft 1

@[simp] private theorem tauUpperMap_basis_zero (c : k) :
    tauUpperMap (k := k) c (basis2 (k := k) 0) =
      basis3 (k := k) 0 + c • basis3 (k := k) 2 := by
  funext i
  fin_cases i <;> simp [tauUpperMap, basis2, basis3]

@[simp] private theorem tauUpperMap_basis_one (c : k) :
    tauUpperMap (k := k) c (basis2 (k := k) 1) =
      basis3 (k := k) 1 + basis3 (k := k) 2 := by
  funext i
  fin_cases i <;> simp [tauUpperMap, basis2, basis3]

@[simp] private theorem tauLowerMap_basis_zero :
    tauLowerMap (k := k) (basis3 (k := k) 0) = basis2 (k := k) 0 := by
  funext i
  fin_cases i <;> simp [tauLowerMap, basis3, basis2]

@[simp] private theorem tauLowerMap_basis_one :
    tauLowerMap (k := k) (basis3 (k := k) 1) = basis2 (k := k) 0 := by
  funext i
  fin_cases i <;> simp [tauLowerMap, basis3, basis2]

@[simp] private theorem tauLowerMap_basis_two :
    tauLowerMap (k := k) (basis3 (k := k) 2) = basis2 (k := k) 1 := by
  funext i
  fin_cases i <;> simp [tauLowerMap, basis3, basis2]

private theorem naturality_tauUpper {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Branch (k := k)) :
    centerComponent f (tauUpperMap (k := k) c x) =
      tauUpperMap (k := k) d (upperComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.tauUpper)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Branch (k := k) ⟶ Central (k := k) ↦ q x) h

private theorem naturality_tauLower {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Central (k := k)) :
    lowerComponent f (tauLowerMap (k := k) x) =
      tauLowerMap (k := k) (centerComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.tauLower)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Central (k := k) ⟶ Branch (k := k) ↦ q x) h

private theorem naturality_betaUpper {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Branch (k := k)) :
    leafComponent f .upperRight (betaUpperMap (k := k) x) =
      betaUpperMap (k := k) (upperComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.betaUpper)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Branch (k := k) ⟶ Leaf (k := k) ↦ q x) h

private theorem naturality_betaCenter {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Central (k := k)) :
    leafComponent f .rightMiddle (betaCenterMap (k := k) x) =
      betaCenterMap (k := k) (centerComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.betaCenter)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Central (k := k) ⟶ Leaf (k := k) ↦ q x) h

private theorem center_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    centerComponent f (basis3 (k := k) 0) =
      coeff f • basis3 (k := k) 0 := by
  have h := f.naturality (generatorHom (k := k) Arrow.alphaCenter)
  simp only [module_map_generator] at h
  have h1 := congrArg
    (fun q : Leaf (k := k) ⟶ Central (k := k) ↦ q 1) h
  change centerComponent f (alphaCenterMap (k := k) 1) =
    alphaCenterMap (k := k) (leafComponent f .leftMiddle 1) at h1
  calc
    centerComponent f (basis3 (k := k) 0) =
        centerComponent f (alphaCenterMap (k := k) 1) := by
      congr 1
      funext i
      fin_cases i <;> simp [alphaCenterMap, basis3]
    _ = alphaCenterMap (k := k) (leafComponent f .leftMiddle 1) := h1
    _ = coeff f • basis3 (k := k) 0 := by
      funext i
      fin_cases i <;> simp [alphaCenterMap, basis3, coeff]

private theorem lower_basis_one {c d : k}
    (f : module (k := k) c ⟶ module d) :
    lowerComponent f (basis2 (k := k) 1) =
      lowerCoeff f • basis2 (k := k) 1 := by
  have h := f.naturality (generatorHom (k := k) Arrow.alphaLower)
  simp only [module_map_generator] at h
  have h1 := congrArg
    (fun q : Leaf (k := k) ⟶ Branch (k := k) ↦ q 1) h
  change lowerComponent f (alphaLowerMap (k := k) 1) =
    alphaLowerMap (k := k) (leafComponent f .lowerLeft 1) at h1
  calc
    lowerComponent f (basis2 (k := k) 1) =
        lowerComponent f (alphaLowerMap (k := k) 1) := by
      congr 1
      funext i
      fin_cases i <;> simp [alphaLowerMap, basis2]
    _ = alphaLowerMap (k := k) (leafComponent f .lowerLeft 1) := h1
    _ = lowerCoeff f • basis2 (k := k) 1 := by
      funext i
      fin_cases i <;> simp [alphaLowerMap, basis2, lowerCoeff]

private theorem upper_basis_zero_shape {c d : k}
    (f : module (k := k) c ⟶ module d) :
    upperComponent f (basis2 (k := k) 0) =
      upperCoeff f • basis2 (k := k) 0 +
        (upperComponent f (basis2 (k := k) 0) 1) • basis2 (k := k) 1 := by
  have h0 := naturality_betaUpper f (basis2 (k := k) 0)
  have hc0 : upperComponent f (basis2 (k := k) 0) 0 = upperCoeff f := by
    simpa [betaUpperMap, basis2, upperCoeff] using h0.symm
  funext i
  fin_cases i
  · simpa [basis2_apply] using hc0
  · simp [basis2_apply]

private theorem upper_basis_one_shape {c d : k}
    (f : module (k := k) c ⟶ module d) :
    upperComponent f (basis2 (k := k) 1) =
      (upperComponent f (basis2 (k := k) 1) 1) • basis2 (k := k) 1 := by
  have h1 := naturality_betaUpper f (basis2 (k := k) 1)
  have hc0 : upperComponent f (basis2 (k := k) 1) 0 = 0 := by
    simpa [betaUpperMap, basis2] using h1.symm
  funext i
  fin_cases i
  · simpa [basis2_apply] using hc0
  · simp [basis2_apply]

private theorem center_basis_one_shape {c d : k}
    (f : module (k := k) c ⟶ module d) :
    centerComponent f (basis3 (k := k) 1) =
      (centerComponent f (basis3 (k := k) 1) 0) • basis3 (k := k) 0 +
        rightCoeff f • basis3 (k := k) 1 +
          (centerComponent f (basis3 (k := k) 1) 2) • basis3 (k := k) 2 := by
  have h1 := naturality_betaCenter f (basis3 (k := k) 1)
  have hc1 : centerComponent f (basis3 (k := k) 1) 1 = rightCoeff f := by
    simpa [betaCenterMap, basis3, rightCoeff] using h1.symm
  funext i
  fin_cases i
  · simp [basis3_apply]
  · simpa [basis3_apply] using hc1
  · simp [basis3_apply]

private theorem center_basis_two_shape {c d : k}
    (f : module (k := k) c ⟶ module d) :
    centerComponent f (basis3 (k := k) 2) =
      (centerComponent f (basis3 (k := k) 2) 0) • basis3 (k := k) 0 +
        (centerComponent f (basis3 (k := k) 2) 2) • basis3 (k := k) 2 := by
  have h2 := naturality_betaCenter f (basis3 (k := k) 2)
  have hc1 : centerComponent f (basis3 (k := k) 2) 1 = 0 := by
    simpa [betaCenterMap, basis3] using h2.symm
  funext i
  fin_cases i
  · simp [basis3_apply]
  · simpa [basis3_apply] using hc1
  · simp [basis3_apply]

private theorem coefficient_relations {c d : k}
    (f : module (k := k) c ⟶ module d) :
    centerComponent f (basis3 (k := k) 1) 0 = 0 ∧
      centerComponent f (basis3 (k := k) 1) 2 = 0 ∧
      centerComponent f (basis3 (k := k) 2) 0 = 0 ∧
      centerComponent f (basis3 (k := k) 2) 2 = coeff f ∧
      rightCoeff f = coeff f ∧
      upperComponent f (basis2 (k := k) 1) 1 = coeff f ∧
      lowerCoeff f = coeff f ∧
      upperCoeff f = coeff f ∧
      upperComponent f (basis2 (k := k) 0) 1 = 0 ∧
      c * coeff f = d * coeff f := by
  have hlower0 := naturality_tauLower f (basis3 (k := k) 0)
  rw [tauLowerMap_basis_zero, center_basis_zero, map_smul,
    tauLowerMap_basis_zero] at hlower0

  have hlower1 := naturality_tauLower f (basis3 (k := k) 1)
  rw [tauLowerMap_basis_one, hlower0, center_basis_one_shape,
    map_add, map_add, map_smul, map_smul, map_smul,
    tauLowerMap_basis_zero, tauLowerMap_basis_one,
    tauLowerMap_basis_two] at hlower1
  have hsum : coeff f =
      centerComponent f (basis3 (k := k) 1) 0 + rightCoeff f := by
    have h := congrArg (fun y : Branch (k := k) ↦ y 0) hlower1
    simpa [basis2_apply] using h
  have hw : centerComponent f (basis3 (k := k) 1) 2 = 0 := by
    have h := congrArg (fun y : Branch (k := k) ↦ y 1) hlower1
    simpa [basis2_apply] using h.symm

  have hlower2 := naturality_tauLower f (basis3 (k := k) 2)
  rw [tauLowerMap_basis_two, lower_basis_one, center_basis_two_shape,
    map_add, map_smul, map_smul, tauLowerMap_basis_zero,
    tauLowerMap_basis_two] at hlower2
  have hv : centerComponent f (basis3 (k := k) 2) 0 = 0 := by
    have h := congrArg (fun y : Branch (k := k) ↦ y 0) hlower2
    simpa [basis2_apply] using h.symm
  have hz : centerComponent f (basis3 (k := k) 2) 2 = lowerCoeff f := by
    have h := congrArg (fun y : Branch (k := k) ↦ y 1) hlower2
    simpa [basis2_apply] using h.symm

  have hupper1 := naturality_tauUpper f (basis2 (k := k) 1)
  rw [tauUpperMap_basis_one, map_add, center_basis_one_shape,
    center_basis_two_shape, upper_basis_one_shape, map_smul,
    tauUpperMap_basis_one] at hupper1
  have huv : centerComponent f (basis3 (k := k) 1) 0 +
      centerComponent f (basis3 (k := k) 2) 0 = 0 := by
    have h := congrArg (fun y : Central (k := k) ↦ y 0) hupper1
    simpa [basis3_apply] using h
  have hq : rightCoeff f =
      upperComponent f (basis2 (k := k) 1) 1 := by
    have h := congrArg (fun y : Central (k := k) ↦ y 1) hupper1
    simpa [basis3_apply] using h
  have hwz : centerComponent f (basis3 (k := k) 1) 2 +
      centerComponent f (basis3 (k := k) 2) 2 =
        upperComponent f (basis2 (k := k) 1) 1 := by
    have h := congrArg (fun y : Central (k := k) ↦ y 2) hupper1
    simpa [basis3_apply] using h
  have hu : centerComponent f (basis3 (k := k) 1) 0 = 0 := by
    rw [hv, add_zero] at huv
    exact huv
  have hright : rightCoeff f = coeff f := by
    rw [hu, zero_add] at hsum
    exact hsum.symm
  have hupperOne : upperComponent f (basis2 (k := k) 1) 1 = coeff f :=
    hq.symm.trans hright
  have hlower : lowerCoeff f = coeff f := by
    rw [hw, zero_add, hz, hupperOne] at hwz
    exact hwz
  have hcenterTwo : centerComponent f (basis3 (k := k) 2) 2 = coeff f :=
    hz.trans hlower

  have hupper0 := naturality_tauUpper f (basis2 (k := k) 0)
  rw [tauUpperMap_basis_zero, map_add, map_smul, center_basis_zero,
    center_basis_two_shape, hv, hcenterTwo, zero_smul, zero_add,
    upper_basis_zero_shape, map_add, map_smul, map_smul,
    tauUpperMap_basis_zero, tauUpperMap_basis_one] at hupper0
  have hupper : upperCoeff f = coeff f := by
    have h := congrArg (fun y : Central (k := k) ↦ y 0) hupper0
    simpa [basis3_apply] using h.symm
  have hp : upperComponent f (basis2 (k := k) 0) 1 = 0 := by
    have h := congrArg (fun y : Central (k := k) ↦ y 1) hupper0
    simpa [basis3_apply] using h.symm
  have hparameter : c * coeff f = d * coeff f := by
    have h := congrArg (fun y : Central (k := k) ↦ y 2) hupper0
    have hcd : c * coeff f = coeff f * d := by
      simpa [basis3_apply, hupper, hp] using h
    exact hcd.trans (mul_comm (coeff f) d)
  exact ⟨hu, hw, hv, hcenterTwo, hright, hupperOne, hlower,
    hupper, hp, hparameter⟩

private theorem upper_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Branch (k := k)) :
    upperComponent f x = coeff f • x := by
  rcases coefficient_relations f with
    ⟨_, _, _, _, _, hone, _, hupper, hp, _⟩
  have h0 : upperComponent f (basis2 (k := k) 0) =
      coeff f • basis2 (k := k) 0 := by
    rw [upper_basis_zero_shape, hupper, hp, zero_smul, add_zero]
  have h1 : upperComponent f (basis2 (k := k) 1) =
      coeff f • basis2 (k := k) 1 := by
    rw [upper_basis_one_shape, hone]
  have hx : x = x 0 • basis2 (k := k) 0 + x 1 • basis2 (k := k) 1 := by
    funext i
    fin_cases i <;> simp [basis2]
  rw [hx, map_add, map_smul, map_smul, h0, h1]
  module

private theorem center_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Central (k := k)) :
    centerComponent f x = coeff f • x := by
  rcases coefficient_relations f with
    ⟨hu, hw, hv, hz, hright, _, _, _, _, _⟩
  have h1 : centerComponent f (basis3 (k := k) 1) =
      coeff f • basis3 (k := k) 1 := by
    rw [center_basis_one_shape, hu, hw, hright]
    simp
  have h2 : centerComponent f (basis3 (k := k) 2) =
      coeff f • basis3 (k := k) 2 := by
    rw [center_basis_two_shape, hv, hz, zero_smul, zero_add]
  have hx : x = x 0 • basis3 (k := k) 0 +
      x 1 • basis3 (k := k) 1 + x 2 • basis3 (k := k) 2 := by
    funext i
    fin_cases i <;> simp [basis3]
  rw [hx, map_add, map_add, map_smul, map_smul, map_smul,
    center_basis_zero, h1, h2]
  module

private theorem lower_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    lowerComponent f (basis2 (k := k) 0) =
      coeff f • basis2 (k := k) 0 := by
  have h := naturality_tauLower f (basis3 (k := k) 0)
  rw [tauLowerMap_basis_zero, center_basis_zero, map_smul,
    tauLowerMap_basis_zero] at h
  exact h

private theorem lower_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Branch (k := k)) :
    lowerComponent f x = coeff f • x := by
  rcases coefficient_relations f with ⟨_, _, _, _, _, _, hlower, _, _, _⟩
  have h1 : lowerComponent f (basis2 (k := k) 1) =
      coeff f • basis2 (k := k) 1 := by
    rw [lower_basis_one, hlower]
  have hx : x = x 0 • basis2 (k := k) 0 + x 1 • basis2 (k := k) 1 := by
    funext i
    fin_cases i <;> simp [basis2]
  rw [hx, map_add, map_smul, map_smul, lower_basis_zero, h1]
  module

private theorem leaf_map_eq_mul (g : Leaf (k := k) ⟶ Leaf (k := k))
    (x : k) : g x = x * g 1 := by
  simpa using g.hom.map_smul x 1

/-- The characteristic-free matrix calculation for the explicit Figure-13E
family. -/
theorem hasScalarControl : HasScalarControl (k := k) := by
  intro c d f
  rcases coefficient_relations f with
    ⟨_, _, _, _, hright, _, hlower, hupper, _, hparameter⟩
  refine ⟨coeff f, hparameter, ?_⟩
  intro a x
  cases a with
  | upperMiddle => exact upper_scalar f x
  | center => exact center_scalar f x
  | lowerMiddle => exact lower_scalar f x
  | leftMiddle =>
      change leafComponent f .leftMiddle x = coeff f • x
      rw [leaf_map_eq_mul]
      change x * coeff f = coeff f * x
      exact mul_comm _ _
  | upperRight =>
      change leafComponent f .upperRight x = coeff f • x
      rw [leaf_map_eq_mul]
      change x * upperCoeff f = coeff f • x
      rw [hupper]
      change x * coeff f = coeff f * x
      exact mul_comm _ _
  | rightMiddle =>
      change leafComponent f .rightMiddle x = coeff f • x
      rw [leaf_map_eq_mul]
      change x * rightCoeff f = coeff f • x
      rw [hright]
      change x * coeff f = coeff f * x
      exact mul_comm _ _
  | lowerLeft =>
      change leafComponent f .lowerLeft x = coeff f • x
      rw [leaf_map_eq_mul]
      change x * lowerCoeff f = coeff f • x
      rw [hlower]
      change x * coeff f = coeff f * x
      exact mul_comm _ _

section ControlledFamily

theorem parameter_eq_of_iso {c d : k}
    (hcontrol : HasScalarControl (k := k))
    (e : module (k := k) c ≅ module d) : c = d := by
  obtain ⟨r, hr, hscalar⟩ := hcontrol e.hom
  have hr0 : r ≠ 0 := by
    intro hz
    let X : LinearSource (k := k) := vertexObj (k := k) .leftMiddle
    have hhom := hscalar .leftMiddle (1 : obj (k := k) .leftMiddle)
    rw [hz, zero_smul] at hhom
    have hzeroImage :
        e.hom.app X (0 : k) = (0 : (module (k := k) d).obj X) :=
      map_zero _
    have heq : e.hom.app X (1 : k) = e.hom.app X (0 : k) :=
      hhom.trans hzeroImage.symm
    have honezero : (1 : k) = 0 :=
      (ConcreteCategory.bijective_of_isIso (e.hom.app X)).1 heq
    exact one_ne_zero honezero
  exact mul_right_cancel₀ hr0 hr

theorem end_eq_zero_or_id_of_idempotent (c : k)
    (hcontrol : HasScalarControl (k := k))
    (f : module (k := k) c ⟶ module c) (hf : f ≫ f = f) :
    f = 0 ∨ f = 𝟙 _ := by
  obtain ⟨r, _, hscalar⟩ := hcontrol f
  have hr : r * r = r := by
    have h := congrArg
      (fun g : module (k := k) c ⟶ module c ↦
        g.app (vertexObj (k := k) .leftMiddle) (1 : k)) hf
    change f.app (vertexObj (k := k) .leftMiddle)
      (f.app (vertexObj (k := k) .leftMiddle) (1 : k)) =
        f.app (vertexObj (k := k) .leftMiddle) (1 : k) at h
    rw [hscalar, hscalar] at h
    simpa [smul_smul] using h
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [pow_two] using hr) with h0 | h1
  · left
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases X with ⟨X⟩
    change f.app (vertexObj (k := k) X.unop) x = 0
    rw [hscalar X.unop, h0, zero_smul]
  · right
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases X with ⟨X⟩
    change f.app (vertexObj (k := k) X.unop) x = x
    rw [hscalar X.unop, h1, one_smul]

theorem module_not_isZero (c : k) : ¬ IsZero (module (k := k) c) := by
  intro hzero
  have hid : (𝟙 (module (k := k) c) : module c ⟶ module c) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hzero
  have h := congrArg
    (fun f : module (k := k) c ⟶ module c ↦
      f.app (vertexObj (k := k) .leftMiddle) (1 : k)) hid
  change (1 : k) = 0 at h
  exact one_ne_zero h

theorem module_indecomposable
    (hcontrol : HasScalarControl (k := k)) (c : k) :
    Indecomposable (module (k := k) c) := by
  refine ⟨module_not_isZero c, ?_⟩
  intro Y Z e
  let p : module (k := k) c ⟶ module c :=
    e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by simp [p, Category.assoc]
  rcases end_eq_zero_or_id_of_idempotent c hcontrol p hp with hp0 | hp1
  · left
    apply (IsZero.iff_id_eq_zero Y).mpr
    calc
      𝟙 Y = (biprod.inl ≫ e.inv) ≫ p ≫ (e.hom ≫ biprod.fst) := by
        dsimp [p]
        simp
      _ = 0 := by rw [hp0]; simp
  · right
    apply (IsZero.iff_id_eq_zero Z).mpr
    calc
      𝟙 Z = (biprod.inr ≫ e.inv) ≫ p ≫ (e.hom ≫ biprod.snd) := by
        rw [hp1]
        simp
      _ = 0 := by dsimp [p]; simp

instance module_obj_finite (c : k) (X : LinearSource (k := k)) :
    Module.Finite k ((module (k := k) c).obj X) := by
  change Module.Finite k (obj (k := k)
    (LinearPathCategory.vertex X.as).unop)
  unfold obj Central Branch Leaf
  cases (LinearPathCategory.vertex X.as).unop <;> infer_instance

theorem module_end_isLocalRing (c : k) :
    IsLocalRing (CategoryTheory.End (module (k := k) c)) :=
  LargeIndecomposable.ClosedZigzagTransfer.functor_end_isLocalRing
    (module (k := k) c) (fun X ↦ module_obj_finite c X)
      (module_indecomposable (hasScalarControl (k := k)) c)

section Infinite

variable [Infinite k]

def family (n : ℕ) : LinearSource (k := k) ⥤ ModuleCat k :=
  module (Infinite.natEmbedding k n)

instance family_additive (n : ℕ) : (family (k := k) n).Additive := by
  unfold family
  infer_instance

instance family_linear (n : ℕ) : (family (k := k) n).Linear k := by
  unfold family
  infer_instance

theorem family_obj_finite (n : ℕ) (X : LinearSource (k := k)) :
    Module.Finite k ((family (k := k) n).obj X) := by
  unfold family
  exact module_obj_finite _ X

theorem family_indecomposable (n : ℕ) :
    Indecomposable (family (k := k) n) :=
  module_indecomposable (hasScalarControl (k := k)) _

theorem family_eq_of_iso {m n : ℕ}
    (e : family (k := k) m ≅ family n) : m = n := by
  apply (Infinite.natEmbedding k).injective
  exact parameter_eq_of_iso (hasScalarControl (k := k)) e

theorem family_end_isLocalRing (n : ℕ) :
    IsLocalRing (CategoryTheory.End (family (k := k) n)) := by
  unfold family
  exact module_end_isLocalRing _

def sourceFamily :
    CleavingSourceFamily (k := k) (LinearSource (k := k)) where
  anchor := vertexObj (k := k) .center
  module := family (k := k)
  additive := fun _ ↦ inferInstance
  linear := fun _ ↦ inferInstance
  obj_finite := family_obj_finite
  indecomposable := family_indecomposable
  eq_of_iso := fun h ↦ family_eq_of_iso (Classical.choice h)
  end_isLocalRing := family_end_isLocalRing

end Infinite

end ControlledFamily

section Diagram

universe v w

variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- Literal ambient Figure-13E data, including its displayed zero relation. -/
structure DiagramData where
  object : Vertex → C
  arrow : ∀ {a b : Vertex}, (a ⟶ b) → (object a ⟶ object b)
  main_zero : arrow Arrow.alphaCenter ≫ arrow Arrow.betaCenter = 0

namespace DiagramData

def freeFunctor (G : DiagramData (C := C)) : FreeLinearSource k ⥤ C :=
  LinearPathCategory.lift
    (fun a ↦ G.object a.unop)
    (fun e ↦ G.arrow e.unop)

instance freeFunctor_additive (G : DiagramData (C := C)) :
    (G.freeFunctor (k := k)).Additive := by unfold freeFunctor; infer_instance

instance freeFunctor_linear (G : DiagramData (C := C)) :
    (G.freeFunctor (k := k)).Linear k := by unfold freeFunctor; infer_instance

@[simp] theorem freeFunctor_map_generator (G : DiagramData (C := C))
    {a b : Vertex} (e : a ⟶ b) :
    (G.freeFunctor (k := k)).map (freeGeneratorHom (k := k) e) =
      G.arrow e := by
  unfold freeFunctor freeGeneratorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

theorem freeFunctor_main_zero (G : DiagramData (C := C)) :
    (G.freeFunctor (k := k)).map (mainComposite (k := k)) = 0 := by
  unfold mainComposite
  rw [Functor.map_comp]
  simp only [freeFunctor_map_generator]
  exact G.main_zero

def functor (G : DiagramData (C := C)) : LinearSource (k := k) ⥤ C :=
  quotientLift (G.freeFunctor (k := k)) (G.freeFunctor_main_zero (k := k))

instance functor_additive (G : DiagramData (C := C)) :
    (G.functor (k := k)).Additive := by unfold functor; infer_instance

instance functor_linear (G : DiagramData (C := C)) :
    (G.functor (k := k)).Linear k := by unfold functor; infer_instance

@[simp] theorem functor_obj (G : DiagramData (C := C)) (a : Vertex) :
    (G.functor (k := k)).obj (vertexObj (k := k) a) = G.object a := rfl

@[simp] theorem functor_map_generator (G : DiagramData (C := C))
    {a b : Vertex} (e : a ⟶ b) :
    (G.functor (k := k)).map (generatorHom (k := k) e) = G.arrow e := by
  unfold functor generatorHom
  rw [quotientLift_map_quotient]
  exact G.freeFunctor_map_generator (k := k) e

end DiagramData

end Diagram

section AmbientContradiction

universe uA x

variable [Infinite k]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

/-- Exact Figure-13E contradiction boundary.  The representation-infinite
bound source is proved above; an ambient application supplies its literal
Hom-bifunctor retraction. -/
theorem not_isRepresentationFinite_of_figure13EData
    (G : DiagramData (C := S.ProjectiveCategory))
    (hG : HomBifunctorRetraction (k := k) (G.functor (k := k))) :
    ¬ LargeIndecomposable.IsRepresentationFinite k A :=
  CriticalSingularCleaving.not_isRepresentationFinite_of_homBifunctorRetraction
    (S := S) (D := G.functor (k := k))
      (sourceFamily (k := k)) hG

end AmbientContradiction

end LargeIndecomposable.RoiterFigure13E
