module

public import LargeIndecomposable.Cleaving.ClosedChains.CoendExtension
public import LargeIndecomposable.Cleaving.ClosedChains.GenericFiniteness
public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueCategory
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackle
public import Mathlib.Data.Fintype.Card
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import LargeIndecomposable.Modules.KrullSchmidt.LocalEndFiniteDimensional
public import LargeIndecomposable.Cleaving.ClosedChains.ProjectiveModuleRealization
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteUniverse
public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayCategory
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayPathLift
public import LargeIndecomposable.RayCategories.Basic.RayMorphismDepth
public import LargeIndecomposable.Cleaving.ClosedChains.SupplementRetraction
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Category.ULift

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.ClosedZigzagCrossUniverse

universe u vK wK vC wC

variable {k : Type u} [Field k]

/-! `ULiftHom` supplies the common large Hom universe needed by the existing
coend implementation.  The additive and linear structures are the evident
ones obtained by lifting the original Hom groups and modules. -/

local instance uliftHomPreadditive
    {C : Type vC} [Category.{wC} C] [Preadditive C] :
    Preadditive (ULiftHom.{max wK wC} C) where
  homGroup _ _ := ULift.addCommGroup
  add_comp _ _ _ f g h := by
    apply ULift.down_injective
    exact Preadditive.add_comp _ _ _ f.down g.down h.down
  comp_add _ _ _ f g h := by
    apply ULift.down_injective
    exact Preadditive.comp_add _ _ _ f.down g.down h.down

local instance uliftHomLinear
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C] :
    Linear k (ULiftHom.{max wK wC} C) where
  homModule _ _ := ULift.module'
  smul_comp _ _ _ r f g := by
    apply ULift.down_injective
    exact Linear.smul_comp _ _ _ r f.down g.down
  comp_smul _ _ _ f r g := by
    apply ULift.down_injective
    exact Linear.comp_smul _ _ _ f.down r g.down

/-- Hom-bifunctor retraction with independent source and target Hom
universes.  `LinearMap` itself needs no resizing: its domain and codomain may
live in different universes. -/
structure HomBifunctorRetraction
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Additive] [D.Linear k] where
  retraction : ∀ X Y : K, (D.obj X ⟶ D.obj Y) →ₗ[k] (X ⟶ Y)
  map_retraction : ∀ {X Y : K} (f : X ⟶ Y),
    retraction X Y (D.map f) = f
  naturality : ∀ {X' X Y Y' : K} (a : X' ⟶ X)
      (g : D.obj X ⟶ D.obj Y) (b : Y ⟶ Y'),
    retraction X' Y' (D.map a ≫ g ≫ D.map b) =
      a ≫ retraction X Y g ≫ b

/-- Compatibility inclusion of the original same-Hom-universe interface. -/
def HomBifunctorRetraction.ofLegacy
    {K : Type vK} [Category.{u} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{u} C] [Preadditive C] [Linear k C]
    {D : K ⥤ C} [D.Additive] [D.Linear k]
    (hD : ClosedZigzagTransfer.HomBifunctorRetraction (k := k) D) :
    HomBifunctorRetraction (k := k) D where
  retraction := hD.retraction
  map_retraction := hD.map_retraction
  naturality := hD.naturality

/-- Lift both Hom types to their common maximum universe. -/
def liftHomFunctor
    {K : Type vK} [Category.{wK} K]
    {C : Type vC} [Category.{wC} C]
    (D : K ⥤ C) :
    ULiftHom.{max wK wC} K ⥤ ULiftHom.{max wK wC} C where
  obj X := ULiftHom.objUp (D.obj X.objDown)
  map f := ULift.up (D.map f.down)
  map_id X := by
    apply ULift.down_injective
    exact D.map_id X.objDown
  map_comp f g := by
    apply ULift.down_injective
    exact D.map_comp f.down g.down

instance liftHomFunctor_additive
    {K : Type vK} [Category.{wK} K] [Preadditive K]
    {C : Type vC} [Category.{wC} C] [Preadditive C]
    (D : K ⥤ C) [D.Additive] :
    (liftHomFunctor D).Additive where
  map_add {X Y} f g := by
    apply ULift.down_injective
    exact D.map_add (f := f.down) (g := g.down)

instance liftHomFunctor_linear
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Linear k] :
    (liftHomFunctor D).Linear k where
  map_smul f r := by
    apply ULift.down_injective
    exact D.map_smul r f.down

/-- A cross-universe Hom retraction becomes an ordinary same-Hom-universe
retraction after lifting both Hom types to the common maximum. -/
def HomBifunctorRetraction.ulift
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    {D : K ⥤ C} [D.Additive] [D.Linear k]
    (hD : HomBifunctorRetraction (k := k) D) :
    ClosedZigzagTransfer.HomBifunctorRetraction (k := k)
      (liftHomFunctor D) where
  retraction X Y := by
    change ULift.{max wK wC} (D.obj X.objDown ⟶ D.obj Y.objDown) →ₗ[k]
      ULift.{max wK wC} (X.objDown ⟶ Y.objDown)
    exact ULift.moduleEquiv.symm.toLinearMap.comp
      ((hD.retraction X.objDown Y.objDown).comp
        ULift.moduleEquiv.toLinearMap)
  map_retraction f := by
    apply ULift.down_injective
    exact hD.map_retraction f.down
  naturality a g b := by
    apply ULift.down_injective
    exact hD.naturality a.down g.down b.down

universe W

local instance uliftHomFintype
    {K : Type vK} [Fintype K] :
    Fintype (ULiftHom.{W} K) :=
  Fintype.ofEquiv K ULiftHom.objEquiv

local instance uliftHomDown_additive
    {K : Type vK} [Category.{wK} K] [Preadditive K] :
    (ULiftHom.down : ULiftHom.{max wK wC} K ⥤ K).Additive where
  map_add := by
    intros
    rfl

local instance uliftHomDown_linear
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K] :
    (ULiftHom.down : ULiftHom.{max wK wC} K ⥤ K).Linear k where
  map_smul := by
    intros
    rfl

local instance uliftHomUp_additive
    {C : Type vC} [Category.{wC} C] [Preadditive C] :
    (ULiftHom.up : C ⥤ ULiftHom.{max wK wC} C).Additive where
  map_add := by
    intros
    rfl

local instance uliftHomUp_linear
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C] :
    (ULiftHom.up : C ⥤ ULiftHom.{max wK wC} C).Linear k where
  map_smul := by
    intros
    rfl

/-- Regard a large-universe coefficient functor as a functor on the
Hom-lifted source. -/
abbrev liftedCoefficientFunctor
    {K : Type vK} [Category.{wK} K]
    {C : Type vC} [Category.{wC} C]
    (M : K ⥤ ModuleCat.{max vK wK wC} k) :
    ULiftHom.{max wK wC} K ⥤ ModuleCat.{max vK wK wC} k :=
  ULiftHom.down ⋙ M

/-- Cross-Hom-universe finite coend.  Its carrier universe is the maximum of
the source-object universe, both Hom universes, and an optional ambient
module universe. -/
def coendExtension
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Linear k]
    (M : K ⥤ ModuleCat.{max vK wK wC} k) [M.Linear k]
    [Fintype K] :
    C ⥤ ModuleCat.{max vK wK wC} k :=
  ULiftHom.up ⋙
    ClosedZigzagTransfer.coendExtension
      (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)

instance coendExtension_additive
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Linear k]
    (M : K ⥤ ModuleCat.{max vK wK wC} k) [M.Linear k]
    [Fintype K] :
    (coendExtension D M).Additive := by
  unfold coendExtension
  infer_instance

instance coendExtension_linear
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Linear k]
    (M : K ⥤ ModuleCat.{max vK wK wC} k) [M.Linear k]
    [Fintype K] :
    (coendExtension D M).Linear k := by
  unfold coendExtension
  infer_instance

instance coendExtension_obj_finite
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Linear k]
    (M : K ⥤ ModuleCat.{max vK wK wC} k) [M.Linear k]
    [Fintype K]
    [∀ (a : K) (c : C), Module.Finite k (D.obj a ⟶ c)]
    [∀ a : K, Module.Finite k (M.obj a)] (c : C) :
    Module.Finite k ((coendExtension D M).obj c) := by
  letI (a : ULiftHom.{max wK wC} K)
      (d : ULiftHom.{max wK wC} C) :
      Module.Finite k ((liftHomFunctor D).obj a ⟶ d) := by
    change Module.Finite k (ULift.{max wK wC}
      (D.obj a.objDown ⟶ d.objDown))
    infer_instance
  letI (a : ULiftHom.{max wK wC} K) :
      Module.Finite k ((liftedCoefficientFunctor (C := C) M).obj a) := by
    change Module.Finite k (M.obj a.objDown)
    infer_instance
  change Module.Finite k
    ((ClosedZigzagTransfer.coendExtension
      (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)).obj
        (ULiftHom.objUp c))
  infer_instance

/-- The coend unit, descended from the common-Hom-universe construction. -/
def coendUnit
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Linear k]
    (M : K ⥤ ModuleCat.{max vK wK wC} k) [M.Linear k]
    [Fintype K] :
    M ⟶ D ⋙ coendExtension D M where
  app a :=
    (ClosedZigzagTransfer.coendUnit
      (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)).app
        (ULiftHom.objUp a)
  naturality {a b} f := by
    change
      (liftedCoefficientFunctor (C := C) M).map (ULift.up f) ≫
          (ClosedZigzagTransfer.coendUnit
            (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)).app
              (ULiftHom.objUp b) =
        (ClosedZigzagTransfer.coendUnit
            (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)).app
              (ULiftHom.objUp a) ≫
          (ClosedZigzagTransfer.coendExtension
            (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)).map
              ((liftHomFunctor D).map (ULift.up f))
    exact (ClosedZigzagTransfer.coendUnit
      (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)).naturality
        (ULift.up f)

/-- The cross-universe coend retraction induced by the generalized Hom
retraction. -/
def coendRetraction
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Additive] [D.Linear k]
    (M : K ⥤ ModuleCat.{max vK wK wC} k) [M.Additive] [M.Linear k]
    [Fintype K]
    (hD : HomBifunctorRetraction (k := k) D) :
    D ⋙ coendExtension D M ⟶ M where
  app a :=
    (ClosedZigzagTransfer.coendRetraction
      (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M) hD.ulift).app
        (ULiftHom.objUp a)
  naturality {a b} f := by
    change
      (ClosedZigzagTransfer.coendExtension
          (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)).map
            ((liftHomFunctor D).map (ULift.up f)) ≫
        (ClosedZigzagTransfer.coendRetraction
          (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M) hD.ulift).app
            (ULiftHom.objUp b) =
      (ClosedZigzagTransfer.coendRetraction
          (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M) hD.ulift).app
            (ULiftHom.objUp a) ≫
        (liftedCoefficientFunctor (C := C) M).map (ULift.up f)
    exact (ClosedZigzagTransfer.coendRetraction
      (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M) hD.ulift).naturality
        (ULift.up f)

/-- The generalized coend unit is split, with no equality required between
the source and target Hom universes. -/
theorem coendUnit_retraction
    {K : Type vK} [Category.{wK} K] [Preadditive K] [Linear k K]
    {C : Type vC} [Category.{wC} C] [Preadditive C] [Linear k C]
    (D : K ⥤ C) [D.Additive] [D.Linear k]
    (M : K ⥤ ModuleCat.{max vK wK wC} k) [M.Additive] [M.Linear k]
    [Fintype K]
    (hD : HomBifunctorRetraction (k := k) D) :
    coendUnit D M ≫ coendRetraction D M hD = 𝟙 M := by
  ext a m
  change
    ClosedZigzagTransfer.coendRetractionLinear
        (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M) hD.ulift
          (ULiftHom.objUp a)
        (ClosedZigzagTransfer.coendUnitLinear
          (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M)
            (ULiftHom.objUp a) m) = m
  exact ClosedZigzagTransfer.coendRetractionLinear_unit
    (liftHomFunctor D) (liftedCoefficientFunctor (C := C) M) hD.ulift
      (ULiftHom.objUp a) m

section ClosedChainAssembly

universe uA x

open LargeIndecomposable.ClosedZigzagTransfer

variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

/-- The algebra lifted into the common carrier universe. -/
abbrev largeAlgebra (_k : Type u) (A : Type uA) := ULift.{u} A

/-- Restriction along `ULift A ≃ₐ[k] A` identifies large-carrier `A`-modules
with large-carrier modules over the universe-lifted algebra. -/
abbrev largeModuleEquivalence :
    ModuleCat.{max u uA} A ≌
      ModuleCat.{max u uA} (largeAlgebra k A) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.algEquiv (R := k) (A := A)).toRingEquiv

/-- The forward module-equivalence functor preserves the underlying
`k`-vector space. -/
def largeModuleEquivalenceObjLinearEquiv
    (M : ModuleCat.{max u uA} A) :
    M ≃ₗ[k] (largeModuleEquivalence (k := k) (A := A)).functor.obj M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse module-equivalence functor also preserves the underlying
`k`-vector space. -/
def largeModuleEquivalenceInverseObjLinearEquiv
    (M : ModuleCat.{max u uA} (largeAlgebra k A)) :
    M ≃ₗ[k] (largeModuleEquivalence (k := k) (A := A)).inverse.obj M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance largeAlgebra_finite :
    Module.Finite k (largeAlgebra k A) := by
  infer_instance

end ClosedChainAssembly

end LargeIndecomposable.ClosedZigzagCrossUniverse
