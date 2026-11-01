module

public import LargeIndecomposable.Cleaving.ClosedChains.Assembly
public import LargeIndecomposable.Cleaving.ClosedChains.ProjectiveStableSupplement
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

open LargeIndecomposable.ClosedZigzag
open LargeIndecomposable.ClosedZigzagTransfer

variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

abbrev chainRepresentative
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) :=
  stableChainRepresentativeLinearFunctor (k := k) t

/-- Restriction in the common carrier universe `max u uA`. -/
def chainRestriction
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) :
    ModuleCat.{max u uA} A ⥤
      (LinearSource k (t.length - 1) ⥤ ModuleCat.{max u uA} k) :=
  LargeIndecomposable.SplitBasicIdempotents.projectiveRestriction
      (k := k) S ⋙
    (Functor.whiskeringLeft
      (LinearSource k (t.length - 1)) S.ProjectiveCategory
        (ModuleCat.{max u uA} k)).obj
      (chainRepresentative S t)

instance chainRestriction_additive
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) :
    (chainRestriction S t).Additive := by
  unfold chainRestriction
  infer_instance

/-- Lift the exact thin family to the common coend carrier universe. -/
def chainThinFamily [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    LinearSource k (t.length - 1) ⥤ ModuleCat.{max u uA} k :=
  linearFamily (k := k) (t.length - 1) m ⋙
    ModuleCat.uliftFunctor.{uA} k

instance chainThinFamily_additive [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    (chainThinFamily S t m).Additive := by
  unfold chainThinFamily linearFamily
  infer_instance

instance chainThinFamily_linear [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    (chainThinFamily S t m).Linear k := by
  unfold chainThinFamily linearFamily
  infer_instance

instance chainThinFamily_obj_finite [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ)
    (X : LinearSource k (t.length - 1)) :
    Module.Finite k ((chainThinFamily S t m).obj X) := by
  letI : Module.Finite k
      ((linearFamily (k := k) (t.length - 1) m).obj X) :=
    linearFamily_obj_finite (t.length - 1) m X
  change Module.Finite k
    (ULift.{uA} ((linearFamily (k := k) (t.length - 1) m).obj X))
  infer_instance

abbrev chainCoendExtension [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :=
  coendExtension (chainRepresentative S t) (chainThinFamily S t m)

instance chainCoendExtension_additive [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    (chainCoendExtension S t m).Additive := by
  unfold chainCoendExtension
  infer_instance

instance chainCoendExtension_linear [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    (chainCoendExtension S t m).Linear k := by
  unfold chainCoendExtension
  infer_instance

abbrev chainRealizedExtension [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :=
  LargeIndecomposable.SplitBasicIdempotents.realizedModule S
    (chainCoendExtension S t m)

theorem chainRealizedExtension_finite [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    Module.Finite k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj
        (chainRealizedExtension S t m)) := by
  let F := chainCoendExtension S t m
  letI : Module.Finite k
      (LargeIndecomposable.SplitBasicIdempotents.realizedCarrier S F) := by
    infer_instance
  let e :
      ULift.{0} (LargeIndecomposable.SplitBasicIdempotents.realizedCarrier S F) ≃ₗ[k]
        ((ModuleCat.restrictScalars (algebraMap k A)).obj
          (LargeIndecomposable.SplitBasicIdempotents.realizedModule S F)) :=
    { toFun := fun q ↦ q.down
      invFun := fun q ↦ ULift.up q
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c q ↦ by
        change c • q.down =
          (LargeIndecomposable.SplitBasicIdempotents.realizedActionAlgHom S F
            (algebraMap k A c)) q.down
        rw [(LargeIndecomposable.SplitBasicIdempotents.realizedActionAlgHom S F).commutes]
        rfl }
  exact Module.Finite.equiv e

/-- Cross-universe coend splitting transported across projective
realization--restriction. -/
theorem chainThinFamily_isRetract [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (hD : HomBifunctorRetraction (k := k) (chainRepresentative S t))
    (m : ℕ) :
    IsRetractOf (chainThinFamily S t m)
      ((chainRestriction S t).obj (chainRealizedExtension S t m)) := by
  change IsRetractOf (chainThinFamily S t m)
    ((chainRepresentative S t) ⋙
      LargeIndecomposable.SplitBasicIdempotents.projectiveRestrictionObj S
        (LargeIndecomposable.SplitBasicIdempotents.realizedModule S
          (chainCoendExtension S t m)))
  let e :=
    LargeIndecomposable.SplitBasicIdempotents.realizedRestrictionWhiskerLeftNatIso
      S (chainCoendExtension S t m) (chainRepresentative S t)
  refine ⟨coendUnit (chainRepresentative S t) (chainThinFamily S t m) ≫ e.inv,
    e.hom ≫ coendRetraction (chainRepresentative S t)
      (chainThinFamily S t m) hD, ?_⟩
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact coendUnit_retraction (chainRepresentative S t)
    (chainThinFamily S t m) hD

abbrev thinFamilyLiftFunctor (_A : Type uA) (n : ℕ) :
    (LinearSource k n ⥤ ModuleCat.{u} k) ⥤
      (LinearSource k n ⥤ ModuleCat.{max u uA} k) :=
  (Functor.whiskeringRight
    (LinearSource k n) (ModuleCat.{u} k)
      (ModuleCat.{max u uA} k)).obj
    (ModuleCat.uliftFunctor.{uA} k)

theorem chainThinFamily_eq_of_iso [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    {m n : ℕ} (e : chainThinFamily S t m ≅ chainThinFamily S t n) :
    m = n := by
  let W := thinFamilyLiftFunctor (k := k) A (t.length - 1)
  let hW : W.FullyFaithful :=
    (ModuleCat.fullyFaithfulUliftFunctor (R := k)).whiskeringRight
      (LinearSource k (t.length - 1))
  change W.obj (linearFamily (k := k) (t.length - 1) m) ≅
    W.obj (linearFamily (k := k) (t.length - 1) n) at e
  exact linearFamily_eq_of_iso (hW.preimageIso e)

theorem chainThinFamily_indecomposable [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    Indecomposable (chainThinFamily S t m) := by
  let W := thinFamilyLiftFunctor (k := k) A (t.length - 1)
  let X := linearFamily (k := k) (t.length - 1) m
  let hW : W.FullyFaithful :=
    (ModuleCat.fullyFaithfulUliftFunctor (R := k)).whiskeringRight
      (LinearSource k (t.length - 1))
  change Indecomposable (W.obj X)
  apply indecomposable_of_idempotent_eq_zero_or_id_preadditive
  · intro hzero
    have hXzero : IsZero X :=
      IsZero.of_full_of_faithful_of_isZero W X hzero
    exact (linearFamily_indecomposable (k := k)
      (t.length - 1) m).1 hXzero
  · intro p hp
    let q : X ⟶ X := hW.preimage p
    have hq : q ≫ q = q := by
      apply W.map_injective
      exact hp
    have hpq : W.map q = p := hW.map_preimage p
    rcases idempotent_eq_zero_or_id_of_indecomposable_preadditive
        (linearFamily_indecomposable (k := k) (t.length - 1) m)
        q hq with hq0 | hq1
    · left
      rw [← hpq, hq0, W.map_zero]
    · right
      rw [← hpq, hq1, W.map_id]

theorem chainThinFamily_end_isLocalRing [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    IsLocalRing (CategoryTheory.End (chainThinFamily S t m)) := by
  let W := thinFamilyLiftFunctor (k := k) A (t.length - 1)
  let X := linearFamily (k := k) (t.length - 1) m
  let hW : W.FullyFaithful :=
    (ModuleCat.fullyFaithfulUliftFunctor (R := k)).whiskeringRight
      (LinearSource k (t.length - 1))
  let e : CategoryTheory.End X ≃+* CategoryTheory.End (W.obj X) :=
    { hW.mulEquivEnd X with
      map_add' := fun f g ↦ W.map_add }
  letI : IsLocalRing (CategoryTheory.End X) :=
    linearFamily_end_isLocalRing (k := k) (t.length - 1) m
  change IsLocalRing (CategoryTheory.End (W.obj X))
  exact LargeIndecomposable.RingEquiv.isLocalRing_noncommutative e

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

/-- Restriction of modules over the lifted algebra, followed by the original
primitive-projective restriction. -/
def largeChainRestriction
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) :
    ModuleCat.{max u uA} (largeAlgebra k A) ⥤
      (LinearSource k (t.length - 1) ⥤ ModuleCat.{max u uA} k) :=
  (largeModuleEquivalence (k := k) (A := A)).inverse ⋙
    chainRestriction S t

instance largeChainRestriction_additive
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) :
    (largeChainRestriction S t).Additive := by
  unfold largeChainRestriction
  infer_instance

abbrev largeRealizedExtension [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :=
  (largeModuleEquivalence (k := k) (A := A)).functor.obj
    (chainRealizedExtension S t m)

theorem largeRealizedExtension_finite [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    Module.Finite k (largeRealizedExtension S t m) := by
  letI : Module.Finite k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj
        (chainRealizedExtension S t m)) :=
    chainRealizedExtension_finite S t m
  let e :
      ((ModuleCat.restrictScalars (algebraMap k A)).obj
          (chainRealizedExtension S t m)) ≃ₗ[k]
        largeRealizedExtension S t m :=
    { toFun := fun q ↦ q
      invFun := fun q ↦ q
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.equiv e

/-- Transport the realized coend retract across the unit isomorphism of the
large-algebra module equivalence. -/
theorem chainThinFamily_isRetract_large [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (hD : HomBifunctorRetraction (k := k) (chainRepresentative S t))
    (m : ℕ) :
    IsRetractOf (chainThinFamily S t m)
      ((largeChainRestriction S t).obj (largeRealizedExtension S t m)) := by
  obtain ⟨i, p, hip⟩ := chainThinFamily_isRetract S t hD m
  let e := largeModuleEquivalence (k := k) (A := A)
  let eu : chainRealizedExtension S t m ≅
      e.inverse.obj (e.functor.obj (chainRealizedExtension S t m)) :=
    { hom := e.unitIso.hom.app (chainRealizedExtension S t m)
      inv := e.unitIso.inv.app (chainRealizedExtension S t m)
      hom_inv_id := by
        simp
      inv_hom_id := by
        simp }
  let er := (chainRestriction S t).mapIso eu
  exact ⟨i ≫ er.hom, er.inv ≫ p, by simp [Category.assoc, hip]⟩

/-- Restriction to a primitive projective component preserves finite
dimensionality, independently of the carrier universe of `A`. -/
theorem chainRestriction_obj_finite
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (M : ModuleCat.{max u uA} A)
    (hM : Module.Finite k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj M))
    (X : LinearSource k (t.length - 1)) :
    Module.Finite k (((chainRestriction S t).obj M).obj X) := by
  letI : Module.Finite k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj M) := hM
  change Module.Finite k
    (LargeIndecomposable.SplitBasicIdempotents.projectiveRestrictionComponent
      S M ((chainRepresentative S t).obj X))
  let inclusion :
      LargeIndecomposable.SplitBasicIdempotents.projectiveRestrictionComponent
          S M ((chainRepresentative S t).obj X) →ₗ[k]
        ((ModuleCat.restrictScalars (algebraMap k A)).obj M) :=
    { toFun := fun q ↦ q.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.of_injective inclusion Subtype.val_injective

/-- A chosen Krull--Schmidt decomposition after lifting the algebra carrier to
the common universe. -/
def largeRealizedExtension_decomposition [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    FiniteIndecomposableDecomposition (largeRealizedExtension S t m) :=
  Classical.choice
    (@finiteIndecomposableDecomposition_exists k _ (largeAlgebra k A) _ _ _
      (largeRealizedExtension S t m)
      (largeRealizedExtension_finite S t m))

/-- Each indecomposable summand of the large-algebra realized extension has
finite retract spectrum after stable-chain restriction. -/
def largeChainRestriction_spectrum [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (m : ℕ)
    (j : Fin (largeRealizedExtension_decomposition S t m).n) :
    FiniteIndecomposableRetractSpectrum
      ((largeChainRestriction S t).obj
        ((largeRealizedExtension_decomposition S t m).summand j)) := by
  apply finiteIndecomposableRetractSpectrum_functor
  intro X
  apply chainRestriction_obj_finite S t
  let N := (largeRealizedExtension_decomposition S t m).summand j
  letI : Module.Finite k N :=
    (largeRealizedExtension_decomposition S t m).summand_finite
      (largeRealizedExtension_finite S t m) j
  exact Module.Finite.equiv
    (largeModuleEquivalenceInverseObjLinearEquiv (k := k) (A := A) N)

/-- Arbitrary-universe closed-chain endpoint.  The target algebra is first
lifted to the common carrier universe only for the generic Krull--Schmidt
transfer; the stable representative and its Hom retraction retain their
original, independent Hom universes. -/
def infiniteFiniteIndecomposableFamily_large_of_rayClosedChain [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (hD : HomBifunctorRetraction (k := k) (chainRepresentative S t)) :
    InfiniteFiniteIndecomposableFamily k (largeAlgebra k A) := by
  apply infiniteFiniteIndecomposableFamilyOfCleavingExtensions
    (k := k) (A := largeAlgebra k A)
    (largeChainRestriction S t)
    (chainThinFamily S t)
    (chainThinFamily_indecomposable S t)
    (fun {_ _} h ↦ chainThinFamily_eq_of_iso S t (Classical.choice h))
    (chainThinFamily_end_isLocalRing S t)
    (largeRealizedExtension S t)
    (largeRealizedExtension_finite S t)
    (chainThinFamily_isRetract_large S t hD)
    (largeRealizedExtension_decomposition S t)
  exact largeChainRestriction_spectrum S t

/-- A stable closed-chain Hom retraction contradicts representation-finiteness
without any equality assumption on the universes of `k` and `A`. -/
theorem not_isRepresentationFinite_of_rayClosedChain [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (hD : HomBifunctorRetraction (k := k) (chainRepresentative S t)) :
    ¬ IsRepresentationFinite k A := by
  let X : S.ProjectiveCategory := (t.chain.x 0).as
  letI : Nontrivial (X ⟶ X) :=
    ⟨⟨𝟙 X, 0,
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.id_ne_zero S X⟩⟩
  letI : Nontrivial A :=
    (show Function.Injective (fun q : (X ⟶ X) ↦ (q.1 : A)) from
      Subtype.val_injective).nontrivial
  intro hfinite
  have hlarge : IsRepresentationFinite k (largeAlgebra k A) :=
    hfinite.of_crossUniverse_algEquiv
      (ULift.algEquiv (R := k) (A := A)).symm
  apply hlarge.not_infiniteFiniteIndecomposableFamily.false
  exact infiniteFiniteIndecomposableFamily_large_of_rayClosedChain S t hD

end ClosedChainAssembly

end LargeIndecomposable.ClosedZigzagCrossUniverse
