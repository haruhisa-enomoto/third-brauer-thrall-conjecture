module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift
public import LargeIndecomposable.Modules.KrullSchmidt.LocalEndFiniteDimensional
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open scoped ModuleCat.Algebra

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w x

variable {k : Type u} [Field k]

/-- The exact Hom-bifunctor retraction in BGRS Proposition 3.2.  It is a
concrete cleaving datum, not a callback asserting representation-infinite
behavior. -/
structure HomBifunctorRetraction
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : CategoryTheory.Functor K C) [D.Additive] [D.Linear k] where
  retraction : ∀ X Y : K, (D.obj X ⟶ D.obj Y) →ₗ[k] (X ⟶ Y)
  map_retraction : ∀ {X Y : K} (f : X ⟶ Y),
    retraction X Y (D.map f) = f
  naturality : ∀ {X' X Y Y' : K} (a : X' ⟶ X)
      (g : D.obj X ⟶ D.obj Y) (b : Y ⟶ Y'),
    retraction X' Y' (D.map a ≫ g ≫ D.map b) =
      a ≫ retraction X Y g ≫ b

/-- The supplement formulation used in BGRS 3.4.  The image of every Hom map
has a chosen linear complement, and those complements form a subfunctor of
the target Hom bifunctor.  This is precisely the concrete datum called a
`cleavage` in the source. -/
structure HomComplementCleavage
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : CategoryTheory.Functor K C) [D.Additive] [D.Linear k] where
  supplement : ∀ X Y : K, Submodule k (D.obj X ⟶ D.obj Y)
  map_injective : ∀ X Y : K,
    Function.Injective (D.mapLinearMap k (X := X) (Y := Y))
  isCompl : ∀ X Y : K,
    IsCompl (LinearMap.range (D.mapLinearMap k (X := X) (Y := Y)))
      (supplement X Y)
  comp_mem : ∀ {X' X Y Y' : K} (a : X' ⟶ X)
      {g : D.obj X ⟶ D.obj Y} (_hg : g ∈ supplement X Y) (b : Y ⟶ Y'),
    D.map a ≫ g ≫ D.map b ∈ supplement X' Y'

/-- Projection along the supplements of a Hom cleavage. -/
def HomComplementCleavage.retraction
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    {D : CategoryTheory.Functor K C} [D.Additive] [D.Linear k]
    (h : HomComplementCleavage (k := k) D) (X Y : K) :
    (D.obj X ⟶ D.obj Y) →ₗ[k] (X ⟶ Y) :=
  LinearMap.linearProjOfIsCompl (h.supplement X Y)
    (D.mapLinearMap k) (h.map_injective X Y) (h.isCompl X Y)

@[simp]
theorem HomComplementCleavage.retraction_map
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    {D : CategoryTheory.Functor K C} [D.Additive] [D.Linear k]
    (h : HomComplementCleavage (k := k) D) {X Y : K} (f : X ⟶ Y) :
    h.retraction X Y (D.map f) = f := by
  exact LinearMap.linearProjOfIsCompl_apply_left
    (h.supplement X Y) (D.mapLinearMap k) (h.map_injective X Y)
      (h.isCompl X Y) f

theorem HomComplementCleavage.sub_map_retraction_mem
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    {D : CategoryTheory.Functor K C} [D.Additive] [D.Linear k]
    (h : HomComplementCleavage (k := k) D) {X Y : K}
    (g : D.obj X ⟶ D.obj Y) :
    g - D.map (h.retraction X Y g) ∈ h.supplement X Y := by
  rw [← LinearMap.ker_linearProjOfIsCompl
    (h.supplement X Y) (D.mapLinearMap k) (h.map_injective X Y)
      (h.isCompl X Y)]
  change h.retraction X Y (g - D.map (h.retraction X Y g)) = 0
  rw [LinearMap.map_sub, h.retraction_map, sub_self]

/-- BGRS 3.4's functorial supplements give the Hom-bifunctor retraction of
BGRS 3.2.  The proof is the canonical projection-along-a-complement
calculation; no module-theoretic transfer conclusion is assumed. -/
def HomComplementCleavage.homBifunctorRetraction
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    {D : CategoryTheory.Functor K C} [D.Additive] [D.Linear k]
    (h : HomComplementCleavage (k := k) D) :
    HomBifunctorRetraction (k := k) D where
  retraction := h.retraction
  map_retraction := h.retraction_map
  naturality := by
    intro X' X Y Y' a g b
    let p : X ⟶ Y := h.retraction X Y g
    let r : D.obj X ⟶ D.obj Y :=
      g - D.map p
    have hr : r ∈ h.supplement X Y :=
      h.sub_map_retraction_mem g
    have hcomp : D.map a ≫ r ≫ D.map b ∈ h.supplement X' Y' :=
      h.comp_mem a hr b
    have hzero : h.retraction X' Y'
        (D.map a ≫ r ≫ D.map b) = 0 := by
      exact LinearMap.linearProjOfIsCompl_apply_right'
        (h.supplement X' Y') (D.mapLinearMap k)
          (h.map_injective X' Y') (h.isCompl X' Y') _ hcomp
    have hdecomp : g = D.map p + r := by
      dsimp [r, p]
      abel
    change h.retraction X' Y' (D.map a ≫ g ≫ D.map b) =
      a ≫ p ≫ b
    calc
      h.retraction X' Y' (D.map a ≫ g ≫ D.map b) =
          h.retraction X' Y'
            (D.map a ≫ (D.map p + r) ≫ D.map b) := by rw [hdecomp]
      _ = h.retraction X' Y'
            ((D.map a ≫ D.map p ≫ D.map b) +
              (D.map a ≫ r ≫ D.map b)) := by
            congr 1
            rw [Preadditive.add_comp, Preadditive.comp_add]
      _ = h.retraction X' Y' (D.map (a ≫ p ≫ b)) +
            h.retraction X' Y' (D.map a ≫ r ≫ D.map b) := by
            rw [LinearMap.map_add]
            congr 1
            simp only [D.map_comp]
      _ = a ≫ p ≫ b := by
            rw [h.retraction_map, hzero, add_zero]

/-- Mathlib constructs the linear coyoneda object but currently only installs
its additivity.  Postcomposition is also linear, as required for treating the
covariant representable as an enriched module. -/
instance linearCoyonedaObjLinear
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    (X : K) : ((linearCoyoneda k K).obj (Opposite.op X)).Linear k where
  map_smul f r := by
    ext g
    change g ≫ (r • f) = r • (g ≫ f)
    simp

/-- The enriched covariant Yoneda equivalence.  Mathlib's
`linearCoyoneda` currently supplies only the ordinary full/faithful theorem,
so this is the small missing linear universal property used below. -/
def linearCoyonedaHomEquiv
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    (X : K) (N : CategoryTheory.Functor K (ModuleCat k))
    [N.Additive] [N.Linear k] :
    ((linearCoyoneda k K).obj (Opposite.op X) ⟶ N) ≃ₗ[k] N.obj X where
  toFun α := α.app X (𝟙 X)
  invFun x :=
    { app := fun Y ↦ ModuleCat.ofHom
        { toFun := fun f ↦ N.map f x
          map_add' := by
            intro f g
            rw [N.map_add]
            rfl
          map_smul' := by
            intro r f
            rw [N.map_smul]
            rfl }
      naturality := by
        intro Y Z f
        ext g
        change N.map (g ≫ f) x = N.map f (N.map g x)
        rw [N.map_comp]
        rfl }
  left_inv α := by
    ext Y f
    change N.map f (α.app X (𝟙 X)) = α.app Y f
    have h := (α.naturality_apply f (𝟙 X)).symm
    change N.map f (α.app X (𝟙 X)) = α.app Y ((𝟙 X) ≫ f) at h
    simpa using h
  right_inv x := by
    change N.map (𝟙 X) x = x
    rw [N.map_id]
    rfl
  map_add' α β := rfl
  map_smul' r α := rfl

/-- On a covariant representable, the unit of extension along `D` is just
`D.map`, componentwise. -/
def representableUnit
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : CategoryTheory.Functor K C) [D.Additive] [D.Linear k]
    (X : K) :
    (linearCoyoneda k K).obj (Opposite.op X) ⟶
      D ⋙ (linearCoyoneda k C).obj (Opposite.op (D.obj X)) where
  app Y := ModuleCat.ofHom (D.mapLinearMap k)
  naturality := by
    intro Y Z f
    ext g
    change D.map (g ≫ f) = D.map g ≫ D.map f
    exact D.map_comp g f

/-- A Hom-bifunctor retraction restricts componentwise to a retraction of the
representable extension unit.  This is the representable base case of BGRS
Proposition 3.2. -/
def representableRetraction
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    {D : CategoryTheory.Functor K C} [D.Additive] [D.Linear k]
    (h : HomBifunctorRetraction (k := k) D) (X : K) :
    D ⋙ (linearCoyoneda k C).obj (Opposite.op (D.obj X)) ⟶
      (linearCoyoneda k K).obj (Opposite.op X) where
  app Y := ModuleCat.ofHom (h.retraction X Y)
  naturality := by
    intro Y Z f
    ext g
    change h.retraction X Z (g ≫ D.map f) =
      h.retraction X Y g ≫ f
    simpa using h.naturality (𝟙 X) g f

/-- The representable unit is split by the Hom-bifunctor retraction. -/
theorem representableUnit_retraction
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    {D : CategoryTheory.Functor K C} [D.Additive] [D.Linear k]
    (h : HomBifunctorRetraction (k := k) D) (X : K) :
    representableUnit D X ≫ representableRetraction h X =
      𝟙 ((linearCoyoneda k K).obj (Opposite.op X)) := by
  ext Y g
  exact h.map_retraction g

/-- The precise enriched left-Kan-extension interface missing from Mathlib's
ordinary Kan-extension API.  The comparison equivalence is explicitly
linear on natural transformations and quantifies only over linear target
functors. -/
structure EnrichedLeftKanExtension
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : CategoryTheory.Functor K C) [D.Additive] [D.Linear k]
    (M : CategoryTheory.Functor K (ModuleCat k)) [M.Additive] [M.Linear k] where
  extension : CategoryTheory.Functor C (ModuleCat k)
  extension_additive : extension.Additive
  extension_linear : extension.Linear k
  unit : M ⟶ D ⋙ extension
  homEquiv : ∀ (N : CategoryTheory.Functor C (ModuleCat k))
    [N.Additive] [N.Linear k],
    (extension ⟶ N) ≃ₗ[k] (M ⟶ D ⋙ N)
  homEquiv_apply : ∀ (N : CategoryTheory.Functor C (ModuleCat k))
      [N.Additive] [N.Linear k] (f : extension ⟶ N),
    homEquiv N f = unit ≫ whiskerLeft D f

/-- A cleaving enriched extension is an enriched left Kan extension whose
unit is split, exactly as in BGRS 3.1. -/
structure CleavingEnrichedLeftKanExtension
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : CategoryTheory.Functor K C) [D.Additive] [D.Linear k]
    (M : CategoryTheory.Functor K (ModuleCat k)) [M.Additive] [M.Linear k]
    extends EnrichedLeftKanExtension D M where
  retraction : D ⋙ extension ⟶ M
  unit_retraction : unit ≫ retraction = 𝟙 M

/-- The cleaving unit is a split monomorphism. -/
def CleavingEnrichedLeftKanExtension.splitMono
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    {D : CategoryTheory.Functor K C} [D.Additive] [D.Linear k]
    {M : CategoryTheory.Functor K (ModuleCat k)} [M.Additive] [M.Linear k]
    (L : CleavingEnrichedLeftKanExtension D M) : SplitMono L.unit where
  retraction := L.retraction
  id := L.unit_retraction

/-- The covariant Yoneda equivalence after restriction along `D`, with its
codomain displayed at `D.obj X` to avoid exposing composition reducibility. -/
def restrictedLinearCoyonedaHomEquiv
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : CategoryTheory.Functor K C) [D.Additive] [D.Linear k]
    (X : K) (N : CategoryTheory.Functor C (ModuleCat k))
    [N.Additive] [N.Linear k] :
    ((linearCoyoneda k K).obj (Opposite.op X) ⟶ D ⋙ N) ≃ₗ[k]
      N.obj (D.obj X) :=
  linearCoyonedaHomEquiv (k := k) X (D ⋙ N)

/-- Covariant representables have the expected enriched left Kan extension:
extension along `D` sends `K(X,-)` to `C(DX,-)`. -/
def representableEnrichedLeftKanExtension
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : CategoryTheory.Functor K C) [D.Additive] [D.Linear k]
    (X : K) :
    EnrichedLeftKanExtension D
      ((linearCoyoneda k K).obj (Opposite.op X)) where
  extension := (linearCoyoneda k C).obj (Opposite.op (D.obj X))
  extension_additive := inferInstance
  extension_linear := inferInstance
  unit := representableUnit D X
  homEquiv := fun N ↦
    (linearCoyonedaHomEquiv (k := k) (D.obj X) N).trans
      (restrictedLinearCoyonedaHomEquiv (k := k) D X N).symm
  homEquiv_apply := by
    intro N _ _ f
    apply (restrictedLinearCoyonedaHomEquiv (k := k) D X N).injective
    rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    change f.app (D.obj X) (𝟙 (D.obj X)) =
      f.app (D.obj X) (D.map (𝟙 X))
    rw [D.map_id]

/-- The Hom-bifunctor retraction makes the representable enriched extension
cleaving.  No finiteness or representation-type conclusion is assumed. -/
def representableCleavingEnrichedLeftKanExtension
    {K : Type v} [Category.{w} K] [Preadditive K] [Linear k K]
    {C : Type x} [Category.{w} C] [Preadditive C] [Linear k C]
    {D : CategoryTheory.Functor K C} [D.Additive] [D.Linear k]
    (h : HomBifunctorRetraction (k := k) D) (X : K) :
    CleavingEnrichedLeftKanExtension D
      ((linearCoyoneda k K).obj (Opposite.op X)) where
  toEnrichedLeftKanExtension := representableEnrichedLeftKanExtension D X
  retraction := representableRetraction h X
  unit_retraction := representableUnit_retraction h X

/-- `X` is a direct factor of `Y`, expressed without choosing a biproduct
complement. -/
def IsRetractOf {R : Type v} [Category.{w} R] (X Y : R) : Prop :=
  ∃ (i : X ⟶ Y) (p : Y ⟶ X), i ≫ p = 𝟙 X

/-- A fixed object has only finitely many isomorphism classes of
indecomposable retracts.  Finite-dimensional Krull--Schmidt proves this
property; keeping it separate isolates the exact remaining theorem needed
for the BGRS transfer. -/
structure FiniteIndecomposableRetractSpectrum
    {R : Type v} [Category.{w} R] [Preadditive R]
    [HasBinaryBiproducts R] (X : R) where
  n : ℕ
  representative : Fin n → R
  complete : ∀ (M : R), Indecomposable M → IsRetractOf M X →
    ∃ i, Nonempty (M ≅ representative i)

/-- If an object with local endomorphism ring retracts off a finite
biproduct, it already retracts off one summand.  Unlike the stronger
Krull--Schmidt exchange statement below, the summands need not themselves
have local endomorphism rings. -/
theorem localEnd_retract_biproduct_retract_summand
    {R : Type v} [Category.{w} R] [Preadditive R]
    [HasBinaryBiproducts R] [HasFiniteBiproducts R]
    {J : Type} [Fintype J] (N : J → R)
    {M : R} [IsLocalRing (CategoryTheory.End M)]
    (hret : IsRetractOf M (⨁ N)) :
    ∃ j, IsRetractOf M (N j) := by
  classical
  obtain ⟨i, p, hip⟩ := hret
  let f (j : J) : M ⟶ N j := i ≫ biproduct.π N j
  let g (j : J) : N j ⟶ M := biproduct.ι N j ≫ p
  let a (j : J) : CategoryTheory.End M :=
    CategoryTheory.End.of (f j ≫ g j)
  have hsum : ∑ j, a j = 1 := by
    apply CategoryTheory.End.ext
    change (∑ j, f j ≫ g j) = 𝟙 M
    calc
      (∑ j, f j ≫ g j) =
          i ≫ (∑ j, biproduct.π N j ≫ biproduct.ι N j) ≫ p := by
        simp only [f, g, Category.assoc, Preadditive.comp_sum,
          Preadditive.sum_comp]
      _ = i ≫ p := by rw [biproduct.total]; simp
      _ = 𝟙 M := hip
  have hexists : ∃ j, IsUnit (a j) := by
    by_contra hnone
    push Not at hnone
    have hnonunit_sum : ∀ s : Finset J, ¬ IsUnit (∑ j ∈ s, a j) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (not_isUnit_zero :
          ¬ IsUnit (0 : CategoryTheory.End M))
      | @insert j s hjs ih =>
          rw [Finset.sum_insert hjs]
          exact IsLocalRing.nonunits_add (hnone j) ih
    have hbad : ¬ IsUnit (∑ j, a j) := by
      simpa using hnonunit_sum Finset.univ
    rw [hsum] at hbad
    exact hbad isUnit_one
  obtain ⟨j, hj⟩ := hexists
  letI : IsIso (f j ≫ g j) :=
    (CategoryTheory.isUnit_iff_isIso _).mp hj
  refine ⟨j, f j, g j ≫ inv (f j ≫ g j), ?_⟩
  rw [← Category.assoc, IsIso.hom_inv_id]

/-- Local endomorphism rings give the Krull--Schmidt exchange step: an
indecomposable retract of a finite biproduct is isomorphic to one of its
summands. -/
theorem indecomposable_retract_biproduct_iso_summand
    {R : Type v} [Category.{w} R] [Preadditive R]
    [HasBinaryBiproducts R] [HasFiniteBiproducts R]
    {J : Type} [Fintype J] (N : J → R)
    [hlocal : ∀ j, IsLocalRing (CategoryTheory.End (N j))]
    {M : R} [IsLocalRing (CategoryTheory.End M)]
    (hret : IsRetractOf M (⨁ N)) :
    ∃ j, Nonempty (M ≅ N j) := by
  classical
  obtain ⟨i, p, hip⟩ := hret
  let f (j : J) : M ⟶ N j := i ≫ biproduct.π N j
  let g (j : J) : N j ⟶ M := biproduct.ι N j ≫ p
  let a (j : J) : CategoryTheory.End M :=
    CategoryTheory.End.of (f j ≫ g j)
  have hsum : ∑ j, a j = 1 := by
    apply CategoryTheory.End.ext
    change (∑ j, f j ≫ g j) = 𝟙 M
    calc
      (∑ j, f j ≫ g j) =
          i ≫ (∑ j, biproduct.π N j ≫ biproduct.ι N j) ≫ p := by
        simp only [f, g, Category.assoc, Preadditive.comp_sum,
          Preadditive.sum_comp]
      _ = i ≫ p := by rw [biproduct.total]; simp
      _ = 𝟙 M := hip
  have hexists : ∃ j, IsUnit (a j) := by
    by_contra hnone
    push Not at hnone
    have hnonunit_sum : ∀ s : Finset J, ¬ IsUnit (∑ j ∈ s, a j) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (not_isUnit_zero :
          ¬ IsUnit (0 : CategoryTheory.End M))
      | @insert j s hjs ih =>
          rw [Finset.sum_insert hjs]
          exact IsLocalRing.nonunits_add (hnone j) (ih)
    have hbad : ¬ IsUnit (∑ j, a j) := by
      simpa using hnonunit_sum Finset.univ
    rw [hsum] at hbad
    exact hbad isUnit_one
  obtain ⟨j, hj⟩ := hexists
  exact ⟨j, nonempty_iso_of_isUnit_comp (f j) (g j) hj⟩

/-- A displayed finite biproduct decomposition into local-end summands gives
the required finite indecomposable-retract spectrum. -/
def finiteIndecomposableRetractSpectrumOfBiproductIso
    {R : Type v} [Category.{w} R] [Preadditive R]
    [HasBinaryBiproducts R] [HasFiniteBiproducts R]
    {n : ℕ} (N : Fin n → R)
    [∀ j, IsLocalRing (CategoryTheory.End (N j))]
    (hlocalInd : ∀ (M : R), Indecomposable M →
      IsLocalRing (CategoryTheory.End M))
    (X : R) (e : X ≅ ⨁ N) :
    FiniteIndecomposableRetractSpectrum X where
  n := n
  representative := N
  complete := by
    intro M hM hret
    letI : IsLocalRing (CategoryTheory.End M) := hlocalInd M hM
    obtain ⟨i, p, hip⟩ := hret
    apply indecomposable_retract_biproduct_iso_summand N
    refine ⟨i ≫ e.hom, e.inv ≫ p, ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hip]

/-- A finite family of objects with finite indecomposable-retract spectra
cannot collectively contain an infinite pairwise-nonisomorphic family as
direct factors.  This is the finite pigeonhole step at the end of BGRS 3.1. -/
theorem not_infinite_pairwise_nonisomorphic_retract_family
    {R : Type v} [Category.{w} R] [Preadditive R]
    [HasBinaryBiproducts R]
    (F : ℕ → R) (hF_ind : ∀ m, Indecomposable (F m))
    (hF_iso : ∀ {m n}, Nonempty (F m ≅ F n) → m = n)
    {r : ℕ} (X : Fin r → R)
    (hX : ∀ j, FiniteIndecomposableRetractSpectrum (X j))
    (hcover : ∀ m, ∃ j, IsRetractOf (F m) (X j)) : False := by
  let witness : ∀ m, {j : Fin r // IsRetractOf (F m) (X j)} := fun m ↦
    ⟨Classical.choose (hcover m), Classical.choose_spec (hcover m)⟩
  let localIndex (m : ℕ) : Fin (hX (witness m).1).n :=
    Classical.choose
      ((hX (witness m).1).complete (F m) (hF_ind m) (witness m).2)
  let color (m : ℕ) : Σ j, Fin (hX j).n :=
    ⟨(witness m).1, localIndex m⟩
  let target : (Σ j, Fin (hX j).n) → R := fun q ↦
    (hX q.1).representative q.2
  have familyIso (m : ℕ) : Nonempty (F m ≅ target (color m)) :=
    Classical.choose_spec
      ((hX (witness m).1).complete (F m) (hF_ind m) (witness m).2)
  obtain ⟨m, n, hmn, hcolor⟩ :=
    Finite.exists_ne_map_eq_of_infinite color
  obtain ⟨em⟩ := familyIso m
  obtain ⟨en⟩ := familyIso n
  let etarget : target (color m) ≅ target (color n) :=
    eqToIso (congrArg target hcolor)
  exact hmn (hF_iso ⟨em.trans (etarget.trans en.symm)⟩)

/-- Isomorphism of the objects in a sequence is an equivalence relation on
its index set. -/
def objectIsoSetoid {R : Type v} [Category.{w} R] (X : ℕ → R) : Setoid ℕ where
  r m n := Nonempty (X m ≅ X n)
  iseqv := {
    refl := fun m ↦ ⟨Iso.refl (X m)⟩
    symm := fun h ↦ h.map Iso.symm
    trans := fun hmn hnp ↦ Nonempty.map2 Iso.trans hmn hnp }

/-- A concrete finite decomposition into indecomposable summands.  Its
existence for finite-dimensional modules is the standard decomposition half
of Krull--Schmidt. -/
structure FiniteIndecomposableDecomposition
    {R : Type v} [Category.{w} R] [Preadditive R]
    [HasBinaryBiproducts R] [HasFiniteBiproducts R] (X : R) where
  n : ℕ
  summand : Fin n → R
  indecomposable : ∀ j, Indecomposable (summand j)
  isoBiproduct : X ≅ ⨁ summand

/-- Every displayed direct summand of a finite-dimensional module remains
finite-dimensional. -/
theorem FiniteIndecomposableDecomposition.summand_finite
    {A : Type w} [Ring A] [Algebra k A]
    {X : ModuleCat.{w} A} (d : FiniteIndecomposableDecomposition X)
    (hX : Module.Finite k X) (j : Fin d.n) :
    Module.Finite k (d.summand j) := by
  letI : Module.Finite k X := hX
  let i : d.summand j ⟶ X :=
    biproduct.ι d.summand j ≫ d.isoBiproduct.inv
  let p : X ⟶ d.summand j :=
    d.isoBiproduct.hom ≫ biproduct.π d.summand j
  have hip : i ≫ p = 𝟙 (d.summand j) := by
    simp [i, p, Category.assoc]
  apply Module.Finite.of_injective (i.hom.restrictScalars k)
  exact (show Function.LeftInverse p i from fun x ↦ by
    change (i ≫ p) x = x
    rw [hip]
    rfl).injective

/-- Restriction by an additive functor carries a displayed target
decomposition to a source biproduct.  A source object with local endomorphism
ring that retracts off the whole restriction therefore retracts off one
restricted target indecomposable. -/
theorem localEnd_retract_restricted_decomposition_summand
    {S : Type v} [Category.{w} S] [Preadditive S]
    [HasBinaryBiproducts S] [HasFiniteBiproducts S]
    {R : Type x} [Category.{w} R] [Preadditive R]
    [HasBinaryBiproducts R] [HasFiniteBiproducts R]
    (Res : CategoryTheory.Functor R S) [Res.Additive]
    {M : S} [IsLocalRing (CategoryTheory.End M)] {E : R}
    (hret : IsRetractOf M (Res.obj E))
    (d : FiniteIndecomposableDecomposition E) :
    ∃ j, IsRetractOf M (Res.obj (d.summand j)) := by
  obtain ⟨i, p, hip⟩ := hret
  let e : Res.obj E ≅ ⨁ fun j ↦ Res.obj (d.summand j) :=
    (Res.mapIso d.isoBiproduct).trans (Res.mapBiproduct d.summand)
  apply localEnd_retract_biproduct_retract_summand
    (fun j ↦ Res.obj (d.summand j))
  exact ⟨i ≫ e.hom, e.inv ≫ p, by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hip]⟩

/-- Generic final step of cleaving transfer.  The target lifts may repeat:
the finite retract spectrum of each restricted lift forces infinitely many
target isomorphism classes, from which the theorem extracts a countable
pairwise-nonisomorphic subfamily. -/
def infiniteFiniteIndecomposableFamilyOfCleavingLifts
    {S : Type v} [Category.{w} S] [Preadditive S]
    [HasBinaryBiproducts S]
    {A : Type w} [Ring A] [Algebra k A]
    (Res : CategoryTheory.Functor (ModuleCat.{w} A) S)
    (F : ℕ → S) (hF_ind : ∀ m, Indecomposable (F m))
    (hF_iso : ∀ {m n}, Nonempty (F m ≅ F n) → m = n)
    (N : ℕ → ModuleCat.{w} A)
    (hN_finite : ∀ m, Module.Finite k (N m))
    (hN_ind : ∀ m, Indecomposable (N m))
    (hret : ∀ m, IsRetractOf (F m) (Res.obj (N m)))
    (hspectrum : ∀ m,
      FiniteIndecomposableRetractSpectrum (Res.obj (N m))) :
    InfiniteFiniteIndecomposableFamily k A := by
  classical
  let s : Setoid ℕ := objectIsoSetoid N
  have hquotInfinite : Infinite (Quotient s) := by
    rw [← not_finite_iff_infinite]
    intro hfinite
    letI : Finite (Quotient s) := hfinite
    letI : Fintype (Quotient s) := Fintype.ofFinite (Quotient s)
    let e : Quotient s ≃ Fin (Fintype.card (Quotient s)) :=
      Fintype.equivFin (Quotient s)
    let X : Fin (Fintype.card (Quotient s)) → S := fun j ↦
      Res.obj (N (e.symm j).out)
    apply not_infinite_pairwise_nonisomorphic_retract_family
      F hF_ind hF_iso X
    · intro j
      exact hspectrum (e.symm j).out
    · intro m
      let q : Quotient s := Quotient.mk'' m
      let j := e q
      refine ⟨j, ?_⟩
      have hout : (e.symm j).out ≈ m := by
        apply Quotient.exact
        calc
          Quotient.mk'' (e.symm j).out = e.symm j :=
            Quotient.out_eq' (e.symm j)
          _ = q := e.symm_apply_apply q
          _ = Quotient.mk'' m := rfl
      obtain ⟨eout⟩ := hout
      obtain ⟨i, p, hip⟩ := hret m
      let er : Res.obj (N m) ≅ Res.obj (N (e.symm j).out) :=
        Res.mapIso eout.symm
      exact ⟨i ≫ er.hom, er.inv ≫ p, by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, hip]⟩
  letI : Infinite (Quotient s) := hquotInfinite
  let emb : ℕ ↪ Quotient s := Infinite.natEmbedding (Quotient s)
  exact {
    module := fun m ↦ N (emb m).out
    finite := fun m ↦ hN_finite (emb m).out
    indecomposable := fun m ↦ hN_ind (emb m).out
    eq_of_iso := by
      intro m n hmn
      apply emb.injective
      apply Quotient.out_equiv_out.mp
      exact hmn }

/-- Generic cleaving transfer from split extension objects.  Each extension
may be decomposable.  Finite-dimensionality and a displayed finite
indecomposable decomposition produce one target lift for each source object;
the preceding theorem then removes repetitions. -/
def infiniteFiniteIndecomposableFamilyOfCleavingExtensions
    {S : Type v} [Category.{w} S] [Preadditive S]
    [HasBinaryBiproducts S] [HasFiniteBiproducts S]
    {A : Type w} [Ring A] [Algebra k A]
    (Res : CategoryTheory.Functor (ModuleCat.{w} A) S) [Res.Additive]
    (F : ℕ → S) (hF_ind : ∀ m, Indecomposable (F m))
    (hF_iso : ∀ {m n}, Nonempty (F m ≅ F n) → m = n)
    (hF_local : ∀ m, IsLocalRing (CategoryTheory.End (F m)))
    (E : ℕ → ModuleCat.{w} A)
    (hE_finite : ∀ m, Module.Finite k (E m))
    (hret : ∀ m, IsRetractOf (F m) (Res.obj (E m)))
    (decomposition : ∀ m, FiniteIndecomposableDecomposition (E m))
    (hspectrum : ∀ m (j : Fin (decomposition m).n),
      FiniteIndecomposableRetractSpectrum
        (Res.obj ((decomposition m).summand j))) :
    InfiniteFiniteIndecomposableFamily k A := by
  let hasLift (m : ℕ) :
      ∃ j : Fin (decomposition m).n,
        IsRetractOf (F m)
          (Res.obj ((decomposition m).summand j)) := by
    letI : IsLocalRing (CategoryTheory.End (F m)) := hF_local m
    exact localEnd_retract_restricted_decomposition_summand
      Res (hret m) (decomposition m)
  let liftIndex (m : ℕ) : Fin (decomposition m).n :=
    Classical.choose (hasLift m)
  let N (m : ℕ) : ModuleCat.{w} A :=
    (decomposition m).summand (liftIndex m)
  apply infiniteFiniteIndecomposableFamilyOfCleavingLifts
    Res F hF_ind hF_iso N
  · intro m
    exact (decomposition m).summand_finite
      (hE_finite m) (liftIndex m)
  · intro m
    exact (decomposition m).indecomposable (liftIndex m)
  · intro m
    exact Classical.choose_spec (hasLift m)
  · intro m
    exact hspectrum m (liftIndex m)

end LargeIndecomposable.ClosedZigzagTransfer
