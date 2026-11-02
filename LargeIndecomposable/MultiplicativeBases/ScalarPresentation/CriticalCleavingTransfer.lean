module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalSingularPath
public import LargeIndecomposable.Cleaving.ClosedChains.CrossUniverseAssembly
public import LargeIndecomposable.Cleaving.ClosedChains.GenericFiniteness
public import LargeIndecomposable.Modules.KrullSchmidt.LocalEndFiniteDimensional
public import Mathlib.Tactic

@[expose] public section

/-!
# A source-independent coend boundary for the BGRS critical diagrams

This file extracts the part of the closed-chain/Figure-16 argument which does
not depend on the shape of the finite source.  A `CleavingSourceFamily` is an
explicit countable family of finite-dimensional, indecomposable,
pairwise-nonisomorphic source modules with local endomorphism rings.  A
Hom-bifunctor retraction for a realization of that source in the primitive
projectives then produces an infinite family over the ambient algebra by the
cross-universe coend construction.

The point of the interface is that the callbacks which remain in Figures 14
and 15 are literal cleaving (Hom-bifunctor retraction) callbacks.  No
representation-infinite conclusion is assumed in the package.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.CriticalSingularCleaving

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u uA x

variable {k : Type u} [Field k]

/-- The exact source-side representation-infinite witness consumed by the
generic cleaving transfer.  All its fields concern modules over the displayed
finite source; it contains no assertion about the ambient algebra. -/
structure CleavingSourceFamily
    (K : Type) [Category.{u} K] [Preadditive K] [Linear k K] where
  anchor : K
  module : ℕ → K ⥤ ModuleCat.{u} k
  additive : ∀ n, (module n).Additive
  linear : ∀ n, (module n).Linear k
  obj_finite : ∀ n X, Module.Finite k ((module n).obj X)
  indecomposable : ∀ n, Indecomposable (module n)
  eq_of_iso : ∀ {m n}, Nonempty (module m ≅ module n) → m = n
  end_isLocalRing : ∀ n, IsLocalRing (CategoryTheory.End (module n))

namespace CleavingSourceFamily

variable {K : Type} [Category.{u} K] [Preadditive K] [Linear k K]

instance module_additive (F : CleavingSourceFamily (k := k) K) (n : ℕ) :
    (F.module n).Additive := F.additive n

instance module_linear (F : CleavingSourceFamily (k := k) K) (n : ℕ) :
    (F.module n).Linear k := F.linear n

/-- Universe lift of a source family to the common coend carrier universe. -/
def lifted (F : CleavingSourceFamily (k := k) K)
    (_A : Type uA) (n : ℕ) :
    K ⥤ ModuleCat.{max u uA} k :=
  F.module n ⋙ ModuleCat.uliftFunctor.{uA} k

instance lifted_additive (F : CleavingSourceFamily (k := k) K)
    (A : Type uA) (n : ℕ) : (F.lifted A n).Additive := by
  unfold lifted
  infer_instance

instance lifted_linear (F : CleavingSourceFamily (k := k) K)
    (A : Type uA) (n : ℕ) : (F.lifted A n).Linear k := by
  unfold lifted
  infer_instance

instance lifted_obj_finite (F : CleavingSourceFamily (k := k) K)
    (A : Type uA) (n : ℕ) (X : K) :
    Module.Finite k ((F.lifted A n).obj X) := by
  letI : Module.Finite k ((F.module n).obj X) := F.obj_finite n X
  change Module.Finite k (ULift.{uA} ((F.module n).obj X))
  infer_instance

abbrev liftFunctor (_A : Type uA) :
    (K ⥤ ModuleCat.{u} k) ⥤ (K ⥤ ModuleCat.{max u uA} k) :=
  (Functor.whiskeringRight K (ModuleCat.{u} k)
      (ModuleCat.{max u uA} k)).obj
    (ModuleCat.uliftFunctor.{uA} k)

theorem lifted_eq_of_iso (F : CleavingSourceFamily (k := k) K)
    (A : Type uA) {m n : ℕ}
    (e : F.lifted A m ≅ F.lifted A n) : m = n := by
  let W := liftFunctor (k := k) (K := K) A
  let hW : W.FullyFaithful :=
    (ModuleCat.fullyFaithfulUliftFunctor (R := k)).whiskeringRight K
  change W.obj (F.module m) ≅ W.obj (F.module n) at e
  exact F.eq_of_iso ⟨hW.preimageIso e⟩

theorem lifted_indecomposable (F : CleavingSourceFamily (k := k) K)
    (A : Type uA) (n : ℕ) : Indecomposable (F.lifted A n) := by
  let W := liftFunctor (k := k) (K := K) A
  let X := F.module n
  let hW : W.FullyFaithful :=
    (ModuleCat.fullyFaithfulUliftFunctor (R := k)).whiskeringRight K
  change Indecomposable (W.obj X)
  apply indecomposable_of_idempotent_eq_zero_or_id_preadditive
  · intro hzero
    have hXzero : IsZero X := IsZero.of_full_of_faithful_of_isZero W X hzero
    exact (F.indecomposable n).1 hXzero
  · intro p hp
    let q : X ⟶ X := hW.preimage p
    have hq : q ≫ q = q := by
      apply W.map_injective
      exact hp
    have hpq : W.map q = p := hW.map_preimage p
    rcases idempotent_eq_zero_or_id_of_indecomposable_preadditive
        (F.indecomposable n) q hq with hq0 | hq1
    · left
      rw [← hpq, hq0, W.map_zero]
    · right
      rw [← hpq, hq1, W.map_id]

theorem lifted_end_isLocalRing (F : CleavingSourceFamily (k := k) K)
    (A : Type uA) (n : ℕ) :
    IsLocalRing (CategoryTheory.End (F.lifted A n)) := by
  let W := liftFunctor (k := k) (K := K) A
  let X := F.module n
  let hW : W.FullyFaithful :=
    (ModuleCat.fullyFaithfulUliftFunctor (R := k)).whiskeringRight K
  let e : CategoryTheory.End X ≃+* CategoryTheory.End (W.obj X) :=
    { hW.mulEquivEnd X with map_add' := fun _ _ ↦ W.map_add }
  letI : IsLocalRing (CategoryTheory.End X) := F.end_isLocalRing n
  change IsLocalRing (CategoryTheory.End (W.obj X))
  exact LargeIndecomposable.RingEquiv.isLocalRing_noncomm e

end CleavingSourceFamily

section Transfer

variable {K : Type} [Category.{u} K] [Preadditive K] [Linear k K]
variable [Fintype K]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))
variable (F : CleavingSourceFamily (k := k) K)
variable (D : K ⥤ S.ProjectiveCategory)
variable [D.Additive] [D.Linear k]

/-- Restriction of an algebra module to an arbitrary finite cleaving source
realized in the primitive projectives. -/
def restriction :
    ModuleCat.{max u uA} A ⥤ (K ⥤ ModuleCat.{max u uA} k) :=
  LargeIndecomposable.SplitBasicIdempotents.projectiveRestriction
      (k := k) S ⋙
    (Functor.whiskeringLeft K S.ProjectiveCategory
      (ModuleCat.{max u uA} k)).obj D

instance restriction_additive : (restriction S D).Additive := by
  unfold restriction
  infer_instance

abbrev coendFamily (n : ℕ) :=
  ClosedZigzagCrossUniverse.coendExtension D (F.lifted A n)

instance coendFamily_additive (n : ℕ) :
    (coendFamily S F D n).Additive := by
  unfold coendFamily
  infer_instance

instance coendFamily_linear (n : ℕ) :
    (coendFamily S F D n).Linear k := by
  unfold coendFamily
  infer_instance

abbrev realizedFamily (n : ℕ) :=
  LargeIndecomposable.SplitBasicIdempotents.realizedModule S
    (coendFamily S F D n)

omit [D.Additive] in
theorem realizedFamily_finite (n : ℕ) :
    Module.Finite k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj
        (realizedFamily S F D n)) := by
  let G := coendFamily S F D n
  letI : Module.Finite k
      (LargeIndecomposable.SplitBasicIdempotents.realizedCarrier S G) := by
    infer_instance
  let e :
      ULift.{0} (LargeIndecomposable.SplitBasicIdempotents.realizedCarrier S G) ≃ₗ[k]
        ((ModuleCat.restrictScalars (algebraMap k A)).obj
          (LargeIndecomposable.SplitBasicIdempotents.realizedModule S G)) :=
    { toFun := fun q ↦ q.down
      invFun := fun q ↦ ULift.up q
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c q ↦ by
        change c • q.down =
          (LargeIndecomposable.SplitBasicIdempotents.realizedActionAlgHom S G
            (algebraMap k A c)) q.down
        rw [(LargeIndecomposable.SplitBasicIdempotents.realizedActionAlgHom S G).commutes]
        rfl }
  exact Module.Finite.equiv e

omit [Module.Finite k A] in
/-- The cross-universe coend unit remains a retract after projective
realization. -/
theorem liftedFamily_isRetract
    (hD : ClosedZigzagCrossUniverse.HomBifunctorRetraction (k := k) D)
    (n : ℕ) :
    IsRetractOf (F.lifted A n)
      ((restriction S D).obj (realizedFamily S F D n)) := by
  change IsRetractOf (F.lifted A n)
    (D ⋙ LargeIndecomposable.SplitBasicIdempotents.projectiveRestrictionObj S
      (LargeIndecomposable.SplitBasicIdempotents.realizedModule S
        (coendFamily S F D n)))
  let e :=
    LargeIndecomposable.SplitBasicIdempotents.realizedRestrictionWhiskerLeftNatIso
      S (coendFamily S F D n) D
  refine ⟨ClosedZigzagCrossUniverse.coendUnit D (F.lifted A n) ≫ e.inv,
    e.hom ≫ ClosedZigzagCrossUniverse.coendRetraction D
      (F.lifted A n) hD, ?_⟩
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ClosedZigzagCrossUniverse.coendUnit_retraction D (F.lifted A n) hD

omit [Preadditive K] [Linear k K] [Fintype K] [Module.Finite k A]
    [D.Additive] [D.Linear k] in
/-- Restriction to a primitive projective component preserves finite
dimensionality. -/
theorem restriction_obj_finite
    (M : ModuleCat.{max u uA} A)
    (hM : Module.Finite k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj M))
    (X : K) : Module.Finite k (((restriction S D).obj M).obj X) := by
  letI : Module.Finite k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj M) := hM
  change Module.Finite k
    (LargeIndecomposable.SplitBasicIdempotents.projectiveRestrictionComponent
      S M (D.obj X))
  let inclusion :
      LargeIndecomposable.SplitBasicIdempotents.projectiveRestrictionComponent
          S M (D.obj X) →ₗ[k]
        ((ModuleCat.restrictScalars (algebraMap k A)).obj M) :=
    { toFun := fun q ↦ q.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.of_injective inclusion Subtype.val_injective

def largeRestriction :
    ModuleCat.{max u uA} (ClosedZigzagCrossUniverse.largeAlgebra k A) ⥤
      (K ⥤ ModuleCat.{max u uA} k) :=
  (ClosedZigzagCrossUniverse.largeModuleEquivalence
      (k := k) (A := A)).inverse ⋙ restriction S D

instance largeRestriction_additive : (largeRestriction S D).Additive := by
  unfold largeRestriction
  infer_instance

abbrev largeRealizedFamily (n : ℕ) :=
  (ClosedZigzagCrossUniverse.largeModuleEquivalence
      (k := k) (A := A)).functor.obj (realizedFamily S F D n)

omit [D.Additive] in
theorem largeRealizedFamily_finite (n : ℕ) :
    Module.Finite k (largeRealizedFamily S F D n) := by
  letI : Module.Finite k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj
        (realizedFamily S F D n)) := realizedFamily_finite S F D n
  let e :
      ((ModuleCat.restrictScalars (algebraMap k A)).obj
          (realizedFamily S F D n)) ≃ₗ[k]
        largeRealizedFamily S F D n :=
    { toFun := fun q ↦ q
      invFun := fun q ↦ q
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.equiv e

omit [Module.Finite k A] in
theorem liftedFamily_isRetract_large
    (hD : ClosedZigzagCrossUniverse.HomBifunctorRetraction (k := k) D)
    (n : ℕ) :
    IsRetractOf (F.lifted A n)
      ((largeRestriction S D).obj (largeRealizedFamily S F D n)) := by
  obtain ⟨i, p, hip⟩ := liftedFamily_isRetract S F D hD n
  let e := ClosedZigzagCrossUniverse.largeModuleEquivalence
    (k := k) (A := A)
  let eu : realizedFamily S F D n ≅
      e.inverse.obj (e.functor.obj (realizedFamily S F D n)) :=
    { hom := e.unitIso.hom.app (realizedFamily S F D n)
      inv := e.unitIso.inv.app (realizedFamily S F D n)
      hom_inv_id := by simp
      inv_hom_id := by simp }
  let er := (restriction S D).mapIso eu
  exact ⟨i ≫ er.hom, er.inv ≫ p, by simp [Category.assoc, hip]⟩

def largeRealizedFamily_decomposition (n : ℕ) :
    FiniteIndecomposableDecomposition (largeRealizedFamily S F D n) :=
  Classical.choice
    (@finiteIndecomposableDecomposition_exists k _
      (ClosedZigzagCrossUniverse.largeAlgebra k A) _ _ _
      (largeRealizedFamily S F D n)
      (largeRealizedFamily_finite S F D n))

def largeRestriction_spectrum (n : ℕ)
    (j : Fin (largeRealizedFamily_decomposition S F D n).n) :
    FiniteIndecomposableRetractSpectrum
      ((largeRestriction S D).obj
        ((largeRealizedFamily_decomposition S F D n).summand j)) := by
  apply finiteIndecomposableRetractSpectrum_functor
  intro X
  apply restriction_obj_finite S D
  let N := (largeRealizedFamily_decomposition S F D n).summand j
  letI : Module.Finite k N :=
    (largeRealizedFamily_decomposition S F D n).summand_finite
      (largeRealizedFamily_finite S F D n) j
  exact Module.Finite.equiv
    (ClosedZigzagCrossUniverse.largeModuleEquivalenceInverseObjLinearEquiv
      (k := k) (A := A) N)

/-- Generic coend transfer: a literal Hom-bifunctor retraction of a finite
source carrying an explicit infinite family constructs an infinite family
over the lifted ambient algebra. -/
def infiniteFamily_of_homBifunctorRetraction [Infinite k]
    (F : CleavingSourceFamily (k := k) K)
    (hD : ClosedZigzagCrossUniverse.HomBifunctorRetraction (k := k) D) :
    InfiniteFiniteIndecomposableFamily k
      (ClosedZigzagCrossUniverse.largeAlgebra k A) := by
  apply infiniteFiniteIndecomposableFamilyOfCleavingExtensions
    (k := k) (A := ClosedZigzagCrossUniverse.largeAlgebra k A)
    (largeRestriction S D) (F.lifted A)
    (F.lifted_indecomposable A)
    (fun {_ _} h ↦ F.lifted_eq_of_iso A (Classical.choice h))
    (F.lifted_end_isLocalRing A)
    (largeRealizedFamily S F D)
    (largeRealizedFamily_finite S F D)
    (liftedFamily_isRetract_large S F D hD)
    (largeRealizedFamily_decomposition S F D)
  exact largeRestriction_spectrum S F D

/-- Generic source-faithful cleaving contradiction.  The only ambient input
is the Hom-bifunctor retraction of the displayed finite diagram. -/
theorem not_isRepresentationFinite_of_homBifunctorRetraction [Infinite k]
    (F : CleavingSourceFamily (k := k) K)
    (hD : ClosedZigzagCrossUniverse.HomBifunctorRetraction (k := k) D) :
    ¬ LargeIndecomposable.IsRepresentationFinite k A := by
  let X : S.ProjectiveCategory := D.obj F.anchor
  letI : Nontrivial (X ⟶ X) :=
    ⟨⟨𝟙 X, 0,
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.id_ne_zero S X⟩⟩
  letI : Nontrivial A :=
    (show Function.Injective (fun q : (X ⟶ X) ↦ (q.1 : A)) from
      Subtype.val_injective).nontrivial
  intro hfinite
  have hlarge : LargeIndecomposable.IsRepresentationFinite k
      (ClosedZigzagCrossUniverse.largeAlgebra k A) :=
    hfinite.of_crossUniverse_algEquiv
      (ULift.algEquiv (R := k) (A := A)).symm
  apply hlarge.not_infiniteFiniteIndecomposableFamily.false
  exact infiniteFamily_of_homBifunctorRetraction (S := S) (D := D) F hD

end Transfer

end LargeIndecomposable.CriticalSingularCleaving
