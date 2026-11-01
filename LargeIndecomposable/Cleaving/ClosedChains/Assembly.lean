module

public import LargeIndecomposable.Cleaving.ClosedChains.CoendExtension
public import LargeIndecomposable.Cleaving.ClosedChains.GenericFiniteness
public import LargeIndecomposable.Cleaving.ClosedChains.LinearThinFamily
public import LargeIndecomposable.Cleaving.ClosedChains.ProjectiveModuleRealization
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteUniverse
public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayCategory
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.ClosedZigzagAssembly

universe u x

open LargeIndecomposable.ClosedZigzag
open LargeIndecomposable.ClosedZigzagTransfer

variable {k : Type u} [Field k]
variable {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

instance linearSourceFintype (n : ℕ) : Fintype (LinearSource k n) :=
  Fintype.ofEquiv (Vertex n)
    { toFun := Opposite.op
      invFun := Opposite.unop
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Restrict an `A`-module to the primitive-projective category and then
along the representative functor of a fixed closed ray chain. -/
def chainRestriction
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) :
    ModuleCat.{u} A ⥤
      (LinearSource k (t.length - 1) ⥤ ModuleCat.{u} k) :=
  LargeIndecomposable.SplitBasicIdempotents.projectiveRestriction
      (k := k) S ⋙
    (Functor.whiskeringLeft
      (LinearSource k (t.length - 1)) S.ProjectiveCategory
        (ModuleCat.{u} k)).obj
      (chainRepresentativeLinearFunctor (k := k) t)

instance chainRestriction_additive
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) :
    (chainRestriction S t).Additive := by
  unfold chainRestriction
  infer_instance

abbrev chainRepresentative
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) :=
  chainRepresentativeLinearFunctor (k := k) t

abbrev chainThinFamily [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :=
  linearFamily (k := k) (t.length - 1) m

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
    Module.Finite k ((chainThinFamily S t m).obj X) :=
  linearFamily_obj_finite (t.length - 1) m X

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

/-- The coend split injection, transported across realization--restriction,
exhibits every thin source representation as a retract of an actual
`A`-module restriction.  The same universe for `k` and `A` is explicit in
this file because the current `HomBifunctorRetraction` interface gives its
source and target categories the same Hom universe. -/
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

/-- A chosen Krull--Schmidt decomposition of each finite realized coend
extension. -/
def chainRealizedExtension_decomposition [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory)) (m : ℕ) :
    FiniteIndecomposableDecomposition (chainRealizedExtension S t m) :=
  Classical.choice
    (@finiteIndecomposableDecomposition_exists k _ A _ _ _
      (chainRealizedExtension S t m)
      (chainRealizedExtension_finite S t m))

/-- Restriction to a primitive idempotent component preserves finite
dimensionality over `k`. -/
theorem chainRestriction_obj_finite
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (M : ModuleCat.{u} A)
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

/-- Every indecomposable summand of a realized coend extension has finite
indecomposable retract spectrum after restriction to the finite linear
source. -/
def chainRestriction_spectrum [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (m : ℕ)
    (j : Fin (chainRealizedExtension_decomposition S t m).n) :
    FiniteIndecomposableRetractSpectrum
      ((chainRestriction S t).obj
        ((chainRealizedExtension_decomposition S t m).summand j)) := by
  apply finiteIndecomposableRetractSpectrum_functor
  intro X
  apply chainRestriction_obj_finite S t
  exact (chainRealizedExtension_decomposition S t m).summand_finite
    (chainRealizedExtension_finite S t m) j

/-- Same-universe closed-chain endpoint.  A Hom-bifunctor retraction for
the representative functor is the only additional callback: the coend split
retraction, projective realization, Krull--Schmidt decomposition, and finite
retract-spectrum argument construct the infinite target family.  The
restriction `k A : Type u` reflects the current same-Hom-universe binder in
`HomBifunctorRetraction`. -/
def infiniteFiniteIndecomposableFamily_of_rayClosedChain [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (hD : HomBifunctorRetraction (k := k) (chainRepresentative S t)) :
    InfiniteFiniteIndecomposableFamily k A := by
  apply infiniteFiniteIndecomposableFamilyOfCleavingExtensions
    (k := k) (A := A)
    (chainRestriction S t)
    (chainThinFamily S t)
    (fun m ↦ linearFamily_indecomposable (t.length - 1) m)
    (fun {_ _} h ↦ linearFamily_eq_of_iso (Classical.choice h))
    (fun m ↦ linearFamily_end_isLocalRing (t.length - 1) m)
    (chainRealizedExtension S t)
    (chainRealizedExtension_finite S t)
    (chainThinFamily_isRetract S t hD)
    (chainRealizedExtension_decomposition S t)
  exact chainRestriction_spectrum S t

/-- Under the present same-universe interface, a closed ray chain with its
Hom-bifunctor retraction contradicts representation-finiteness. -/
theorem not_isRepresentationFinite_of_rayClosedChain [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
    (hD : HomBifunctorRetraction (k := k) (chainRepresentative S t)) :
    ¬ IsRepresentationFinite k A := by
  intro hfinite
  apply hfinite.not_infiniteFiniteIndecomposableFamily.false
  exact infiniteFiniteIndecomposableFamily_of_rayClosedChain S t hD

end LargeIndecomposable.ClosedZigzagAssembly
