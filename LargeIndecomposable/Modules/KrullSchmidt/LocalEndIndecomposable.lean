module

public import LargeIndecomposable.RepresentationType.Basic.RightModuleFiniteType
public import LargeIndecomposable.Foundations.CategoryTheory.IndecomposableOfLocalEnd
public import LargeIndecomposable.Modules.KrullSchmidt.LocalEndFiniteDimensional
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFitting
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

set_option backward.isDefEq.respectTransparency.types false

/-!
# Local endomorphism rings of finite-dimensional indecomposable modules

Fitting decomposition shows that every endomorphism of a finite-dimensional
indecomposable module is either invertible or nilpotent.  Consequently its
endomorphism ring is local.  The result is then transported through the fully
faithful inclusion of finitely generated modules into all modules.

The file also records a ring-level form: a finite-dimensional algebra with
no nontrivial idempotents is local.  This follows by applying Fitting's lemma
to its right regular module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace LargeIndecomposable

universe u₁ u₂ v

namespace Categorical.Functor

variable {C : Type u₁} [Category.{v} C] [Preadditive C]
variable {D : Type u₂} [Category.{v} D] [Preadditive D]

/-- A fully faithful additive functor identifies the endomorphism rings of an
object and its image. -/
def endRingEquivOfFullyFaithful
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] (X : C) :
    End X ≃+* End (F.obj X) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' _ _ := F.map_add
  map_mul' f g := F.map_comp g f

@[simp]
theorem endRingEquivOfFullyFaithful_apply
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (X : C) (f : End X) :
    endRingEquivOfFullyFaithful F X f = F.map f :=
  rfl

end Categorical.Functor

universe u

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

/-- Left multiplication identifies a ring with the endomorphism ring of its
right regular module. -/
noncomputable def rightRegularEndEquiv (R : Type v) [Ring R] :
    R ≃+* Module.End Rᵐᵒᵖ R where
  toFun a := LinearMap.mulLeft Rᵐᵒᵖ a
  invFun f := f 1
  left_inv a := by simp
  right_inv f := by
    apply LinearMap.ext
    intro x
    have hx := f.map_smul (MulOpposite.op x) (1 : R)
    simpa using hx.symm
  map_add' a b := by
    apply LinearMap.ext
    intro x
    exact add_mul a b x
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    simp [Module.End.mul_apply]

/-- A finite-dimensional algebra whose only idempotents are zero and one is
local.  Fitting is applied to the right regular module, whose endomorphism
ring is the original ring through left multiplication. -/
theorem finiteDimensional_isLocalRing_of_idempotents
    (R : Type v) [Ring R] [Algebra k R] [Nontrivial R]
    [FiniteDimensional k R]
    (hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsLocalRing R := by
  let E := rightRegularEndEquiv R
  have hind :
      LargeIndecomposable.Foundation.IsIndecomposableModule
        Rᵐᵒᵖ R := by
    rw [LargeIndecomposable.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
    refine ⟨inferInstance, ?_⟩
    intro f hf
    have ha : IsIdempotentElem (E.symm f) := hf.map E.symm
    rcases hidem (E.symm f) ha with ha | ha
    · left
      simpa using congrArg E ha
    · right
      simpa using congrArg E ha
  letI : Module.Finite k Rᵐᵒᵖ := inferInstance
  letI : IsArtinianRing Rᵐᵒᵖ := IsArtinianRing.of_finite k Rᵐᵒᵖ
  letI : Module.Finite Rᵐᵒᵖ R :=
    Module.Finite.of_restrictScalars_finite k Rᵐᵒᵖ R
  letI : IsArtinian Rᵐᵒᵖ R := inferInstance
  letI : IsNoetherian Rᵐᵒᵖ R := inferInstance
  letI : IsLocalRing (Module.End Rᵐᵒᵖ R) :=
    LargeIndecomposable.Foundation.isLocalRing_end_of_isIndecomposable
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨inferInstance, inferInstance⟩) hind
  exact RingEquiv.isLocalRing_noncomm E.symm



namespace RightModule.FiniteIndecomposableSkeleton

variable [FiniteDimensional k A]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The chosen skeleton object's endomorphism ring remains local after it is
bundled in the literal category of finitely generated right modules. -/
theorem fgObj_end_isLocalRing (i : Fin S.n) :
    IsLocalRing (End (S.fgObj i)) := by
  let U := forget₂ (RightModule.FinitelyGeneratedCategory A)
    (RightModule.Category A)
  letI : U.Additive := ⟨by intros; rfl⟩
  letI : Module.Finite k Aᵐᵒᵖ := inferInstance
  letI : Module.Finite k (S.obj i) := S.obj_finite i
  letI : IsLocalRing (End (U.obj (S.fgObj i))) := by
    change IsLocalRing (End (S.obj i))
    exact moduleCat_end_isLocalRing (k := k) (A := Aᵐᵒᵖ)
      (S.obj i) (S.obj_indecomposable i)
  exact RingEquiv.isLocalRing_noncomm
    (Categorical.Functor.endRingEquivOfFullyFaithful U (S.fgObj i)).symm

end RightModule.FiniteIndecomposableSkeleton

end LargeIndecomposable
