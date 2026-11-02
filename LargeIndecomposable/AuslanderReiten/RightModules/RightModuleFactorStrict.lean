module

public import LargeIndecomposable.AuslanderReiten.RightModules.RightModuleTauAssembly
public import Mathlib.CategoryTheory.Quotient.Linear
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.CategoryTheory.Quotient.Preadditive
public import LargeIndecomposable.Foundations.CategoryTheory.CategoricalRadical
public import LargeIndecomposable.Foundations.CategoryTheory.HomIdeal
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.RingTheory.Idempotents
public import Mathlib.CategoryTheory.Simple
public import LargeIndecomposable.AuslanderReiten.TauCategories.HomUnitEquations

set_option backward.isDefEq.respectTransparency.types false

/-!
# Strictness criteria for literal finite-module factors

The primitive deletion in the frozen manuscript has a distinguished
projective source `P` whose covariant representable functor on the factor is
faithful and which has no maps to killed modules.  This file isolates the
exact categorical consequences of those two facts: quotient images of
ambient monomorphisms remain monic, and hence all chosen factor right meshes
are strict.  The dual criterion treats a distinguished injective sink.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open LargeIndecomposable
open LargeIndecomposable.CategoricalIdeal
open LargeIndecomposable.Iyama
open scoped ModuleCat.Algebra ZeroObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The first map of every ambient selected-label right mesh is monic. -/
theorem labelRightMesh_f_mono (x : Fin S.n) :
    Mono (S.labelRightMesh x).f := by
  classical
  by_cases hx : Projective (S.fgObj x)
  · rw [show S.labelRightMesh x = S.projectiveRightMesh x hx by
      simp [labelRightMesh, hx]]
    dsimp only [projectiveRightMesh]
    exact (isZero_zero (RightModule.FinitelyGeneratedCategory A)).mono _
  · rw [show S.labelRightMesh x =
      S.nonprojectiveRightMesh ⟨x, hx⟩ by
      simp [labelRightMesh, hx]]
    dsimp only [nonprojectiveRightMesh]
    infer_instance

/-- The second map of every ambient selected-label left mesh is epic. -/
theorem labelLeftMesh_g_epi (x : Fin S.n) :
    Epi (S.labelLeftMesh x).g := by
  classical
  by_cases hx : Injective (S.fgObj x)
  · have hzero : IsZero (S.labelLeftMesh x).X₃ :=
      (S.labelLeftMesh_X₃_isZero_iff_injective x).2 hx
    exact hzero.epi _
  · let z := (S.rightTranslationEquiv).symm
      (⟨x, hx⟩ : {y : Fin S.n // ¬ Injective (S.fgObj y)})
    let B := S.minimalRightAlmostSplitAt z.1
    have hBEpi : Epi B.map :=
      IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
        S.almostSplitSkeleton B.map B.rightAlmostSplit z.2
    rw [show S.labelLeftMesh x =
        S.noninjectiveLeftMesh
          (⟨x, hx⟩ : {y : Fin S.n // ¬ Injective (S.fgObj y)}) by
      simp [labelLeftMesh, hx]]
    change Epi B.map
    exact hBEpi

end LargeIndecomposable.RightModule.FiniteIndecomposableSkeleton
