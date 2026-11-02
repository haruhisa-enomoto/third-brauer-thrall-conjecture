/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Monomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Noetherian.Basic
public import LargeIndecomposable.Quivers.Representations.DimensionVector
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.LeftExact
-- Non-public: monomorphisms and epimorphisms of functors into an abelian category are
-- monomorphisms and epimorphisms at every object.
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! Ported from TauCeti (`TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional`, commit 580b6f9d5, Apache 2.0). -/

/-!
# Finite-dimensional quiver representations

A representation of a quiver is **pointwise finite-dimensional** when the vector space it puts at
every vertex is finite-dimensional. This file defines that property, `LargeIndecomposable.Foundations.IsFinDim`, proves
that it is stable under subobjects and quotients, equips its full subcategory with an abelian
structure and an exact inclusion, proves essential smallness for a finite vertex set, and shows
that a path algebra module finite-dimensional over the base field gives such a representation.

## Main definitions

* `LargeIndecomposable.Foundations.IsFinDim`: a representation is finite-dimensional at every vertex.

## Main results

* `LargeIndecomposable.Foundations.IsFinDim.of_iso`: pointwise finite-dimensionality transports along an isomorphism.
* `LargeIndecomposable.Foundations.IsFinDim.of_mono` and `LargeIndecomposable.Foundations.IsFinDim.of_epi`: subobjects and quotients of pointwise
  finite-dimensional representations are pointwise finite-dimensional.
* The full subcategory of `IsFinDim` representations is abelian, by Mathlib's abelian
  full-subcategory construction. Its inclusion preserves finite limits and colimits, so kernels,
  cokernels and short exact sequences have their ambient pointwise meaning.
* `LargeIndecomposable.Foundations.isFinDim_biproduct`: finite biproducts of finite-dimensional representations are
  finite-dimensional.
* The full subcategory of `IsFinDim` representations is essentially small for finite `Q`.
* `LargeIndecomposable.Foundations.module_finite_asModule_of_isFinDim`: a pointwise finite-dimensional representation
  gives a finite module over the path algebra when the vertex set is finite.
* `LargeIndecomposable.Foundations.module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim`: the module it is carried to
  by `LargeIndecomposable.Foundations.quiverRepEquivalence` is finite-dimensional over the base field.
* `LargeIndecomposable.Foundations.isFinDim_quiverRepFunctor_obj`: finite-dimensionality passes from a module to its
  associated representation.

## Implementation notes

`IsFinDim` is stated vertex by vertex rather than as a single finiteness of the total space: the
category of representations is a functor category, with no ambient module to be finite over, and
over an infinite vertex set the two conditions genuinely differ. Over a finite quiver they agree,
and that is the setting the theory is meant for.

-/

public section

namespace LargeIndecomposable.Foundations

open CategoryTheory
open scoped ModuleCat

universe u v w t

/-- **Pointwise finite-dimensionality** of a quiver representation: the vector space at every
vertex is finite-dimensional. Over a finite quiver this is total finite-dimensionality, and it is
the finiteness condition under which the indecomposables can be counted; the functor category
itself contains infinite-dimensional objects. -/
def IsFinDim (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
    (M : QuiverRep.{u, v, w, t} k Q) : Prop :=
  ∀ v : Paths Q, FiniteDimensional k (M.obj v)

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **The elimination and introduction rule for `LargeIndecomposable.Foundations.IsFinDim`**: it is finite-dimensionality
at every vertex. -/
@[simp]
theorem isFinDim_iff {M : QuiverRep.{u, v, w, t} k Q} :
    IsFinDim k Q M ↔ ∀ v : Paths Q, FiniteDimensional k (M.obj v) :=
  Iff.rfl

/-- Finite-dimensionality at each vertex transports along an isomorphism of representations. -/
theorem IsFinDim.of_iso {M N : QuiverRep.{u, v, w, t} k Q} (h : IsFinDim k Q M) (e : M ≅ N) :
    IsFinDim k Q N := by
  intro v
  have := h v
  exact (e.app v).toLinearEquiv.finiteDimensional

/-- **A subobject of a pointwise finite-dimensional representation is pointwise
finite-dimensional.** A monomorphism of representations is a monomorphism at every vertex, hence an
injective linear map into a finite-dimensional space. The intended instance is a biproduct summand,
`CategoryTheory.Limits.biproduct.ι` being a split monomorphism. -/
theorem IsFinDim.of_mono {M N : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M)
    (f : N ⟶ M) [Mono f] : IsFinDim k Q N := by
  rw [isFinDim_iff] at hM ⊢
  intro x
  have hMx := hM x
  have hmono : Mono (f.app x) := inferInstance
  rw [ModuleCat.mono_iff_injective] at hmono
  exact FiniteDimensional.of_injective (f.app x).hom hmono

/-- A quotient of a pointwise finite-dimensional representation is pointwise finite-dimensional.
No finiteness of the quiver is required. -/
theorem IsFinDim.of_epi {M N : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M)
    (f : M ⟶ N) [Epi f] : IsFinDim k Q N := by
  intro x
  have := hM x
  exact Module.Finite.of_surjective (f.app x).hom
    ((ModuleCat.epi_iff_surjective (f.app x)).mp inferInstance)

section ExactStructure

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

open CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped ZeroObject

/-- Subobjects stay in the pointwise finite-dimensional subcategory. -/
instance : ObjectProperty.IsClosedUnderSubobjects (IsFinDim.{u, v, w, t} k Q) where
  prop_of_mono f _ h := h.of_mono f

/-- Quotients stay in the pointwise finite-dimensional subcategory. -/
instance : ObjectProperty.IsClosedUnderQuotients (IsFinDim.{u, v, w, t} k Q) where
  prop_of_epi f _ h := h.of_epi f

/-- The zero representation belongs to the finite-dimensional full subcategory. -/
instance : ObjectProperty.ContainsZero (IsFinDim.{u, v, w, t} k Q) where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    rw [isFinDim_iff]
    intro i
    have hi : IsZero ((0 : QuiverRep.{u, v, w, t} k Q).obj i) := Functor.zero_obj i
    let : Subsingleton ((0 : QuiverRep.{u, v, w, t} k Q).obj i) :=
      ModuleCat.subsingleton_of_isZero hi
    infer_instance

end ExactStructure

variable (k Q) [Finite Q]

end LargeIndecomposable.Foundations
