module

public import LargeIndecomposable.RepresentationType.Basic.RepresentationFinite
public import LargeIndecomposable.Foundations.CategoryTheory.LinearMat
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

@[expose] public section

/-!
# Finite skeletons of indecomposable modules

Representation-finiteness is stated using a finite family which may contain
repetitions.  Auslander--Reiten constructions require an actual finite
skeleton.  This file quotients such a family by module isomorphism, chooses
one representative of every quotient class, and equips the resulting finite
index with its induced full linear category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace LargeIndecomposable

universe u v

variable (k : Type u) [Field k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- A finite skeleton of the finite-dimensional indecomposable left
`A`-modules. -/
structure IndecomposableModuleSkeleton where
  n : ℕ
  obj : Fin n → ModuleCat.{v} A
  obj_finite : ∀ i, Module.Finite k (obj i)
  obj_indecomposable : ∀ i, Indecomposable (obj i)
  eq_of_iso : ∀ {i j}, Nonempty (obj i ≅ obj j) → i = j
  complete : ∀ M : ModuleCat.{v} A,
    IsFiniteIndecomposable k A M → ∃ i, Nonempty (M ≅ obj i)

namespace IndecomposableModuleSkeleton

variable {k A}

/-- Isomorphism of members of a module family is an equivalence relation on
its index type. -/
def moduleIsoSetoid {σ : Type*} (X : σ → ModuleCat.{v} A) : Setoid σ where
  r i j := Nonempty (X i ≅ X j)
  iseqv := {
    refl := fun i ↦ ⟨Iso.refl (X i)⟩
    symm := fun h ↦ h.map Iso.symm
    trans := fun hij hjl ↦ Nonempty.map2 Iso.trans hij hjl }

/-- Representation-finiteness supplies a finite skeleton with no repeated
isomorphism classes. -/
theorem exists_of_isRepresentationFinite
    (hA : IsRepresentationFinite k A) :
    Nonempty (IndecomposableModuleSkeleton k A) := by
  obtain ⟨n, X, hX, hcover⟩ := hA
  let s : Setoid (Fin n) := moduleIsoSetoid X
  letI : DecidableRel ((· ≈ ·) : Fin n → Fin n → Prop) :=
    Classical.decRel _
  letI : Fintype (Quotient s) := Quotient.fintype s
  let e : Quotient s ≃ Fin (Fintype.card (Quotient s)) :=
    Fintype.equivFin (Quotient s)
  let Y : Fin (Fintype.card (Quotient s)) → ModuleCat.{v} A :=
    fun i ↦ X (e.symm i).out
  refine ⟨{
    n := Fintype.card (Quotient s)
    obj := Y
    obj_finite := ?_
    obj_indecomposable := ?_
    eq_of_iso := ?_
    complete := ?_ }⟩
  · intro i
    exact (hX (e.symm i).out).1
  · intro i
    exact (hX (e.symm i).out).2
  · intro i j hij
    apply e.symm.injective
    apply Quotient.out_equiv_out.mp
    exact hij
  · intro M hM
    obtain ⟨i, ⟨hMi⟩⟩ := hcover M hM
    let q : Quotient s := Quotient.mk'' i
    let j := e q
    have hq : e.symm j = q := e.symm_apply_apply q
    have hout : (e.symm j).out ≈ i := by
      apply Quotient.exact
      rw [hq, Quotient.out_eq]
    obtain ⟨houtIso⟩ := hout
    exact ⟨j, ⟨hMi.trans houtIso.symm⟩⟩

variable (S : IndecomposableModuleSkeleton k A)

/-- The full category on the chosen finite indecomposable skeleton. -/
abbrev Category :=
  InducedCategory (ModuleCat.{v} A) S.obj

noncomputable instance categoryFintype : Fintype S.Category := by
  change Fintype (Fin S.n)
  infer_instance

/-- The fully faithful inclusion of the finite indecomposable skeleton in the
module category. -/
abbrev inclusion : S.Category ⥤ ModuleCat.{v} A :=
  inducedFunctor S.obj

instance inclusion_additive : S.inclusion.Additive :=
  by infer_instance

instance inclusion_linear : S.inclusion.Linear k :=
  by infer_instance

/-- Every skeleton object is finite-dimensional over the coefficient field. -/
theorem category_obj_finite (i : S.Category) :
    Module.Finite k (S.inclusion.obj i) :=
  S.obj_finite i

/-- Every skeleton object is indecomposable. -/
theorem category_obj_indecomposable (i : S.Category) :
    Indecomposable (S.inclusion.obj i) :=
  S.obj_indecomposable i

/-- The space of module homomorphisms between two finite-dimensional
`A`-modules is finite-dimensional over `k`. -/
theorem moduleCat_hom_finite (M N : ModuleCat.{v} A)
    [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (M ⟶ N) := by
  let f : (M ⟶ N) →ₗ[k] (M →ₗ[k] N) :=
    (LinearMap.restrictScalarsₗ k A M N k).comp
      ModuleCat.homLinearEquiv.toLinearMap
  exact Module.Finite.of_injective f
    ((LinearMap.restrictScalars_injective k).comp
      ModuleCat.homLinearEquiv.injective)

noncomputable instance categoryHomFinite (i j : S.Category) :
    Module.Finite k (i ⟶ j) := by
  letI : Module.Finite k (S.obj i) := S.obj_finite i
  letI : Module.Finite k (S.obj j) := S.obj_finite j
  exact (moduleCat_hom_finite (k := k) (A := A) (S.obj i) (S.obj j)).equiv
    InducedCategory.homLinearEquiv.symm

/-- Isomorphic objects of the chosen skeleton have equal indices. -/
theorem category_eq_of_iso {i j : S.Category} (h : Nonempty (i ≅ j)) :
    i = j := by
  apply S.eq_of_iso
  exact h.map (fun e ↦ S.inclusion.mapIso e)

/-- One copy of every indecomposable in the finite skeleton, viewed in the
additive matrix envelope. -/
def additiveGenerator : Mat_ S.Category where
  ι := Fin S.n
  X := fun i ↦ i

/-- The Auslander algebra attached to the chosen finite indecomposable
skeleton.  Its elements are matrices of maps between all indecomposable
representatives. -/
abbrev AuslanderAlgebra := CategoryTheory.End S.additiveGenerator

noncomputable instance auslanderAlgebraFinite :
    Module.Finite k S.AuslanderAlgebra := by
  letI (i j : S.Category) : Module.Finite k (i ⟶ j) :=
    categoryHomFinite S i j
  change Module.Finite k
    (∀ i j : S.additiveGenerator.ι,
      S.additiveGenerator.X i ⟶ S.additiveGenerator.X j)
  exact Module.Finite.pi

end IndecomposableModuleSkeleton

end LargeIndecomposable
