module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-!
# Representation-finite algebras

This file defines representation-finiteness as finiteness of the isomorphism
classes of finite-dimensional indecomposable left modules.  It also records
the categorical invariance of indecomposability and the invariance of
representation-finiteness under algebra equivalence.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v w

section Categorical

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Indecomposability is invariant under isomorphism. -/
theorem indecomposable_iff_of_iso {X Y : C} (e : X ≅ Y) :
    Indecomposable X ↔ Indecomposable Y := by
  constructor
  · rintro ⟨hX0, hX⟩
    refine ⟨?_, ?_⟩
    · intro hY0
      exact hX0 ((e.isZero_iff).2 hY0)
    · intro Z W hYW
      exact hX Z W (e.trans hYW)
  · rintro ⟨hY0, hY⟩
    refine ⟨?_, ?_⟩
    · intro hX0
      exact hY0 ((e.isZero_iff).1 hX0)
    · intro Z W hXW
      exact hY Z W (e.symm.trans hXW)

variable {D : Type w} [Category.{v} D] [Preadditive D] [HasBinaryBiproducts D]

/-- An additive equivalence preserves and reflects indecomposable objects. -/
theorem indecomposable_functor_obj_iff (E : C ≌ D) [E.functor.Additive]
    [E.inverse.Additive] (X : C) :
    Indecomposable (E.functor.obj X) ↔ Indecomposable X := by
  letI : PreservesBinaryBiproducts E.functor :=
    preservesBinaryBiproducts_of_preservesBinaryProducts E.functor
  letI : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts E.inverse
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hX0
      exact h.1 (E.functor.map_isZero hX0)
    · intro Y Z i
      let i' : E.functor.obj X ≅ E.functor.obj Y ⊞ E.functor.obj Z :=
        (E.functor.mapIso i).trans (E.functor.mapBiprod _ _)
      rcases h.2 _ _ i' with hY | hZ
      · exact Or.inl <| (E.unitIso.app Y).isZero_iff.mpr
          (E.inverse.map_isZero hY)
      · exact Or.inr <| (E.unitIso.app Z).isZero_iff.mpr
          (E.inverse.map_isZero hZ)
  · intro h
    refine ⟨?_, ?_⟩
    · intro hFX0
      exact h.1 ((E.unitIso.app X).isZero_iff.mpr
        (E.inverse.map_isZero hFX0))
    · intro Y Z i
      let i' : X ≅ E.inverse.obj Y ⊞ E.inverse.obj Z :=
        (E.unitIso.app X).trans ((E.inverse.mapIso i).trans
          (E.inverse.mapBiprod _ _))
      rcases h.2 _ _ i' with hY | hZ
      · exact Or.inl <| (E.counitIso.app Y).isZero_iff.mp
          (E.functor.map_isZero hY)
      · exact Or.inr <| (E.counitIso.app Z).isZero_iff.mp
          (E.functor.map_isZero hZ)

end Categorical

section RepresentationFinite

variable (k : Type u) [Field k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- A finite-dimensional indecomposable left module. -/
def IsFiniteIndecomposable (M : ModuleCat.{v} A) : Prop :=
  Module.Finite k M ∧ Indecomposable M

/-- There are only finitely many isomorphism classes of finite-dimensional
indecomposable left modules.  The finite family may contain repetitions. -/
def IsRepresentationFinite : Prop :=
  ∃ n : ℕ, ∃ X : Fin n → ModuleCat.{v} A,
    (∀ i, IsFiniteIndecomposable k A (X i)) ∧
      ∀ M : ModuleCat.{v} A, IsFiniteIndecomposable k A M →
        ∃ i, Nonempty (M ≅ X i)

theorem isRepresentationFinite_iff : IsRepresentationFinite k A ↔
    ∃ n : ℕ, ∃ X : Fin n → ModuleCat.{v} A,
      (∀ i, Module.Finite k (X i) ∧ Indecomposable (X i)) ∧
        ∀ M : ModuleCat.{v} A, Module.Finite k M ∧ Indecomposable M →
          ∃ i, Nonempty (M ≅ X i) :=
  Iff.rfl

/-- An infinite sequence of pairwise nonisomorphic finite-dimensional
indecomposable modules. -/
structure InfiniteFiniteIndecomposableFamily where
  module : ℕ → ModuleCat.{v} A
  finite : ∀ n, Module.Finite k (module n)
  indecomposable : ∀ n, Indecomposable (module n)
  eq_of_iso : ∀ {m n}, Nonempty (module m ≅ module n) → m = n

/-- A representation-finite algebra admits no infinite pairwise
nonisomorphic family of finite-dimensional indecomposable modules. -/
theorem IsRepresentationFinite.not_infiniteFiniteIndecomposableFamily
    (hA : IsRepresentationFinite k A) :
    IsEmpty (InfiniteFiniteIndecomposableFamily k A) :=
  ⟨fun F ↦ by
    obtain ⟨r, X, _, hcover⟩ := hA
    let index : ℕ → Fin r := fun n ↦
      Classical.choose
        (hcover (F.module n) ⟨F.finite n, F.indecomposable n⟩)
    have hindexIso (n : ℕ) :
        Nonempty (F.module n ≅ X (index n)) :=
      Classical.choose_spec
        (hcover (F.module n) ⟨F.finite n, F.indecomposable n⟩)
    obtain ⟨m, n, hmn, hindex⟩ :=
      Finite.exists_ne_map_eq_of_infinite index
    obtain ⟨em⟩ := hindexIso m
    obtain ⟨en⟩ := hindexIso n
    let eindex : X (index m) ≅ X (index n) :=
      eqToIso (congrArg X hindex)
    have hmodules : Nonempty (F.module m ≅ F.module n) :=
      ⟨em.trans (eindex.trans en.symm)⟩
    exact hmn (F.eq_of_iso hmodules)⟩

/-- Finite-dimensionality over the coefficient field is invariant under an
isomorphism of modules. -/
theorem moduleFinite_iff_of_iso {M N : ModuleCat.{v} A} (e : M ≅ N) :
    Module.Finite k M ↔ Module.Finite k N := by
  let e' : M ≃ₗ[k] N := (e.toLinearEquiv).restrictScalars k
  exact Module.Finite.equiv_iff e'

/-- The class of finite-dimensional indecomposable modules is invariant under
module isomorphism. -/
theorem isFiniteIndecomposable_iff_of_iso {M N : ModuleCat.{v} A} (e : M ≅ N) :
    IsFiniteIndecomposable k A M ↔ IsFiniteIndecomposable k A N := by
  exact and_congr (moduleFinite_iff_of_iso k A e) (indecomposable_iff_of_iso e)

variable {k A}
variable {B : Type v} [Ring B] [Algebra k B]

/-- Representation-finiteness is transported by an additive module-category
equivalence which preserves finite-dimensionality over the coefficient
field. -/
theorem IsRepresentationFinite.of_equivalence
    (hA : IsRepresentationFinite k A)
    (E : ModuleCat.{v} A ≌ ModuleCat.{v} B)
    [E.functor.Additive] [E.inverse.Additive]
    (hfinite : ∀ M : ModuleCat.{v} A,
      Module.Finite k M ↔ Module.Finite k (E.functor.obj M)) :
    IsRepresentationFinite k B := by
  obtain ⟨n, X, hX, hcover⟩ := hA
  refine ⟨n, fun i ↦ E.functor.obj (X i), ?_, ?_⟩
  · intro i
    exact ⟨(hfinite (X i)).mp (hX i).1,
      (indecomposable_functor_obj_iff E (X i)).mpr (hX i).2⟩
  · intro M hM
    have hFGMfinite : Module.Finite k
        (E.functor.obj (E.inverse.obj M)) :=
      (moduleFinite_iff_of_iso k B (E.counitIso.app M)).mpr hM.1
    have hGMfinite : Module.Finite k (E.inverse.obj M) :=
      (hfinite (E.inverse.obj M)).mpr hFGMfinite
    have hFGMind : Indecomposable
        (E.functor.obj (E.inverse.obj M)) :=
      (indecomposable_iff_of_iso (E.counitIso.app M)).mpr hM.2
    have hGMind : Indecomposable (E.inverse.obj M) :=
      (indecomposable_functor_obj_iff E (E.inverse.obj M)).mp hFGMind
    obtain ⟨i, ⟨e⟩⟩ := hcover (E.inverse.obj M) ⟨hGMfinite, hGMind⟩
    exact ⟨i, ⟨(E.counitIso.app M).symm.trans (E.functor.mapIso e)⟩⟩

/-- The equivalence of left-module categories induced by an algebra
equivalence, oriented from `A`-modules to `B`-modules. -/
abbrev moduleEquivalenceOfAlgEquiv (f : A ≃ₐ[k] B) :
    ModuleCat.{v} A ≌ ModuleCat.{v} B :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv

/-- Restriction along an algebra equivalence leaves the underlying
`k`-vector space unchanged. -/
def moduleEquivalenceOfAlgEquivObjLinearEquiv (f : A ≃ₐ[k] B)
    (M : ModuleCat.{v} A) :
    M ≃ₗ[k] (moduleEquivalenceOfAlgEquiv f).functor.obj M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    exact congrArg (fun a : A ↦ a • x) (f.symm.commutes c).symm

/-- Representation-finiteness is preserved by algebra equivalence. -/
theorem IsRepresentationFinite.of_algEquiv
    (hA : IsRepresentationFinite k A) (f : A ≃ₐ[k] B) :
    IsRepresentationFinite k B := by
  apply hA.of_equivalence (moduleEquivalenceOfAlgEquiv f)
  intro M
  exact Module.Finite.equiv_iff (moduleEquivalenceOfAlgEquivObjLinearEquiv f M)

/-- Representation-finiteness is invariant under algebra equivalence. -/
theorem IsRepresentationFinite.algEquiv_iff (f : A ≃ₐ[k] B) :
    IsRepresentationFinite k A ↔ IsRepresentationFinite k B :=
  ⟨fun h ↦ h.of_algEquiv f, fun h ↦ h.of_algEquiv f.symm⟩

end RepresentationFinite

end LargeIndecomposable
