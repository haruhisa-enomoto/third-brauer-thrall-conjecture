module

public import LargeIndecomposable.RepresentationType.Basic.RepresentationFinite
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.RingTheory.Finiteness.Small

@[expose] public section

/-!
# Cross-universe transport of representation-finiteness

Finite-dimensional modules can be resized through `Shrink`.  Combined with
the idempotent characterization of indecomposability, this removes the
same-universe restriction from transport of representation-finiteness across
an algebra equivalence.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v w x y

section Idempotents

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C] [IsIdempotentComplete C]

/-- In an idempotent-complete additive category, an indecomposable object's
idempotent endomorphisms are trivial. -/
theorem idempotent_eq_zero_or_id_of_indecomposable_preadditive
    {X : C} (hX : Indecomposable X) (p : X ⟶ X) (hp : p ≫ p = p) :
    p = 0 ∨ p = 𝟙 X := by
  let q : X ⟶ X := 𝟙 X - p
  have hq : q ≫ q = q := Idempotents.idem_of_id_sub_idem p hp
  obtain ⟨Y, i, e, hie, hei⟩ :=
    IsIdempotentComplete.idempotents_split X p hp
  obtain ⟨Z, j, r, hjr, hrj⟩ :=
    IsIdempotentComplete.idempotents_split X q hq
  have hip : i ≫ p = i := by
    rw [← hei, ← Category.assoc, hie, Category.id_comp]
  have hiq : i ≫ q = 0 := by
    dsimp [q]
    rw [Preadditive.comp_sub, Category.comp_id, hip, sub_self]
  have hqr : q ≫ r = r := by
    rw [← hrj, Category.assoc, hjr, Category.comp_id]
  have hir : i ≫ r = 0 := by
    calc
      i ≫ r = i ≫ (q ≫ r) := by rw [hqr]
      _ = 0 := by rw [← Category.assoc, hiq, zero_comp]
  have hjq : j ≫ q = j := by
    rw [← hrj, ← Category.assoc, hjr, Category.id_comp]
  have hjp : j ≫ p = 0 := by
    have h := hjq
    dsimp [q] at h
    rw [Preadditive.comp_sub, Category.comp_id] at h
    exact sub_eq_self.mp h
  have hje : j ≫ e = 0 := by
    have hpe : p ≫ e = e := by
      rw [← hei, Category.assoc, hie, Category.comp_id]
    calc
      j ≫ e = j ≫ (p ≫ e) := by rw [hpe]
      _ = (j ≫ p) ≫ e := (Category.assoc _ _ _).symm
      _ = 0 := by rw [hjp, zero_comp]
  let d : X ≅ Y ⊞ Z :=
    { hom := biprod.lift e r
      inv := biprod.desc i j
      hom_inv_id := by
        simp only [biprod.lift_desc]
        rw [hei, hrj]
        simp [q]
      inv_hom_id := by
        apply biprod.hom_ext'
        · apply biprod.hom_ext <;> simp [hie, hir]
        · apply biprod.hom_ext <;> simp [hjr, hje] }
  rcases hX.2 Y Z d with hY | hZ
  · left
    rw [← hei]
    rw [hY.eq_of_tgt e 0]
    simp
  · right
    have hq0 : q = 0 := by
      rw [← hrj]
      rw [hZ.eq_of_tgt r 0]
      simp
    exact (sub_eq_zero.mp hq0).symm

omit [IsIdempotentComplete C] in
/-- An object with no nontrivial idempotent endomorphism is indecomposable,
provided it is nonzero. -/
theorem indecomposable_of_idempotent_eq_zero_or_id_preadditive
    {X : C} (hX0 : ¬IsZero X)
    (hidem : ∀ (p : X ⟶ X), p ≫ p = p → p = 0 ∨ p = 𝟙 X) :
    Indecomposable X := by
  refine ⟨hX0, ?_⟩
  intro Y Z d
  let p : X ⟶ X := d.hom ≫ biprod.fst ≫ biprod.inl ≫ d.inv
  have hp : p ≫ p = p := by
    dsimp [p]
    simp
  rcases hidem p hp with hp0 | hp1
  · left
    apply (IsZero.iff_id_eq_zero Y).mpr
    calc
      𝟙 Y = (biprod.inl ≫ d.inv) ≫ p ≫ (d.hom ≫ biprod.fst) := by
        dsimp [p]
        simp
      _ = 0 := by rw [hp0]; simp
  · right
    apply (IsZero.iff_id_eq_zero Z).mpr
    calc
      𝟙 Z = (biprod.inr ≫ d.inv) ≫ p ≫ (d.hom ≫ biprod.snd) := by
        rw [hp1]
        simp
      _ = 0 := by
        dsimp [p]
        simp

end Idempotents

section CrossUniverseIndecomposable

variable {R : Type u} [Ring R]
variable {M : ModuleCat.{v} R} {N : ModuleCat.{w} R}

private theorem indecomposable_of_crossUniverse_linearEquiv
    (e : M ≃ₗ[R] N) (hN : Indecomposable N) : Indecomposable M := by
  apply indecomposable_of_idempotent_eq_zero_or_id_preadditive
  · intro hM0
    have hMs : Subsingleton M := ModuleCat.subsingleton_of_isZero hM0
    have hNs : Subsingleton N :=
      ⟨fun a b ↦ e.symm.injective (hMs.elim (e.symm a) (e.symm b))⟩
    letI : Subsingleton N := hNs
    exact hN.1 (ModuleCat.isZero_of_subsingleton N)
  · intro p hp
    let c : Module.End R M ≃+* Module.End R N :=
      LinearEquiv.conjRingEquiv e
    let q : N ⟶ N := ModuleCat.ofHom (c p.hom)
    have hp' : p.hom * p.hom = p.hom := by
      exact congrArg ModuleCat.Hom.hom hp
    have hq : q ≫ q = q := by
      apply ModuleCat.hom_ext
      change c p.hom * c p.hom = c p.hom
      rw [← map_mul, hp']
    rcases idempotent_eq_zero_or_id_of_indecomposable_preadditive hN q hq with hq0 | hq1
    · left
      apply ModuleCat.hom_ext
      have hc := congrArg ModuleCat.Hom.hom hq0
      change c p.hom = (0 : Module.End R N) at hc
      exact c.injective (hc.trans c.map_zero.symm)
    · right
      apply ModuleCat.hom_ext
      have hc := congrArg ModuleCat.Hom.hom hq1
      change c p.hom = (1 : Module.End R N) at hc
      exact c.injective (hc.trans c.map_one.symm)

/-- Indecomposability of modules is invariant under a linear equivalence even
when the module carriers live in different universes. -/
theorem indecomposable_iff_of_crossUniverse_linearEquiv (e : M ≃ₗ[R] N) :
    Indecomposable M ↔ Indecomposable N :=
  ⟨fun h ↦ indecomposable_of_crossUniverse_linearEquiv e.symm h,
    fun h ↦ indecomposable_of_crossUniverse_linearEquiv e h⟩

end CrossUniverseIndecomposable

section CrossUniverseRepresentationFinite

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {B : Type w} [Ring B] [Algebra k B]

abbrev crossUniverseModuleEquivalenceOfAlgEquiv
    (f : A ≃ₐ[k] B) :
    ModuleCat.{x} A ≌ ModuleCat.{x} B :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv

def crossUniverseModuleEquivalenceObjLinearEquiv
    (f : A ≃ₐ[k] B) (M : ModuleCat.{x} A) :
    M ≃ₗ[k] (crossUniverseModuleEquivalenceOfAlgEquiv f).functor.obj M where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    exact congrArg (fun b : A ↦ b • a) (f.symm.commutes c).symm

def shrinkModule (R : Type u) [Ring R]
    (M : ModuleCat.{x} R) [Small.{y} M] : ModuleCat.{y} R :=
  ModuleCat.of R (Shrink.{y} M)

def shrinkModuleLinearEquiv (R : Type u) [Ring R]
    (M : ModuleCat.{x} R) [Small.{y} M] :
    shrinkModule R M ≃ₗ[R] M :=
  Shrink.linearEquiv R M

private theorem shrinkModule_moduleFinite (R : Type u) [Ring R]
    {K : Type v} [Field K] [Algebra K R]
    (M : ModuleCat.{x} R) [Small.{y} M] [Module.Finite K M] :
    Module.Finite K (shrinkModule R M) := by
  exact (Module.Finite.equiv_iff
    ((shrinkModuleLinearEquiv R M).restrictScalars K)).mpr inferInstance

/-- Representation-finiteness is invariant under a cross-universe algebra
equivalence, provided the source algebra is nontrivial. -/
theorem IsRepresentationFinite.of_crossUniverse_algEquiv [Nontrivial A]
    (hA : IsRepresentationFinite k A) (f : A ≃ₐ[k] B) :
    IsRepresentationFinite k B := by
  letI : Nontrivial B := f.symm.toEquiv.nontrivial
  letI : Small.{v} k :=
    small_of_injective (algebraMap k A).injective
  letI : Small.{w} k :=
    small_of_injective (algebraMap k B).injective
  let E : ModuleCat.{v} A ≌ ModuleCat.{v} B :=
    crossUniverseModuleEquivalenceOfAlgEquiv f
  obtain ⟨n, X, hX, hcover⟩ := hA
  let T : Fin n → ModuleCat.{v} B := fun i ↦ E.functor.obj (X i)
  have hTfinite (i : Fin n) : Module.Finite k (T i) := by
    exact (Module.Finite.equiv_iff
      (crossUniverseModuleEquivalenceObjLinearEquiv f (X i))).mp (hX i).1
  let Y : Fin n → ModuleCat.{w} B := fun i ↦
    letI : Module.Finite k (T i) := hTfinite i
    letI : Small.{w} (T i) := Module.Finite.small.{w} k (T i)
    shrinkModule B (T i)
  refine ⟨n, Y, ?_, ?_⟩
  · intro i
    letI : Module.Finite k (T i) := hTfinite i
    letI : Small.{w} (T i) := Module.Finite.small.{w} k (T i)
    have hTind : Indecomposable (T i) :=
      (indecomposable_functor_obj_iff E (X i)).mpr (hX i).2
    exact
      ⟨shrinkModule_moduleFinite B (T i),
        (indecomposable_iff_of_crossUniverse_linearEquiv
          (shrinkModuleLinearEquiv B (T i))).mpr hTind⟩
  · intro M hM
    letI : Module.Finite k M := hM.1
    letI : Small.{v} M := Module.Finite.small.{v} k M
    let Mv : ModuleCat.{v} B := shrinkModule B M
    have hMvfinite : Module.Finite k Mv := shrinkModule_moduleFinite B M
    have hMvind : Indecomposable Mv :=
      (indecomposable_iff_of_crossUniverse_linearEquiv
        (shrinkModuleLinearEquiv B M)).mpr hM.2
    let N : ModuleCat.{v} A := E.inverse.obj Mv
    have hNfinite : Module.Finite k N := by
      exact (Module.Finite.equiv_iff
        (crossUniverseModuleEquivalenceObjLinearEquiv f.symm Mv)).mp hMvfinite
    have hENind : Indecomposable (E.functor.obj N) :=
      (indecomposable_iff_of_iso (E.counitIso.app Mv)).mpr hMvind
    have hNind : Indecomposable N :=
      (indecomposable_functor_obj_iff E N).mp hENind
    obtain ⟨i, ⟨eA⟩⟩ := hcover N ⟨hNfinite, hNind⟩
    let eB : Mv ≅ T i :=
      (E.counitIso.app Mv).symm.trans (E.functor.mapIso eA)
    letI : Module.Finite k (T i) := hTfinite i
    letI : Small.{w} (T i) := Module.Finite.small.{w} k (T i)
    let eFinal : M ≃ₗ[B] shrinkModule B (T i) :=
      ((shrinkModuleLinearEquiv B M).symm.trans eB.toLinearEquiv).trans
        (shrinkModuleLinearEquiv B (T i)).symm
    exact ⟨i, ⟨eFinal.toModuleIso⟩⟩

/-- Cross-universe transport can infer source nontriviality from a nontrivial
target algebra. -/
theorem IsRepresentationFinite.of_crossUniverse_algEquiv_of_nontrivial_target
    [Nontrivial B] (hA : IsRepresentationFinite k A) (f : A ≃ₐ[k] B) :
    IsRepresentationFinite k B := by
  letI : Nontrivial A := f.toEquiv.nontrivial
  exact hA.of_crossUniverse_algEquiv f

end CrossUniverseRepresentationFinite

end LargeIndecomposable
