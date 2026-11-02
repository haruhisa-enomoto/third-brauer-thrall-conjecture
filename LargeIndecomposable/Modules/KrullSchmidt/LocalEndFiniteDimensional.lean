module

public import LargeIndecomposable.Foundations.Ring.LocalRingJacobson
public import LargeIndecomposable.Foundations.CategoryTheory.IndecomposableOfLocalEnd
public import LargeIndecomposable.Foundations.CategoryTheory.LinearMat
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFinite
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

/-!
# Local endomorphism rings of finite-dimensional indecomposable modules

Fitting decomposition shows that every endomorphism of a finite-dimensional
indecomposable module is either invertible or nilpotent.  Consequently its
endomorphism ring is local.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace LargeIndecomposable

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]


/-- If `End(X)` is nontrivial and `End(Y)` is local, then a pair of maps
`X ⟶ Y ⟶ X` with invertible composite exhibits `X` and `Y` as isomorphic.
This is the categorical form of the fact that a nonzero retract of an object
with local endomorphism ring is the whole object. -/
theorem nonempty_iso_of_isUnit_comp
    {C : Type*} [Category C] [Preadditive C] {X Y : C}
    [Nontrivial (CategoryTheory.End X)] [IsLocalRing (CategoryTheory.End Y)]
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : IsUnit (CategoryTheory.End.of (f ≫ g))) :
    Nonempty (X ≅ Y) := by
  letI : IsIso (f ≫ g) := (CategoryTheory.isUnit_iff_isIso _).mp hfg
  let r : Y ⟶ X := g ≫ inv (f ≫ g)
  have hfr : f ≫ r = 𝟙 X := by
    dsimp [r]
    rw [← Category.assoc, IsIso.hom_inv_id]
  let e : CategoryTheory.End Y := r ≫ f
  have heidem_mul : e * e = e := by
    apply CategoryTheory.End.ext
    change (r ≫ f) ≫ (r ≫ f) = r ≫ f
    rw [Category.assoc, ← Category.assoc f r f, hfr,
      Category.id_comp]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (a := e) (b := 1 - e) (add_sub_cancel e 1) with he | h_one_sub
  · have he_one : e = 1 := by
      apply he.mul_left_cancel
      simp [heidem_mul]
    exact ⟨{
      hom := f
      inv := r
      hom_inv_id := hfr
      inv_hom_id := by
        have h := congrArg CategoryTheory.End.asHom he_one
        simpa [e] using h }⟩
  · have he_zero : e = 0 := by
      apply h_one_sub.mul_left_cancel
      rw [sub_mul, one_mul, heidem_mul, sub_self, mul_zero]
    have he_zero_hom : r ≫ f = 0 := by
      have h := congrArg CategoryTheory.End.asHom he_zero
      change r ≫ f = 0 at h
      exact h
    have hX_zero : (𝟙 X : X ⟶ X) = 0 := by
      calc
        𝟙 X = f ≫ r := hfr.symm
        _ = (f ≫ r) ≫ (f ≫ r) := by simp [hfr]
        _ = f ≫ ((r ≫ f) ≫ r) := by
          rw [Category.assoc, ← Category.assoc r f r]
        _ = 0 := by simp [he_zero_hom]
    have hEnd_zero : (1 : CategoryTheory.End X) = 0 := by
      change (𝟙 X : X ⟶ X) = 0
      exact hX_zero
    exact False.elim ((one_ne_zero : (1 : CategoryTheory.End X) ≠ 0) hEnd_zero)

/-- A finite-dimensional indecomposable module has the Fitting alternative:
each endomorphism is invertible or nilpotent. -/
theorem isUnit_or_isNilpotent_of_finite_indecomposable
    [Module.Finite k A] (M : ModuleCat.{v} A) [Module.Finite k M]
    (hM : Indecomposable M) (f : CategoryTheory.End M) :
    IsUnit f ∨ IsNilpotent f := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  letI : Module.Finite A M :=
    Module.Finite.of_restrictScalars_finite k A M
  letI : IsArtinian A M := inferInstance
  letI : IsNoetherian A M := inferInstance
  let φ : Module.End A M := f.hom
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    φ.eventually_isCompl_ker_pow_range_pow
  let n := N + 1
  have hn : N ≤ n := Nat.le_succ N
  have hcompl : IsCompl (LinearMap.ker (φ ^ n))
      (LinearMap.range (φ ^ n)) := hN n hn
  let K : ModuleCat.{v} A := ModuleCat.of A (LinearMap.ker (φ ^ n))
  let R : ModuleCat.{v} A := ModuleCat.of A (LinearMap.range (φ ^ n))
  let eProd : ModuleCat.of A
      (LinearMap.ker (φ ^ n) × LinearMap.range (φ ^ n)) ≅ M :=
    (Submodule.prodEquivOfIsCompl _ _ hcompl).toModuleIso
  let e : M ≅ K ⊞ R :=
    eProd.symm.trans (ModuleCat.biprodIsoProd K R).symm
  rcases hM.2 K R e with hK | hR
  · left
    have hker : LinearMap.ker (φ ^ n) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      let y : K := ⟨x, hx⟩
      haveI : Subsingleton K := ModuleCat.subsingleton_of_isZero hK
      exact congrArg Subtype.val (Subsingleton.elim y 0)
    have hnpos : 0 < n := by simp [n]
    have hkerle : LinearMap.ker φ ≤ LinearMap.ker (φ ^ n) := by
      simpa using φ.iterateKer.monotone hnpos
    have hfker : LinearMap.ker φ = ⊥ :=
      le_antisymm (hkerle.trans_eq hker) bot_le
    have hfinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hfker
    have hfsurj : Function.Surjective φ :=
      (φ.restrictScalars k).surjective_of_injective hfinj
    apply (isUnit_map_iff (ModuleCat.endRingEquiv M) f).mp
    exact (Module.End.isUnit_iff φ).2 ⟨hfinj, hfsurj⟩
  · right
    have hrange : LinearMap.range (φ ^ n) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      let y : R := ⟨x, hx⟩
      haveI : Subsingleton R := ModuleCat.subsingleton_of_isZero hR
      exact congrArg Subtype.val (Subsingleton.elim y 0)
    refine ⟨n, ?_⟩
    apply (ModuleCat.endRingEquiv M).injective
    rw [map_pow, map_zero]
    exact LinearMap.range_eq_bot.mp hrange

/-- The categorical endomorphism ring of a finite-dimensional indecomposable
module is local. -/
theorem moduleCat_end_isLocalRing [Module.Finite k A]
    (M : ModuleCat.{v} A) [Module.Finite k M] (hM : Indecomposable M) :
    IsLocalRing (CategoryTheory.End M) := by
  have hnsub : ¬ Subsingleton M :=
    (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1 hM.1
  letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hnsub
  letI : Nontrivial (CategoryTheory.End M) :=
    (ModuleCat.endRingEquiv M).symm.injective.nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  rcases isUnit_or_isNilpotent_of_finite_indecomposable
    (k := k) (A := A) M hM f with hf | hf
  · exact Or.inl hf
  · exact Or.inr hf.isUnit_one_sub

end LargeIndecomposable
