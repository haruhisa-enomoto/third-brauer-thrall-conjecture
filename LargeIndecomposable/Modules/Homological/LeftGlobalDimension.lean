module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Morita.Basic

@[expose] public section

/-!
# Left global dimension

This file records the algebra-wide projective-dimension bound used to
terminate all simple resolutions at one common homological length.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u₀ u v w

/-- A fully faithful exact functor which preserves projective objects reflects
finite projective-dimension bounds. -/
theorem hasProjectiveDimensionLT_of_functor_obj
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {D : Type u} [Category.{v} D] [Abelian D] [EnoughProjectives D]
    [HasExt.{w} C] [HasExt.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F.Full] [F.Faithful]
    [F.PreservesProjectiveObjects]
    {X : C} (n : ℕ) (h : HasProjectiveDimensionLT (F.obj X) n) :
    HasProjectiveDimensionLT X n := by
  rw [hasProjectiveDimensionLT_iff] at h ⊢
  intro i hi Y a
  apply (F.mapExt_bijective_of_preservesProjectiveObjects X Y i).injective
  simpa using h i hi (F.mapExtAddHom X Y i a)

/-- A ring has left global dimension at most `n` in a fixed universe when
every left module in that universe has projective dimension at most `n`. -/
def HasLeftGlobalDimensionLE (A : Type u) [Ring A] (n : ℕ) : Prop :=
  ∀ M : ModuleCat.{u} A, HasProjectiveDimensionLE M n

/-- A ring has finite left global dimension when it has some uniform finite
projective-dimension bound for all left modules. -/
def HasFiniteLeftGlobalDimension (A : Type u) [Ring A] : Prop :=
  ∃ n : ℕ, HasLeftGlobalDimensionLE A n

/-- An algebra-wide left-global-dimension bound applies to every specified
left module. -/
theorem hasProjectiveDimensionLE_of_leftGlobalDimensionLE
    {A : Type u} [Ring A] {n : ℕ}
    (hA : HasLeftGlobalDimensionLE A n) (M : ModuleCat.{u} A) :
    HasProjectiveDimensionLE M n :=
  hA M

/-- A left-global-dimension bound remains valid after increasing the
numerical bound. -/
theorem HasLeftGlobalDimensionLE.of_le
    {A : Type u} [Ring A] {n m : ℕ}
    (hA : HasLeftGlobalDimensionLE A n) (hnm : n ≤ m) :
    HasLeftGlobalDimensionLE A m := by
  intro M
  letI : HasProjectiveDimensionLE M n := hA M
  exact hasProjectiveDimensionLT_of_ge M (n + 1) (m + 1) (Nat.add_le_add_right hnm 1)

/-- A Morita equivalence transports a left-global-dimension bound without
changing its numerical value. -/
theorem HasLeftGlobalDimensionLE.of_moritaEquivalence
    {R : Type u₀} [CommSemiring R]
    {A B : Type u} [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    {n : ℕ} (e : MoritaEquivalence R A B)
    (hA : HasLeftGlobalDimensionLE A n) :
    HasLeftGlobalDimensionLE B n := by
  letI : e.eqv.inverse.Linear R := e.eqv.inverseLinear R
  intro M
  apply hasProjectiveDimensionLT_of_functor_obj e.eqv.inverse (n + 1)
  exact hA (e.eqv.inverse.obj M)

/-- Left-global-dimension bounds are Morita invariant. -/
theorem HasLeftGlobalDimensionLE.moritaEquivalence_iff
    {R : Type u₀} [CommSemiring R]
    {A B : Type u} [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    {n : ℕ} (e : MoritaEquivalence R A B) :
    HasLeftGlobalDimensionLE A n ↔ HasLeftGlobalDimensionLE B n :=
  ⟨fun h ↦ h.of_moritaEquivalence e,
    fun h ↦ h.of_moritaEquivalence (e.symm R)⟩

/-- Finite left global dimension is transported by a Morita equivalence. -/
theorem HasFiniteLeftGlobalDimension.of_moritaEquivalence
    {R : Type u₀} [CommSemiring R]
    {A B : Type u} [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B)
    (hA : HasFiniteLeftGlobalDimension A) :
    HasFiniteLeftGlobalDimension B := by
  obtain ⟨n, hn⟩ := hA
  exact ⟨n, hn.of_moritaEquivalence e⟩

/-- Finite left global dimension is Morita invariant. -/
theorem HasFiniteLeftGlobalDimension.moritaEquivalence_iff
    {R : Type u₀} [CommSemiring R]
    {A B : Type u} [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B) :
    HasFiniteLeftGlobalDimension A ↔ HasFiniteLeftGlobalDimension B :=
  ⟨fun h ↦ h.of_moritaEquivalence e,
    fun h ↦ h.of_moritaEquivalence (e.symm R)⟩

/-- Finite left global dimension supplies one common projective-dimension
bound for every finite family of modules. -/
theorem exists_common_projectiveDimensionLE
    {A : Type u} [Ring A] (hA : HasFiniteLeftGlobalDimension A)
    {ι : Type*} (M : ι → ModuleCat.{u} A) :
    ∃ n : ℕ, ∀ i, HasProjectiveDimensionLE (M i) n := by
  obtain ⟨n, hn⟩ := hA
  exact ⟨n, fun i ↦ hn (M i)⟩

end LargeIndecomposable
