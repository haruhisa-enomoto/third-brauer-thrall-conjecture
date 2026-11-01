module

public import LargeIndecomposable.Statement
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Indecomposable modules and fully faithful functors

`isIndecomposable_iff`: a module is indecomposable in the sense of
`Statement.IsIndecomposable` (no decomposition into two nonzero submodules)
if and only if it is nonzero and its only idempotent endomorphisms are `0`
and `1`. Consequently fully faithful functors between module categories that
preserve zero morphisms preserve and reflect indecomposability
(`isIndecomposable_map_iff`), and representation-finiteness can be pulled back
along them (`exists_list_of_isRepresentationFinite`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

namespace Reduction

variable {R : Type u} [Ring R]

theorem isZero_iff_not_nontrivial (M : ModuleCat.{u} R) : IsZero M ↔ ¬ Nontrivial M := by
  rw [not_nontrivial_iff_subsingleton]
  exact ⟨ModuleCat.subsingleton_of_isZero, fun _ ↦ ModuleCat.isZero_of_subsingleton M⟩

/-- Indecomposability through idempotent endomorphisms. -/
theorem isIndecomposable_iff (M : ModuleCat.{u} R) :
    IsIndecomposable R M ↔ ¬ IsZero M ∧ ∀ f : M ⟶ M, f ≫ f = f → f = 0 ∨ f = 𝟙 M := by
  rw [isZero_iff_not_nontrivial, not_not]
  refine ⟨fun ⟨hnt, h⟩ ↦ ⟨hnt, fun f hf ↦ ?_⟩, fun ⟨hnt, h⟩ ↦ ⟨hnt, fun N N' hNN' ↦ ?_⟩⟩
  · have hφ : IsIdempotentElem f.hom := by
      change f.hom.comp f.hom = f.hom
      rw [← ModuleCat.hom_comp, hf]
    rcases h _ _ (LinearMap.IsIdempotentElem.isCompl hφ) with h0 | h1
    · left
      ext x
      have : f.hom x ∈ LinearMap.range f.hom := LinearMap.mem_range_self _ x
      rw [h0] at this
      simpa using this
    · right
      ext x
      have hinj : Function.Injective f.hom := LinearMap.ker_eq_bot.mp h1
      apply hinj
      change (f.hom * f.hom) x = f.hom x
      rw [hφ.eq]
  · let p : M →ₗ[R] M := N.subtype ∘ₗ Submodule.projectionOnto N N' hNN'
    have hp : ∀ x : N, p x = x := fun x ↦ by
      simp [p, Submodule.projectionOnto_apply_left]
    have hp' : ∀ x : N', p x = 0 := fun x ↦ by
      simp [p, Submodule.projectionOnto_apply_right]
    have hpp : ∀ x, p (p x) = p x := fun x ↦ hp ⟨_, (Submodule.projectionOnto N N' hNN' x).2⟩
    rcases h (ModuleCat.ofHom p) (by ext x; exact hpp x) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : p x = 0 := by
        have := congrArg (fun g ↦ g.hom x) h0
        simpa using this
      rw [hp ⟨x, hx⟩] at this
      simpa using this
    · right
      rw [eq_bot_iff]
      intro x hx
      have : p x = x := by
        have := congrArg (fun g ↦ g.hom x) h1
        simpa using this
      rw [hp' ⟨x, hx⟩] at this
      simpa using this.symm

variable {S : Type u} [Ring S]

/-- Fully faithful functors preserving zero morphisms preserve and reflect
indecomposability. -/
theorem isIndecomposable_map_iff (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Full] [F.Faithful]
    [F.PreservesZeroMorphisms] (M : ModuleCat.{u} R) :
    IsIndecomposable S (F.obj M) ↔ IsIndecomposable R M := by
  rw [isIndecomposable_iff, isIndecomposable_iff, IsZero.iff_id_eq_zero,
    IsZero.iff_id_eq_zero, ← F.map_id, ← F.map_zero, F.map_injective.eq_iff]
  refine and_congr Iff.rfl ⟨fun h f hf ↦ ?_, fun h g hg ↦ ?_⟩
  · rcases h (F.map f) (by rw [← F.map_comp, hf]) with h0 | h1
    · left; apply F.map_injective; rw [h0, F.map_zero]
    · right; apply F.map_injective; rw [h1, F.map_id]
  · rcases h (F.preimage g) (F.map_injective (by simp [hg])) with h0 | h1
    · left; rw [← F.map_preimage g, h0, F.map_zero]
    · right; rw [← F.map_preimage g, h1, F.map_id]

/-- Representation-finiteness of `R` gives finitely many objects of `Mod S`
covering the images of finitely generated indecomposable `R`-modules under a
functor `F`. -/
theorem exists_list_of_isRepresentationFinite (hR : IsRepresentationFinite R)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) :
    ∃ (n : ℕ) (X : Fin n → ModuleCat.{u} S), ∀ (N : ModuleCat.{u} R) [Module.Finite R N],
      IsIndecomposable R N → ∃ i, Nonempty (F.obj N ≅ X i) := by
  obtain ⟨n, Y, hY⟩ := hR
  refine ⟨n, fun i ↦ F.obj (Y i), fun N _ hN ↦ ?_⟩
  obtain ⟨i, ⟨φ⟩⟩ := hY N hN
  exact ⟨i, ⟨F.mapIso φ.toModuleIso⟩⟩

/-- A ring is representation-finite once finitely many modules cover all
finitely generated indecomposable modules up to isomorphism. -/
theorem isRepresentationFinite_of_cover (n : ℕ) (X : Fin n → ModuleCat.{u} S)
    (h : ∀ (M : ModuleCat.{u} S) [Module.Finite S M], IsIndecomposable S M →
      ∃ i, Nonempty (M ≅ X i)) :
    IsRepresentationFinite S := by
  refine ⟨n, X, fun M _ _ _ hM ↦ ?_⟩
  obtain ⟨i, ⟨φ⟩⟩ := h (ModuleCat.of S M) hM
  exact ⟨i, ⟨φ.toLinearEquiv⟩⟩

/-- Indecomposability is invariant under isomorphism. -/
theorem isIndecomposable_of_iso {M N : ModuleCat.{u} R} (i : M ≅ N) (hM : IsIndecomposable R M) :
    IsIndecomposable R N := by
  rw [isIndecomposable_iff] at hM ⊢
  refine ⟨fun hN ↦ hM.1 (hN.of_iso i), fun f hf ↦ ?_⟩
  rcases hM.2 (i.hom ≫ f ≫ i.inv) (by simp [reassoc_of% hf]) with h0 | h1
  · left
    have : i.inv ≫ (i.hom ≫ f ≫ i.inv) ≫ i.hom = f := by simp
    rw [← this, h0]; simp
  · right
    have : i.inv ≫ (i.hom ≫ f ≫ i.inv) ≫ i.hom = f := by simp
    rw [← this, h1]; simp

/-- Representation-finiteness pulled back along two fully faithful functors
whose images cover the finitely generated indecomposable modules. -/
theorem isRepresentationFinite_of_two {S₁ S₂ : Type u} [Ring S₁] [Ring S₂]
    (h₁ : IsRepresentationFinite S₁) (h₂ : IsRepresentationFinite S₂)
    (F₁ : ModuleCat.{u} S₁ ⥤ ModuleCat.{u} S) (F₂ : ModuleCat.{u} S₂ ⥤ ModuleCat.{u} S)
    [F₁.Full] [F₁.Faithful] [F₁.PreservesZeroMorphisms]
    [F₂.Full] [F₂.Faithful] [F₂.PreservesZeroMorphisms]
    (h : ∀ (M : ModuleCat.{u} S) [Module.Finite S M], IsIndecomposable S M →
      (∃ (N : ModuleCat.{u} S₁) (_ : Module.Finite S₁ N), Nonempty (F₁.obj N ≅ M)) ∨
      (∃ (N : ModuleCat.{u} S₂) (_ : Module.Finite S₂ N), Nonempty (F₂.obj N ≅ M))) :
    IsRepresentationFinite S := by
  obtain ⟨n₁, X₁, hX₁⟩ := exists_list_of_isRepresentationFinite h₁ F₁
  obtain ⟨n₂, X₂, hX₂⟩ := exists_list_of_isRepresentationFinite h₂ F₂
  refine isRepresentationFinite_of_cover (n₁ + n₂) (Fin.append X₁ X₂) fun M _ hM ↦ ?_
  rcases h M hM with ⟨N, _, ⟨i⟩⟩ | ⟨N, _, ⟨i⟩⟩
  · have hN : IsIndecomposable S₁ N :=
      (isIndecomposable_map_iff F₁ N).mp (isIndecomposable_of_iso i.symm hM)
    obtain ⟨j, ⟨φ⟩⟩ := hX₁ N hN
    exact ⟨Fin.castAdd n₂ j, ⟨i.symm ≪≫ φ ≪≫ eqToIso (Fin.append_left X₁ X₂ j).symm⟩⟩
  · have hN : IsIndecomposable S₂ N :=
      (isIndecomposable_map_iff F₂ N).mp (isIndecomposable_of_iso i.symm hM)
    obtain ⟨j, ⟨φ⟩⟩ := hX₂ N hN
    exact ⟨Fin.natAdd n₁ j, ⟨i.symm ≪≫ φ ≪≫ eqToIso (Fin.append_right X₁ X₂ j).symm⟩⟩

end Reduction

end LargeIndecomposable
