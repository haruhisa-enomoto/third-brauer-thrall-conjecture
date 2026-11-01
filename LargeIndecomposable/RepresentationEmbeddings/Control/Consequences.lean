module

public import LargeIndecomposable.RepresentationEmbeddings.Control.Retraction
public import LargeIndecomposable.Modules.KrullSchmidt.LocalEnd

/-!
# Consequences of retractions with nilpotent kernels

If a functor `Ψ : 𝒞 ⥤ Mod A` has retractions (Definition 2.4) and every
composite of `n` maps in their kernels vanishes, then `Ψ` preserves
indecomposability and reflects isomorphism classes (Section 1.4 and the end of
the proof of Proposition 2.5). Indecomposability in `𝒞` means: the identity is
nonzero and the only idempotent endomorphisms are `0` and `1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement

universe v w u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
  {𝒞 : Type w} [Category.{v} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {Ψ : 𝒞 ⥤ ModuleCat.{u} A} (R : Retractions k Ψ)

namespace Retractions

/-- The `m`-fold composite of an endomorphism. -/
def iter {M : ModuleCat.{u} A} (e : M ⟶ M) : ℕ → (M ⟶ M)
  | 0 => 𝟙 M
  | m + 1 => iter e m ≫ e

lemma kerChain_iter {X : 𝒞} (e : Ψ.obj X ⟶ Ψ.obj X) (he : R.ρ X X e = 0) (m : ℕ) :
    R.KerChain m (iter e m) := by
  induction m with
  | zero => exact KerChain.nil X
  | succ m ih => exact KerChain.cons ih he

lemma iter_idem {M : ModuleCat.{u} A} (e : M ⟶ M) (he : e ≫ e = e) (m : ℕ) (hm : 1 ≤ m) :
    iter e m = e := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp [iter]
    · rw [iter, ih h, he]

/-- An idempotent in the kernel of the retractions vanishes. -/
lemma eq_zero_of_idem {n : ℕ} (hn : R.NilpotentBound n) {X : 𝒞} (e : Ψ.obj X ⟶ Ψ.obj X)
    (he : e ≫ e = e) (h0 : R.ρ X X e = 0) : e = 0 := by
  have := hn _ (R.kerChain_iter e h0 n)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have h1 : (𝟙 (Ψ.obj X) : Ψ.obj X ⟶ Ψ.obj X) = 0 := this
    rw [← Category.id_comp e, h1, Limits.zero_comp]
  · rwa [iter_idem e he n hpos] at this

/-- Retractions with nilpotent kernels preserve indecomposability. -/
theorem isIndecomposable {n : ℕ} (hn : R.NilpotentBound n) {X : 𝒞} (hX0 : (𝟙 X : X ⟶ X) ≠ 0)
    (hX : ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X) : IsIndecomposable A (Ψ.obj X) := by
  rw [isIndecomposable_iff]
  have hid : (𝟙 (Ψ.obj X) : Ψ.obj X ⟶ Ψ.obj X) ≠ 0 := fun h ↦ hX0 (by
    rw [← R.ρ_id, h, map_zero])
  refine ⟨?_, fun f hf ↦ ?_⟩
  · by_contra hn'
    rw [not_nontrivial_iff_subsingleton] at hn'
    exact hid (by ext x; exact Subsingleton.elim _ _)
  let e : Ψ.obj X ⟶ Ψ.obj X := ModuleCat.ofHom f
  have he : e ≫ e = e := by ext x; exact congrArg (fun g : Module.End A (Ψ.obj X) ↦ g x) hf.eq
  have hρ : R.ρ X X e ≫ R.ρ X X e = R.ρ X X e := by rw [← R.map_comp, he]
  rcases hX _ hρ with h0 | h1
  · left
    have := R.eq_zero_of_idem hn e he h0
    exact congrArg ModuleCat.Hom.hom this
  · right
    have h1' : R.ρ X X (𝟙 _ - e) = 0 := by rw [map_sub, R.ρ_id, h1, sub_self]
    have hidem : (𝟙 _ - e) ≫ (𝟙 _ - e) = 𝟙 _ - e := by
      simp [Preadditive.sub_comp, Preadditive.comp_sub, he]
    have := R.eq_zero_of_idem hn _ hidem h1'
    have : e = 𝟙 _ := (sub_eq_zero.1 this).symm
    exact congrArg ModuleCat.Hom.hom this

include R in
/-- Retractions reflect isomorphism classes. -/
theorem reflects_iso {X Y : 𝒞} (e : Ψ.obj X ≅ Ψ.obj Y) : Nonempty (X ≅ Y) :=
  ⟨{ hom := R.ρ X Y e.hom
     inv := R.ρ Y X e.inv
     hom_inv_id := by rw [← R.map_comp, e.hom_inv_id, R.ρ_id]
     inv_hom_id := by rw [← R.map_comp, e.inv_hom_id, R.ρ_id] }⟩

end Retractions

end LargeIndecomposable
