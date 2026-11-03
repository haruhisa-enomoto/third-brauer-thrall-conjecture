module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Block matrices and cancellation

The matrix computations in the proof of Theorem 2.7. Let
`f : X ⊕ Y → X' ⊕ Y'` be an isomorphism, written through binary bicones, with
blocks `α, β, γ, δ` and inverse blocks `α', β', γ', δ'`. Then (2.5)

`α'α = 1 - β'γ`, `αα' = 1 - βγ'`,

so `α` is an isomorphism when `β'γ` and `βγ'` are nilpotent; and when `α` is
an isomorphism, the Schur complement `δ - γα⁻¹β` is an isomorphism with
inverse `δ'`. Morphisms compose diagrammatically (`f ≫ g` is `g ∘ f`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- `𝟙 - n` is an isomorphism when `n` is nilpotent. -/
lemma isIso_id_sub_of_isNilpotent {X : C} (n : X ⟶ X) (hn : IsNilpotent (show End X from n)) :
    IsIso (𝟙 X - n) := by
  have := hn.isUnit_one_sub
  exact (isUnit_iff_isIso _).1 this

omit [Preadditive C] in
/-- A morphism with an invertible composite on each side is an isomorphism. -/
lemma isIso_of_comp_isIso {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X) (h₁ : IsIso (a ≫ b))
    (h₂ : IsIso (b ≫ a)) : IsIso a := by
  have hl : (inv (b ≫ a) ≫ b) ≫ a = 𝟙 Y := by rw [Category.assoc, IsIso.inv_hom_id]
  have hr : a ≫ (b ≫ inv (a ≫ b)) = 𝟙 X := by rw [← Category.assoc, IsIso.hom_inv_id]
  refine ⟨b ≫ inv (a ≫ b), hr, ?_⟩
  calc (b ≫ inv (a ≫ b)) ≫ a = ((inv (b ≫ a) ≫ b) ≫ a) ≫ (b ≫ inv (a ≫ b)) ≫ a := by
        rw [hl, Category.id_comp]
    _ = (inv (b ≫ a) ≫ b) ≫ (a ≫ (b ≫ inv (a ≫ b))) ≫ a := by simp only [Category.assoc]
    _ = 𝟙 Y := by rw [hr, Category.id_comp, hl]

section Blocks

variable {X Y X' Y' : C} (b : BinaryBicone X Y) (b' : BinaryBicone X' Y')
  (hb : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt)
  (hb' : b'.fst ≫ b'.inl + b'.snd ≫ b'.inr = 𝟙 b'.pt) (e : b.pt ≅ b'.pt)

/-- The block `X → X'` of `e`. -/
def blockα : X ⟶ X' := b.inl ≫ e.hom ≫ b'.fst
/-- The block `Y → X'` of `e`. -/
def blockβ : Y ⟶ X' := b.inr ≫ e.hom ≫ b'.fst
/-- The block `X → Y'` of `e`. -/
def blockγ : X ⟶ Y' := b.inl ≫ e.hom ≫ b'.snd
/-- The block `Y → Y'` of `e`. -/
def blockδ : Y ⟶ Y' := b.inr ≫ e.hom ≫ b'.snd

include hb' in
lemma blockα_comp_blockα_symm :
    blockα b b' e ≫ blockα b' b e.symm = 𝟙 X - blockγ b b' e ≫ blockβ b' b e.symm := by
  rw [eq_sub_iff_add_eq]
  simp only [blockα, blockβ, blockγ, Iso.symm_hom, Category.assoc]
  rw [← Preadditive.comp_add, ← Preadditive.comp_add, ← Category.assoc b'.fst,
    ← Category.assoc b'.snd, ← Preadditive.add_comp, hb', Category.id_comp, e.hom_inv_id_assoc,
    BinaryBicone.inl_fst]

include hb in
lemma blockα_symm_comp_blockα :
    blockα b' b e.symm ≫ blockα b b' e = 𝟙 X' - blockγ b' b e.symm ≫ blockβ b b' e := by
  rw [eq_sub_iff_add_eq]
  simp only [blockα, blockβ, blockγ, Iso.symm_hom, Category.assoc]
  rw [← Preadditive.comp_add, ← Preadditive.comp_add, ← Category.assoc b.fst,
    ← Category.assoc b.snd, ← Preadditive.add_comp, hb, Category.id_comp, e.inv_hom_id_assoc,
    BinaryBicone.inl_fst]

include hb hb' in
/-- (2.5): `α` is an isomorphism when the two error terms are nilpotent. -/
theorem isIso_blockα
    (h₁ : IsNilpotent (show End X from blockγ b b' e ≫ blockβ b' b e.symm))
    (h₂ : IsNilpotent (show End X' from blockγ b' b e.symm ≫ blockβ b b' e)) :
    IsIso (blockα b b' e) := by
  refine isIso_of_comp_isIso _ (blockα b' b e.symm) ?_ ?_
  · rw [blockα_comp_blockα_symm b b' hb' e]
    exact isIso_id_sub_of_isNilpotent _ h₁
  · rw [blockα_symm_comp_blockα b b' hb e]
    exact isIso_id_sub_of_isNilpotent _ h₂

include hb hb' in
/-- The Schur complement `δ - γα⁻¹β` is an isomorphism with inverse `δ'`. -/
theorem isIso_schur [IsIso (blockα b b' e)] :
    IsIso (blockδ b b' e - blockβ b b' e ≫ inv (blockα b b' e) ≫ blockγ b b' e) := by
  -- block identities from `e ≫ e⁻¹ = 1` and `e⁻¹ ≫ e = 1`
  have hYY : blockβ b b' e ≫ blockγ b' b e.symm + blockδ b b' e ≫ blockδ b' b e.symm = 𝟙 Y := by
    simp only [blockβ, blockγ, blockδ, Iso.symm_hom, Category.assoc]
    rw [← Preadditive.comp_add, ← Preadditive.comp_add, ← Category.assoc b'.fst,
      ← Category.assoc b'.snd, ← Preadditive.add_comp, hb', Category.id_comp,
      e.hom_inv_id_assoc, BinaryBicone.inr_snd]
  have hXY : blockα b b' e ≫ blockγ b' b e.symm + blockγ b b' e ≫ blockδ b' b e.symm = 0 := by
    simp only [blockα, blockγ, blockδ, Iso.symm_hom, Category.assoc]
    rw [← Preadditive.comp_add, ← Preadditive.comp_add, ← Category.assoc b'.fst,
      ← Category.assoc b'.snd, ← Preadditive.add_comp, hb', Category.id_comp,
      e.hom_inv_id_assoc, BinaryBicone.inl_snd]
  have hY'Y' : blockβ b' b e.symm ≫ blockγ b b' e + blockδ b' b e.symm ≫ blockδ b b' e =
      𝟙 Y' := by
    simp only [blockβ, blockγ, blockδ, Iso.symm_hom, Category.assoc]
    rw [← Preadditive.comp_add, ← Preadditive.comp_add, ← Category.assoc b.fst,
      ← Category.assoc b.snd, ← Preadditive.add_comp, hb, Category.id_comp,
      e.inv_hom_id_assoc, BinaryBicone.inr_snd]
  have hY'X' : blockβ b' b e.symm ≫ blockα b b' e + blockδ b' b e.symm ≫ blockβ b b' e = 0 := by
    simp only [blockα, blockβ, blockδ, Iso.symm_hom, Category.assoc]
    rw [← Preadditive.comp_add, ← Preadditive.comp_add, ← Category.assoc b.fst,
      ← Category.assoc b.snd, ← Preadditive.add_comp, hb, Category.id_comp,
      e.inv_hom_id_assoc, BinaryBicone.inr_fst]
  refine ⟨blockδ b' b e.symm, ?_, ?_⟩
  · have h : blockγ b b' e ≫ blockδ b' b e.symm = - (blockα b b' e ≫ blockγ b' b e.symm) :=
      eq_neg_of_add_eq_zero_right hXY
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, h]
    simp only [Preadditive.comp_neg, IsIso.inv_hom_id_assoc, sub_neg_eq_add]
    rw [add_comm]; exact hYY
  · have h : blockδ b' b e.symm ≫ blockβ b b' e = - (blockβ b' b e.symm ≫ blockα b b' e) :=
      eq_neg_of_add_eq_zero_right hY'X'
    rw [Preadditive.comp_sub, ← Category.assoc, h]
    simp only [Preadditive.neg_comp, Category.assoc, IsIso.hom_inv_id_assoc, sub_neg_eq_add]
    rw [add_comm]; exact hY'Y'

end Blocks

end LargeIndecomposable
