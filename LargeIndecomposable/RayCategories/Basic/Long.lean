module

public import LargeIndecomposable.RayCategories.Basic.ResidueQuiver

/-!
# Long morphisms

A nonzero morphism `μ` is maximal if `μ ≤ ν` (that is `ν = α ≫ μ ≫ β`) with
`ν ≠ 0` forces `ν ≤ μ`; a long morphism is a maximal morphism that is not
irreducible (Bongartz, *Indecomposables live in all smaller lengths*, Section
2.1). The order is antisymmetric (`RayCat.le_antisymm`), so a nonzero morphism
factoring through a maximal `μ` is `μ` itself (`RayCat.isLongAt_of_maximal`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- An isomorphism of a ray category is an equality of objects with the identity. -/
lemma eq_eqToHom_of_isIso {x y : P} (f : x ⟶ y) [IsIso f] : ∃ h : x = y, f = eqToHom h := by
  have hxy : x = y := IsRayCategory.skeletal ⟨asIso f⟩
  subst hxy
  refine ⟨rfl, ?_⟩
  have e : 𝟙 x = f ≫ 𝟙 x ≫ inv f := by simp
  exact (IsRayCategory.eq_id_of_two_sided _ (IsRayCategory.id_ne_zero x) f (inv f) e).1

/-- Antisymmetry of the order on nonzero morphisms. -/
lemma le_antisymm {μ ν : RayMor P} (h₁ : RayMor.Le μ ν) (h₂ : RayMor.Le ν μ) (hμ : μ.2.2 ≠ 0) :
    μ = ν := by
  obtain ⟨α, β, hν⟩ := h₁
  obtain ⟨α', β', hμ'⟩ := h₂
  have hν0 : ν.2.2 ≠ 0 := fun h ↦ hμ (by rw [hμ', h, zero_comp, comp_zero])
  have e1 : μ.2.2 = (α' ≫ α) ≫ μ.2.2 ≫ (β ≫ β') := by
    conv_lhs => rw [hμ', hν]
    simp [Category.assoc]
  have e2 : ν.2.2 = (α ≫ α') ≫ ν.2.2 ≫ (β' ≫ β) := by
    conv_lhs => rw [hν, hμ']
    simp [Category.assoc]
  obtain ⟨h1, h2⟩ := IsRayCategory.eq_id_of_two_sided _ hμ _ _ e1
  obtain ⟨h3, h4⟩ := IsRayCategory.eq_id_of_two_sided _ hν0 _ _ e2
  have : IsIso α := ⟨α', h3, h1⟩
  have : IsIso β := ⟨β', h2, h4⟩
  obtain ⟨hx, rfl⟩ := eq_eqToHom_of_isIso α
  obtain ⟨hy, rfl⟩ := eq_eqToHom_of_isIso β
  obtain ⟨x, y, f⟩ := μ
  obtain ⟨x', y', g⟩ := ν
  change x' = x at hx
  change y = y' at hy
  subst hx hy
  change g = 𝟙 _ ≫ f ≫ 𝟙 _ at hν
  rw [Category.id_comp, Category.comp_id] at hν
  rw [hν]

/-- A nonzero morphism factoring through a maximal morphism is that morphism. -/
lemma isLongAt_of_maximal {a b : P} (μ : a ⟶ b) (hμ : μ ≠ 0)
    (hmax : ∀ ν : RayMor P, ν.2.2 ≠ 0 → RayMor.Le ⟨a, b, μ⟩ ν → RayMor.Le ν ⟨a, b, μ⟩)
    {x y : P} (f : x ⟶ y) (hf : f ≠ 0) (hfac : ∃ (α : x ⟶ a) (β : b ⟶ y), f = α ≫ μ ≫ β) :
    ∃ (hx : x = a) (hy : y = b), f = eqToHom hx ≫ μ ≫ eqToHom hy.symm := by
  obtain ⟨α, β, rfl⟩ := hfac
  have hle : RayMor.Le ⟨a, b, μ⟩ ⟨x, y, α ≫ μ ≫ β⟩ := ⟨α, β, rfl⟩
  have heq := le_antisymm hle (hmax _ hf hle) hμ
  obtain ⟨hax, hrest⟩ := Sigma.mk.inj heq
  subst hax
  obtain ⟨hby, hm⟩ := Sigma.mk.inj (eq_of_heq hrest)
  subst hby
  refine ⟨rfl, rfl, ?_⟩
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (eq_of_heq hm).symm

end RayCat

end LargeIndecomposable
