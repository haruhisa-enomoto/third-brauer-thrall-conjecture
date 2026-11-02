module

public import LargeIndecomposable.RayCategories.Linearization.LinMul

/-!
# Twisted multiplicative bases

A twisted multiplicative basis of a `k`-algebra `A` over a finite ray category
`P` is a family `elt f ∈ A` of the morphisms of `P`, zero exactly on zero
morphisms, whose nonzero members form a basis, with
`elt g * elt f = tw f g • elt (f ≫ g)` for normalized scalars `tw f g ∈ kˣ`,
`elt g * elt f = 0` for non-composable `f`, `g`, and `∑ₓ elt (𝟙 x) = 1`
(Gabriel–Roiter 13.9: the twisted linearizations `k^f(P)`). The linearization
`k(P)` has one with `tw = 1` (`RayQuiver.linMulBasis`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayQuiver

variable (k : Type*) [Field k] (P : Type) [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] (A : Type*) [Ring A] [Algebra k A]

/-- A twisted multiplicative basis of `A` over `P`. -/
structure MulBasis where
  elt : ∀ {x y : P}, (x ⟶ y) → A
  tw : ∀ {x y z : P}, (x ⟶ y) → (y ⟶ z) → kˣ
  elt_zero : ∀ {x y : P}, elt (0 : x ⟶ y) = 0
  elt_mul : ∀ {x y z : P} (f : x ⟶ y) (g : y ⟶ z), elt g * elt f = (tw f g : k) • elt (f ≫ g)
  elt_mul_ne : ∀ {x y y' z : P} (f : x ⟶ y) (g : y' ⟶ z), y ≠ y' → elt g * elt f = 0
  sum_id : ∑ x : P, elt (𝟙 x) = 1
  tw_id_left : ∀ {x y : P} (f : x ⟶ y), tw (𝟙 x) f = 1
  tw_id_right : ∀ {x y : P} (f : x ⟶ y), tw f (𝟙 y) = 1
  linearIndependent : LinearIndependent k fun μ : NZ P ↦ elt μ.2.2.1
  span : Submodule.span k (Set.range fun μ : NZ P ↦ elt μ.2.2.1) = ⊤

namespace MulBasis

variable {k P A} (B : MulBasis k P A)

/-- The basis of nonzero morphisms. -/
def basis : Module.Basis (NZ P) k A := Module.Basis.mk B.linearIndependent B.span.ge

lemma basis_apply (μ : NZ P) : B.basis μ = B.elt μ.2.2.1 := Module.Basis.mk_apply _ _ _

lemma id_mul {x y : P} (f : x ⟶ y) : B.elt (𝟙 y) * B.elt f = B.elt f := by
  rw [B.elt_mul, B.tw_id_right, Units.val_one, one_smul, Category.comp_id]

lemma mul_id {x y : P} (f : x ⟶ y) : B.elt f * B.elt (𝟙 x) = B.elt f := by
  rw [B.elt_mul, B.tw_id_left, Units.val_one, one_smul, Category.id_comp]

/-- Two `k`-linear maps out of `A` agreeing on the basis elements agree. -/
lemma linMap_ext {V : Type*} [AddCommMonoid V] [Module k V] {φ ψ : A →ₗ[k] V}
    (h : ∀ {s t : P} (ρ : s ⟶ t), φ (B.elt ρ) = ψ (B.elt ρ)) : φ = ψ :=
  B.basis.ext fun μ ↦ by rw [basis_apply]; exact h _

end MulBasis

/-- The untwisted multiplicative basis of `k(P)`. -/
def linMulBasis : MulBasis k P (Linearization P k) where
  elt f := morElt k f
  tw _ _ := 1
  elt_zero := morElt_zero k
  elt_mul f g := by rw [morElt_mul, Units.val_one, one_smul]
  elt_mul_ne f g h := morElt_mul_ne k f g h
  sum_id := sum_morElt_id k
  tw_id_left _ := rfl
  tw_id_right _ := rfl
  linearIndependent := by
    have := (linBasis (P := P) k).linearIndependent
    convert this using 1
    funext μ
    rw [linBasis_apply, rayElt_eq_morElt]
  span := by
    have := (linBasis (P := P) k).span_eq
    convert this using 2
    ext a
    simp only [Set.mem_range]
    refine ⟨fun ⟨μ, hμ⟩ ↦ ⟨μ, ?_⟩, fun ⟨μ, hμ⟩ ↦ ⟨μ, ?_⟩⟩
    · rw [linBasis_apply, rayElt_eq_morElt]; exact hμ
    · rw [← hμ, linBasis_apply, rayElt_eq_morElt]


/-! ### Rescaling -/

end RayQuiver

end LargeIndecomposable
