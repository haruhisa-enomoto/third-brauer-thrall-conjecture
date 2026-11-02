module

public import LargeIndecomposable.RayCategories.Contours.ContourFunction

@[expose] public section

/-!
# Contour functions induced by path realizations

For a reversed linear realization of a quiver, declare two parallel paths
related when their values are nonzero scalar multiples.  The unique scalar
relating every such pair is a genuine contour function.  Consequently
Roiter-style contour-cohomology vanishing applies directly to the scalar
discrepancies of a path realization.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.LinearPathCategory

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {D : Type z} [CategoryTheory.Category D] [Preadditive D]
  [CategoryTheory.Linear k D]

/-- Two parallel paths are related when the first has nonzero realization and
is a nonzero scalar multiple of the second.  The second realization is then
automatically nonzero as well. -/
def nonzeroScalarMultiplePathRelation
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i)) :
    PathContourRelation Q where
  related := fun p q ↦
    pathMap F₀ F₁ p ≠ 0 ∧
      ∃ c : kˣ, pathMap F₀ F₁ p = (c : k) • pathMap F₀ F₁ q
  symm' := by
    intro i j p q h
    obtain ⟨hp, c, hc⟩ := h
    have hq : pathMap F₀ F₁ q ≠ 0 := by
      intro hq
      apply hp
      rw [hc, hq, smul_zero]
    refine ⟨hq, c⁻¹, ?_⟩
    rw [hc, smul_smul]
    simp
  trans' := by
    intro i j p q r hpq hqr
    obtain ⟨hp, c, hc⟩ := hpq
    obtain ⟨hq, d, hd⟩ := hqr
    refine ⟨hp, c * d, ?_⟩
    rw [hc, hd, smul_smul]
    rfl

/-- The right-hand path in a nonzero scalar-multiple relation also has
nonzero realization. -/
theorem pathMap_ne_zero_right_of_related
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {i j : Q} {p q : Quiver.Path i j}
    (h : (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁).related p q) :
    pathMap F₀ F₁ q ≠ 0 := by
  obtain ⟨hp, c, hc⟩ := h
  intro hq
  apply hp
  rw [hc, hq, smul_zero]

end LargeIndecomposable.LinearPathCategory
