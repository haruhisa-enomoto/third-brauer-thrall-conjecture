module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift
public import Mathlib.Combinatorics.Quiver.Path.Weight

@[expose] public section

/-!
# Rescaling free linear path realizations

Rescaling each arrow representative multiplies the realization of a path by
the product of its arrow scalars.  This is the algebraic content of the final
contour-function correction in multiplicative-basis standardness proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.LinearPathCategory

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {C : Type z} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]

/-- Multiply every reversed arrow representative by its assigned scalar. -/
def rescaleArrow (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (s : ∀ {i j : Q}, (i ⟶ j) → k)
    {i j : Q} (a : i ⟶ j) : F₀ j ⟶ F₀ i :=
  s a • F₁ a

/-- A path evaluated with rescaled arrows is its original value multiplied by
the product of the arrow scalars along that path. -/
theorem pathMap_rescaleArrow (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (s : ∀ {i j : Q}, (i ⟶ j) → k)
    {i j : Q} (p : Quiver.Path i j) :
    pathMap F₀ (rescaleArrow F₀ F₁ s) p =
      p.weight s • pathMap F₀ F₁ p := by
  induction p with
  | nil => simp
  | cons p a ih =>
      simp only [pathMap_cons, rescaleArrow, ih,
        CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul,
        Quiver.Path.weight_cons, smul_smul]

/-- The corresponding free linear functors satisfy the same formula on every
path-basis morphism. -/
theorem lift_rescaleArrow_map_pathHom (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (s : ∀ {i j : Q}, (i ⟶ j) → k)
    {i j : Q} (p : Quiver.Path i j) :
    (lift (k := k) F₀ (rescaleArrow F₀ F₁ s)).map
        (pathHom p : obj k Q j ⟶ obj k Q i) =
      p.weight s •
        (lift (k := k) F₀ F₁).map
          (pathHom p : obj k Q j ⟶ obj k Q i) := by
  rw [lift_map_pathHom, lift_map_pathHom, pathMap_rescaleArrow]
  rfl

/-- A scalar contour discrepancy disappears after arrow rescaling whenever
the two path weights satisfy the displayed coboundary equation. -/
theorem pathMap_rescaleArrow_eq_of_contour
    (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (s : ∀ {i j : Q}, (i ⟶ j) → k)
    {i j : Q} (p q : Quiver.Path i j) (c : k)
    (hcontour : pathMap F₀ F₁ p = c • pathMap F₀ F₁ q)
    (hweight : p.weight s * c = q.weight s) :
    pathMap F₀ (rescaleArrow F₀ F₁ s) p =
      pathMap F₀ (rescaleArrow F₀ F₁ s) q := by
  rw [pathMap_rescaleArrow, pathMap_rescaleArrow, hcontour, smul_smul,
    hweight]

/-- The same contour correction stated for path-basis morphisms under the two
free linear realization functors. -/
theorem lift_rescaleArrow_map_pathHom_eq_of_contour
    (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (s : ∀ {i j : Q}, (i ⟶ j) → k)
    {i j : Q} (p q : Quiver.Path i j) (c : k)
    (hcontour :
      (lift (k := k) F₀ F₁).map
          (pathHom p : obj k Q j ⟶ obj k Q i) =
        c • (lift (k := k) F₀ F₁).map
          (pathHom q : obj k Q j ⟶ obj k Q i))
    (hweight : p.weight s * c = q.weight s) :
    (lift (k := k) F₀ (rescaleArrow F₀ F₁ s)).map
        (pathHom p : obj k Q j ⟶ obj k Q i) =
      (lift (k := k) F₀ (rescaleArrow F₀ F₁ s)).map
        (pathHom q : obj k Q j ⟶ obj k Q i) := by
  simp only [lift_map_pathHom] at hcontour ⊢
  exact pathMap_rescaleArrow_eq_of_contour F₀ F₁ s p q c
    hcontour hweight

end LargeIndecomposable.LinearPathCategory
