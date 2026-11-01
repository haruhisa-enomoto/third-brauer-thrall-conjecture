module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift
public import LargeIndecomposable.Quivers.Paths.LoopPower

@[expose] public section

/-!
# Literal powers of closed quiver paths

BGRS writes powers of a selected closed path literally.  Keep that
combinatorial datum separate from the weaker assertion that an arbitrary path
has the same image as a power.  Reversed path evaluation sends a literal path
power to the corresponding endomorphism power.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace Quiver.Path

universe u v

variable {Q : Type u} [Quiver.{v} Q]

-- `loopPow`, `loopPow_zero`, `loopPow_succ`, `length_loopPow` and `loopPow_add` are shared with
-- `LargeIndecomposable.TC.Combinatorics.Quiver.LoopPower`.
attribute [simp] loopPow_zero loopPow_succ length_loopPow

theorem loopPow_one {i : Q} (p : Quiver.Path i i) :
    loopPow p 1 = p := by
  rw [loopPow_succ, loopPow_zero, Quiver.Path.nil_comp]

/-- The same successor power with the new copy displayed on the left. -/
theorem loopPow_succ_left {i : Q} (p : Quiver.Path i i) (n : ℕ) :
    loopPow p (n + 1) = p.comp (loopPow p n) := by
  rw [show n + 1 = 1 + n by omega, loopPow_add, loopPow_one]

end Quiver.Path

namespace LargeIndecomposable.LinearPathCategory

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {C : Type z} [CategoryTheory.Category C] [Preadditive C] [Linear k C]

omit [Preadditive C] in
/-- Reversed path evaluation respects literal powers of a closed path. -/
theorem pathMap_loopPow
    (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {i : Q} (p : Quiver.Path i i) (n : ℕ) :
    pathMap F₀ F₁ (Quiver.Path.loopPow p n) =
      (End.of (pathMap F₀ F₁ p) : End (F₀ i)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Quiver.Path.loopPow_succ, pathMap_comp, ih]
      change (End.of (pathMap F₀ F₁ p) : End (F₀ i)).asHom ≫
          ((End.of (pathMap F₀ F₁ p) : End (F₀ i)) ^ n).asHom =
        ((End.of (pathMap F₀ F₁ p) : End (F₀ i)) ^ (n + 1)).asHom
      rw [pow_succ, End.mul_def]

end LargeIndecomposable.LinearPathCategory
