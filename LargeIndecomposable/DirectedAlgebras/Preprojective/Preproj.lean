module

public import LargeIndecomposable.AuslanderReiten.Lengths.Component
public import LargeIndecomposable.AuslanderReiten.Irreducible.Irreducible

/-!
# Preprojective components

A preprojective component (`PreprojComp`) is a nonempty class of nonzero indecomposables, closed
under isomorphism and under irreducible maps in both directions, in which every member has
finitely many predecessors up to isomorphism (of bounded dimension) and lies on no cycle.

Members are directing (`PreprojComp.directing`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- A preprojective component. -/
structure PreprojComp (𝒞 : FDMod k A → Prop) : Prop where
  nonempty : ∃ X, 𝒞 X
  indNT : ∀ X, 𝒞 X → IndNT X
  iso : ∀ X Y, 𝒞 X → IsoM X Y → 𝒞 Y
  pred : ∀ X Y, 𝒞 X → IndNT Y → ∀ f : Y ⟶ X, IsIrr f → 𝒞 Y
  succ : ∀ X Y, 𝒞 X → IndNT Y → ∀ f : X ⟶ Y, IsIrr f → 𝒞 Y
  finPred : ∀ X, 𝒞 X → ∃ b, ∀ n Y, PredN X n Y → finrank k Y ≤ b
  finIso : ∀ X, 𝒞 X → ∃ L : List (FDMod k A), ∀ n Y, PredN X n Y → ∃ Z ∈ L, IsoM Y Z
  noCycle : ∀ X, 𝒞 X → ∀ n Y, 0 < n → PredN X n Y → ¬IsoM Y X

namespace PreprojComp

variable {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞)
include h𝒞

/-- **Members of a preprojective component are directing**, hence bricks. -/
theorem directing {X : FDMod k A} (hX : 𝒞 X) : Directing X := by
  obtain ⟨b, hb⟩ := h𝒞.finPred X hX
  exact directing_of_noCycle (h𝒞.indNT X hX) hb (h𝒞.noCycle X hX)

end PreprojComp

end LargeIndecomposable.AR
