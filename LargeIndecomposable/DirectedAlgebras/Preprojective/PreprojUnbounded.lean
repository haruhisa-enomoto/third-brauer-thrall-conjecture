module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.PreprojDir

/-!
# Preprojective components of unbounded representation length

If a connected algebra with a preprojective component containing a module has indecomposables of
unbounded dimension, then the component itself has members of unbounded dimension
(`PreprojComp.unbounded`): a component of bounded length is a closed class, hence contains every
indecomposable (`all_of_closed`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **A preprojective component of a connected algebra of unbounded length is unbounded.** -/
theorem PreprojComp.unbounded {ι : Type} [Fintype ι] (e : ι → A) (he : ∀ x, IsIdempotentElem (e x))
    (hsum : ∑ x, e x = 1) (hP : ∀ x, IndNT (projE (k := k) (he x)))
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ x y, x ∈ S → (∃ a, e x * a * e y ≠ 0) ∨ (∃ a, e y * a * e x ≠ 0) → y ∈ S) →
        S = Set.univ)
    {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞)
    (hunb : ∀ b, ∃ N : FDMod k A, IndNT N ∧ b < finrank k N) (b : ℕ) :
    ∃ X, 𝒞 X ∧ b < finrank k X := by
  by_contra hno
  push Not at hno
  have hcl : ClosedClass 𝒞 :=
    { indNT := h𝒞.indNT
      iso := h𝒞.iso
      pred := h𝒞.pred_chosen
      las := h𝒞.lasFam
      bound := ⟨b, hno⟩ }
  obtain ⟨M, hM⟩ := h𝒞.nonempty
  obtain ⟨N, hN, hNb⟩ := hunb b
  have := hno N (all_of_closed e he hsum hP hconn hcl hM N hN)
  omega

end LargeIndecomposable.AR
