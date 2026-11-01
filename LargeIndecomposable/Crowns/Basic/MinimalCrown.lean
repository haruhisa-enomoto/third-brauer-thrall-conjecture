module

public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisQuot

/-!
# Crowns in minimal representation-infinite algebras

Let `A` have a twisted multiplicative basis over `P`, and suppose every proper
quotient of `A` is representation-finite. Then every closed chain (crown) of
`P` contains a morphism factoring through any given non-invertible nonzero
`τ`: otherwise the crown survives in `P/τ`, and `A/⟨τ⟩` is
representation-infinite (`RayQuiver.MulBasis.crown_meets`). This is the first
step of the strategy of BO13a, Proposition 2 ("each long morphism `τ` occurs
in `C`").
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [LargeIndecomposable.IsFiniteRayCategory P]
  {a b : P} (τ : a ⟶ b)

/-- A closed chain avoiding `τ` gives a closed chain of `P/τ`. -/
def ClosedChain.toRes {m : ℕ} (C : ClosedChain P m)
    (hρ : ∀ i, ¬LargeIndecomposable.FactorsThroughMorphism τ (C.ρ i))
    (hσ : ∀ i, ¬LargeIndecomposable.FactorsThroughMorphism τ (C.σ i)) : ClosedChain (Res τ) m where
  x i := (resF τ).obj (C.x i)
  z i := (resF τ).obj (C.z i)
  ρ i := (resF τ).map (C.ρ i)
  σ i := (resF τ).map (C.σ i)
  ρ_ne i h := hρ i ((LargeIndecomposable.rayResidueFunctor_map_eq_zero_iff τ _).1 h)
  σ_ne i h := hσ i ((LargeIndecomposable.rayResidueFunctor_map_eq_zero_iff τ _).1 h)
  peak₁ i := by
    rintro ⟨c, hc⟩
    refine C.peak₁ i ⟨lift τ c, (resF_map_injective τ (hρ i) ?_).symm⟩
    rw [Functor.map_comp, resF_lift, hc]
  peak₂ i := by
    rintro ⟨c, hc⟩
    refine C.peak₂ i ⟨lift τ c, (resF_map_injective τ (hσ i) ?_).symm⟩
    rw [Functor.map_comp, resF_lift, hc]
  valley₁ i := by
    rintro ⟨c, hc⟩
    refine C.valley₁ i ⟨lift τ c, (resF_map_injective τ (hρ (i + 1)) ?_).symm⟩
    rw [Functor.map_comp, resF_lift, hc]
  valley₂ i := by
    rintro ⟨c, hc⟩
    refine C.valley₂ i ⟨lift τ c, (resF_map_injective τ (hσ i) ?_).symm⟩
    rw [Functor.map_comp, resF_lift, hc]

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [LargeIndecomposable.IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **Every crown meets every non-invertible nonzero morphism** of a ray
category over which a minimal representation-infinite algebra has a twisted
multiplicative basis. -/
theorem crown_meets
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ) (hτ0 : τ ≠ 0) {m : ℕ} (C : ClosedChain P m) :
    (∃ i, LargeIndecomposable.FactorsThroughMorphism τ (C.ρ i)) ∨
      ∃ i, LargeIndecomposable.FactorsThroughMorphism τ (C.σ i) := by
  by_contra h
  push_neg at h
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
  exact (C.toRes τ h.1 h.2).not_isRepresentationFinite (B.quot τ hτ)
    (hmin _ (ideal_ne_bot hτ0))

end MulBasis

end RayQuiver

end LargeIndecomposable
