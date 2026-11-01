module

public import LargeIndecomposable.RayCategories.Basic.RayQuiverArrowRigidity
public import Mathlib.SetTheory.Cardinal.Embedding

@[expose] public section

/-!
# Four-arrow fork dichotomies

Since a finite ray category has no parallel irreducible arrows, four arrows at
one endpoint either admit four noncentral neighboring vertices or admit a
single loop together with three noncentral neighbors.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Four outgoing arrows in a finite ray category have exactly the following
shape relevant to the affine-star obstruction: either four can be chosen with
noncentral targets, or there is a loop and three further arrows with
noncentral targets.  Parallel-arrow cases do not occur. -/
theorem outgoingFourArrow_fork_dichotomy
    [Finite C] [IsFiniteRayCategory C]
    (x : RayVertex C) (hfour : 4 ≤ Nat.card (OutgoingQuiverArrow x)) :
    (∃ a : Fin 4 ↪ OutgoingQuiverArrow x, ∀ i, (a i).1 ≠ x) ∨
      ∃ l : OutgoingQuiverArrow x, l.1 = x ∧
        ∃ a : Fin 3 ↪ OutgoingQuiverArrow x,
          Disjoint ({l} : Set (OutgoingQuiverArrow x)) (Set.range a) ∧
            ∀ i, (a i).1 ≠ x := by
  classical
  letI : Finite (OutgoingQuiverArrow x) := outgoingQuiverArrow_finite x
  by_cases hloop : ∃ l : OutgoingQuiverArrow x, l.1 = x
  · right
    obtain ⟨l, hl⟩ := hloop
    obtain ⟨a, ha⟩ :=
      Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card
        (α := OutgoingQuiverArrow x) (n := 3)
        (s := ({l} : Set (OutgoingQuiverArrow x)))
        (by simpa using hfour)
    refine ⟨l, hl, a, ha, ?_⟩
    intro i hi
    have hai : a i = l :=
      outgoingQuiverArrow_fst_injective x (hi.trans hl.symm)
    have : a i ∈ ({l} : Set (OutgoingQuiverArrow x)) := by simp [hai]
    exact (Set.disjoint_left.1 ha this ⟨i, rfl⟩).elim
  · left
    obtain ⟨a, _⟩ :=
      Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card
        (α := OutgoingQuiverArrow x) (n := 4)
        (s := (∅ : Set (OutgoingQuiverArrow x)))
        (by simpa using hfour)
    exact ⟨a, fun i hi ↦ hloop ⟨a i, hi⟩⟩

/-- Incoming analogue of `outgoingFourArrow_fork_dichotomy`. -/
theorem incomingFourArrow_fork_dichotomy
    [Finite C] [IsFiniteRayCategory C]
    (z : RayVertex C) (hfour : 4 ≤ Nat.card (IncomingQuiverArrow z)) :
    (∃ a : Fin 4 ↪ IncomingQuiverArrow z, ∀ i, (a i).1 ≠ z) ∨
      ∃ l : IncomingQuiverArrow z, l.1 = z ∧
        ∃ a : Fin 3 ↪ IncomingQuiverArrow z,
          Disjoint ({l} : Set (IncomingQuiverArrow z)) (Set.range a) ∧
            ∀ i, (a i).1 ≠ z := by
  classical
  letI : Finite (IncomingQuiverArrow z) := incomingQuiverArrow_finite z
  by_cases hloop : ∃ l : IncomingQuiverArrow z, l.1 = z
  · right
    obtain ⟨l, hl⟩ := hloop
    obtain ⟨a, ha⟩ :=
      Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card
        (α := IncomingQuiverArrow z) (n := 3)
        (s := ({l} : Set (IncomingQuiverArrow z)))
        (by simpa using hfour)
    refine ⟨l, hl, a, ha, ?_⟩
    intro i hi
    have hai : a i = l :=
      incomingQuiverArrow_fst_injective z (hi.trans hl.symm)
    have : a i ∈ ({l} : Set (IncomingQuiverArrow z)) := by simp [hai]
    exact (Set.disjoint_left.1 ha this ⟨i, rfl⟩).elim
  · left
    obtain ⟨a, _⟩ :=
      Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card
        (α := IncomingQuiverArrow z) (n := 4)
        (s := (∅ : Set (IncomingQuiverArrow z)))
        (by simpa using hfour)
    exact ⟨a, fun i hi ↦ hloop ⟨a i, hi⟩⟩

end LargeIndecomposable
