module

public import LargeIndecomposable.RayCategories.Basic.OneSided
public import LargeIndecomposable.Crowns.Basic.CrownFunctor
public import LargeIndecomposable.RayCategories.Basic.ResidueQuiver

/-!
# Order relations between neighbours in a crown

BO13a Lemma 5 b), d) (§2.2.1). Index dictionary: BO13a's `σᵢ₊₁, ρᵢ₊₁` are
our `σ i : x (i+1) → z i` and `ρ (i+1) : x (i+1) → z (i+1)`; BO13a's `ρᵢ` is
our `ρ i`.

* `ClosedChain.not_le_both_σ`: the two neighbours of `σ i` are not both
  below it (Lemma 5 b)); `not_le_both_ρ` is the dual statement.
* `ClosedChain.le_ρ_of_le_σ`: Lemma 5 d).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

namespace RayCat

namespace ClosedChain

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] {m : ℕ} (C : ClosedChain Q m)

/-- **BO13a Lemma 5 b).** The two neighbours `ρ i`, `ρ (i+1)` of `σ i` do not
both lie below `σ i`. -/
theorem not_le_both_σ (hQ : OneSidedCyclic Q) (i : Fin (m + 1)) :
    ¬(FactorsThroughMorphism (C.ρ i) (C.σ i) ∧ FactorsThroughMorphism (C.ρ (i + 1)) (C.σ i)) := by
  rintro ⟨⟨a, b, hab⟩, ⟨a', b', hab'⟩⟩
  rcases hQ (C.x (i + 1)) (C.z i) with h | h
  · obtain ⟨c, hc⟩ := h (C.ρ (i + 1) ≫ b') (C.σ i) (C.σ_ne i)
      ⟨End.of a', 𝟙 _, by rw [hab']; simp [End.of]⟩
    exact C.valley₂ i ⟨b' ≫ c, by rw [hc, Category.assoc]⟩
  · obtain ⟨c, hc⟩ := h (a ≫ C.ρ i) (C.σ i) (C.σ_ne i)
      ⟨𝟙 _, End.of b, by rw [hab]; simp [End.of]⟩
    exact C.peak₂ i ⟨c ≫ a, by rw [hc, Category.assoc]⟩

/-- **BO13a Lemma 5 b)**, dual form: the two neighbours `σ (j+1)`, `σ j` of
`ρ (j+1)` do not both lie below `ρ (j+1)`. -/
theorem not_le_both_ρ (hQ : OneSidedCyclic Q) (j : Fin (m + 1)) :
    ¬(FactorsThroughMorphism (C.σ (j + 1)) (C.ρ (j + 1)) ∧
      FactorsThroughMorphism (C.σ j) (C.ρ (j + 1))) := by
  rintro ⟨⟨a, b, hab⟩, ⟨a', b', hab'⟩⟩
  rcases hQ (C.x (j + 1)) (C.z (j + 1)) with h | h
  · obtain ⟨c, hc⟩ := h (C.σ j ≫ b') (C.ρ (j + 1)) (C.ρ_ne _)
      ⟨End.of a', 𝟙 _, by rw [hab']; simp [End.of]⟩
    exact C.valley₁ j ⟨b' ≫ c, by rw [hc, Category.assoc]⟩
  · obtain ⟨c, hc⟩ := h (a ≫ C.σ (j + 1)) (C.ρ (j + 1)) (C.ρ_ne _)
      ⟨𝟙 _, End.of b, by rw [hab]; simp [End.of]⟩
    exact C.peak₁ (j + 1) ⟨c ≫ a, by rw [hc, Category.assoc]⟩

/-- **BO13a Lemma 5 d).** If `ρ (j+1)` is long and `σ (j+1) ≤ σ j`, then
`σ (j+1) ≤ ρ (j+1)`. -/
theorem le_ρ_of_le_σ [IsFiniteRayCategory Q] (j : Fin (m + 1)) (hρ : IsLongAt (C.ρ (j + 1)))
    (h : FactorsThroughMorphism (C.σ (j + 1)) (C.σ j)) :
    FactorsThroughMorphism (C.σ (j + 1)) (C.ρ (j + 1)) := by
  obtain ⟨φ, ψ, hφψ⟩ := h
  have hg : φ ≫ C.σ (j + 1) ≠ 0 := fun h0 ↦ C.σ_ne j (by rw [hφψ, ← Category.assoc, h0, zero_comp])
  rcases IsFiniteRayCategory.factorization_comparable (φ ≫ C.σ (j + 1)) (C.ρ (j + 1)) with
    ⟨a, b, hab⟩ | ⟨a, b, hab⟩
  · exact ⟨a ≫ φ, b, by rw [hab]; simp [Category.assoc]⟩
  · exfalso
    obtain ⟨hx, hy, he⟩ := hρ _ hg ⟨a, b, by rw [hab, Category.assoc]⟩
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    exact C.valley₂ j ⟨ψ, by rw [← he, hφψ, Category.assoc]⟩

end ClosedChain

end RayCat

end LargeIndecomposable
