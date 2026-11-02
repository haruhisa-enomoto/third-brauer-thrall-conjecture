module

public import LargeIndecomposable.RayCategories.Distributive.OneSided
public import LargeIndecomposable.Crowns.Basic.CrownFunctor
public import LargeIndecomposable.RayCategories.Quotients.ResidueQuiver
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# BO13a Lemma 4 c), first part

Let `σ, ρ` start at `x`, neither factoring through the other on the right,
with `ρ ≤ σ`, i.e. `σ = φ ≫ ρ ≫ ψ`. If `σ = γ ≫ δ` and `ρ = γ ≫ ρ'` share the
first factor `γ`, then `δ` is reducible (`RayCat.lemma4c`). The proof uses
one-sided cyclicity of `P(m, y₀)`, comparability, right cancellation and
nilpotence of non-identity endomorphisms (the printed argument is garbled;
this is a reconstruction).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [IsFiniteRayCategory P]

/-- **BO13a Lemma 4 c), first part.** -/
theorem lemma4c (hQ : OneSidedCyclic P) (hR : RightCancel P) {x y₀ y₁ m : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hv₁ : ¬∃ c, ρ ≫ c = σ) (γ : x ⟶ m) (δ : m ⟶ y₀)
    (ρ' : m ⟶ y₁) (hσ : γ ≫ δ = σ) (hρ : γ ≫ ρ' = ρ) (φ : x ⟶ x) (ψ : y₁ ⟶ y₀)
    (hle : φ ≫ ρ ≫ ψ = σ) (hσ0 : σ ≠ 0) :
    ∃ (m' : P) (d₁ : m ⟶ m') (d₂ : m' ⟶ y₀), d₁ ≫ d₂ = δ ∧ ¬IsIso d₁ ∧ ¬IsIso d₂ := by
  have hδ0 : δ ≠ 0 := fun h ↦ hσ0 (by rw [← hσ, h, comp_zero])
  have hσ' : σ = φ ≫ γ ≫ ρ' ≫ ψ := by rw [← hle, ← hρ]; simp
  have hf0 : ρ' ≫ ψ ≠ 0 := fun h ↦ hσ0 (by rw [hσ', h]; simp)
  -- `σ = ρ ≫ ψ'` is excluded
  have hno : ¬(ρ' ≫ ψ = δ) := fun h ↦ hv₁ ⟨ψ, by rw [← hρ, Category.assoc, h, hσ]⟩
  rcases IsFiniteRayCategory.factorization_comparable (ρ' ≫ ψ) δ with hT | hT
  · -- `δ` is a two-sided multiple of `ρ' ≫ ψ`
    rcases hQ m y₀ with h | h
    · obtain ⟨b, hb⟩ := h _ _ hδ0 hT
      refine absurd ⟨ψ ≫ b, ?_⟩ hv₁
      rw [← hσ, hb, ← hρ]
      simp
    · obtain ⟨a, ha⟩ := h _ _ hδ0 hT
      by_cases ha1 : (show m ⟶ m from a) = 𝟙 m
      · exact absurd (by rw [ha, ha1]; exact (Category.id_comp _).symm) hno
      · refine ⟨m, a, ρ' ≫ ψ, ha.symm, fun hi ↦ ha1 ?_, fun hi ↦ ?_⟩
        · have : IsIso (show m ⟶ m from a) := hi
          obtain ⟨h0, he⟩ := eq_eqToHom_of_isIso (show m ⟶ m from a)
          simpa using he
        · apply hv₁
          refine ⟨ψ ≫ inv (ρ' ≫ ψ) ≫ a ≫ ρ' ≫ ψ, ?_⟩
          have hγ : γ = ρ ≫ ψ ≫ inv (ρ' ≫ ψ) := by
            rw [← hρ, Category.assoc, ← Category.assoc ρ' ψ, IsIso.hom_inv_id, Category.comp_id]
          rw [← hσ, ha, hγ]
          simp only [Category.assoc]
  · -- `ρ' ≫ ψ` is a two-sided multiple of `δ`
    exfalso
    rcases hQ m y₀ with h | h
    · obtain ⟨b, hb⟩ := h _ _ hf0 hT
      have h2 : σ = φ ≫ σ ≫ b := by
        calc σ = φ ≫ γ ≫ ρ' ≫ ψ := hσ'
          _ = φ ≫ γ ≫ (δ ≫ b) := by rw [hb]
          _ = φ ≫ (γ ≫ δ) ≫ b := by simp
          _ = φ ≫ σ ≫ b := by rw [hσ]
      obtain ⟨-, hb1⟩ := IsRayCategory.eq_id_of_two_sided σ hσ0 φ (show y₀ ⟶ y₀ from b) h2
      exact hno (by rw [hb, hb1]; exact Category.comp_id _)
    · obtain ⟨a, ha⟩ := h _ _ hf0 hT
      have hc : (φ ≫ γ ≫ a) ≫ δ = γ ≫ δ := by
        rw [hσ, hσ', ha]
        simp
      have hγ := hR _ _ _ hc (by rw [hc, hσ]; exact hσ0)
      have hγ0 : γ ≠ 0 := fun h ↦ hσ0 (by rw [← hσ, h, zero_comp])
      obtain ⟨-, ha1⟩ := IsRayCategory.eq_id_of_two_sided γ hγ0 φ (show m ⟶ m from a)
        hγ.symm
      exact hno (by rw [ha, ha1]; exact Category.id_comp _)

end RayCat

end LargeIndecomposable
