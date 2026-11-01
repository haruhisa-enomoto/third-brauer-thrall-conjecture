module

public import LargeIndecomposable.Crowns.Basic.Lemma4c
public import LargeIndecomposable.RayCategories.Basic.Op

/-!
# The ray axioms in the opposite category

One-sided cyclicity and cancellation pass to `Pᵒᵖ`; applying Lemma 4 c) in
`Pᵒᵖ` gives its dual (`RayCat.lemma4c_dual`: a common last factor).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable Opposite

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma oneSidedCyclic_op (h : OneSidedCyclic P) : OneSidedCyclic Pᵒᵖ := by
  intro X Y
  have tsf : ∀ f g : X ⟶ Y, TwoSidedEndomorphismFactors f g →
      TwoSidedEndomorphismFactors f.unop g.unop := by
    rintro f g ⟨a, b, hab⟩
    exact ⟨End.of b.unop, End.of a.unop, by rw [hab]; simp [End.of]⟩
  have nz : ∀ g : X ⟶ Y, g ≠ 0 → g.unop ≠ 0 := fun g hg h0 ↦ hg (by
    rw [← Quiver.Hom.op_unop g, h0]; rfl)
  rcases h (unop Y) (unop X) with h | h
  · refine Or.inr fun f g hg hfg ↦ ?_
    obtain ⟨b, hb⟩ := h _ _ (nz g hg) (tsf f g hfg)
    exact ⟨End.of (show unop X ⟶ unop X from b).op, by
      rw [← Quiver.Hom.op_unop g, hb]; rfl⟩
  · refine Or.inl fun f g hg hfg ↦ ?_
    obtain ⟨a, ha⟩ := h _ _ (nz g hg) (tsf f g hfg)
    exact ⟨End.of (show unop Y ⟶ unop Y from a).op, by
      rw [← Quiver.Hom.op_unop g, ha]; rfl⟩

variable [Finite P] [IsFiniteRayCategory P]

/-- **BO13a Lemma 4 c), dual form.** `σ, ρ` end at `y` (a peak) with `ρ ≤ σ`,
`σ = δ ≫ γ`, `ρ = ρ' ≫ γ`; then `δ` is reducible. -/
theorem lemma4c_dual (hQ : OneSidedCyclic P) (hL : LeftCancel P) {x₀ x₁ y m : P}
    {σ : x₀ ⟶ y} {ρ : x₁ ⟶ y} (hp : ¬∃ c, c ≫ ρ = σ) (γ : m ⟶ y) (δ : x₀ ⟶ m)
    (ρ' : x₁ ⟶ m) (hσ : δ ≫ γ = σ) (hρ : ρ' ≫ γ = ρ) (φ : y ⟶ y) (ψ : x₀ ⟶ x₁)
    (hle : ψ ≫ ρ ≫ φ = σ) (hσ0 : σ ≠ 0) :
    ∃ (m' : P) (d₁ : x₀ ⟶ m') (d₂ : m' ⟶ m), d₁ ≫ d₂ = δ ∧ ¬IsIso d₁ ∧ ¬IsIso d₂ := by
  let _ : IsRayCategory Pᵒᵖ := isRayCategory_of_finiteRayCategory
  let _ : IsRayCategory P := isRayCategory_of_finiteRayCategory
  have hp' : ¬∃ c, ρ.op ≫ c = σ.op := fun ⟨c, hc⟩ ↦ hp ⟨c.unop, by
    have := congrArg Quiver.Hom.unop hc; simpa using this⟩
  obtain ⟨m', d₁, d₂, hd, h1, h2⟩ := lemma4c (oneSidedCyclic_op hQ) (rightCancel_op hL) hp'
    γ.op δ.op ρ'.op (by rw [← op_comp, hσ]) (by rw [← op_comp, hρ]) φ.op ψ.op
    (by rw [← op_comp, ← op_comp, Category.assoc, hle]) (fun h ↦ hσ0 (by
      rw [← Quiver.Hom.unop_op σ, h]; rfl))
  refine ⟨unop m', d₂.unop, d₁.unop, ?_, fun hi ↦ h2 ?_, fun hi ↦ h1 ?_⟩
  · rw [← unop_comp, hd]; rfl
  · have : IsIso d₂.unop.op := inferInstance
    simpa using this
  · have : IsIso d₁.unop.op := inferInstance
    simpa using this

end RayCat

end LargeIndecomposable
