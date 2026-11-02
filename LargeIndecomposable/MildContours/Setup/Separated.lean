module

public import LargeIndecomposable.MildContours.Contours.Lemma22

/-!
# Separated-quiver arguments under `MildHyp`

An arrow (irreducible morphism) never factors through a non-irreducible `τ`,
and distinct arrows with a common source (or target) never factor through each
other. Hence a crown made of arrows — a cycle in the separated quiver — cleaves
into every proper residue `P/τ` with `τ` not irreducible, which `MildHyp`
excludes (`MildHyp.not_arrow_crown2`, `MildHyp.not_arrow_crown3`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

/-- An irreducible morphism does not factor through a non-irreducible non-invertible
morphism. -/
lemma not_ftm_of_irreducible {a b x y : P} {τ : a ⟶ b} (hτ : ¬IsIso τ) (hτi : ¬IsIrreducible τ)
    {e : x ⟶ y} (he : IsIrreducible e) : ¬FactorsThroughMorphism τ e := by
  rintro ⟨u, v, rfl⟩
  rcases he.2.2 _ u (τ ≫ v) rfl with h | h
  · obtain ⟨hxa, hu⟩ := RayQuiver.eq_id_of_isIso u
    subst hxa
    have hu' : u = 𝟙 _ := by rw [hu]; rfl
    subst hu'
    rw [Category.id_comp] at he
    rcases he.2.2 _ τ v rfl with h' | h'
    · exact hτ h'
    · obtain ⟨hby, hv⟩ := RayQuiver.eq_id_of_isIso v
      subst hby
      have hv' : v = 𝟙 _ := by rw [hv]; rfl
      subst hv'
      rw [Category.comp_id] at he
      exact hτi he
  · exact hτ (ray_isIso_factors τ v).1

/-- Distinct arrows out of a vertex do not factor through each other. -/
lemma arrows_out_apart {m u₁ u₂ : RayVert P} (e₁ : m ⟶ u₁) (e₂ : m ⟶ u₂)
    (hne : ¬∃ h : u₁ = u₂, HEq e₁ e₂) : (¬∃ g, e₁.1 ≫ g = e₂.1) ∧ ¬∃ g, e₂.1 ≫ g = e₁.1 :=
  (arrows_eq_or_apart_out e₁ e₂).resolve_left hne

/-- Distinct arrows into a vertex do not factor through each other. -/
lemma arrows_in_apart {m u₁ u₂ : RayVert P} (e₁ : u₁ ⟶ m) (e₂ : u₂ ⟶ m)
    (hne : ¬∃ h : u₁ = u₂, HEq e₁ e₂) : ArrowsApart e₁ e₂ :=
  (arrows_eq_or_apart e₁ e₂).resolve_left hne

/-- **No crown of four arrows** (a 4-cycle in the separated quiver). -/
theorem MildHyp.not_arrow_crown2 (hM : MildHyp k P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (hτi : ¬IsIrreducible τ) {x₀ x₁ z₀ z₁ : RayVert P}
    (ρ₀ : x₀ ⟶ z₀) (σ₀ : x₁ ⟶ z₀) (ρ₁ : x₁ ⟶ z₁) (σ₁ : x₀ ⟶ z₁)
    (hz₀ : ¬∃ h : x₀ = x₁, HEq ρ₀ σ₀) (hz₁ : ¬∃ h : x₁ = x₀, HEq ρ₁ σ₁)
    (hx₀ : ¬∃ h : z₀ = z₁, HEq ρ₀ σ₁) (hx₁ : ¬∃ h : z₀ = z₁, HEq σ₀ ρ₁) : False := by
  have a₀ := arrows_in_apart ρ₀ σ₀ hz₀
  have a₁ := arrows_in_apart ρ₁ σ₁ hz₁
  have b₀ := arrows_out_apart ρ₀ σ₁ hx₀
  have b₁ := arrows_out_apart σ₀ ρ₁ hx₁
  exact hM.not_crown2 τ hτ hτ0 ρ₀.1 σ₀.1 ρ₁.1 σ₁.1 (not_ftm_of_irreducible hτ hτi ρ₀.2)
    (not_ftm_of_irreducible hτ hτi σ₀.2) (not_ftm_of_irreducible hτ hτi ρ₁.2)
    (not_ftm_of_irreducible hτ hτi σ₁.2) a₀.1 a₀.2 a₁.1 a₁.2 b₁.1 b₁.2 b₀.2 b₀.1

end RayCat

end LargeIndecomposable
