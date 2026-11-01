module

public import LargeIndecomposable.Cleaving.Zigzags.ZigzagFork2
public import LargeIndecomposable.Crowns.Lemma5.Propagation

/-!
# BO13a Lemma 5 a), case `τ = σᵢ`

If the next long morphism after `σ₁` is `τ = σ (p+L)`, take two distinct last
arrows `G` of contours of `τ`. Either `ρ (p+L)` factors through none of them
(a zigzag ending at a sink with two in-arrows), or the propagation starts at
the source `x (p+L)` (`lemma5a_stateB`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- An isomorphism followed by an irreducible morphism is irreducible. -/
lemma IsIrreducible.isIso_comp {x y z : P} {α : y ⟶ z} (hα : IsIrreducible α) (T : x ⟶ y)
    [IsIso T] : IsIrreducible (T ≫ α) := by
  refine ⟨fun h ↦ hα.1 (by simpa using congrArg (inv T ≫ ·) h), fun h ↦ hα.2.1 ?_, ?_⟩
  · have : IsIso (inv T ≫ T ≫ α) := inferInstance
    simpa using this
  · intro w g h he
    rcases hα.2.2 w (inv T ≫ g) h (by rw [Category.assoc, ← he]; simp) with h1 | h1
    · exact Or.inl (by simpa using (inferInstance : IsIso (T ≫ inv T ≫ g)))
    · exact Or.inr h1

/-- Two irreducible morphisms into `z`, one a suffix of the other, agree. -/
lemma eq_of_suffix_irr {z : P} {f g : Σ y : P, y ⟶ z} (hf : IsIrreducible f.2)
    (hg : IsIrreducible g.2) (h : ∃ c, c ≫ f.2 = g.2) : f = g := by
  obtain ⟨c, hc⟩ := h
  rcases hg.2.2 _ _ _ hc.symm with h1 | h1
  · obtain ⟨hxy, rfl⟩ := eq_eqToHom_of_isIso c
    obtain ⟨y, f⟩ := f
    obtain ⟨y', g⟩ := g
    change y' = y at hxy
    subst hxy
    simp only [eqToHom_refl, Category.id_comp] at hc
    rw [hc]
  · exact absurd h1 hf.2.1

omit [IsRayCategory P] in
/-- The dual of `not_comp_eq_irr`. -/
lemma not_comp_eq_irr' {x x' y : P} {f : x ⟶ y} {α : x' ⟶ y} (hα : IsIrreducible α)
    (hf : ¬IsIso f) (hfα : ¬∃ g, g ≫ α = f) : ¬∃ g, g ≫ f = α := by
  rintro ⟨g, hg⟩
  rcases hα.2.2 _ g f hg.symm with h | h
  · exact hfα ⟨inv g, by rw [← hg, IsIso.inv_hom_id_assoc]⟩
  · exact hf h

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a), case `τ = σᵢ`.** -/
theorem lemma5a_caseB
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} {μ : a ⟶ b} (hμ : IsLong μ)
    (Z : ZChain P) (p L : ℕ)
    (hnρ : ∀ j ≤ L, ¬IsLong (Z.ρ (p + j))) (hnσ : ∀ j < L, ¬IsLong (Z.σ (p + j)))
    (F : Fin 2 → BMor (Z.x p)) (hFi : ∀ i, IsIrreducible (F i).2) (hF01 : F 0 ≠ F 1)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p)
    (G : Fin 2 → Σ y : P, y ⟶ Z.z (p + L)) (hGi : ∀ i, IsIrreducible (G i).2)
    (hG01 : G 0 ≠ G 1) (hGτ : ∀ i, ∃ t, t ≫ (G i).2 = Z.σ (p + L))
    (hτμ : ¬FactorsThroughMorphism μ (Z.σ (p + L)))
    (hτr : ¬IsIrreducible (Z.σ (p + L))) : False := by
  have hτ := hμ.2.1
  have hτ0 := hμ.1
  by_cases hρG : ∃ i, ∃ g, g ≫ (G i).2 = Z.ρ (p + L)
  · obtain ⟨i, R', hR'⟩ := hρG
    obtain ⟨t, ht⟩ := hGτ i
    refine B.lemma5a_stateB hmin hL hR hμ Z p L hnρ hnσ F hFi hF01 hFρ R' t (G i).2 hR' ht ?_
      (hGi i).2.1 (fun h ↦ hτμ (by rw [← ht]; exact FactorsThroughMorphism.comp_right h _))
      (not_factorsThrough_irr hτ hτ0 hμ.2.2.1 (hGi i)) (by rw [ht]; exact hτμ)
    intro h
    exact hτr (by rw [← ht]; exact IsIrreducible.isIso_comp (hGi i) t)
  · push_neg at hρG
    have hGG : ∀ i i', i ≠ i' → ¬∃ g, g ≫ (G i).2 = (G i').2 := fun i i' hii' hg ↦ by
      have := eq_of_suffix_irr (hGi i) (hGi i') hg
      fin_cases i <;> fin_cases i' <;> simp_all
    have hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2 := fun i i' hii' hg ↦ by
      have := eq_of_bLe_irr (hFi i) (hFi i') hg
      fin_cases i <;> fin_cases i' <;> simp_all
    exact B.not_zigzag_forks_in hmin hL hR μ hτ hτ0 Z p L F G
      (fun j hj ↦ not_factorsThrough_of_not_isLong hμ (Z.ρ_ne _) (hnρ j hj))
      (fun j hj ↦ not_factorsThrough_of_not_isLong hμ (Z.σ_ne _) (hnσ j hj))
      (fun i ↦ not_factorsThrough_irr hτ hτ0 hμ.2.2.1 (hFi i))
      (fun i ↦ not_factorsThrough_irr hτ hτ0 hμ.2.2.1 (hGi i)) (fun i ↦ (hFi i).2.1)
      (fun i ↦ (hGi i).2.1) hFF hGG hFρ (fun i ↦ not_comp_eq_irr (hFi i) (Z.ρ_not_isIso p) (hFρ i))
      (fun i ⟨g, hg⟩ ↦ hρG i g hg)
      (fun i ↦ not_comp_eq_irr' (hGi i) (Z.ρ_not_isIso _) (fun ⟨g, hg⟩ ↦ hρG i g hg))

end MulBasis

end RayQuiver

end LargeIndecomposable
