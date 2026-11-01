module

public import LargeIndecomposable.Crowns.Lemma6.Chain

/-!
# Helpers for the chain-level proof of BO13a Lemma 6
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- A morphism divisible by a long `σ` and by `μ` makes `σ` divisible by `μ`. -/
lemma ftm_trans_long {a b c d X Y : P} {σ : a ⟶ b} {μ : c ⟶ d} (hσ : IsLong σ) {f : X ⟶ Y}
    (hf : f ≠ 0) (h1 : FactorsThroughMorphism σ f) (h2 : FactorsThroughMorphism μ f) :
    FactorsThroughMorphism μ σ := by
  obtain ⟨hx, hy, rfl⟩ := hσ.2.2.2 f hf h1
  subst hx hy
  simpa using h2

lemma eq_of_rayMor_eq {X Y X' Y' : P} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : (⟨X, Y, f⟩ : RayMor P) = ⟨X', Y', g⟩) :
    ∃ (hx : X = X') (hy : Y = Y'), f = eqToHom hx ≫ g ≫ eqToHom hy.symm := by
  cases h
  exact ⟨rfl, rfl, by simp⟩

variable [IsRayCategory P]

namespace L6Data

variable {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (D : L6Data σ ρ)

/-- An irreducible `t → y₀` with `σ ∤ t` does not factor through `w₂` or `u₂`. -/
lemma irr_y₀ (hσ : ¬IsIrreducible σ) {T : P} {t : T ⟶ y₀} (ht : IsIrreducible t)
    (hpk : ¬∃ g, g ≫ t = σ) : (¬∃ g, g ≫ D.W = t) ∧ ¬∃ g, g ≫ D.U = t := by
  constructor
  · rintro ⟨g, hg⟩
    rcases ht.2.2 _ g D.W hg.symm with h | h
    · exact hpk ⟨D.β.1 ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.βW]⟩
    · exact D.W_not_isIso hσ h
  · rintro ⟨g, hg⟩
    rcases ht.2.2 _ g D.U hg.symm with h | h
    · exact hpk ⟨D.ψ ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.ψU]⟩
    · exact D.U_not_isIso h

/-- An irreducible `t → y₁` with `ρ ∤ t` does not factor through `w₂'` or `u₂'`. -/
lemma irr_y₁ (hρ : ¬IsIrreducible ρ) {T : P} {t : T ⟶ y₁} (ht : IsIrreducible t)
    (hpk : ¬∃ g, g ≫ t = ρ) : (¬∃ g, g ≫ D.W' = t) ∧ ¬∃ g, g ≫ D.U' = t := by
  constructor
  · rintro ⟨g, hg⟩
    rcases ht.2.2 _ g D.W' hg.symm with h | h
    · exact hpk ⟨D.β'.1 ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.βW']⟩
    · exact D.W'_not_isIso hρ h
  · rintro ⟨g, hg⟩
    rcases ht.2.2 _ g D.U' hg.symm with h | h
    · exact hpk ⟨D.ψ ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.ψU']⟩
    · exact D.U'_not_isIso h

end L6Data

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- A long `μ` in a contour has a last contour arrow through which a morphism
`ρ` incomparable with `μ` from the left does not factor. -/
theorem exists_last_not
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} {μ : a ⟶ b} (hμ : IsLong μ)
    (hc : ¬NotInContour μ) {z : P} (ρ : z ⟶ b) (hρ : ρ ≠ 0) (h1 : ¬∃ c, c ≫ μ = ρ)
    (h2 : ¬∃ c, c ≫ ρ = μ) :
    ∃ (T : P) (e : T ⟶ b), IsIrreducible e ∧ ¬∃ g, g ≫ e = ρ := by
  obtain ⟨c, d, α, β, v, w, hv, hw, hni⟩ := exists_contour_last hμ hc
  by_contra hne
  push Not at hne
  refine B.not_factors_both_last hmin hL hR α β v w (by rw [hv, hw]) (by rw [hv]; exact hμ.1) hni
    ρ hρ (by rw [hv]; exact h1) (by rw [hv]; exact h2) ?_ ?_
  · exact hne _ α.1 α.2
  · exact hne _ β.1 β.2

include B in
/-- A long `μ` in a contour has a first contour arrow through which a morphism
`ρ` incomparable with `μ` from the right does not factor. -/
theorem exists_first_not
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} {μ : a ⟶ b} (hμ : IsLong μ)
    (hc : ¬NotInContour μ) {z : P} (ρ : a ⟶ z) (hρ : ρ ≠ 0) (h1 : ¬∃ c, μ ≫ c = ρ)
    (h2 : ¬∃ c, ρ ≫ c = μ) :
    ∃ (T : P) (e : a ⟶ T), IsIrreducible e ∧ ¬∃ g, e ≫ g = ρ := by
  obtain ⟨c, d, α, β, v, w, hv, hw, hni⟩ := exists_contour_first hμ hc
  by_contra hne
  push Not at hne
  refine B.not_factors_both hmin hL hR α β v w (by rw [hv, hw]) (by rw [hv]; exact hμ.1) hni
    ⟨z, ρ⟩ hρ ?_ ?_ ?_ ?_
  · rintro ⟨c', hc'⟩
    rw [hv] at hc'
    exact h1 ⟨c', hc'⟩
  · rintro ⟨c', hc'⟩
    change ρ ≫ c' = pathVal (α.toPath.comp v) at hc'
    rw [hv] at hc'
    exact h2 ⟨c', hc'⟩
  · exact hne _ α.1 α.2
  · exact hne _ β.1 β.2

end MulBasis

end RayQuiver

end LargeIndecomposable
