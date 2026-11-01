module

public import LargeIndecomposable.Crowns.Lemma6.Statement

/-!
# Long morphisms of a minimal crown (BO13a Lemma 5 b), c))

* `ZChain.not_le_both_σ`, `ZChain.not_le_both_ρ`: Lemma 5 b) for chains.
* `MulBasis.long_entry`: every long morphism is an entry of every crown.
* `MulBasis.σ_nbr_red`, `MulBasis.ρ_nbr_red`: the neighbours of a long entry
  are reducible (Lemma 5 a)).
* `MulBasis.lemma5c`: a crown with a long entry has a second, different long
  entry.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

namespace ZChain

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (Z : ZChain Q)

/-- **BO13a Lemma 5 b)**: the neighbours `ρ s`, `ρ (s+1)` of `σ s` are not both
below `σ s`. -/
theorem not_le_both_σ (hQ : OneSidedCyclic Q) (s : ℕ) :
    ¬(FactorsThroughMorphism (Z.ρ s) (Z.σ s) ∧ FactorsThroughMorphism (Z.ρ (s + 1)) (Z.σ s)) := by
  rintro ⟨⟨a, b, hab⟩, ⟨a', b', hab'⟩⟩
  rcases hQ (Z.x (s + 1)) (Z.z s) with h | h
  · obtain ⟨c, hc⟩ := h (Z.ρ (s + 1) ≫ b') (Z.σ s) (Z.σ_ne s)
      ⟨End.of a', 𝟙 _, by rw [hab']; simp [End.of]⟩
    exact Z.valley₂ s ⟨b' ≫ c, by rw [hc, Category.assoc]⟩
  · obtain ⟨c, hc⟩ := h (a ≫ Z.ρ s) (Z.σ s) (Z.σ_ne s)
      ⟨𝟙 _, End.of b, by rw [hab]; simp [End.of]⟩
    exact Z.peak₂ s ⟨c ≫ a, by rw [hc, Category.assoc]⟩

/-- **BO13a Lemma 5 b)**, dual form: the neighbours `σ t`, `σ (t+1)` of
`ρ (t+1)` are not both below `ρ (t+1)`. -/
theorem not_le_both_ρ (hQ : OneSidedCyclic Q) (t : ℕ) :
    ¬(FactorsThroughMorphism (Z.σ t) (Z.ρ (t + 1)) ∧
      FactorsThroughMorphism (Z.σ (t + 1)) (Z.ρ (t + 1))) := by
  rintro ⟨⟨a', b', hab'⟩, ⟨a, b, hab⟩⟩
  rcases hQ (Z.x (t + 1)) (Z.z (t + 1)) with h | h
  · obtain ⟨c, hc⟩ := h (Z.σ t ≫ b') (Z.ρ (t + 1)) (Z.ρ_ne _)
      ⟨End.of a', 𝟙 _, by rw [hab']; simp [End.of]⟩
    exact Z.valley₁ t ⟨b' ≫ c, by rw [hc, Category.assoc]⟩
  · obtain ⟨c, hc⟩ := h (a ≫ Z.σ (t + 1)) (Z.ρ (t + 1)) (Z.ρ_ne _)
      ⟨𝟙 _, End.of b, by rw [hab]; simp [End.of]⟩
    exact Z.peak₁ (t + 1) ⟨c ≫ a, by rw [hc, Category.assoc]⟩

end ZChain

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- Every long morphism is an entry of every crown. -/
theorem long_entry
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (C : Crown P) {a b : P} (μ : a ⟶ b) (hμ : IsLong μ) : ∃ t, C.f t = ⟨a, b, μ⟩ := by
  obtain ⟨t, h | h⟩ := B.long_meets hmin C μ hμ
  · obtain ⟨hx, hy, he⟩ := hμ.2.2.2 _ (C.toZChain.ρ_ne t) h
    subst hx hy
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    exact ⟨2 * t, by rw [← C.toZChain_ρ, he]⟩
  · obtain ⟨hx, hy, he⟩ := hμ.2.2.2 _ (C.toZChain.σ_ne t) h
    subst hx hy
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    exact ⟨2 * t + 1, by rw [← C.toZChain_σ, he]⟩

include B in
/-- The neighbours of a long `σ s` are reducible (Lemma 5 a)). -/
theorem σ_nbr_red
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (s : ℕ) (hσ : IsLong (C.toZChain.σ s)) :
    ¬IsIrreducible (C.toZChain.ρ (s + 1)) ∧ ¬IsIrreducible (C.toZChain.ρ s) := by
  constructor
  · intro hirr
    obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_first hσ (hcont _ hσ)
    have key : ∀ {c : RayVert P} (α : RayVert.mk (C.toZChain.x (s + 1)) ⟶ c)
        (v' : Quiver.Path c (RayVert.mk (C.toZChain.z s))),
        pathVal (α.toPath.comp v') = C.toZChain.σ s →
          ¬∃ g, α.1 ≫ g = C.toZChain.ρ (s + 1) := by
      intro c α v' hv ⟨g, hg⟩
      rcases hirr.2.2 _ α.1 g hg.symm with h | h
      · exact α.2.2.1 h
      · exact C.toZChain.valley₂ s ⟨inv g ≫ pathVal v', by
          rw [← hv, ← hg, Category.assoc, IsIso.hom_inv_id_assoc, pathVal_comp, pathVal_toPath]⟩
    refine B.lemma5a hmin hL hR hQ hcont C.toZChain s hσ ⟨C.n - 1, ?_⟩ α β v' w' hv hw hni
      (key α v' hv) (key β w' hw)
    have := C.isLong_σ_add s hσ
    rwa [show s + 1 + (C.n - 1) = s + C.n by have := C.hn; omega]
  · intro hirr
    obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_last hσ (hcont _ hσ)
    have key : ∀ {c : RayVert P} (α : c ⟶ RayVert.mk (C.toZChain.z s))
        (v' : Quiver.Path (RayVert.mk (C.toZChain.x (s + 1))) c),
        pathVal (v'.cons α) = C.toZChain.σ s → ¬∃ g, g ≫ α.1 = C.toZChain.ρ s := by
      intro c α v' hv ⟨g, hg⟩
      rcases hirr.2.2 _ g α.1 hg.symm with h | h
      · exact C.toZChain.peak₂ s ⟨pathVal v' ≫ inv g, by
          rw [← hv, ← hg, Category.assoc, IsIso.inv_hom_id_assoc]; rfl⟩
      · exact α.2.2.1 h
    exact B.lemma5a_last hmin hL hR hQ hcont C s hσ α β v' w' hv hw hni (key α v' hv)
      (key β w' hw)

include B in
/-- The neighbours of a long `ρ (t+1)` are reducible (Lemma 5 a)). -/
theorem ρ_nbr_red
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (t : ℕ) (hρ : IsLong (C.toZChain.ρ (t + 1))) :
    ¬IsIrreducible (C.toZChain.σ t) ∧ ¬IsIrreducible (C.toZChain.σ (t + 1)) := by
  constructor
  · intro hirr
    obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_first hρ (hcont _ hρ)
    have key : ∀ {c : RayVert P} (α : RayVert.mk (C.toZChain.x (t + 1)) ⟶ c)
        (v' : Quiver.Path c (RayVert.mk (C.toZChain.z (t + 1)))),
        pathVal (α.toPath.comp v') = C.toZChain.ρ (t + 1) →
          ¬∃ g, α.1 ≫ g = C.toZChain.σ t := by
      intro c α v' hv ⟨g, hg⟩
      rcases hirr.2.2 _ α.1 g hg.symm with h | h
      · exact α.2.2.1 h
      · exact C.toZChain.valley₁ t ⟨inv g ≫ pathVal v', by
          rw [← hv, ← hg, Category.assoc, IsIso.hom_inv_id_assoc, pathVal_comp, pathVal_toPath]⟩
    exact B.lemma5a_rho_first hmin hL hR hQ hcont C t hρ α β v' w' hv hw hni (key α v' hv)
      (key β w' hw)
  · intro hirr
    obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_last hρ (hcont _ hρ)
    have key : ∀ {c : RayVert P} (α : c ⟶ RayVert.mk (C.toZChain.z (t + 1)))
        (v' : Quiver.Path (RayVert.mk (C.toZChain.x (t + 1))) c),
        pathVal (v'.cons α) = C.toZChain.ρ (t + 1) →
          ¬∃ g, g ≫ α.1 = C.toZChain.σ (t + 1) := by
      intro c α v' hv ⟨g, hg⟩
      rcases hirr.2.2 _ g α.1 hg.symm with h | h
      · exact C.toZChain.peak₁ (t + 1) ⟨pathVal v' ≫ inv g, by
          rw [← hv, ← hg, Category.assoc, IsIso.inv_hom_id_assoc]; rfl⟩
      · exact α.2.2.1 h
    exact B.lemma5a_rho_last hmin hL hR hQ hcont C (t + 1) hρ α β v' w' hv hw hni (key α v' hv)
      (key β w' hw)

include B in
/-- **BO13a Lemma 5 c)**: a crown with a long entry has a second, different long
entry. -/
theorem lemma5c
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (t₀ : ℕ) (h₀ : IsLong (C.f t₀).2.2) :
    ∃ t, IsLong (C.f t).2.2 ∧ C.f t ≠ C.f t₀ := by
  by_contra hno
  push Not at hno
  have hall : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → C.f t₀ = ⟨a, b, μ⟩ := by
    intro a b μ hμ
    obtain ⟨t, ht⟩ := B.long_entry hmin C μ hμ
    rw [← ht]
    exact (hno t (by rw [ht]; exact hμ)).symm
  have below : ∀ {x y : P} (f : x ⟶ y), f ≠ 0 → ¬IsIso f → ¬IsIrreducible f →
      FactorsThroughMorphism f (C.f t₀).2.2 := by
    intro x y f hf0 hfi hfr
    obtain ⟨_, _, μ, hμ, hfμ⟩ := exists_isLong_above hf0 hfi hfr
    rw [hall μ hμ]
    exact hfμ
  have hn := C.hn
  rcases Nat.even_or_odd t₀ with ⟨q, hq⟩ | ⟨q, hq⟩
  · obtain ⟨s, hs⟩ : ∃ s, s = q + C.n - 1 := ⟨_, rfl⟩
    have e : (⟨_, _, C.toZChain.ρ (s + 1)⟩ : RayMor P) = C.f t₀ := by
      rw [C.toZChain_ρ, hq, show 2 * (s + 1) = q + q + 2 * C.n * 1 by omega, C.f_add_mul]
    have hρ : IsLong (C.toZChain.ρ (s + 1)) := isLong_of_rayMor_eq e.symm h₀
    obtain ⟨h1, h2⟩ := B.ρ_nbr_red hmin hL hR hQ hcont C s hρ
    exact C.toZChain.not_le_both_ρ hQ s
      ⟨ftm_of_rayMor_eq e.symm (below _ (C.toZChain.σ_ne _) (C.toZChain.σ_not_isIso _) h1),
        ftm_of_rayMor_eq e.symm (below _ (C.toZChain.σ_ne _) (C.toZChain.σ_not_isIso _) h2)⟩
  · have e : (⟨_, _, C.toZChain.σ q⟩ : RayMor P) = C.f t₀ := by rw [C.toZChain_σ, hq]
    have hσ : IsLong (C.toZChain.σ q) := isLong_of_rayMor_eq e.symm h₀
    obtain ⟨h1, h2⟩ := B.σ_nbr_red hmin hL hR hQ hcont C q hσ
    exact C.toZChain.not_le_both_σ hQ q
      ⟨ftm_of_rayMor_eq e.symm (below _ (C.toZChain.ρ_ne _) (C.toZChain.ρ_not_isIso _) h2),
        ftm_of_rayMor_eq e.symm (below _ (C.toZChain.ρ_ne _) (C.toZChain.ρ_not_isIso _) h1)⟩

end MulBasis

end RayQuiver

end LargeIndecomposable
