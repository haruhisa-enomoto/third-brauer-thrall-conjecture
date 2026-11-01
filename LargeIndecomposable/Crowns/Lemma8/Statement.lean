module

public import LargeIndecomposable.Crowns.Lemma8.FinalStar

/-!
# BO13a Lemma 8: the factorization of a neighbour stops after one step

`MulBasis.lemma8`: in a minimal crown (every long morphism in a contour), let `σ₁` be long
with a contour `(v₁ v₂, w)` and `ρ₁ = v₁ ≫ ρ₁'`. Then `σ₂` does not factor as
`σ₂' ≫ ρ₁'`. The contour is permeable or reflecting by Lemma 5 a) (`l8_perm`,
`l8_claim`, `l8_refl`).
Reconstruction: `notes/2026-10-30-074207-bo13a-lemma8-reconstruction.md`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayQuiver

namespace MulBasis

/-- The representation-infinite thin categories used in BO13a Lemmas 7 and 8. -/
structure L8Shapes (k : Type u) [Field k] : Prop where
  f73 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F73.thin) k)
  f83 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F83.thin) k)
  f84 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F84.thin) k)
  f8r1d : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F8R1D.thin) k)
  f86 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F86.thin) k)
  f87 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F87.thin) k)
  f810 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810.thin) k)
  f810d : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810D.thin) k)

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 8.** -/
theorem lemma8
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (s : ℕ)
    (hσ : IsLong (C.toZChain.σ (s + 2)))
    {a : RayVert P} (v₁ : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) a)
    (v₂ : Quiver.Path a (RayVert.mk (C.toZChain.z (s + 2))))
    (w : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) (RayVert.mk (C.toZChain.z (s + 2))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = C.toZChain.σ (s + 2)) (hw : pathVal w = C.toZChain.σ (s + 2))
    (hni : ¬Interlaced (v₁.comp v₂) w)
    (ρ₁' : a.out ⟶ C.toZChain.z (s + 3)) (hρ₁' : pathVal v₁ ≫ ρ₁' = C.toZChain.ρ (s + 3))
    (σ₂' : C.toZChain.x (s + 4) ⟶ a.out) (hσ₂' : σ₂' ≫ ρ₁' = C.toZChain.σ (s + 3)) : False := by
  have hσ0 := hσ.1
  -- no long neighbours (Lemma 6)
  have nb1 : ∀ t, IsLong (C.toZChain.σ t) → IsLong (C.toZChain.ρ t) → False := fun t h1 h2 ↦
    B.lemma6 hmin hL hR hQ hcont C hC hS (2 * t) h2 (isLong_of_rayMor_eq (C.toZChain_σ t) h1)
  have nb2 : ∀ t, IsLong (C.toZChain.σ t) → IsLong (C.toZChain.ρ (t + 1)) → False :=
    fun t h1 h2 ↦ B.lemma6 hmin hL hR hQ hcont C hC hS (2 * t + 1)
      (isLong_of_rayMor_eq (C.toZChain_σ t) h1)
      (by rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring]; exact h2)
  have hρ₁l : ¬IsLong (C.toZChain.ρ (s + 3)) := fun h ↦ nb2 (s + 2) hσ h
  have hρnl : ¬IsLong (C.toZChain.ρ (s + 2)) := fun h ↦ nb1 (s + 2) hσ h
  -- crowns of length four do not exist (Lemma 7)
  have h4 : NoCrown4 P := by
    have h7 := B.lemma7 hmin hL hR hQ hcont C hC hS hS8.f73 _ hσ
    have h2 := Crown.two_le_n hQ C
    have hn3 : 2 < C.n := by omega
    intro a₀ a₁ b₀ b₁ f₀ f₁ f₂ f₃
    exact Crown.noCrown4 hC hn3
  -- a second long morphism (Lemma 5 c))
  obtain ⟨t, ht, hne⟩ := B.lemma5c hmin hL hR hQ hcont C (2 * (s + 2) + 1)
    (isLong_of_rayMor_eq (C.toZChain_σ (s + 2)) hσ)
  have hτσ : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, (C.f t).2.2⟩ := fun h ↦
    hne (by rw [← C.toZChain_σ]; exact h.symm)
  have hp1 : ¬∃ c, c ≫ C.toZChain.σ (s + 3) = C.toZChain.ρ (s + 3) := C.toZChain.peak₁ (s + 3)
  have hp2 : ¬∃ c, c ≫ C.toZChain.ρ (s + 3) = C.toZChain.σ (s + 3) := C.toZChain.peak₂ (s + 3)
  have hv1 : ¬∃ c, C.toZChain.σ (s + 2) ≫ c = C.toZChain.ρ (s + 3) := C.toZChain.valley₁ (s + 2)
  have hv2 : ¬∃ c, C.toZChain.ρ (s + 3) ≫ c = C.toZChain.σ (s + 2) := C.toZChain.valley₂ (s + 2)
  have hV : pathVal v₁ ≫ pathVal v₂ = C.toZChain.σ (s + 2) := by rw [← pathVal_comp]; exact hv
  -- `σ₂' ≫ v₂ = 0` (figure 2.1 at `a`)
  have hz : σ₂' ≫ pathVal v₂ = 0 := by
    by_contra h0
    refine no_fig21 hL hR h4 (pathVal v₁) σ₂' ρ₁' (pathVal v₂) ?_ ?_ ?_ ?_
      (by rw [hρ₁']; exact C.toZChain.ρ_ne _) (by rw [hσ₂']; exact C.toZChain.σ_ne _) h0
      (by rw [hV]; exact hσ0)
    · exact fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hσ₂', ← hg, ← hρ₁', Category.assoc]⟩
    · exact fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hσ₂', ← hρ₁', ← hg, Category.assoc]⟩
    · exact fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ₁', ← hV, Category.assoc, hg]⟩
    · exact fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hV, ← hρ₁', Category.assoc, hg]⟩
  -- permeable or reflecting (Lemma 5 a))
  obtain ⟨c, v₂', e, rfl⟩ := exists_last_arrow v₂ (not_isIso_pathVal v₂ hv₂)
  obtain ⟨b, w₁, ω, rfl⟩ := exists_last_arrow w (by rw [hw]; exact hσ.2.1)
  by_cases hω : ∃ g, g ≫ ω.1 = C.toZChain.ρ (s + 2)
  · -- permeable
    have hw₁ : 0 < w₁.length := by
      cases w₁ with
      | cons _ _ => simp
      | nil =>
        exfalso
        apply hσ.2.2.1
        rw [← hw]
        change IsIrreducible (𝟙 _ ≫ ω.1)
        rw [Category.id_comp]
        exact ω.2
    exact B.l8_perm hmin hL hR hQ hcont h4 C.toZChain s hσ hρ₁l hρnl
      (fun h ↦ ⟨fun h' ↦ nb2 (s + 3) h' h, fun h' ↦ nb1 (s + 4) h' h⟩) _ ht hτσ v₁
      (v₂'.cons e) w₁ ω hv₁ hv₂ hw₁ hv hw hni ρ₁' hρ₁' σ₂' hσ₂' hω hS8.f83 hS8.f84
  by_cases he : ∃ g, g ≫ e.1 = C.toZChain.ρ (s + 2)
  · -- reflecting
    obtain ⟨d, β, w', hβw⟩ := exists_first_arrow (w₁.cons ω) (by rw [hw]; exact hσ.2.1)
    rw [hβw] at hw hni
    obtain ⟨d₁, α, v₁', rfl⟩ := exists_first_arrow v₁ (not_isIso_pathVal v₁ hv₁)
    have hβρ : ¬∃ g, β.1 ≫ g = C.toZChain.ρ (s + 3) := by
      rintro ⟨g, hg⟩
      have hval : pathVal (α.toPath.comp (v₁'.comp (v₂'.cons e))) = C.toZChain.σ (s + 2) := by
        rw [← Quiver.Path.comp_assoc]; exact hv
      refine B.not_factors_both hmin hL hR α β (v₁'.comp (v₂'.cons e)) w' (by rw [hval, hw])
        (by rw [hval]; exact hσ0) (by rw [← Quiver.Path.comp_assoc]; exact hni)
        ⟨_, C.toZChain.ρ (s + 3)⟩ (C.toZChain.ρ_ne _)
        (fun ⟨c', hc'⟩ ↦ hv1 ⟨c', by rw [← hval]; exact hc'⟩)
        (fun ⟨c', hc'⟩ ↦ hv2 ⟨c', by rw [← hval]; exact hc'⟩) ⟨pathVal v₁' ≫ ρ₁', ?_⟩ ⟨g, hg⟩
      change α.1 ≫ pathVal v₁' ≫ ρ₁' = C.toZChain.ρ (s + 3)
      rw [← hρ₁', pathVal_comp, pathVal_toPath, Category.assoc]
    obtain ⟨r, hr⟩ := B.l8_claim hmin hL hR hQ hcont h4 C.toZChain s hσ hρ₁l hρnl _ ht hτσ
      (α.toPath.comp v₁') v₂' e β w' hv₁ hv hw hni hβρ ρ₁' hρ₁' σ₂' hσ₂' hz he hS8.f8r1d
    exact B.l8_refl hmin hL hR hQ hcont h4 C.toZChain s hσ hρ₁l hρnl
      (fun h ↦ ⟨fun h' ↦ nb1 (s + 1) h' h, fun h' ↦ nb2 s h' h⟩) _ ht hτσ (α.toPath.comp v₁')
      (v₂'.cons e) β w' hv₁ hv₂ hv hw hni hβρ ρ₁' hρ₁' σ₂' hσ₂' hz r hr hS8.f86 hS8.f87
      hS8.f810 hS8.f810d
  · exact B.lemma5a_last hmin hL hR hQ hcont C (s + 2) hσ e ω (v₁.comp v₂') w₁ hv hw hni he hω

end MulBasis

end RayQuiver

end LargeIndecomposable
