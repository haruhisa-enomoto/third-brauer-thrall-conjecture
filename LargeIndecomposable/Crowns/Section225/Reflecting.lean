module

public import LargeIndecomposable.Crowns.Basic.CrownGen

/-!
# BO13a §2.2.5, first step: contours of long entries are reflecting

`MulBasis.s225_perm`: in a minimal crown (every long morphism in a contour), if `ρ₁`
factors through the first arrow of one path of a contour of a long `σ₁` and `ρₙ`
through the last arrow of the other path, then replacing `σ₁, ρ₁` by `v₂, ρ₁'` gives a
crown of the same length and smaller weight (BO13a figure 9.1; Lemma 8 gives the peak
`ρ₁', σ₂`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a §2.2.5, permeable contours** do not occur. -/
theorem s225_perm
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (s : ℕ)
    (hσ : IsLong (C.toZChain.σ (s + 2))) {a b : RayVert P}
    (α : RayVert.mk (C.toZChain.x (s + 3)) ⟶ a) (v' : Quiver.Path a (RayVert.mk (C.toZChain.z (s + 2))))
    (w₁ : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) b) (ω : b ⟶ RayVert.mk (C.toZChain.z (s + 2)))
    (hv : pathVal (α.toPath.comp v') = C.toZChain.σ (s + 2))
    (hw : pathVal (w₁.cons ω) = C.toZChain.σ (s + 2))
    (hni : ¬Interlaced (α.toPath.comp v') (w₁.cons ω))
    (hα : ∃ g, α.1 ≫ g = C.toZChain.ρ (s + 3)) (hω : ∃ g, g ≫ ω.1 = C.toZChain.ρ (s + 2)) :
    False := by
  obtain ⟨g, hg⟩ := hα
  have hσ0 := hσ.1
  have hV : α.1 ≫ pathVal v' = C.toZChain.σ (s + 2) := by
    rw [← hv, pathVal_comp, pathVal_toPath]
  have hv'0 : 0 < v'.length := by
    cases v' with
    | cons _ _ => simp
    | nil =>
      exfalso
      apply hσ.2.2.1
      rw [← hV]
      change IsIrreducible (α.1 ≫ 𝟙 _)
      rw [Category.comp_id]
      exact α.2
  -- the peak `ρ₁', σ₂` (Lemma 8)
  have h8 : ¬∃ c, c ≫ g = C.toZChain.σ (s + 3) := fun ⟨σ₂', hσ₂'⟩ ↦
    B.lemma8 hmin hL hR hQ hcont C hC hS hS8 s hσ α.toPath v' (w₁.cons ω) (by simp) hv'0 hv hw hni
      g (by rw [pathVal_toPath]; exact hg) σ₂' hσ₂'
  -- `ρₙ` does not factor through `v'` (Lemma 4 b), last arrows)
  have hρv : ¬∃ c, c ≫ pathVal v' = C.toZChain.ρ (s + 2) := by
    rintro ⟨c, hc⟩
    obtain ⟨d, v'', l, rfl⟩ := exists_last_arrow v' (not_isIso_pathVal _ hv'0)
    have h0 : pathVal ((α.toPath.comp v'').cons l) ≠ 0 := by
      change pathVal (α.toPath.comp (v''.cons l)) ≠ 0
      rw [hv]; exact hσ0
    refine B.not_factors_both_last hmin hL hR l ω (α.toPath.comp v'') w₁
      (by rw [hw]; exact hv) h0 hni _ (C.toZChain.ρ_ne _)
      (fun ⟨c', hc'⟩ ↦ C.toZChain.peak₁ (s + 2) ⟨c', by rw [← hv]; exact hc'⟩)
      (fun ⟨c', hc'⟩ ↦ C.toZChain.peak₂ (s + 2) ⟨c', by rw [← hv]; exact hc'⟩)
      ⟨c ≫ pathVal v'', by rw [Category.assoc, ← hc]; rfl⟩ hω
  have hn2 := Crown.two_le_n hQ C
  have h1 : Peak (C.f (2 * (s + 2))) ⟨_, _, pathVal v'⟩ :=
    (peak_mk_iff (C.toZChain.ρ (s + 2)) (pathVal v')).2
      ⟨hρv, fun ⟨c, hc⟩ ↦ C.toZChain.peak₂ (s + 2) ⟨α.1 ≫ c, by rw [Category.assoc, hc, hV]⟩⟩
  have h2 : Valley (⟨_, _, pathVal v'⟩ : RayMor P) ⟨_, _, g⟩ :=
    (valley_mk_iff (pathVal v') g).2
      ⟨fun ⟨c, hc⟩ ↦ C.toZChain.valley₁ (s + 2) ⟨c, by rw [← hV, Category.assoc, hc, hg]⟩,
        fun ⟨c, hc⟩ ↦ C.toZChain.valley₂ (s + 2) ⟨c, by rw [← hg, Category.assoc, hc, hV]⟩⟩
  have h3 : Peak (⟨_, _, g⟩ : RayMor P) (C.f (2 * (s + 2) + 3)) := by
    rw [show 2 * (s + 2) + 3 = 2 * (s + 3) + 1 by ring, ← C.toZChain_σ]
    exact (peak_mk_iff g (C.toZChain.σ (s + 3))).2
      ⟨fun ⟨c, hc⟩ ↦ C.toZChain.peak₁ (s + 3) ⟨α.1 ≫ c, by rw [Category.assoc, hc, hg]⟩, h8⟩
  have h01 : pathVal v' ≠ 0 := fun h ↦ hσ0 (by rw [← hV, h, comp_zero])
  have h02 : g ≠ 0 := fun h ↦ C.toZChain.ρ_ne (s + 3) (by rw [← hg, h, comp_zero])
  have hw' := C.weight_replace hn2 (s + 2) _ _ h1 h2 h3 h01 h02
  have hmin' := hC (C.replace hn2 (s + 2) _ _ h1 h2 h3 h01 h02)
  have e1 : depth (C.f (2 * (s + 2) + 1)).2.2 = depth (C.toZChain.σ (s + 2)) :=
    (depth_of_rayMor_eq (C.toZChain_σ (s + 2))).symm
  have e2 : depth (C.f (2 * (s + 2) + 2)).2.2 = depth (C.toZChain.ρ (s + 3)) := by
    rw [show 2 * (s + 2) + 2 = 2 * (s + 3) by ring]; rfl
  have d1 := depth_add_le α.1 (pathVal v') (by rw [hV]; exact hσ0)
  have d2 := depth_add_le α.1 g (by rw [hg]; exact C.toZChain.ρ_ne _)
  have d0 := one_le_depth (α.2.1) α.2.2.1
  rw [hV] at d1
  rw [hg] at d2
  simp only at hw'
  rw [e1, e2] at hw'
  rcases hmin' with h | h
  · exact absurd h (lt_irrefl _)
  · have h' := h.2
    omega

end MulBasis

end RayQuiver

end LargeIndecomposable
