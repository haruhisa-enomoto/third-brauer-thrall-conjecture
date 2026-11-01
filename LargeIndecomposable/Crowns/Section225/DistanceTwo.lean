module

public import LargeIndecomposable.Crowns.Section225.ShorterCrown
public import LargeIndecomposable.Cleaving.Shapes.ShapeF93

/-!
# BO13a §2.2.5: two long entries are never at distance two

* `MulBasis.refl_contour`: a long entry `σ (s+2)` of a minimal crown has a contour `v` with
  `ρ (s+3)` through the first arrow and `ρ (s+2)` through the last arrow of `v`
  (Lemma 5 a) and `s225_perm`).
* `MulBasis.b1`: `σ (s+2)` and `σ (s+3)` are not both long (BO13a figures 9.2, 9.3: the
  `D̃₅` tree `F8R1A` in `P/τ`, `P/σ₁` or `P/σ₂`, or GR category 12 (`F93`) in `P/σ₁`).
  A gap in BO13a (the outs `v₂, ρ₁''` at `a`) is closed by a second contour of `σ₁` split at
  `c'` and Lemma 8.
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
/-- **A reflecting contour of a long `σ`-entry.** -/
theorem refl_contour
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (s : ℕ)
    (hσ : IsLong (C.toZChain.σ (s + 2))) :
    ∃ (b c : RayVert P) (α : RayVert.mk (C.toZChain.x (s + 3)) ⟶ b)
      (v' : Quiver.Path b (RayVert.mk (C.toZChain.z (s + 2))))
      (u : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) c)
      (ω : c ⟶ RayVert.mk (C.toZChain.z (s + 2)))
      (w : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) (RayVert.mk (C.toZChain.z (s + 2)))),
      α.toPath.comp v' = u.cons ω ∧ pathVal (α.toPath.comp v') = C.toZChain.σ (s + 2) ∧
        pathVal w = C.toZChain.σ (s + 2) ∧ ¬Interlaced (α.toPath.comp v') w ∧
          (∃ g, α.1 ≫ g = C.toZChain.ρ (s + 3)) ∧ ∃ g, g ≫ ω.1 = C.toZChain.ρ (s + 2) := by
  have hn := C.hn
  obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_first hσ (hcont _ hσ)
  have hnext : ∃ j, IsLong (C.toZChain.σ (s + 2 + 1 + j)) := ⟨C.n - 1, by
    have := C.isLong_σ_add (s + 2) hσ
    rwa [show s + 2 + 1 + (C.n - 1) = s + 2 + C.n by omega]⟩
  have key : ∀ {c' d' : RayVert P} (α' : RayVert.mk (C.toZChain.x (s + 3)) ⟶ c')
      (β' : RayVert.mk (C.toZChain.x (s + 3)) ⟶ d')
      (v'' : Quiver.Path c' (RayVert.mk (C.toZChain.z (s + 2))))
      (w'' : Quiver.Path d' (RayVert.mk (C.toZChain.z (s + 2)))),
      pathVal (α'.toPath.comp v'') = C.toZChain.σ (s + 2) →
      pathVal (β'.toPath.comp w'') = C.toZChain.σ (s + 2) →
      ¬Interlaced (α'.toPath.comp v'') (β'.toPath.comp w'') →
      (∃ g, α'.1 ≫ g = C.toZChain.ρ (s + 3)) →
      ∃ (b c : RayVert P) (α : RayVert.mk (C.toZChain.x (s + 3)) ⟶ b)
        (v' : Quiver.Path b (RayVert.mk (C.toZChain.z (s + 2))))
        (u : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) c)
        (ω : c ⟶ RayVert.mk (C.toZChain.z (s + 2)))
        (w : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) (RayVert.mk (C.toZChain.z (s + 2)))),
        α.toPath.comp v' = u.cons ω ∧ pathVal (α.toPath.comp v') = C.toZChain.σ (s + 2) ∧
          pathVal w = C.toZChain.σ (s + 2) ∧ ¬Interlaced (α.toPath.comp v') w ∧
            (∃ g, α.1 ≫ g = C.toZChain.ρ (s + 3)) ∧ ∃ g, g ≫ ω.1 = C.toZChain.ρ (s + 2) := by
    intro c' d' α' β' v'' w'' hv' hw' hni' hα'
    obtain ⟨c₁, u, ω, hu⟩ := exists_last_arrow (α'.toPath.comp v'') (by rw [hv']; exact hσ.2.1)
    obtain ⟨d₁, u', ω', hu'⟩ := exists_last_arrow (β'.toPath.comp w'') (by rw [hw']; exact hσ.2.1)
    by_cases hω : ∃ g, g ≫ ω.1 = C.toZChain.ρ (s + 2)
    · exact ⟨_, _, α', v'', u, ω, _, hu, hv', hw', hni', hα', hω⟩
    by_cases hω' : ∃ g, g ≫ ω'.1 = C.toZChain.ρ (s + 2)
    · exfalso
      exact B.s225_perm hmin hL hR hQ hcont C hC hS hS8 s hσ α' v'' u' ω' hv'
        (by rw [← hu']; exact hw') (by rw [← hu']; exact hni') hα' hω'
    · exfalso
      exact B.lemma5a_last hmin hL hR hQ hcont C (s + 2) hσ ω ω' u u'
        (by rw [← hu]; exact hv') (by rw [← hu']; exact hw') (by rw [← hu, ← hu']; exact hni')
        hω hω'
  by_cases hα : ∃ g, α.1 ≫ g = C.toZChain.ρ (s + 3)
  · exact key α β v' w' hv hw hni hα
  by_cases hβ : ∃ g, β.1 ≫ g = C.toZChain.ρ (s + 3)
  · exact key β α w' v' hw hv (fun h ↦ hni h.symm) hβ
  exact (B.lemma5a hmin hL hR hQ hcont C.toZChain (s + 2) hσ hnext α β v' w' hv hw hni hα
    hβ).elim

include B in
/-- **A reflecting contour of a long `ρ`-entry.** -/
theorem refl_contour_rho
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (t : ℕ)
    (hρ : IsLong (C.toZChain.ρ (t + 2))) :
    ∃ (b c : RayVert P) (α : RayVert.mk (C.toZChain.x (t + 2)) ⟶ b)
      (v' : Quiver.Path b (RayVert.mk (C.toZChain.z (t + 2))))
      (u : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) c)
      (ω : c ⟶ RayVert.mk (C.toZChain.z (t + 2)))
      (w : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) (RayVert.mk (C.toZChain.z (t + 2)))),
      α.toPath.comp v' = u.cons ω ∧ pathVal (α.toPath.comp v') = C.toZChain.ρ (t + 2) ∧
        pathVal w = C.toZChain.ρ (t + 2) ∧ ¬Interlaced (α.toPath.comp v') w ∧
          (∃ g, α.1 ≫ g = C.toZChain.σ (t + 1)) ∧ ∃ g, g ≫ ω.1 = C.toZChain.σ (t + 2) := by
  obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_first hρ (hcont _ hρ)
  have key : ∀ {c' d' : RayVert P} (α' : RayVert.mk (C.toZChain.x (t + 2)) ⟶ c')
      (β' : RayVert.mk (C.toZChain.x (t + 2)) ⟶ d')
      (v'' : Quiver.Path c' (RayVert.mk (C.toZChain.z (t + 2))))
      (w'' : Quiver.Path d' (RayVert.mk (C.toZChain.z (t + 2)))),
      pathVal (α'.toPath.comp v'') = C.toZChain.ρ (t + 2) →
      pathVal (β'.toPath.comp w'') = C.toZChain.ρ (t + 2) →
      ¬Interlaced (α'.toPath.comp v'') (β'.toPath.comp w'') →
      (∃ g, α'.1 ≫ g = C.toZChain.σ (t + 1)) →
      ∃ (b c : RayVert P) (α : RayVert.mk (C.toZChain.x (t + 2)) ⟶ b)
        (v' : Quiver.Path b (RayVert.mk (C.toZChain.z (t + 2))))
        (u : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) c)
        (ω : c ⟶ RayVert.mk (C.toZChain.z (t + 2)))
        (w : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) (RayVert.mk (C.toZChain.z (t + 2)))),
        α.toPath.comp v' = u.cons ω ∧ pathVal (α.toPath.comp v') = C.toZChain.ρ (t + 2) ∧
          pathVal w = C.toZChain.ρ (t + 2) ∧ ¬Interlaced (α.toPath.comp v') w ∧
            (∃ g, α.1 ≫ g = C.toZChain.σ (t + 1)) ∧ ∃ g, g ≫ ω.1 = C.toZChain.σ (t + 2) := by
    intro c' d' α' β' v'' w'' hv' hw' hni' hα'
    obtain ⟨c₁, u, ω, hu⟩ := exists_last_arrow (α'.toPath.comp v'') (by rw [hv']; exact hρ.2.1)
    obtain ⟨d₁, u', ω', hu'⟩ := exists_last_arrow (β'.toPath.comp w'') (by rw [hw']; exact hρ.2.1)
    by_cases hω : ∃ g, g ≫ ω.1 = C.toZChain.σ (t + 2)
    · exact ⟨_, _, α', v'', u, ω, _, hu, hv', hw', hni', hα', hω⟩
    by_cases hω' : ∃ g, g ≫ ω'.1 = C.toZChain.σ (t + 2)
    · exfalso
      exact B.s225_perm_rho hmin hL hR hQ hcont C hC hS hS8 t hρ α' v'' u' ω' hv'
        (by rw [← hu']; exact hw') (by rw [← hu']; exact hni') hα' hω'
    · exfalso
      exact B.lemma5a_rho_last hmin hL hR hQ hcont C (t + 2) hρ ω ω' u u'
        (by rw [← hu]; exact hv') (by rw [← hu']; exact hw') (by rw [← hu, ← hu']; exact hni')
        hω hω'
  by_cases hα : ∃ g, α.1 ≫ g = C.toZChain.σ (t + 1)
  · exact key α β v' w' hv hw hni hα
  by_cases hβ : ∃ g, β.1 ≫ g = C.toZChain.σ (t + 1)
  · exact key β α w' v' hw hv (fun h ↦ hni h.symm) hβ
  exact (B.lemma5a_rho_first hmin hL hR hQ hcont C (t + 1) hρ α β v' w' hv hw hni hα hβ).elim

include B in
/-- **BO13a §2.2.5: two long `σ`-entries are not at distance two.** -/
theorem b1
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k)
    (hD93 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F93.thin) k)) (s : ℕ)
    (hσ₁ : IsLong (C.toZChain.σ (s + 2))) (hσ₂ : IsLong (C.toZChain.σ (s + 3))) : False := by
  have hσ0 := hσ₁.1
  have hσ0' := hσ₂.1
  -- no long neighbours; no crowns of length four
  have nb1 : ∀ t, IsLong (C.toZChain.σ t) → IsLong (C.toZChain.ρ t) → False := fun t h1 h2 ↦
    B.lemma6 hmin hL hR hQ hcont C hC hS (2 * t) h2 (isLong_of_rayMor_eq (C.toZChain_σ t) h1)
  have nb2 : ∀ t, IsLong (C.toZChain.σ t) → IsLong (C.toZChain.ρ (t + 1)) → False :=
    fun t h1 h2 ↦ B.lemma6 hmin hL hR hQ hcont C hC hS (2 * t + 1)
      (isLong_of_rayMor_eq (C.toZChain_σ t) h1)
      (by rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring]; exact h2)
  have h4 : NoCrown4 P := by
    have h7 := B.lemma7 hmin hL hR hQ hcont C hC hS hS8.f73 _ hσ₁
    have h2 := Crown.two_le_n hQ C
    have hn3 : 2 < C.n := by omega
    intro a₀ a₁ b₀ b₁ f₀ f₁ f₂ f₃
    exact Crown.noCrown4 hC hn3
  have hρ₁l : ¬IsLong (C.toZChain.ρ (s + 3)) := fun h ↦ nb2 (s + 2) hσ₁ h
  have hρnl : ¬IsLong (C.toZChain.ρ (s + 2)) := fun h ↦ nb1 (s + 2) hσ₁ h
  have hρ₂l : ¬IsLong (C.toZChain.ρ (s + 4)) := fun h ↦ nb2 (s + 3) hσ₂ h
  have hρ₁0 := C.toZChain.ρ_ne (s + 3)
  have h12 : ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.σ (s + 3)) :=
    not_ftm_valley_peak hQ hσ₁ hρ₁0 hσ0' (C.toZChain.valley₁ (s + 2)) (C.toZChain.valley₂ (s + 2))
      (C.toZChain.peak₁ (s + 3)) (C.toZChain.peak₂ (s + 3))
  have h21 : ¬FactorsThroughMorphism (C.toZChain.σ (s + 3)) (C.toZChain.σ (s + 2)) := by
    intro h
    obtain ⟨hx, hy, he⟩ := hσ₂.2.2.2 _ hσ0 h
    exact h12 ⟨eqToHom hx.symm, eqToHom hy, by rw [he]; simp⟩
  have h13 : ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.σ (s + 4)) :=
    C.toZChain.not_ftm_σ_add_two h4 (s + 2) hσ₁
  -- the split of `σ₁` (longest prefix)
  obtain ⟨b, c, α, v', u, ω, w, hvu, hv, hw, hni, hα, hω⟩ :=
    B.refl_contour hmin hL hR hQ hcont C hC hS hS8 s hσ₁
  obtain ⟨a, v₁, v₂, ρ₁', r, e, hv₁, hv₂, hρ₁', hr, hz, d, e₁, p₂, hv₂e, hmax⟩ :=
    B.split_refl hmin hL hR h4 _ _ _ hσ₁ hρ₁l hρnl hρ₁0 (C.toZChain.ρ_ne _)
      (C.toZChain.valley₁ (s + 2)) (C.toZChain.valley₂ (s + 2)) (C.toZChain.peak₁ (s + 2))
      (C.toZChain.peak₂ (s + 2)) _ hσ₂ h21 α v' u ω hvu hv hα hω
  have hV : pathVal v₁ ≫ pathVal v₂ = C.toZChain.σ (s + 2) := by
    rw [← pathVal_comp, e, hv]
  have hni₁ : ¬Interlaced (v₁.comp v₂) w := by rw [e]; exact hni
  have hv₁₂ : pathVal (v₁.comp v₂) = C.toZChain.σ (s + 2) := by rw [e, hv]
  have hiV₁ := not_isIso_pathVal v₁ hv₁
  have hiV₂ := not_isIso_pathVal v₂ hv₂
  -- the split of `σ₂` (longest suffix)
  obtain ⟨b', c'', α', v'', u', ω', w', hvu', hv', hw', hni', hα', hω'⟩ :=
    B.refl_contour hmin hL hR hQ hcont C hC hS hS8 (s + 1) hσ₂
  obtain ⟨c', v₁', v₂', ρ₂', r', e', hv₁', hv₂', hρ₂', hr', hz', d', u₁', f', hv₁'e, hmax'⟩ :=
    B.split_refl_suf hmin hL hR h4 _ _ _ hσ₂ hρ₂l hρ₁l (C.toZChain.ρ_ne _) hρ₁0
      (C.toZChain.valley₁ (s + 3)) (C.toZChain.valley₂ (s + 3)) (C.toZChain.peak₁ (s + 3))
      (C.toZChain.peak₂ (s + 3)) _ hσ₁ h12 α' v'' u' ω' hvu' hv' hα' hω'
  have hV' : pathVal v₁' ≫ pathVal v₂' = C.toZChain.σ (s + 3) := by
    rw [← pathVal_comp, e', hv']
  have hni₂ : ¬Interlaced (v₁'.comp v₂') w' := by rw [e']; exact hni'
  have hv₁₂' : pathVal (v₁'.comp v₂') = C.toZChain.σ (s + 3) := by rw [e', hv']
  have hiV₁' := not_isIso_pathVal v₁' hv₁'
  have hiV₂' := not_isIso_pathVal v₂' hv₂'
  -- Lemma 8 at `σ₁` and at `σ₂`
  have L8a : ¬∃ c, c ≫ ρ₁' = C.toZChain.σ (s + 3) := fun ⟨c, hc⟩ ↦
    B.lemma8 hmin hL hR hQ hcont C hC hS hS8 s hσ₁ v₁ v₂ w hv₁ hv₂ hv₁₂ hw hni₁ ρ₁' hρ₁' c hc
  have L8b : ¬∃ c, c ≫ ρ₂' = C.toZChain.σ (s + 4) := fun ⟨c, hc⟩ ↦
    B.lemma8 hmin hL hR hQ hcont C hC hS hS8 (s + 1) hσ₂ v₁' v₂' w' hv₁' hv₂' hv₁₂' hw' hni₂
      ρ₂' hρ₂' c hc
  have hρ₂0 := C.toZChain.ρ_ne (s + 4)
  have hlam_ρ₁ : pathVal v₁ ≫ ρ₁' ≠ 0 := by rw [hρ₁']; exact hρ₁0
  have hval₁ : pathVal (v₁.comp v₂) = pathVal w := by rw [hv₁₂, hw]
  have hval₂ : pathVal (v₁'.comp v₂') = pathVal w' := by rw [hv₁₂', hw']
  by_cases hcase : ∃ ρ₁'', ρ₁'' ≫ pathVal v₂' = ρ₁'
  · -- case (a): `ρ₁' = ρ₁'' ≫ v₂'`
    obtain ⟨ρ₁'', hρ₁''⟩ := hcase
    have hiρ₁'' : ¬IsIso ρ₁'' := fun _ ↦ L8a ⟨pathVal v₁' ≫ inv ρ₁'', by
      rw [← hρ₁'', ← hV']; simp⟩
    have hρ₁''0 : ρ₁'' ≠ 0 := fun h ↦ hρ₁0 (by rw [← hρ₁', ← hρ₁'', h]; simp)
    -- BO13a's gap: `ρ₁'' ≫ g = v₂` gives a second contour of `σ₁` split at `c'`
    have hnc : ¬∃ g, ρ₁'' ≫ g = pathVal v₂ := by
      rintro ⟨g, hg⟩
      have hg0 : g ≠ 0 := fun h ↦ hσ0 (by rw [← hV, ← hg, h]; simp)
      have hgi : ¬IsIso g := fun _ ↦ C.toZChain.valley₁ (s + 2) ⟨inv g ≫ pathVal v₂', by
        rw [← hV, ← hρ₁', ← hρ₁'', ← hg]; simp⟩
      obtain ⟨p'', hp''⟩ := RayCat.exists_path ρ₁'' hρ₁''0
      obtain ⟨q'', hq''⟩ := RayCat.exists_path g hg0
      have hp0 := length_pos_of_not_isIso p'' (by rw [hp'']; exact hiρ₁'')
      have hq0 := length_pos_of_not_isIso q'' (by rw [hq'']; exact hgi)
      have hI : Interlaced (v₁.comp v₂) (v₁.comp (p''.comp q'')) :=
        Relation.EqvGen.rel _ _ (interStep_prefix v₁ hv₁ v₂ (p''.comp q'')
          (by rw [pathVal_comp p'' q'', hp'', hq'', hg]) (fun h ↦ hσ0 (by rw [← hV, h, comp_zero])))
      refine B.lemma8 hmin hL hR hQ hcont C hC hS hS8 s hσ₁ (v₁.comp p'') q'' w (by simp; omega)
        hq0 ?_ hw ?_ (pathVal v₂') ?_ (pathVal v₁') hV'
      · rw [Quiver.Path.comp_assoc, pathVal_comp v₁ (p''.comp q''), pathVal_comp p'' q'', hp'', hq'',
          hg, hV]
      · intro h
        rw [Quiver.Path.comp_assoc] at h
        exact hni₁ (Relation.EqvGen.trans _ _ _ hI h)
      · rw [pathVal_comp v₁ p'', hp'', Category.assoc, hρ₁'', hρ₁']
    -- the morphisms of the three trees
    have hρ₁'0 : ρ₁' ≠ 0 := fun h ↦ hρ₁0 (by rw [← hρ₁', h, comp_zero])
    have hiρ₁ : ¬IsIso (C.toZChain.ρ (s + 3)) := fun _ ↦ C.toZChain.valley₂ (s + 2)
      ⟨inv (C.toZChain.ρ (s + 3)) ≫ C.toZChain.σ (s + 2), by simp⟩
    have hrρ₁ : ¬IsIrreducible (C.toZChain.ρ (s + 3)) := fun h ↦ by
      rcases h.2.2 _ (pathVal v₁) ρ₁' hρ₁'.symm with h' | h'
      · exact hiV₁ h'
      · exact C.toZChain.valley₂ (s + 2) ⟨inv ρ₁' ≫ pathVal v₂, by
          rw [← hρ₁', ← hV]; simp⟩
    have hl1 : ¬∃ g, pathVal v₂ ≫ g = ρ₁'' := fun ⟨g, hg⟩ ↦ C.toZChain.valley₁ (s + 2)
      ⟨g ≫ pathVal v₂', by rw [← hV, Category.assoc, ← Category.assoc (pathVal v₂), hg, hρ₁'',
        hρ₁']⟩
    have hl2 : ¬∃ g, pathVal v₂ ≫ g = ρ₁'' ≫ pathVal v₂' := fun ⟨g, hg⟩ ↦
      C.toZChain.valley₁ (s + 2) ⟨g, by rw [← hV, Category.assoc, hg, hρ₁'', hρ₁']⟩
    have hr1 : ¬∃ g, g ≫ ρ₁'' = pathVal v₁' := fun ⟨g, hg⟩ ↦
      L8a ⟨g, by rw [← hρ₁'', ← Category.assoc, hg, hV']⟩
    have hr2 : ¬∃ g, g ≫ pathVal v₁' = ρ₁'' := fun ⟨g, hg⟩ ↦ C.toZChain.peak₁ (s + 3)
      ⟨pathVal v₁ ≫ g, by rw [Category.assoc, ← hV', ← Category.assoc g, hg, hρ₁'', hρ₁']⟩
    have hr3 : ¬∃ g, g ≫ pathVal v₁' = pathVal v₁ ≫ ρ₁'' := fun ⟨g, hg⟩ ↦
      C.toZChain.peak₁ (s + 3) ⟨g, by rw [← hV', ← Category.assoc, hg, Category.assoc, hρ₁'',
        hρ₁']⟩
    have hx0 : (pathVal v₁ ≫ ρ₁'') ≫ pathVal v₂' ≠ 0 := by
      rw [Category.assoc, hρ₁'', hρ₁']; exact hρ₁0
    have hA0 : ρ₁'' ≫ pathVal v₂' ≠ 0 := by rw [hρ₁'']; exact hρ₁'0
    obtain ⟨a₀, b₀, lam, hlam, hftm⟩ := exists_isLong_above hρ₁0 hiρ₁ hrρ₁
    by_cases hl₁ : FactorsThroughMorphism lam (C.toZChain.σ (s + 2))
    · -- `ρ₁ ≤ σ₁`: Lemma 4 c) splits `v₂`, the tree in `P/σ₁`
      obtain ⟨hx, hy, he⟩ := hlam.2.2.2 _ hσ0 hl₁
      obtain ⟨φ, ψ, hφψ⟩ := hftm
      obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR (C.toZChain.valley₂ (s + 2))
        (pathVal v₁) (pathVal v₂) ρ₁' hV hρ₁' (eqToHom hx ≫ φ) (ψ ≫ eqToHom hy.symm)
        (by rw [he, hφψ]; simp) hσ0
      have hp₂i : ¬IsIso (pathVal p₂) := by
        intro hi
        have hirr : IsIrreducible (pathVal v₂) := by
          rw [hv₂e, pathVal_comp, pathVal_toPath]; exact IsIrreducible.comp_isIso e₁.2 _
        rcases hirr.2.2 _ d₁ d₂ hd.symm with h | h
        · exact hd₁ h
        · exact hd₂ h
      obtain ⟨d₀, p₃, bb, rfl⟩ := exists_last_arrow p₂ hp₂i
      have hV₂A : pathVal v₂ = (e₁.1 ≫ pathVal p₃) ≫ bb.1 := by
        rw [hv₂e, pathVal_comp, pathVal_toPath]; simp; rfl
      have hiA : ¬IsIso (e₁.1 ≫ pathVal p₃) := by
        have := not_isIso_pathVal (e₁.toPath.comp p₃) (by simp)
        rwa [pathVal_comp, pathVal_toPath] at this
      have hAb0 : (e₁.1 ≫ pathVal p₃) ≫ bb.1 ≠ 0 := by
        rw [← hV₂A]; exact fun h ↦ hσ0 (by rw [← hV, h, comp_zero])
      exact B.not_f8r1a hmin hL hR _ hσ₁.2.1 hσ0 (pathVal v₁) ρ₁'' (pathVal v₂')
        (pathVal v₁') (e₁.1 ≫ pathVal p₃)
        (h0_a_c := not_ftm_prefix_of_long hσ₁ hiV₂' hA0)
        (h0_a_y₀ := by rw [hρ₁'']; exact not_ftm_suffix_of_long hσ₁ hiV₁ hlam_ρ₁)
        (h0_a_y₁ := not_ftm_prefix_of_long hσ₁ bb.2.2.1 hAb0)
        (h0_x_a := not_ftm_prefix_of_long hσ₁ hiV₂ (by rw [hV]; exact hσ0))
        (h0_x_c := not_ftm_prefix_of_long hσ₁ hiV₂' hx0)
        (h0_x_y₀ := by rw [Category.assoc, hρ₁'', hρ₁']
                       exact not_factorsThrough_of_not_isLong hσ₁ hρ₁0 hρ₁l)
        (h0_x_y₁ := not_ftm_prefix_of_long hσ₁ bb.2.2.1 (by
          rw [Category.assoc, ← hV₂A, hV]; exact hσ0))
        (h0_c_y₀ := not_ftm_suffix_of_long hσ₁ hiV₁' (by rw [hV']; exact hσ0'))
        (h0_xn_c := not_ftm_prefix_of_long hσ₁ hiV₂' (by rw [hV']; exact hσ0'))
        (h0_xn_y₀ := by rw [hV']; exact h12)
        (hi_V₁ := hiV₁) (hi_A := hiρ₁'') (hi_Bm := hiV₂') (hi_r := hiV₁') (hi_ρ₁' := hiA)
        (hl_A_ρ₁'_y₁ := fun ⟨g, hg⟩ ↦ hnc ⟨g ≫ bb.1, by rw [← Category.assoc, hg, hV₂A]⟩)
        (hl_ρ₁'_A_c := fun ⟨g, hg⟩ ↦ hmax ⟨pathVal p₃ ≫ g ≫ pathVal v₂', by
          rw [← hρ₁', ← hρ₁'', ← hg]; simp⟩)
        (hl_ρ₁'_A_y₀ := fun ⟨g, hg⟩ ↦ hmax ⟨pathVal p₃ ≫ g, by
          rw [← hρ₁', ← hρ₁'', ← hg]; simp⟩)
        (hr_A_r_xn := hr1) (hr_r_A_a := hr2) (hr_r_A_x := hr3)
    by_cases hl₂ : FactorsThroughMorphism lam (C.toZChain.σ (s + 3))
    · -- `ρ₁ ≤ σ₂`: Lemma 4 c), dual, splits `v₁'`, the tree in `P/σ₂`
      obtain ⟨hx, hy, he⟩ := hlam.2.2.2 _ hσ0' hl₂
      obtain ⟨φ, ψ, hφψ⟩ := hftm
      obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c_dual hQ hL (C.toZChain.peak₂ (s + 3))
        (pathVal v₂') (pathVal v₁') r' hV' hr' (ψ ≫ eqToHom hy.symm) (eqToHom hx ≫ φ)
        (by rw [he, hφψ]; simp) hσ0'
      have hu₁i : ¬IsIso (pathVal u₁') := by
        intro hi
        have hirr : IsIrreducible (pathVal v₁') := by
          rw [hv₁'e]; exact IsIrreducible.isIso_comp f'.2 _
        rcases hirr.2.2 _ d₁ d₂ hd.symm with h | h
        · exact hd₁ h
        · exact hd₂ h
      obtain ⟨d₀, b'', u₃, rfl⟩ := exists_first_arrow u₁' hu₁i
      have hV₁'A : pathVal v₁' = b''.1 ≫ (pathVal u₃ ≫ f'.1) := by
        rw [hv₁'e]; change pathVal (b''.toPath.comp u₃) ≫ f'.1 = _
        rw [pathVal_comp, pathVal_toPath, Category.assoc]
      have hiA' : ¬IsIso (pathVal u₃ ≫ f'.1) := by
        have := not_isIso_pathVal (u₃.cons f') (by simp)
        exact this
      have hA'0 : (pathVal u₃ ≫ f'.1) ≫ pathVal v₂' ≠ 0 := fun h ↦ hσ0' (by
        rw [← hV', hV₁'A, Category.assoc, h, comp_zero])
      exact B.not_f8r1a hmin hL hR _ hσ₂.2.1 hσ0' (pathVal v₁) ρ₁'' (pathVal v₂')
        (pathVal u₃ ≫ f'.1) (pathVal v₂)
        (h0_a_c := not_ftm_prefix_of_long hσ₂ hiV₂' hA0)
        (h0_a_y₀ := by rw [hρ₁'']; exact not_ftm_suffix_of_long hσ₂ hiV₁ hlam_ρ₁)
        (h0_a_y₁ := not_ftm_suffix_of_long hσ₂ hiV₁ (by rw [hV]; exact hσ0))
        (h0_x_a := not_ftm_prefix_of_long hσ₂ hiV₂ (by rw [hV]; exact hσ0))
        (h0_x_c := not_ftm_prefix_of_long hσ₂ hiV₂' hx0)
        (h0_x_y₀ := by rw [Category.assoc, hρ₁'', hρ₁']
                       exact not_factorsThrough_of_not_isLong hσ₂ hρ₁0 hρ₁l)
        (h0_x_y₁ := by rw [hV]; exact h21)
        (h0_c_y₀ := not_ftm_suffix_of_long hσ₂ hiV₁' (by rw [hV']; exact hσ0'))
        (h0_xn_c := not_ftm_prefix_of_long hσ₂ hiV₂' hA'0)
        (h0_xn_y₀ := not_ftm_suffix_of_long hσ₂ b''.2.2.1 (by
          rw [← Category.assoc, ← hV₁'A, hV']; exact hσ0'))
        (hi_V₁ := hiV₁) (hi_A := hiρ₁'') (hi_Bm := hiV₂') (hi_r := hiA') (hi_ρ₁' := hiV₂)
        (hl_A_ρ₁'_y₁ := hnc) (hl_ρ₁'_A_c := hl1) (hl_ρ₁'_A_y₀ := hl2)
        (hr_A_r_xn := fun ⟨g, hg⟩ ↦ L8a ⟨b''.1 ≫ g, by
          rw [← hρ₁'', ← hV', hV₁'A, ← hg]; simp⟩)
        (hr_r_A_a := fun ⟨g, hg⟩ ↦ hmax' ⟨pathVal v₁ ≫ g ≫ pathVal u₃, by
          rw [← hρ₁', ← hρ₁'', ← hg]; simp⟩)
        (hr_r_A_x := fun ⟨g, hg⟩ ↦ hmax' ⟨g ≫ pathVal u₃, by
          rw [← hρ₁', ← hρ₁'', ← Category.assoc (pathVal v₁), ← hg]; simp⟩)
    · -- a third long morphism
      have hτ1 : ¬FactorsThroughMorphism lam (pathVal v₁ ≫ pathVal v₂) := by rw [hV]; exact hl₁
      have hτ2 : ¬FactorsThroughMorphism lam (pathVal v₁' ≫ pathVal v₂') := by rw [hV']; exact hl₂
      exact B.not_f8r1a hmin hL hR lam hlam.2.1 hlam.1 (pathVal v₁) ρ₁'' (pathVal v₂')
        (pathVal v₁') (pathVal v₂)
        (h0_a_c := not_ftm_prefix_of_long hlam hiV₂' hA0)
        (h0_a_y₀ := by rw [hρ₁'']; exact not_ftm_suffix_of_long hlam hiV₁ hlam_ρ₁)
        (h0_a_y₁ := not_ftm_suffix_of_long hlam hiV₁ (by rw [hV]; exact hσ0))
        (h0_x_a := not_ftm_prefix_of_long hlam hiV₂ (by rw [hV]; exact hσ0))
        (h0_x_c := not_ftm_prefix_of_long hlam hiV₂' hx0)
        (h0_x_y₀ := by rw [Category.assoc, hρ₁'', hρ₁']
                       exact not_factorsThrough_of_not_isLong hlam hρ₁0 hρ₁l)
        (h0_x_y₁ := hτ1)
        (h0_c_y₀ := not_ftm_suffix_of_long hlam hiV₁' (by rw [hV']; exact hσ0'))
        (h0_xn_c := not_ftm_prefix_of_long hlam hiV₂' (by rw [hV']; exact hσ0'))
        (h0_xn_y₀ := hτ2)
        (hi_V₁ := hiV₁) (hi_A := hiρ₁'') (hi_Bm := hiV₂') (hi_r := hiV₁') (hi_ρ₁' := hiV₂)
        (hl_A_ρ₁'_y₁ := hnc) (hl_ρ₁'_A_c := hl1) (hl_ρ₁'_A_y₀ := hl2)
        (hr_A_r_xn := hr1) (hr_r_A_a := hr2) (hr_r_A_x := hr3)
  · -- case (b): GR category 12 (figure 9.3) in `P/σ₁`
    obtain ⟨d₂, β', w'', hw'e⟩ := exists_first_arrow w' (by rw [hw']; exact hσ₂.2.1)
    have hw''0 : 0 < w''.length := by
      cases w'' with
      | cons _ _ => simp
      | nil =>
        exfalso
        apply hσ₂.2.2.1
        rw [← hw', hw'e, Quiver.Path.comp_nil, pathVal_toPath]
        exact β'.2
    have hval₂' : pathVal (v₁'.comp v₂') = pathVal (β'.toPath.comp w'') := by rw [← hw'e]; exact hval₂
    have h0₂ : pathVal (v₁'.comp v₂') ≠ 0 := by rw [hv₁₂']; exact hσ0'
    have hni₂' : ¬Interlaced (v₁'.comp v₂') (β'.toPath.comp w'') := by rw [← hw'e]; exact hni₂
    have hW : β'.1 ≫ pathVal w'' = C.toZChain.σ (s + 3) := by
      rw [← hw', hw'e, pathVal_comp, pathVal_toPath]
    have hx₂bc : ¬∃ g, β'.1 ≫ g = pathVal v₁' := by
      have := prefix_cross hL hR _ _ hval₂'.symm (by rw [← hval₂']; exact h0₂)
        (fun h ↦ hni₂' h.symm) β'.toPath w'' v₁' v₂' rfl rfl (by simp) hv₂'
      simpa only [pathVal_toPath] using this
    have hx₂cb : ¬∃ g, pathVal v₁' ≫ g = β'.1 := by
      have := prefix_cross hL hR _ _ hval₂' h0₂ hni₂' v₁' v₂' β'.toPath w'' rfl rfl hv₁' hw''0
      simpa only [pathVal_toPath] using this
    have hcb := (contour_cross hL hR v₁' v₂' β'.toPath w'' hval₂' h0₂ hni₂' hv₁' hw''0).1
    have hbc := (contour_cross hL hR β'.toPath w'' v₁' v₂' hval₂'.symm (by rw [← hval₂']; exact h0₂)
      (fun h ↦ hni₂' h.symm) (by simp) hv₂').1
    -- `ρ₂` does not factor through `β'` (Lemma 4 b))
    have hx₂by₂ : ¬∃ g, β'.1 ≫ g = pathVal v₁' ≫ ρ₂' := by
      rintro ⟨g, hg⟩
      obtain ⟨c₁, α'', v₃, rfl⟩ := exists_first_arrow v₁' hiV₁'
      have ev : (α''.toPath.comp v₃).comp v₂' = α''.toPath.comp (v₃.comp v₂') :=
        Quiver.Path.comp_assoc _ _ _
      refine B.not_factors_both hmin hL hR α'' β' (v₃.comp v₂') w''
        (by rw [← ev]; exact hval₂') (by rw [← ev]; exact h0₂) (by rw [← ev]; exact hni₂')
        ⟨_, C.toZChain.ρ (s + 4)⟩ hρ₂0
        (fun ⟨c', hc'⟩ ↦ C.toZChain.valley₁ (s + 3) ⟨c', by rw [← hv₁₂', ev]; exact hc'⟩)
        (fun ⟨c', hc'⟩ ↦ C.toZChain.valley₂ (s + 3) ⟨c', by rw [← hv₁₂', ev]; exact hc'⟩)
        ⟨pathVal v₃ ≫ ρ₂', ?_⟩ ⟨g, ?_⟩
      · change α''.1 ≫ pathVal v₃ ≫ ρ₂' = C.toZChain.ρ (s + 4)
        rw [← hρ₂', pathVal_comp, pathVal_toPath, Category.assoc]
      · change β'.1 ≫ g = C.toZChain.ρ (s + 4)
        rw [hg, hρ₂']
    -- `ρ₁` does not factor through the last arrow of `w'` (Lemma 4 b), last arrows)
    have hab : ¬∃ g, g ≫ pathVal w'' = ρ₁' := by
      rintro ⟨g, hg⟩
      obtain ⟨c₁, v₀, l, rfl⟩ := exists_last_arrow v₂' hiV₂'
      obtain ⟨c₂, w₀, l', rfl⟩ := exists_last_arrow w'' (not_isIso_pathVal _ hw''0)
      refine B.not_factors_both_last hmin hL hR l l' (v₁'.comp v₀) (β'.toPath.comp w₀)
        hval₂' h0₂ hni₂' (C.toZChain.ρ (s + 3)) hρ₁0
        (fun ⟨c', hc'⟩ ↦ C.toZChain.peak₁ (s + 3) ⟨c', by rw [← hv₁₂']; exact hc'⟩)
        (fun ⟨c', hc'⟩ ↦ C.toZChain.peak₂ (s + 3) ⟨c', by rw [← hv₁₂']; exact hc'⟩)
        ⟨r' ≫ pathVal v₀, ?_⟩ ⟨pathVal v₁ ≫ g ≫ pathVal w₀, ?_⟩
      · rw [← hr', Category.assoc]; rfl
      · rw [← hρ₁', ← hg, Category.assoc, Category.assoc]; rfl
    exact B.not_f93 hmin hL hR _ hσ₁.2.1 hσ0 (pathVal v₂) ρ₁' (pathVal v₁') β'.1 (pathVal v₂')
      (pathVal w'') ρ₂' (C.toZChain.σ (s + 4)) hD93 (by rw [hW, hV'])
      (h0_a_y₀ := not_ftm_suffix_of_long hσ₁ hiV₁ (by rw [hV]; exact hσ0))
      (h0_a_y₁ := not_ftm_suffix_of_long hσ₁ hiV₁ hlam_ρ₁)
      (h0_b'_y₁ := not_ftm_suffix_of_long hσ₁ β'.2.2.1 (by rw [hW]; exact hσ0'))
      (h0_c'_y₁ := not_ftm_suffix_of_long hσ₁ hiV₁' (by rw [hV']; exact hσ0'))
      (h0_c'_y₂ := not_ftm_suffix_of_long hσ₁ hiV₁' (by rw [hρ₂']; exact hρ₂0))
      (h0_x₂_b' := not_ftm_prefix_of_long hσ₁ (not_isIso_pathVal _ hw''0) (by
        rw [hW]; exact hσ0'))
      (h0_x₂_c' := not_ftm_prefix_of_long hσ₁ hiV₂' (by rw [hV']; exact hσ0'))
      (h0_x₂_y₁ := by rw [hV']; exact h12)
      (h0_x₂_y₂ := by rw [hρ₂']; exact not_factorsThrough_of_not_isLong hσ₁ hρ₂0 hρ₂l)
      (h0_x₃_y₂ := h13)
      (hi_V₂ := hiV₂)
      (hi_ρ₁' := fun _ ↦ C.toZChain.valley₂ (s + 2) ⟨inv ρ₁' ≫ pathVal v₂, by
        rw [← hρ₁', ← hV]; simp⟩)
      (hi_V₁' := hiV₁') (hi_W₁' := β'.2.2.1) (hi_V₂' := hiV₂')
      (hi_W₂' := not_isIso_pathVal _ hw''0)
      (hi_ρ₂' := fun _ ↦ C.toZChain.valley₂ (s + 3) ⟨inv ρ₂' ≫ pathVal v₂', by
        rw [← hρ₂', ← hV']; simp⟩)
      (hi_σ₃ := C.toZChain.σ_not_isIso _)
      (hlft_a_y₀_y₁ := fun ⟨g, hg⟩ ↦ C.toZChain.valley₁ (s + 2)
        ⟨g, by rw [← hV, Category.assoc, hg, hρ₁']⟩)
      (hlft_a_y₁_y₀ := fun ⟨g, hg⟩ ↦ C.toZChain.valley₂ (s + 2)
        ⟨g, by rw [← hρ₁', Category.assoc, hg, hV]⟩)
      (hlft_c'_y₁_y₂ := fun ⟨g, hg⟩ ↦ C.toZChain.valley₁ (s + 3)
        ⟨g, by rw [← hV', Category.assoc, hg, hρ₂']⟩)
      (hlft_c'_y₂_y₁ := fun ⟨g, hg⟩ ↦ C.toZChain.valley₂ (s + 3)
        ⟨g, by rw [← hρ₂', Category.assoc, hg, hV']⟩)
      (hlft_x₂_b'_c' := hx₂bc) (hlft_x₂_b'_y₂ := hx₂by₂) (hlft_x₂_c'_b' := hx₂cb)
      (hrgt_x₂_a_y₁ := by rw [hV']; exact L8a)
      (hrgt_c'_a_y₁ := fun ⟨g, hg⟩ ↦ L8a ⟨pathVal v₁' ≫ g, by rw [Category.assoc, hg, hV']⟩)
      (hrgt_b'_a_y₁ := fun ⟨g, hg⟩ ↦ L8a ⟨β'.1 ≫ g, by rw [Category.assoc, hg, hW]⟩)
      (hrgt_a_b'_y₁ := hab) (hrgt_c'_b'_y₁ := hcb) (hrgt_a_c'_y₁ := fun ⟨g, hg⟩ ↦ hcase ⟨g, hg⟩)
      (hrgt_b'_c'_y₁ := hbc) (hrgt_x₃_c'_y₂ := L8b)
      (hrgt_x₂_x₃_y₂ := by rw [hρ₂']; exact C.toZChain.peak₁ (s + 4))
      (hrgt_c'_x₃_y₂ := fun ⟨g, hg⟩ ↦ C.toZChain.peak₁ (s + 4)
        ⟨pathVal v₁' ≫ g, by rw [Category.assoc, hg, hρ₂']⟩)


end MulBasis

end RayQuiver

end LargeIndecomposable
