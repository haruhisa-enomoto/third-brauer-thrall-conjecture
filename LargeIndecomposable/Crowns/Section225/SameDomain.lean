module

public import LargeIndecomposable.Crowns.Section225.DistanceTwo

/-!
# BO13a §2.2.5: all long morphisms have the same domain

* Index-generic forms (`_at`) of the reflecting contours and of Lemma 8.
* `MulBasis.dom_b2`, `MulBasis.dom_b3`: for consecutive long entries `σ (s+2)` and
  `ρ (s+3+L+1)` (resp. `σ (s+3+L+1)`), every long morphism has the domain of `σ (s+2)`.
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

section At

variable (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
  (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
  (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
  (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k)

include B hmin hL hR hQ hcont hC hS hS8

theorem refl_contour_at (q : ℕ) (hq : 2 ≤ q) (hσ : IsLong (C.toZChain.σ q)) :
    ∃ (b c : RayVert P) (α : RayVert.mk (C.toZChain.x (q + 1)) ⟶ b)
      (v' : Quiver.Path b (RayVert.mk (C.toZChain.z q)))
      (u : Quiver.Path (RayVert.mk (C.toZChain.x (q + 1))) c)
      (ω : c ⟶ RayVert.mk (C.toZChain.z q))
      (w : Quiver.Path (RayVert.mk (C.toZChain.x (q + 1))) (RayVert.mk (C.toZChain.z q))),
      α.toPath.comp v' = u.cons ω ∧ pathVal (α.toPath.comp v') = C.toZChain.σ q ∧
        pathVal w = C.toZChain.σ q ∧ ¬Interlaced (α.toPath.comp v') w ∧
          (∃ g, α.1 ≫ g = C.toZChain.ρ (q + 1)) ∧ ∃ g, g ≫ ω.1 = C.toZChain.ρ q := by
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 2 := ⟨q - 2, by omega⟩
  exact B.refl_contour hmin hL hR hQ hcont C hC hS hS8 s hσ

theorem refl_contour_rho_at (p : ℕ) (hp : 1 ≤ p) (hρ : IsLong (C.toZChain.ρ (p + 1))) :
    ∃ (b c : RayVert P) (α : RayVert.mk (C.toZChain.x (p + 1)) ⟶ b)
      (v' : Quiver.Path b (RayVert.mk (C.toZChain.z (p + 1))))
      (u : Quiver.Path (RayVert.mk (C.toZChain.x (p + 1))) c)
      (ω : c ⟶ RayVert.mk (C.toZChain.z (p + 1)))
      (w : Quiver.Path (RayVert.mk (C.toZChain.x (p + 1))) (RayVert.mk (C.toZChain.z (p + 1)))),
      α.toPath.comp v' = u.cons ω ∧ pathVal (α.toPath.comp v') = C.toZChain.ρ (p + 1) ∧
        pathVal w = C.toZChain.ρ (p + 1) ∧ ¬Interlaced (α.toPath.comp v') w ∧
          (∃ g, α.1 ≫ g = C.toZChain.σ p) ∧ ∃ g, g ≫ ω.1 = C.toZChain.σ (p + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 1 := ⟨p - 1, by omega⟩
  exact B.refl_contour_rho hmin hL hR hQ hcont C hC hS hS8 t hρ

theorem lemma8_at (q : ℕ) (hq : 2 ≤ q) (hσ : IsLong (C.toZChain.σ q)) {a : RayVert P}
    (v₁ : Quiver.Path (RayVert.mk (C.toZChain.x (q + 1))) a)
    (v₂ : Quiver.Path a (RayVert.mk (C.toZChain.z q)))
    (w : Quiver.Path (RayVert.mk (C.toZChain.x (q + 1))) (RayVert.mk (C.toZChain.z q)))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = C.toZChain.σ q) (hw : pathVal w = C.toZChain.σ q)
    (hni : ¬Interlaced (v₁.comp v₂) w)
    (ρ₁' : a.out ⟶ C.toZChain.z (q + 1)) (hρ₁' : pathVal v₁ ≫ ρ₁' = C.toZChain.ρ (q + 1))
    (σ₂' : C.toZChain.x (q + 2) ⟶ a.out) (hσ₂' : σ₂' ≫ ρ₁' = C.toZChain.σ (q + 1)) : False := by
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 2 := ⟨q - 2, by omega⟩
  exact B.lemma8 hmin hL hR hQ hcont C hC hS hS8 s hσ v₁ v₂ w hv₁ hv₂ hv hw hni ρ₁' hρ₁' σ₂' hσ₂'

theorem lemma8_peak_at (p : ℕ) (hp : 1 ≤ p) (hσ : IsLong (C.toZChain.σ (p + 1)))
    {a : RayVert P} (v₁ : Quiver.Path (RayVert.mk (C.toZChain.x (p + 1 + 1))) a)
    (v₂ : Quiver.Path a (RayVert.mk (C.toZChain.z (p + 1))))
    (w : Quiver.Path (RayVert.mk (C.toZChain.x (p + 1 + 1))) (RayVert.mk (C.toZChain.z (p + 1))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = C.toZChain.σ (p + 1)) (hw : pathVal w = C.toZChain.σ (p + 1))
    (hni : ¬Interlaced (v₁.comp v₂) w)
    (r : C.toZChain.x (p + 1) ⟶ a.out) (hr : r ≫ pathVal v₂ = C.toZChain.ρ (p + 1))
    (c : a.out ⟶ C.toZChain.z p) (hc : r ≫ c = C.toZChain.σ p) : False := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  exact B.lemma8_peak hmin hL hR hQ hcont C hC hS hS8 s hσ v₁ v₂ w hv₁ hv₂ hv hw hni r hr c hc

theorem lemma8_rho_at (p : ℕ) (hp : 1 ≤ p) (hρ : IsLong (C.toZChain.ρ (p + 1)))
    {a : RayVert P} (v₁ : Quiver.Path (RayVert.mk (C.toZChain.x (p + 1))) a)
    (v₂ : Quiver.Path a (RayVert.mk (C.toZChain.z (p + 1))))
    (w : Quiver.Path (RayVert.mk (C.toZChain.x (p + 1))) (RayVert.mk (C.toZChain.z (p + 1))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = C.toZChain.ρ (p + 1)) (hw : pathVal w = C.toZChain.ρ (p + 1))
    (hni : ¬Interlaced (v₁.comp v₂) w)
    (ρ' : a.out ⟶ C.toZChain.z p) (hρ' : pathVal v₁ ≫ ρ' = C.toZChain.σ p)
    (σ' : C.toZChain.x p ⟶ a.out) (hσ' : σ' ≫ ρ' = C.toZChain.ρ p) : False := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 1 := ⟨p - 1, by omega⟩
  exact B.lemma8_rho hmin hL hR hQ hcont C hC hS hS8 t hρ v₁ v₂ w hv₁ hv₂ hv hw hni ρ' hρ' σ' hσ'

theorem lemma8_rho_peak_at (p : ℕ) (hp : 1 ≤ p) (hρ : IsLong (C.toZChain.ρ (p + 1)))
    {a : RayVert P} (v₁ : Quiver.Path (RayVert.mk (C.toZChain.x (p + 1))) a)
    (v₂ : Quiver.Path a (RayVert.mk (C.toZChain.z (p + 1))))
    (w : Quiver.Path (RayVert.mk (C.toZChain.x (p + 1))) (RayVert.mk (C.toZChain.z (p + 1))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = C.toZChain.ρ (p + 1)) (hw : pathVal w = C.toZChain.ρ (p + 1))
    (hni : ¬Interlaced (v₁.comp v₂) w)
    (r : C.toZChain.x (p + 1 + 1) ⟶ a.out) (hr : r ≫ pathVal v₂ = C.toZChain.σ (p + 1))
    (c : a.out ⟶ C.toZChain.z (p + 1 + 1)) (hc : r ≫ c = C.toZChain.ρ (p + 1 + 1)) : False := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 1 := ⟨p - 1, by omega⟩
  exact B.lemma8_rho_peak hmin hL hR hQ hcont C hC hS hS8 t hρ v₁ v₂ w hv₁ hv₂ hv hw hni r hr c hc

end At

section Arrows

variable (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
  (hL : LeftCancel P) (hR : RightCancel P) (Z : ZChain P)

include B hmin hL hR

omit B hmin hL hR [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] in
/-- The second path of a contour splits after its first arrow. -/
lemma split_w {X Y : P} {σ : X ⟶ Y} (hσ : IsLong σ)
    (w : Quiver.Path (RayVert.mk X) (RayVert.mk Y)) (hw : pathVal w = σ) :
    ∃ (b : RayVert P) (β : RayVert.mk X ⟶ b) (w'' : Quiver.Path b (RayVert.mk Y)),
      w = β.toPath.comp w'' ∧ 0 < w''.length := by
  obtain ⟨b, β, w'', rfl⟩ := exists_first_arrow w (by rw [hw]; exact hσ.2.1)
  refine ⟨b, β, w'', rfl, ?_⟩
  cases w'' with
  | cons _ _ => simp
  | nil =>
    exfalso
    apply hσ.2.2.1
    rw [← hw, Quiver.Path.comp_nil, pathVal_toPath]
    exact β.2

/-- **The parts of the split of a long `σ (q+2)` are arrows** (valley side). -/
theorem arrows_sigma (q : ℕ) (hσ : IsLong (Z.σ (q + 2))) {a : RayVert P}
    (v₁ : Quiver.Path (RayVert.mk (Z.x (q + 3))) a) (v₂ : Quiver.Path a (RayVert.mk (Z.z (q + 2))))
    (w : Quiver.Path (RayVert.mk (Z.x (q + 3))) (RayVert.mk (Z.z (q + 2))))
    (hv₁ : 0 < v₁.length) (hv : pathVal (v₁.comp v₂) = Z.σ (q + 2)) (hw : pathVal w = Z.σ (q + 2))
    (hni : ¬Interlaced (v₁.comp v₂) w) (ρ₁' : a.out ⟶ Z.z (q + 3))
    (hρ₁' : pathVal v₁ ≫ ρ₁' = Z.ρ (q + 3))
    (hmax : ∃ (d : RayVert P) (e : a ⟶ d) (p₂ : Quiver.Path d (RayVert.mk (Z.z (q + 2)))),
      v₂ = e.toPath.comp p₂ ∧ ¬∃ g, (pathVal v₁ ≫ e.1) ≫ g = Z.ρ (q + 3))
    (L8a : ¬∃ c, c ≫ ρ₁' = Z.σ (q + 3))
    (f1 : ¬FactorsThroughMorphism (Z.σ (q + 2)) (Z.σ (q + 3)))
    (f2 : ¬FactorsThroughMorphism (Z.σ (q + 2)) (Z.ρ (q + 4)))
    (f3 : ¬FactorsThroughMorphism (Z.σ (q + 2)) (Z.σ (q + 4)))
    (f4 : ¬FactorsThroughMorphism (Z.σ (q + 2)) (Z.ρ (q + 5))) :
    IsIrreducible (pathVal v₁) ∧ IsIrreducible (pathVal v₂) := by
  obtain ⟨b, β, w'', rfl, hw''⟩ := split_w hσ w hw
  obtain ⟨d, e, p₂, rfl, hmx⟩ := hmax
  constructor
  · obtain ⟨c, Bp, α, rfl⟩ := exists_last_arrow v₁ (not_isIso_pathVal _ hv₁)
    rcases Nat.eq_zero_or_pos Bp.length with h0 | hB
    · cases Bp with
      | cons _ _ => simp at h0
      | nil => change IsIrreducible (𝟙 _ ≫ α.1); rw [Category.id_comp]; exact α.2
    · exact (B.arrow_v1 hmin hL hR _ hσ _ (Z.ρ_ne _) (Z.valley₁ (q + 2)) (Z.valley₂ (q + 2))
        (Z.σ (q + 3)) (Z.ρ (q + 4)) (Z.σ (q + 4)) (Z.ρ (q + 5)) (Z.peak₁ (q + 3))
        (Z.valley₁ (q + 3)) (Z.valley₂ (q + 3)) (Z.peak₁ (q + 4)) (Z.peak₂ (q + 4))
        (Z.valley₁ (q + 4)) (Z.valley₂ (q + 4)) f1 f2 f3 f4 Bp α _ β.toPath w'' hB
        (by simp) (by simp) hw'' hv hw hni ρ₁' hρ₁' L8a).elim
  · rcases Nat.eq_zero_or_pos p₂.length with h0 | hp
    · cases p₂ with
      | cons _ _ => simp at h0
      | nil => rw [Quiver.Path.comp_nil, pathVal_toPath]; exact e.2
    · exact (B.arrow_v2f hmin hL hR _ hσ _ (Z.ρ_ne _) (Z.valley₁ (q + 2)) (Z.valley₂ (q + 2))
        (Z.σ (q + 3)) (Z.ρ (q + 4)) (Z.σ (q + 4)) (Z.ρ (q + 5)) (Z.peak₁ (q + 3))
        (Z.valley₁ (q + 3)) (Z.valley₂ (q + 3)) (Z.peak₁ (q + 4)) (Z.peak₂ (q + 4))
        (Z.valley₁ (q + 4)) (Z.valley₂ (q + 4)) f1 f2 f3 f4 v₁ e p₂ β.toPath w'' hv₁ hp
        (by simp) hw'' hv hw hni ρ₁' hρ₁' hmx L8a).elim

/-- **The parts of the split of a long `ρ (p+3)` are arrows** (valley side, i.e. the entries
before it). -/
theorem arrows_rho (p : ℕ) (hlam : IsLong (Z.ρ (p + 3))) {a : RayVert P}
    (v₁ : Quiver.Path (RayVert.mk (Z.x (p + 3))) a) (v₂ : Quiver.Path a (RayVert.mk (Z.z (p + 3))))
    (w : Quiver.Path (RayVert.mk (Z.x (p + 3))) (RayVert.mk (Z.z (p + 3))))
    (hv₁ : 0 < v₁.length) (hv : pathVal (v₁.comp v₂) = Z.ρ (p + 3)) (hw : pathVal w = Z.ρ (p + 3))
    (hni : ¬Interlaced (v₁.comp v₂) w) (σ' : a.out ⟶ Z.z (p + 2))
    (hσ' : pathVal v₁ ≫ σ' = Z.σ (p + 2))
    (hmax : ∃ (d : RayVert P) (e : a ⟶ d) (p₂ : Quiver.Path d (RayVert.mk (Z.z (p + 3)))),
      v₂ = e.toPath.comp p₂ ∧ ¬∃ g, (pathVal v₁ ≫ e.1) ≫ g = Z.σ (p + 2))
    (L8c : ¬∃ c, c ≫ σ' = Z.ρ (p + 2))
    (f1 : ¬FactorsThroughMorphism (Z.ρ (p + 3)) (Z.ρ (p + 2)))
    (f2 : ¬FactorsThroughMorphism (Z.ρ (p + 3)) (Z.σ (p + 1)))
    (f3 : ¬FactorsThroughMorphism (Z.ρ (p + 3)) (Z.ρ (p + 1)))
    (f4 : ¬FactorsThroughMorphism (Z.ρ (p + 3)) (Z.σ p)) :
    IsIrreducible (pathVal v₁) ∧ IsIrreducible (pathVal v₂) := by
  obtain ⟨b, β, w'', rfl, hw''⟩ := split_w hlam w hw
  obtain ⟨d, e, p₂, rfl, hmx⟩ := hmax
  constructor
  · obtain ⟨c, Bp, α, rfl⟩ := exists_last_arrow v₁ (not_isIso_pathVal _ hv₁)
    rcases Nat.eq_zero_or_pos Bp.length with h0 | hB
    · cases Bp with
      | cons _ _ => simp at h0
      | nil => change IsIrreducible (𝟙 _ ≫ α.1); rw [Category.id_comp]; exact α.2
    · exact (B.arrow_v1 hmin hL hR _ hlam _ (Z.σ_ne _) (Z.valley₂ (p + 2)) (Z.valley₁ (p + 2))
        (Z.ρ (p + 2)) (Z.σ (p + 1)) (Z.ρ (p + 1)) (Z.σ p) (Z.peak₂ (p + 2))
        (Z.valley₂ (p + 1)) (Z.valley₁ (p + 1)) (Z.peak₂ (p + 1)) (Z.peak₁ (p + 1))
        (Z.valley₂ p) (Z.valley₁ p) f1 f2 f3 f4 Bp α _ β.toPath w'' hB
        (by simp) (by simp) hw'' hv hw hni σ' hσ' L8c).elim
  · rcases Nat.eq_zero_or_pos p₂.length with h0 | hp
    · cases p₂ with
      | cons _ _ => simp at h0
      | nil => rw [Quiver.Path.comp_nil, pathVal_toPath]; exact e.2
    · exact (B.arrow_v2f hmin hL hR _ hlam _ (Z.σ_ne _) (Z.valley₂ (p + 2)) (Z.valley₁ (p + 2))
        (Z.ρ (p + 2)) (Z.σ (p + 1)) (Z.ρ (p + 1)) (Z.σ p) (Z.peak₂ (p + 2))
        (Z.valley₂ (p + 1)) (Z.valley₁ (p + 1)) (Z.peak₂ (p + 1)) (Z.peak₁ (p + 1))
        (Z.valley₂ p) (Z.valley₁ p) f1 f2 f3 f4 v₁ e p₂ β.toPath w'' hv₁ hp
        (by simp) hw'' hv hw hni σ' hσ' hmx L8c).elim

/-- **The second part of the split of a long `σ (p+3)` is an arrow** (peak side). -/
theorem arrow_sigma_peak (p : ℕ) (hlam : IsLong (Z.σ (p + 3))) {a : RayVert P}
    (v₁ : Quiver.Path (RayVert.mk (Z.x (p + 4))) a) (v₂ : Quiver.Path a (RayVert.mk (Z.z (p + 3))))
    (w : Quiver.Path (RayVert.mk (Z.x (p + 4))) (RayVert.mk (Z.z (p + 3))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length) (hv : pathVal (v₁.comp v₂) = Z.σ (p + 3))
    (hw : pathVal w = Z.σ (p + 3)) (hni : ¬Interlaced (v₁.comp v₂) w)
    (r : Z.x (p + 3) ⟶ a.out) (hr : r ≫ pathVal v₂ = Z.ρ (p + 3))
    (L8d : ¬∃ c, r ≫ c = Z.σ (p + 2))
    (f1 : ¬FactorsThroughMorphism (Z.σ (p + 3)) (Z.σ (p + 2)))
    (f2 : ¬FactorsThroughMorphism (Z.σ (p + 3)) (Z.ρ (p + 2)))
    (f3 : ¬FactorsThroughMorphism (Z.σ (p + 3)) (Z.σ (p + 1)))
    (f4 : ¬FactorsThroughMorphism (Z.σ (p + 3)) (Z.ρ (p + 1))) : IsIrreducible (pathVal v₂) := by
  obtain ⟨b, β, w'', rfl, hw''⟩ := split_w hlam w hw
  obtain ⟨c, e, Cp, rfl⟩ := exists_first_arrow v₂ (not_isIso_pathVal _ hv₂)
  rcases Nat.eq_zero_or_pos Cp.length with h0 | hC
  · cases Cp with
    | cons _ _ => simp at h0
    | nil => rw [Quiver.Path.comp_nil, pathVal_toPath]; exact e.2
  · exact (B.arrow_v2 hmin hL hR _ hlam _ (Z.ρ_ne _) (Z.peak₁ (p + 3)) (Z.peak₂ (p + 3))
      (Z.σ (p + 2)) (Z.ρ (p + 2)) (Z.σ (p + 1)) (Z.ρ (p + 1)) (Z.valley₁ (p + 2))
      (Z.peak₁ (p + 2)) (Z.peak₂ (p + 2)) (Z.valley₂ (p + 1)) (Z.valley₁ (p + 1))
      (Z.peak₁ (p + 1)) (Z.peak₂ (p + 1)) f1 f2 f3 f4 v₁ e Cp β.toPath w'' hv₁ hC
      (by simp) hw'' hv hw hni r hr L8d).elim

end Arrows

include B in
/-- **BO13a §2.2.5, case `σ₁ … ρⱼ`: every long morphism has the domain of `σ₁`.** -/
theorem dom_b2
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (s L : ℕ)
    (hLn : L + 3 ≤ C.n) (hσ : IsLong (C.toZChain.σ (s + 2)))
    (hlam : IsLong (C.toZChain.ρ (s + 3 + L + 1)))
    (hnρ : ∀ i ≤ L, ¬IsLong (C.toZChain.ρ (s + 3 + i)))
    (hnσ : ∀ i ≤ L, ¬IsLong (C.toZChain.σ (s + 3 + i)))
    (hfwd : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, C.toZChain.ρ (s + 3 + L + 1)⟩ →
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.σ (s + 3)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.ρ (s + 4)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.σ (s + 4)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.ρ (s + 5)))
    (hbwd : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, C.toZChain.ρ (s + 3 + L + 1)⟩ →
      ∀ p, p + 3 = s + 3 + L + 1 →
      ¬FactorsThroughMorphism (C.toZChain.ρ (p + 3)) (C.toZChain.ρ (p + 2)) ∧
      ¬FactorsThroughMorphism (C.toZChain.ρ (p + 3)) (C.toZChain.σ (p + 1)) ∧
      ¬FactorsThroughMorphism (C.toZChain.ρ (p + 3)) (C.toZChain.ρ (p + 1)) ∧
      ¬FactorsThroughMorphism (C.toZChain.ρ (p + 3)) (C.toZChain.σ p)) :
    ∀ {a b : P} (μ : a ⟶ b), IsLong μ → a = C.toZChain.x (s + 3) := by
  have hσ0 := hσ.1
  have hlam0 := hlam.1
  have nb1 : ∀ t, IsLong (C.toZChain.σ t) → IsLong (C.toZChain.ρ t) → False := fun t h1 h2 ↦
    B.lemma6 hmin hL hR hQ hcont C hC hS (2 * t) h2 (isLong_of_rayMor_eq (C.toZChain_σ t) h1)
  have h4 : NoCrown4 P := by
    have h7 := B.lemma7 hmin hL hR hQ hcont C hC hS hS8.f73 _ hσ
    have h2 := Crown.two_le_n hQ C
    have hn3 : 2 < C.n := by omega
    intro a₀ a₁ b₀ b₁ f₀ f₁ f₂ f₃
    exact Crown.noCrown4 hC hn3
  -- a long entry different from `σ₁`, and one different from `ρⱼ`
  obtain ⟨t₀, ht₀, hne₀⟩ := B.lemma5c hmin hL hR hQ hcont C (2 * (s + 2) + 1)
    (isLong_of_rayMor_eq (C.toZChain_σ (s + 2)) hσ)
  have hτ₀ : ¬FactorsThroughMorphism (C.f t₀).2.2 (C.toZChain.σ (s + 2)) :=
    not_ftm_of_ne ht₀ hσ0 (fun h ↦ hne₀ (by rw [← C.toZChain_σ]; exact h.symm))
  obtain ⟨t₁, ht₁, hne₁⟩ := B.lemma5c hmin hL hR hQ hcont C (2 * (s + 3 + L + 1)) hlam
  have hτ₁ : ¬FactorsThroughMorphism (C.f t₁).2.2 (C.toZChain.ρ (s + 3 + L + 1)) :=
    not_ftm_of_ne ht₁ hlam0 (fun h ↦ hne₁ h.symm)
  -- the split of `σ₁`
  have hρ₁l : ¬IsLong (C.toZChain.ρ (s + 3)) := hnρ 0 (Nat.zero_le _)
  have hρnl : ¬IsLong (C.toZChain.ρ (s + 2)) := fun h ↦ nb1 (s + 2) hσ h
  obtain ⟨b, c, α, v', u, ω, w, hvu, hv, hw, hni, hα, hω⟩ :=
    B.refl_contour hmin hL hR hQ hcont C hC hS hS8 s hσ
  obtain ⟨a, v₁, v₂, ρ₁', r, e, hv₁, hv₂, hρ₁', hr, hz, hmax⟩ :=
    B.split_refl hmin hL hR h4 _ _ _ hσ hρ₁l hρnl (C.toZChain.ρ_ne _) (C.toZChain.ρ_ne _)
      (C.toZChain.valley₁ (s + 2)) (C.toZChain.valley₂ (s + 2)) (C.toZChain.peak₁ (s + 2))
      (C.toZChain.peak₂ (s + 2)) _ ht₀ hτ₀ α v' u ω hvu hv hα hω
  have hV : pathVal v₁ ≫ pathVal v₂ = C.toZChain.σ (s + 2) := by rw [← pathVal_comp, e, hv]
  have hv₁₂ : pathVal (v₁.comp v₂) = C.toZChain.σ (s + 2) := by rw [e, hv]
  have hni₁ : ¬Interlaced (v₁.comp v₂) w := by rw [e]; exact hni
  have hiV₁ := not_isIso_pathVal v₁ hv₁
  have hiV₂ := not_isIso_pathVal v₂ hv₂
  -- the split of `ρⱼ`
  have hσjl : ¬IsLong (C.toZChain.σ (s + 3 + L)) := hnσ L le_rfl
  have hσj1l : ¬IsLong (C.toZChain.σ (s + 3 + L + 1)) := fun h ↦ nb1 _ h hlam
  obtain ⟨b', c'', α', v'', u', ω', w', hvu', hv', hw', hni', hα', hω'⟩ :=
    B.refl_contour_rho_at hmin hL hR hQ hcont C hC hS hS8 (s + 3 + L) (by omega) hlam
  obtain ⟨c', v₁', v₂', σ', r'', e', hv₁', hv₂', hσ', hr'', hz', hmax'⟩ :=
    B.split_refl hmin hL hR h4 _ _ _ hlam hσjl hσj1l (C.toZChain.σ_ne _) (C.toZChain.σ_ne _)
      (C.toZChain.valley₂ (s + 3 + L)) (C.toZChain.valley₁ (s + 3 + L))
      (C.toZChain.peak₂ (s + 3 + L + 1)) (C.toZChain.peak₁ (s + 3 + L + 1)) _ ht₁ hτ₁
      α' v'' u' ω' hvu' hv' hα' hω'
  have hV' : pathVal v₁' ≫ pathVal v₂' = C.toZChain.ρ (s + 3 + L + 1) := by
    rw [← pathVal_comp, e', hv']
  have hv₁₂' : pathVal (v₁'.comp v₂') = C.toZChain.ρ (s + 3 + L + 1) := by rw [e', hv']
  have hni₂ : ¬Interlaced (v₁'.comp v₂') w' := by rw [e']; exact hni'
  have hiV₁' := not_isIso_pathVal v₁' hv₁'
  have hiV₂' := not_isIso_pathVal v₂' hv₂'
  -- Lemma 8 in the four positions
  have L8a : ¬∃ c, c ≫ ρ₁' = C.toZChain.σ (s + 3) := fun ⟨c, hc⟩ ↦
    B.lemma8 hmin hL hR hQ hcont C hC hS hS8 s hσ v₁ v₂ w hv₁ hv₂ hv₁₂ hw hni₁ ρ₁' hρ₁' c hc
  have L8b : ¬∃ c, r ≫ c = C.toZChain.σ (s + 1) := fun ⟨c, hc⟩ ↦
    B.lemma8_peak hmin hL hR hQ hcont C hC hS hS8 s hσ v₁ v₂ w hv₁ hv₂ hv₁₂ hw hni₁ r hr c hc
  have L8c : ¬∃ c, c ≫ σ' = C.toZChain.ρ (s + 3 + L) := fun ⟨c, hc⟩ ↦
    B.lemma8_rho_at hmin hL hR hQ hcont C hC hS hS8 (s + 3 + L) (by omega) hlam v₁' v₂' w' hv₁'
      hv₂' hv₁₂' hw' hni₂ σ' hσ' c hc
  have L8d : ¬∃ c, r'' ≫ c = C.toZChain.ρ (s + 3 + L + 1 + 1) := fun ⟨c, hc⟩ ↦
    B.lemma8_rho_peak_at hmin hL hR hQ hcont C hC hS hS8 (s + 3 + L) (by omega) hlam v₁' v₂' w'
      hv₁' hv₂' hv₁₂' hw' hni₂ r'' hr'' c hc
  -- no third long morphism
  have hthird : ∀ {a₀ b₀ : P} (τ : a₀ ⟶ b₀), IsLong τ →
      ¬FactorsThroughMorphism τ (C.toZChain.σ (s + 2)) →
      ¬FactorsThroughMorphism τ (C.toZChain.ρ (s + 3 + L + 1)) → False :=
    fun τ hτ h1 h2 ↦ B.b2_third hmin hL hR C.toZChain s L hnρ hnσ (pathVal v₁) (pathVal v₂) ρ₁'
      hV hρ₁' hiV₁ hiV₂ (pathVal v₁') (pathVal v₂') σ' hV' hσ' hiV₁' hiV₂' L8a L8c τ hτ h1 h2
  have hne : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, C.toZChain.ρ (s + 3 + L + 1)⟩ := by
    intro heq
    refine hthird _ ht₀ hτ₀ ?_
    intro h
    obtain ⟨hx, hy, he⟩ := ht₀.2.2.2 _ hlam0 h
    apply hτ₀
    have e2 := congrArg (fun f : RayMor P ↦ FactorsThroughMorphism (C.f t₀).2.2 f.2.2) heq
    simp only at e2
    rw [e2]
    exact h
  -- the parts of the splits are arrows
  obtain ⟨f1, f2, f3, f4⟩ := hfwd hne
  obtain ⟨hirr₁, hirr₂⟩ := B.arrows_sigma hmin hL hR C.toZChain s hσ v₁ v₂ w hv₁ hv₁₂ hw hni₁ ρ₁'
    hρ₁' hmax L8a f1 f2 f3 f4
  have harr' : IsIrreducible (pathVal v₁') ∧ IsIrreducible (pathVal v₂') := by
    obtain rfl | rfl | ⟨L', rfl⟩ : L = 0 ∨ L = 1 ∨ ∃ L', L = L' + 2 := by
      rcases L with _ | _ | L'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨L', rfl⟩)
    · obtain ⟨g1, g2, g3, g4⟩ := hbwd hne (s + 1) rfl
      exact B.arrows_rho hmin hL hR C.toZChain (s + 1) hlam v₁' v₂' w' hv₁' hv₁₂' hw' hni₂ σ' hσ'
        hmax' L8c g1 g2 g3 g4
    · obtain ⟨g1, g2, g3, g4⟩ := hbwd hne (s + 2) rfl
      exact B.arrows_rho hmin hL hR C.toZChain (s + 2) hlam v₁' v₂' w' hv₁' hv₁₂' hw' hni₂ σ' hσ'
        hmax' L8c g1 g2 g3 g4
    · obtain ⟨g1, g2, g3, g4⟩ := hbwd hne (s + 3 + L') (by ring)
      exact B.arrows_rho hmin hL hR C.toZChain (s + 3 + L') hlam v₁' v₂' w' hv₁' hv₁₂' hw' hni₂
        σ' hσ' hmax' L8c g1 g2 g3 g4
  obtain ⟨hirr₁', hirr₂'⟩ := harr'
  -- `ρ₁ ≤ ρⱼ`
  have hiρ₁ : ¬IsIso (C.toZChain.ρ (s + 3)) := fun _ ↦ C.toZChain.valley₂ (s + 2)
    ⟨inv (C.toZChain.ρ (s + 3)) ≫ C.toZChain.σ (s + 2), by simp⟩
  have hrρ₁ : ¬IsIrreducible (C.toZChain.ρ (s + 3)) := fun h ↦ by
    rcases h.2.2 _ (pathVal v₁) ρ₁' hρ₁'.symm with h' | h'
    · exact hiV₁ h'
    · exact C.toZChain.valley₂ (s + 2) ⟨inv ρ₁' ≫ pathVal v₂, by rw [← hρ₁', ← hV]; simp⟩
  obtain ⟨a₀, b₀, lam, hlm, hftm⟩ := exists_isLong_above (C.toZChain.ρ_ne (s + 3)) hiρ₁ hrρ₁
  have hle : FactorsThroughMorphism (C.toZChain.ρ (s + 3)) (C.toZChain.ρ (s + 3 + L + 1)) := by
    by_cases h1 : FactorsThroughMorphism lam (C.toZChain.σ (s + 2))
    · exfalso
      obtain ⟨hx, hy, he⟩ := hlm.2.2.2 _ hσ0 h1
      obtain ⟨φ, ψ, hφψ⟩ := hftm
      obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR (C.toZChain.valley₂ (s + 2))
        (pathVal v₁) (pathVal v₂) ρ₁' hV hρ₁' (eqToHom hx ≫ φ) (ψ ≫ eqToHom hy.symm)
        (by rw [he, hφψ]; simp) hσ0
      rcases hirr₂.2.2 _ d₁ d₂ hd.symm with h | h
      · exact hd₁ h
      · exact hd₂ h
    by_cases h2 : FactorsThroughMorphism lam (C.toZChain.ρ (s + 3 + L + 1))
    · obtain ⟨hx, hy, he⟩ := hlm.2.2.2 _ hlam0 h2
      obtain ⟨φ, ψ, hφψ⟩ := hftm
      exact ⟨eqToHom hx ≫ φ, ψ ≫ eqToHom hy.symm, by rw [he, hφψ]; simp⟩
    · exact (hthird lam hlm h1 h2).elim
  obtain ⟨γ, δ, hγ⟩ := hle
  -- the shorter crown
  obtain ⟨cc, hcc⟩ := b2_core hL C hC s L hLn (pathVal v₁) (pathVal v₂) ρ₁' r hV hρ₁' hr hz hiV₁
    (pathVal v₁') (pathVal v₂') r'' hV' hr'' hirr₁' hirr₂' γ δ hγ.symm L8b L8d hρ₁l hlam
  have hγi : IsIso γ := by
    rcases hirr₁'.2.2 _ γ (pathVal v₁ ≫ cc) (by rw [← hcc, Category.assoc]) with h | h
    · exact h
    · exact absurd (isIso_of_isIso_comp _ cc hirr₁.1 h) hiV₁
  have hdom : C.toZChain.x (s + 3 + L + 1) = C.toZChain.x (s + 3) :=
    IsRayCategory.skeletal ⟨asIso γ⟩
  intro a₀ b₀ μ hμ
  by_cases h1 : FactorsThroughMorphism μ (C.toZChain.σ (s + 2))
  · obtain ⟨hx, -, -⟩ := hμ.2.2.2 _ hσ0 h1
    exact hx.symm
  by_cases h2 : FactorsThroughMorphism μ (C.toZChain.ρ (s + 3 + L + 1))
  · obtain ⟨hx, -, -⟩ := hμ.2.2.2 _ hlam0 h2
    rw [← hx, hdom]
  exact (hthird μ hμ h1 h2).elim

include B in
/-- **BO13a §2.2.5, case `σ₁ … σⱼ`: every long morphism has the domain of `σ₁`.** -/
theorem dom_b3
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (s L : ℕ)
    (hLn : L + 4 ≤ C.n) (hσ : IsLong (C.toZChain.σ (s + 2)))
    (hlam : IsLong (C.toZChain.σ (s + 3 + L + 1)))
    (hnρ : ∀ i ≤ L + 1, ¬IsLong (C.toZChain.ρ (s + 3 + i)))
    (hnσ : ∀ i ≤ L, ¬IsLong (C.toZChain.σ (s + 3 + i)))
    (hfwd : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, C.toZChain.σ (s + 3 + L + 1)⟩ →
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.σ (s + 3)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.ρ (s + 4)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.σ (s + 4)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) (C.toZChain.ρ (s + 5)))
    (hbwd : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, C.toZChain.σ (s + 3 + L + 1)⟩ →
      ∀ p, p + 3 = s + 3 + L + 1 →
      ¬FactorsThroughMorphism (C.toZChain.σ (p + 3)) (C.toZChain.σ (p + 2)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (p + 3)) (C.toZChain.ρ (p + 2)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (p + 3)) (C.toZChain.σ (p + 1)) ∧
      ¬FactorsThroughMorphism (C.toZChain.σ (p + 3)) (C.toZChain.ρ (p + 1))) :
    ∀ {a b : P} (μ : a ⟶ b), IsLong μ → a = C.toZChain.x (s + 3) := by
  have hσ0 := hσ.1
  have hlam0 := hlam.1
  have nb1 : ∀ t, IsLong (C.toZChain.σ t) → IsLong (C.toZChain.ρ t) → False := fun t h1 h2 ↦
    B.lemma6 hmin hL hR hQ hcont C hC hS (2 * t) h2 (isLong_of_rayMor_eq (C.toZChain_σ t) h1)
  have nb2 : ∀ t, IsLong (C.toZChain.σ t) → IsLong (C.toZChain.ρ (t + 1)) → False :=
    fun t h1 h2 ↦ B.lemma6 hmin hL hR hQ hcont C hC hS (2 * t + 1)
      (isLong_of_rayMor_eq (C.toZChain_σ t) h1) (by rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring]; exact h2)
  have h4 : NoCrown4 P := by
    have h7 := B.lemma7 hmin hL hR hQ hcont C hC hS hS8.f73 _ hσ
    have h2 := Crown.two_le_n hQ C
    have hn3 : 2 < C.n := by omega
    intro a₀ a₁ b₀ b₁ f₀ f₁ f₂ f₃
    exact Crown.noCrown4 hC hn3
  -- a long entry different from `σ₁`, and one different from `σⱼ`
  obtain ⟨t₀, ht₀, hne₀⟩ := B.lemma5c hmin hL hR hQ hcont C (2 * (s + 2) + 1)
    (isLong_of_rayMor_eq (C.toZChain_σ (s + 2)) hσ)
  have hτ₀ : ¬FactorsThroughMorphism (C.f t₀).2.2 (C.toZChain.σ (s + 2)) :=
    not_ftm_of_ne ht₀ hσ0 (fun h ↦ hne₀ (by rw [← C.toZChain_σ]; exact h.symm))
  obtain ⟨t₁, ht₁, hne₁⟩ := B.lemma5c hmin hL hR hQ hcont C (2 * (s + 3 + L + 1) + 1)
    (isLong_of_rayMor_eq (C.toZChain_σ (s + 3 + L + 1)) hlam)
  have hτ₁ : ¬FactorsThroughMorphism (C.f t₁).2.2 (C.toZChain.σ (s + 3 + L + 1)) :=
    not_ftm_of_ne ht₁ hlam0 (fun h ↦ hne₁ (by rw [← C.toZChain_σ]; exact h.symm))
  -- the split of `σ₁`
  have hρ₁l : ¬IsLong (C.toZChain.ρ (s + 3)) := hnρ 0 (Nat.zero_le _)
  have hρnl : ¬IsLong (C.toZChain.ρ (s + 2)) := fun h ↦ nb1 (s + 2) hσ h
  obtain ⟨b, c, α, v', u, ω, w, hvu, hv, hw, hni, hα, hω⟩ :=
    B.refl_contour hmin hL hR hQ hcont C hC hS hS8 s hσ
  obtain ⟨a, v₁, v₂, ρ₁', r, e, hv₁, hv₂, hρ₁', hr, hz, hmax⟩ :=
    B.split_refl hmin hL hR h4 _ _ _ hσ hρ₁l hρnl (C.toZChain.ρ_ne _) (C.toZChain.ρ_ne _)
      (C.toZChain.valley₁ (s + 2)) (C.toZChain.valley₂ (s + 2)) (C.toZChain.peak₁ (s + 2))
      (C.toZChain.peak₂ (s + 2)) _ ht₀ hτ₀ α v' u ω hvu hv hα hω
  have hV : pathVal v₁ ≫ pathVal v₂ = C.toZChain.σ (s + 2) := by rw [← pathVal_comp, e, hv]
  have hv₁₂ : pathVal (v₁.comp v₂) = C.toZChain.σ (s + 2) := by rw [e, hv]
  have hni₁ : ¬Interlaced (v₁.comp v₂) w := by rw [e]; exact hni
  have hiV₁ := not_isIso_pathVal v₁ hv₁
  have hiV₂ := not_isIso_pathVal v₂ hv₂
  -- the split of `σⱼ`
  have hρjl : ¬IsLong (C.toZChain.ρ (s + 3 + L + 1)) := hnρ (L + 1) le_rfl
  have hρj1l : ¬IsLong (C.toZChain.ρ (s + 3 + L + 1 + 1)) := fun h ↦ nb2 _ hlam h
  obtain ⟨b', c'', α', v'', u', ω', w', hvu', hv', hw', hni', hα', hω'⟩ :=
    B.refl_contour_at hmin hL hR hQ hcont C hC hS hS8 (s + 3 + L + 1) (by omega) hlam
  obtain ⟨c', v₁', v₂', ρ'', r', e', hv₁', hv₂', hρ'', hr', hz', hmax'⟩ :=
    B.split_refl hmin hL hR h4 _ _ _ hlam hρj1l hρjl (C.toZChain.ρ_ne _) (C.toZChain.ρ_ne _)
      (C.toZChain.valley₁ (s + 3 + L + 1)) (C.toZChain.valley₂ (s + 3 + L + 1))
      (C.toZChain.peak₁ (s + 3 + L + 1)) (C.toZChain.peak₂ (s + 3 + L + 1)) _ ht₁ hτ₁
      α' v'' u' ω' hvu' hv' hα' hω'
  have hV' : pathVal v₁' ≫ pathVal v₂' = C.toZChain.σ (s + 3 + L + 1) := by
    rw [← pathVal_comp, e', hv']
  have hv₁₂' : pathVal (v₁'.comp v₂') = C.toZChain.σ (s + 3 + L + 1) := by rw [e', hv']
  have hni₂ : ¬Interlaced (v₁'.comp v₂') w' := by rw [e']; exact hni'
  have hiV₁' := not_isIso_pathVal v₁' hv₁'
  have hiV₂' := not_isIso_pathVal v₂' hv₂'
  -- Lemma 8 in the three positions used
  have L8a : ¬∃ c, c ≫ ρ₁' = C.toZChain.σ (s + 3) := fun ⟨c, hc⟩ ↦
    B.lemma8 hmin hL hR hQ hcont C hC hS hS8 s hσ v₁ v₂ w hv₁ hv₂ hv₁₂ hw hni₁ ρ₁' hρ₁' c hc
  have L8b : ¬∃ c, r ≫ c = C.toZChain.σ (s + 1) := fun ⟨c, hc⟩ ↦
    B.lemma8_peak hmin hL hR hQ hcont C hC hS hS8 s hσ v₁ v₂ w hv₁ hv₂ hv₁₂ hw hni₁ r hr c hc
  have L8d : ¬∃ c, r' ≫ c = C.toZChain.σ (s + 3 + L) := fun ⟨c, hc⟩ ↦
    B.lemma8_peak_at hmin hL hR hQ hcont C hC hS hS8 (s + 3 + L) (by omega) hlam v₁' v₂' w'
      hv₁' hv₂' hv₁₂' hw' hni₂ r' hr' c hc
  -- no third long morphism
  have hthird : ∀ {a₀ b₀ : P} (τ : a₀ ⟶ b₀), IsLong τ →
      ¬FactorsThroughMorphism τ (C.toZChain.σ (s + 2)) →
      ¬FactorsThroughMorphism τ (C.toZChain.σ (s + 3 + L + 1)) → False :=
    fun τ hτ h1 h2 ↦ B.b3_third hmin hL hR C.toZChain s L hnρ hnσ (pathVal v₁) (pathVal v₂) ρ₁'
      hV hρ₁' hiV₁ hiV₂ (pathVal v₁') (pathVal v₂') r' hV' hr' hiV₁' hiV₂' L8a L8d τ hτ h1 h2
  have hne : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, C.toZChain.σ (s + 3 + L + 1)⟩ := by
    intro heq
    refine hthird _ ht₀ hτ₀ ?_
    intro h
    apply hτ₀
    have e2 := congrArg (fun f : RayMor P ↦ FactorsThroughMorphism (C.f t₀).2.2 f.2.2) heq
    simp only at e2
    rw [e2]
    exact h
  -- the parts of the splits that are arrows
  obtain ⟨f1, f2, f3, f4⟩ := hfwd hne
  obtain ⟨hirr₁, hirr₂⟩ := B.arrows_sigma hmin hL hR C.toZChain s hσ v₁ v₂ w hv₁ hv₁₂ hw hni₁ ρ₁'
    hρ₁' hmax L8a f1 f2 f3 f4
  have hirr₂' : IsIrreducible (pathVal v₂') := by
    obtain rfl | rfl | ⟨L', rfl⟩ : L = 0 ∨ L = 1 ∨ ∃ L', L = L' + 2 := by
      rcases L with _ | _ | L'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨L', rfl⟩)
    · obtain ⟨g1, g2, g3, g4⟩ := hbwd hne (s + 1) rfl
      exact B.arrow_sigma_peak hmin hL hR C.toZChain (s + 1) hlam v₁' v₂' w' hv₁' hv₂' hv₁₂' hw'
        hni₂ r' hr' L8d g1 g2 g3 g4
    · obtain ⟨g1, g2, g3, g4⟩ := hbwd hne (s + 2) rfl
      exact B.arrow_sigma_peak hmin hL hR C.toZChain (s + 2) hlam v₁' v₂' w' hv₁' hv₂' hv₁₂' hw'
        hni₂ r' hr' L8d g1 g2 g3 g4
    · obtain ⟨g1, g2, g3, g4⟩ := hbwd hne (s + 3 + L') (by ring)
      exact B.arrow_sigma_peak hmin hL hR C.toZChain (s + 3 + L') hlam v₁' v₂' w' hv₁' hv₂' hv₁₂'
        hw' hni₂ r' hr' L8d g1 g2 g3 g4
  -- `ρ₁ ≤ σⱼ`
  have hiρ₁ : ¬IsIso (C.toZChain.ρ (s + 3)) := fun _ ↦ C.toZChain.valley₂ (s + 2)
    ⟨inv (C.toZChain.ρ (s + 3)) ≫ C.toZChain.σ (s + 2), by simp⟩
  have hrρ₁ : ¬IsIrreducible (C.toZChain.ρ (s + 3)) := fun h ↦ by
    rcases h.2.2 _ (pathVal v₁) ρ₁' hρ₁'.symm with h' | h'
    · exact hiV₁ h'
    · exact C.toZChain.valley₂ (s + 2) ⟨inv ρ₁' ≫ pathVal v₂, by rw [← hρ₁', ← hV]; simp⟩
  obtain ⟨a₀, b₀, lam, hlm, hftm⟩ := exists_isLong_above (C.toZChain.ρ_ne (s + 3)) hiρ₁ hrρ₁
  have hle : FactorsThroughMorphism (C.toZChain.ρ (s + 3)) (C.toZChain.σ (s + 3 + L + 1)) := by
    by_cases h1 : FactorsThroughMorphism lam (C.toZChain.σ (s + 2))
    · exfalso
      obtain ⟨hx, hy, he⟩ := hlm.2.2.2 _ hσ0 h1
      obtain ⟨φ, ψ, hφψ⟩ := hftm
      obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR (C.toZChain.valley₂ (s + 2))
        (pathVal v₁) (pathVal v₂) ρ₁' hV hρ₁' (eqToHom hx ≫ φ) (ψ ≫ eqToHom hy.symm)
        (by rw [he, hφψ]; simp) hσ0
      rcases hirr₂.2.2 _ d₁ d₂ hd.symm with h | h
      · exact hd₁ h
      · exact hd₂ h
    by_cases h2 : FactorsThroughMorphism lam (C.toZChain.σ (s + 3 + L + 1))
    · obtain ⟨hx, hy, he⟩ := hlm.2.2.2 _ hlam0 h2
      obtain ⟨φ, ψ, hφψ⟩ := hftm
      exact ⟨eqToHom hx ≫ φ, ψ ≫ eqToHom hy.symm, by rw [he, hφψ]; simp⟩
    · exact (hthird lam hlm h1 h2).elim
  obtain ⟨γ, δ, hγ⟩ := hle
  -- `ρⱼ₊₁ ≤ σ₁`
  have hiρj : ¬IsIso (C.toZChain.ρ (s + 3 + L + 1 + 1)) := fun _ ↦
    C.toZChain.valley₂ (s + 3 + L + 1)
      ⟨inv (C.toZChain.ρ (s + 3 + L + 1 + 1)) ≫ C.toZChain.σ (s + 3 + L + 1), by simp⟩
  have hrρj : ¬IsIrreducible (C.toZChain.ρ (s + 3 + L + 1 + 1)) := fun h ↦ by
    rcases h.2.2 _ (pathVal v₁') ρ'' hρ''.symm with h' | h'
    · exact hiV₁' h'
    · exact C.toZChain.valley₂ (s + 3 + L + 1)
        ⟨inv ρ'' ≫ pathVal v₂', by rw [← hρ'', ← hV']; simp⟩
  obtain ⟨a₁, b₁, lam', hlm', hftm'⟩ :=
    exists_isLong_above (C.toZChain.ρ_ne (s + 3 + L + 1 + 1)) hiρj hrρj
  have hle' : FactorsThroughMorphism (C.toZChain.ρ (s + 3 + L + 1 + 1)) (C.toZChain.σ (s + 2)) := by
    by_cases h2 : FactorsThroughMorphism lam' (C.toZChain.σ (s + 3 + L + 1))
    · exfalso
      obtain ⟨hx, hy, he⟩ := hlm'.2.2.2 _ hlam0 h2
      obtain ⟨φ, ψ, hφψ⟩ := hftm'
      obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR (C.toZChain.valley₂ (s + 3 + L + 1))
        (pathVal v₁') (pathVal v₂') ρ'' hV' hρ'' (eqToHom hx ≫ φ) (ψ ≫ eqToHom hy.symm)
        (by rw [he, hφψ]; simp) hlam0
      rcases hirr₂'.2.2 _ d₁ d₂ hd.symm with h | h
      · exact hd₁ h
      · exact hd₂ h
    by_cases h1 : FactorsThroughMorphism lam' (C.toZChain.σ (s + 2))
    · obtain ⟨hx, hy, he⟩ := hlm'.2.2.2 _ hσ0 h1
      obtain ⟨φ, ψ, hφψ⟩ := hftm'
      exact ⟨eqToHom hx ≫ φ, ψ ≫ eqToHom hy.symm, by rw [he, hφψ]; simp⟩
    · exact (hthird lam' hlm' h1 h2).elim
  obtain ⟨γ', δ', hγ'⟩ := hle'
  -- the shorter crown
  have hγi : IsIso γ := b3_core hL hR hQ C hC s L hLn (pathVal v₁) (pathVal v₂) ρ₁' r hV hρ₁' hr hz
    hirr₁ hirr₂ γ δ hγ.symm γ' δ' hγ'.symm L8b
  have hdom : C.toZChain.x (s + 3 + L + 1 + 1) = C.toZChain.x (s + 3) :=
    IsRayCategory.skeletal ⟨asIso γ⟩
  intro a₀ b₀ μ hμ
  by_cases h1 : FactorsThroughMorphism μ (C.toZChain.σ (s + 2))
  · obtain ⟨hx, -, -⟩ := hμ.2.2.2 _ hσ0 h1
    exact hx.symm
  by_cases h2 : FactorsThroughMorphism μ (C.toZChain.σ (s + 3 + L + 1))
  · obtain ⟨hx, -, -⟩ := hμ.2.2.2 _ hlam0 h2
    rw [← hx, hdom]
  exact (hthird μ hμ h1 h2).elim

omit [IsRayCategory P] [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] in
/-- The first long entry after position `p₀`, when some long entry differs from `C.f p₀`. -/
lemma _root_.LargeIndecomposable.RayCat.Crown.exists_next_long (C : Crown P) (p₀ t : ℕ)
    (ht : IsLong (C.f t).2.2) (hne : C.f t ≠ C.f p₀) :
    ∃ d, 0 < d ∧ d < 2 * C.n ∧ IsLong (C.f (p₀ + d)).2.2 ∧
      ∀ d', 0 < d' → d' < d → ¬IsLong (C.f (p₀ + d')).2.2 := by
  classical
  have hN : 0 < 2 * C.n := by have := C.hn; omega
  have e₀ := Nat.div_add_mod p₀ (2 * C.n)
  have l₀ := Nat.mod_lt p₀ hN
  have l₁ := Nat.mod_lt t hN
  have hft : C.f t = C.f (t % (2 * C.n)) := C.f_mod t
  obtain ⟨d₁, hd₁, hf₁⟩ : ∃ d₁, d₁ < 2 * C.n ∧ C.f (p₀ + d₁) = C.f t := by
    by_cases h : p₀ % (2 * C.n) ≤ t % (2 * C.n)
    · refine ⟨t % (2 * C.n) - p₀ % (2 * C.n), by omega, ?_⟩
      rw [hft, show p₀ + (t % (2 * C.n) - p₀ % (2 * C.n)) =
        t % (2 * C.n) + 2 * C.n * (p₀ / (2 * C.n)) by omega, C.f_add_mul]
    · refine ⟨t % (2 * C.n) + 2 * C.n - p₀ % (2 * C.n), by omega, ?_⟩
      rw [hft, show p₀ + (t % (2 * C.n) + 2 * C.n - p₀ % (2 * C.n)) =
        t % (2 * C.n) + 2 * C.n * (p₀ / (2 * C.n) + 1) by rw [Nat.mul_add]; omega, C.f_add_mul]
  have hd₁0 : 0 < d₁ := by
    rcases Nat.eq_zero_or_pos d₁ with h | h
    · exact absurd (by rw [← hf₁, h, Nat.add_zero]) hne
    · exact h
  have hl₁ : IsLong (C.f (p₀ + d₁)).2.2 := by rw [hf₁]; exact ht
  have hex : ∃ d, 0 < d ∧ IsLong (C.f (p₀ + d)).2.2 := ⟨d₁, hd₁0, hl₁⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).1,
    lt_of_le_of_lt (Nat.find_min' hex ⟨hd₁0, hl₁⟩) hd₁, (Nat.find_spec hex).2,
    fun d' h0 hlt hl ↦ Nat.find_min hex hlt ⟨h0, hl⟩⟩

omit [IsRayCategory P] [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] in
lemma not_ftm_rayMor {f g f' g' : RayMor P} (hf : f' = f) (hg : g' = g) (hl : IsLong f.2.2)
    (hg0 : g.2.2 ≠ 0) (h : ¬IsLong g.2.2 ∨ g ≠ f) : ¬FactorsThroughMorphism f'.2.2 g'.2.2 := by
  subst hf hg
  rcases h with h | h
  · exact not_factorsThrough_of_not_isLong hl hg0 h
  · exact not_ftm_of_ne hl hg0 h

section Pos

variable (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
  (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
  (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
  (hS : L6Shapes k) (hS8 : L8Shapes k)
  (hD93 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F93.thin) k))

include B hmin hL hR hQ hcont hS hS8 hD93

/-- **No two long entries of a minimal crown are at distance two.** -/
theorem no_dist2 (C : Crown P) (hC : C.IsMin) (j : ℕ) (h1 : IsLong (C.f j).2.2)
    (h2 : IsLong (C.f (j + 2)).2.2) : False := by
  have hn := C.hn
  have hn2 := Crown.two_le_n hQ C
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · obtain ⟨K, hK⟩ : ∃ K, K = C.n * (m + 4) := ⟨_, rfl⟩
    have hm : C.n * (m + 4) ≥ m + 4 := Nat.le_mul_of_pos_left _ hn
    have hK2 : 2 * C.n * (m + 4) = 2 * K := by rw [hK]; ring
    have e1 : (⟨_, _, C.rev.toZChain.σ (K - m - 3 + 2)⟩ : RayMor P) = C.f (2 * m + 2) := by
      rw [Crown.toZChain_σ]
      exact C.rev_f_of _ _ (m + 4) (by rw [hK2]; omega)
    have e2 : (⟨_, _, C.rev.toZChain.σ (K - m - 3 + 3)⟩ : RayMor P) = C.f (2 * m) := by
      rw [Crown.toZChain_σ]
      exact C.rev_f_of _ _ (m + 4) (by rw [hK2]; omega)
    exact B.b1 hmin hL hR hQ hcont C.rev hC.rev hS hS8 hD93 (K - m - 3)
      (isLong_of_rayMor_eq e1.symm h2) (isLong_of_rayMor_eq e2.symm h1)
  · have e1 : (⟨_, _, C.toZChain.σ (m + C.n - 2 + 2)⟩ : RayMor P) = C.f (2 * m + 1) := by
      rw [Crown.toZChain_σ, show 2 * (m + C.n - 2 + 2) + 1 = 2 * m + 1 + 2 * C.n by omega, C.per]
    have e2 : (⟨_, _, C.toZChain.σ (m + C.n - 2 + 3)⟩ : RayMor P) = C.f (2 * m + 1 + 2) := by
      rw [Crown.toZChain_σ, show 2 * (m + C.n - 2 + 3) + 1 = 2 * m + 1 + 2 + 2 * C.n by omega,
        C.per]
    exact B.b1 hmin hL hR hQ hcont C hC hS hS8 hD93 (m + C.n - 2)
      (isLong_of_rayMor_eq e1.symm h1) (isLong_of_rayMor_eq e2.symm h2)

/-- **BO13a §2.2.5: all long morphisms have the domain of a long `σ`-entry.** -/
theorem dom_sigma (C : Crown P) (hC : C.IsMin) (s : ℕ) (hσ : IsLong (C.toZChain.σ (s + 2))) :
    ∀ {a b : P} (μ : a ⟶ b), IsLong μ → a = C.toZChain.x (s + 3) := by
  intro a₀ b₀ μ hμ
  have hn := C.hn
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, p₀ = 2 * (s + 2) + 1 := ⟨_, rfl⟩
  have eσ : ∀ m j, 2 * m + 1 = j → (⟨_, _, C.toZChain.σ m⟩ : RayMor P) = C.f j :=
    fun m j h ↦ by rw [C.toZChain_σ, h]
  have eρ : ∀ m j, 2 * m = j → (⟨_, _, C.toZChain.ρ m⟩ : RayMor P) = C.f j :=
    fun m j h ↦ by rw [Crown.toZChain_ρ, h]
  have hσf : IsLong (C.f p₀).2.2 := isLong_of_rayMor_eq (eσ _ _ hp₀.symm) hσ
  have nb : ∀ j, IsLong (C.f j).2.2 → IsLong (C.f (j + 1)).2.2 → False := fun j h1 h2 ↦
    B.lemma6 hmin hL hR hQ hcont C hC hS j h1 h2
  have nd2 : ∀ j, IsLong (C.f j).2.2 → IsLong (C.f (j + 2)).2.2 → False := fun j h1 h2 ↦
    B.no_dist2 hmin hL hR hQ hcont hS hS8 hD93 C hC j h1 h2
  obtain ⟨t, ht, hne⟩ := B.lemma5c hmin hL hR hQ hcont C p₀ hσf
  obtain ⟨d, hd0, hdn, hdl, hdmin⟩ := C.exists_next_long p₀ t ht hne
  have hper : C.f (p₀ + 2 * C.n) = C.f p₀ := C.per _
  have hd1 : d ≠ 1 := by rintro rfl; exact nb _ hσf hdl
  have hd2 : d ≠ 2 := by rintro rfl; exact nd2 _ hσf hdl
  have hdn1 : d ≠ 2 * C.n - 1 := by
    intro h
    apply nb (p₀ + d) hdl
    rw [show p₀ + d + 1 = p₀ + 2 * C.n by omega, hper]
    exact hσf
  have hdn2 : d ≠ 2 * C.n - 2 := by
    intro h
    apply nd2 (p₀ + d) hdl
    rw [show p₀ + d + 2 = p₀ + 2 * C.n by omega, hper]
    exact hσf
  -- the windows
  have fwin : C.f (p₀ + d) ≠ C.f p₀ → ∀ j, 0 < j → j ≤ d + 2 →
      ¬IsLong (C.f (p₀ + j)).2.2 ∨ C.f (p₀ + j) ≠ C.f p₀ := by
    intro hne' j hj0 hjd
    rcases lt_trichotomy j d with h | rfl | h
    · exact Or.inl (hdmin j hj0 h)
    · exact Or.inr hne'
    · refine Or.inl fun hl ↦ ?_
      rcases (show j = d + 1 ∨ j = d + 2 by omega) with rfl | rfl
      · exact nb _ hdl hl
      · exact nd2 _ hdl hl
  have bwin : C.f (p₀ + d) ≠ C.f p₀ → ∀ i, 2 ≤ i → i ≤ d + 2 →
      ¬IsLong (C.f (p₀ + d - i)).2.2 ∨ C.f (p₀ + d - i) ≠ C.f (p₀ + d) := by
    intro hne' i hi2 hid
    rcases lt_trichotomy i d with h | rfl | h
    · refine Or.inl ?_
      have := hdmin (d - i) (by omega) (by omega)
      rwa [show p₀ + (d - i) = p₀ + d - i by omega] at this
    · refine Or.inr ?_
      rw [show p₀ + i - i = p₀ by omega]
      exact fun h ↦ hne' h.symm
    · refine Or.inl fun hl ↦ ?_
      rcases (show i = d + 1 ∨ i = d + 2 by omega) with rfl | rfl
      · apply nb _ hl
        rw [show p₀ + d - (d + 1) + 1 = p₀ by omega]
        exact hσf
      · apply nd2 _ hl
        rw [show p₀ + d - (d + 2) + 2 = p₀ by omega]
        exact hσf
  have fw : C.f (p₀ + d) ≠ C.f p₀ → ∀ (g : RayMor P) j, g = C.f (p₀ + j) → 0 < j → j ≤ d + 2 →
      ¬FactorsThroughMorphism (C.toZChain.σ (s + 2)) g.2.2 := fun hne' g j hg hj0 hjd ↦
    not_ftm_rayMor (f := C.f p₀) (f' := ⟨_, _, C.toZChain.σ (s + 2)⟩) (eσ _ _ hp₀.symm) hg hσf
      (C.ne _) (fwin hne' j hj0 hjd)
  have bw : C.f (p₀ + d) ≠ C.f p₀ → ∀ (lam g : RayMor P) i, lam = C.f (p₀ + d) →
      g = C.f (p₀ + d - i) → 2 ≤ i → i ≤ d + 2 → ¬FactorsThroughMorphism lam.2.2 g.2.2 :=
    fun hne' lam g i hlam hg hi2 hid ↦
      not_ftm_rayMor hlam hg hdl (C.ne _) (bwin hne' i hi2 hid)
  obtain ⟨L, hL'⟩ : ∃ L, d = 2 * L + 3 ∨ d = 2 * L + 4 := ⟨(d - 3) / 2, by omega⟩
  rcases hL' with hd | hd
  · -- `σ₁ … ρⱼ`
    have hlam : IsLong (C.toZChain.ρ (s + 3 + L + 1)) :=
      isLong_of_rayMor_eq (eρ _ (p₀ + d) (by omega)).symm hdl
    have hne' : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠
        ⟨_, _, C.toZChain.ρ (s + 3 + L + 1)⟩ → C.f (p₀ + d) ≠ C.f p₀ := fun hne h ↦
      hne (by rw [eσ _ p₀ hp₀.symm, eρ _ (p₀ + d) (by omega), h])
    exact B.dom_b2 hmin hL hR hQ hcont C hC hS hS8 s L (by omega) hσ hlam
      (fun i hi h ↦ hdmin (2 * i + 1) (by omega) (by omega)
        (isLong_of_rayMor_eq (eρ _ (p₀ + (2 * i + 1)) (by omega)) h))
      (fun i hi h ↦ hdmin (2 * i + 2) (by omega) (by omega)
        (isLong_of_rayMor_eq (eσ _ (p₀ + (2 * i + 2)) (by omega)) h))
      (fun hne ↦ ⟨fw (hne' hne) ⟨_, _, C.toZChain.σ (s + 3)⟩ 2 (eσ _ _ (by omega)) (by omega)
          (by omega),
        fw (hne' hne) ⟨_, _, C.toZChain.ρ (s + 4)⟩ 3 (eρ _ _ (by omega)) (by omega) (by omega),
        fw (hne' hne) ⟨_, _, C.toZChain.σ (s + 4)⟩ 4 (eσ _ _ (by omega)) (by omega) (by omega),
        fw (hne' hne) ⟨_, _, C.toZChain.ρ (s + 5)⟩ 5 (eρ _ _ (by omega)) (by omega) (by omega)⟩)
      (fun hne p hp ↦
        ⟨bw (hne' hne) ⟨_, _, C.toZChain.ρ (p + 3)⟩ ⟨_, _, C.toZChain.ρ (p + 2)⟩ 2
          (eρ _ _ (by omega)) (eρ _ _ (by omega)) (by omega) (by omega),
        bw (hne' hne) ⟨_, _, C.toZChain.ρ (p + 3)⟩ ⟨_, _, C.toZChain.σ (p + 1)⟩ 3
          (eρ _ _ (by omega)) (eσ _ _ (by omega)) (by omega) (by omega),
        bw (hne' hne) ⟨_, _, C.toZChain.ρ (p + 3)⟩ ⟨_, _, C.toZChain.ρ (p + 1)⟩ 4
          (eρ _ _ (by omega)) (eρ _ _ (by omega)) (by omega) (by omega),
        bw (hne' hne) ⟨_, _, C.toZChain.ρ (p + 3)⟩ ⟨_, _, C.toZChain.σ p⟩ 5
          (eρ _ _ (by omega)) (eσ _ _ (by omega)) (by omega) (by omega)⟩) μ hμ
  · -- `σ₁ … σⱼ`
    have hlam : IsLong (C.toZChain.σ (s + 3 + L + 1)) :=
      isLong_of_rayMor_eq (eσ _ (p₀ + d) (by omega)).symm hdl
    have hne' : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) ≠
        ⟨_, _, C.toZChain.σ (s + 3 + L + 1)⟩ → C.f (p₀ + d) ≠ C.f p₀ := fun hne h ↦
      hne (by rw [eσ _ p₀ hp₀.symm, eσ _ (p₀ + d) (by omega), h])
    exact B.dom_b3 hmin hL hR hQ hcont C hC hS hS8 s L (by omega) hσ hlam
      (fun i hi h ↦ hdmin (2 * i + 1) (by omega) (by omega)
        (isLong_of_rayMor_eq (eρ _ (p₀ + (2 * i + 1)) (by omega)) h))
      (fun i hi h ↦ hdmin (2 * i + 2) (by omega) (by omega)
        (isLong_of_rayMor_eq (eσ _ (p₀ + (2 * i + 2)) (by omega)) h))
      (fun hne ↦ ⟨fw (hne' hne) ⟨_, _, C.toZChain.σ (s + 3)⟩ 2 (eσ _ _ (by omega)) (by omega)
          (by omega),
        fw (hne' hne) ⟨_, _, C.toZChain.ρ (s + 4)⟩ 3 (eρ _ _ (by omega)) (by omega) (by omega),
        fw (hne' hne) ⟨_, _, C.toZChain.σ (s + 4)⟩ 4 (eσ _ _ (by omega)) (by omega) (by omega),
        fw (hne' hne) ⟨_, _, C.toZChain.ρ (s + 5)⟩ 5 (eρ _ _ (by omega)) (by omega) (by omega)⟩)
      (fun hne p hp ↦
        ⟨bw (hne' hne) ⟨_, _, C.toZChain.σ (p + 3)⟩ ⟨_, _, C.toZChain.σ (p + 2)⟩ 2
          (eσ _ _ (by omega)) (eσ _ _ (by omega)) (by omega) (by omega),
        bw (hne' hne) ⟨_, _, C.toZChain.σ (p + 3)⟩ ⟨_, _, C.toZChain.ρ (p + 2)⟩ 3
          (eσ _ _ (by omega)) (eρ _ _ (by omega)) (by omega) (by omega),
        bw (hne' hne) ⟨_, _, C.toZChain.σ (p + 3)⟩ ⟨_, _, C.toZChain.σ (p + 1)⟩ 4
          (eσ _ _ (by omega)) (eσ _ _ (by omega)) (by omega) (by omega),
        bw (hne' hne) ⟨_, _, C.toZChain.σ (p + 3)⟩ ⟨_, _, C.toZChain.ρ (p + 1)⟩ 5
          (eσ _ _ (by omega)) (eρ _ _ (by omega)) (by omega) (by omega)⟩) μ hμ

end Pos

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
/-- Two long morphisms with the same ends are equal. -/
lemma long_unique (hQ : OneSidedCyclic P) {X Y : P} {f g : X ⟶ Y} (hf : IsLong f)
    (hg : IsLong g) : f = g := by
  have key : ∀ {f g : X ⟶ Y}, IsLong f → g ≠ 0 → FactorsThroughMorphism f g → f = g :=
    fun {f g} hf hg0 h ↦ by
      obtain ⟨hx, hy, he⟩ := hf.2.2.2 g hg0 h
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
      exact he.symm
  rcases cmp4 hQ f g hf.1 hg.1 with ⟨b, h⟩ | ⟨a, h⟩ | ⟨b, h⟩ | ⟨a, h⟩
  · exact key hf hg.1 ⟨𝟙 _, b, by rw [h, Category.id_comp]⟩
  · exact key hf hg.1 ⟨a, 𝟙 _, by rw [h, Category.comp_id]⟩
  · exact (key hg hf.1 ⟨𝟙 _, b, by rw [h, Category.id_comp]⟩).symm
  · exact (key hg hf.1 ⟨a, 𝟙 _, by rw [h, Category.comp_id]⟩).symm

section Final

variable (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
  (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
  (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
  (hS : L6Shapes k) (hS8 : L8Shapes k)
  (hD93 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F93.thin) k))

include B hmin hL hR hQ hcont hS hS8 hD93

/-- **BO13a §2.2.5: all long morphisms have the same domain.** -/
theorem dom_all (C : Crown P) (hC : C.IsMin) {a₀ b₀ : P} (μ₀ : a₀ ⟶ b₀) (hμ₀ : IsLong μ₀) :
    ∃ X : P, ∀ {a b : P} (μ : a ⟶ b), IsLong μ → a = X := by
  have hn := C.hn
  have hn2 := Crown.two_le_n hQ C
  obtain ⟨t, ht⟩ := B.long_entry hmin C μ₀ hμ₀
  have hl : IsLong (C.f t).2.2 := by rw [ht]; exact hμ₀
  rcases Nat.even_or_odd' t with ⟨m, rfl | rfl⟩
  · obtain ⟨K, hK⟩ : ∃ K, K = C.n * (m + 2) := ⟨_, rfl⟩
    have hm : C.n * (m + 2) ≥ m + 2 := Nat.le_mul_of_pos_left _ hn
    have hK2 : 2 * C.n * (m + 2) = 2 * K := by rw [hK]; ring
    have e : (⟨_, _, C.rev.toZChain.σ (K - m - 2 + 2)⟩ : RayMor P) = C.f (2 * m) := by
      rw [Crown.toZChain_σ]
      exact C.rev_f_of _ _ (m + 2) (by rw [hK2]; omega)
    exact ⟨_, fun μ hμ ↦ B.dom_sigma hmin hL hR hQ hcont hS hS8 hD93 C.rev hC.rev (K - m - 2)
      (isLong_of_rayMor_eq e.symm hl) μ hμ⟩
  · have e : (⟨_, _, C.toZChain.σ (m + C.n - 2 + 2)⟩ : RayMor P) = C.f (2 * m + 1) := by
      rw [Crown.toZChain_σ, show 2 * (m + C.n - 2 + 2) + 1 = 2 * m + 1 + 2 * C.n by omega, C.per]
    exact ⟨_, fun μ hμ ↦ B.dom_sigma hmin hL hR hQ hcont hS hS8 hD93 C hC (m + C.n - 2)
      (isLong_of_rayMor_eq e.symm hl) μ hμ⟩

/-- **BO13a §2.2.5: all long morphisms have the same codomain** (dual). -/
theorem cod_all (C : Crown P) (hC : C.IsMin) {a₀ b₀ : P} (μ₀ : a₀ ⟶ b₀) (hμ₀ : IsLong μ₀) :
    ∃ Y : P, ∀ {a b : P} (μ : a ⟶ b), IsLong μ → b = Y := by
  let _ : IsRayCategory Pᵒᵖ := isRayCategory_of_finiteRayCategory
  let _ : Fintype Pᵒᵖ := Fintype.ofFinite _
  let _ : DecidableEq Pᵒᵖ := Classical.decEq _
  have _ : FiniteDimensional k A := B.finiteDimensional
  obtain ⟨X, hX⟩ := (B.op).dom_all (hmin_op (k := k) hmin) (leftCancel_op hR) (rightCancel_op hL)
    (oneSidedCyclic_op hQ) (hcont_op hcont) hS hS8 hD93 C.op hC.op μ₀.op
    ((isLong_op_iff _).2 hμ₀)
  exact ⟨X.unop, fun μ hμ ↦ by rw [← hX μ.op ((isLong_op_iff _).2 hμ)]⟩

/-- **BO13a Proposition 2 (§2.2): with a crown, some long morphism lies in no contour.** -/
theorem s225_final (C : Crown P) {a₀ b₀ : P} (μ₀ : a₀ ⟶ b₀) (hμ₀ : IsLong μ₀) : False := by
  obtain ⟨C', hC'⟩ := Crown.exists_isMin ⟨C⟩
  obtain ⟨X, hX⟩ := B.dom_all hmin hL hR hQ hcont hS hS8 hD93 C' hC' μ₀ hμ₀
  obtain ⟨Y, hY⟩ := B.cod_all hmin hL hR hQ hcont hS hS8 hD93 C' hC' μ₀ hμ₀
  obtain ⟨t₀, ht₀⟩ := B.long_entry hmin C' μ₀ hμ₀
  obtain ⟨t, ht, hne⟩ := B.lemma5c hmin hL hR hQ hcont C' t₀ (by rw [ht₀]; exact hμ₀)
  rw [ht₀] at hne
  generalize C'.f t = g at ht hne
  obtain ⟨x, y, τ⟩ := g
  have hx := hX τ ht
  have hy := hY τ ht
  have ha := hX μ₀ hμ₀
  have hb := hY μ₀ hμ₀
  subst hx hy ha hb
  have he : τ = μ₀ := long_unique hQ ht hμ₀
  exact hne (by rw [he])

end Final

end MulBasis

end RayQuiver

end LargeIndecomposable
