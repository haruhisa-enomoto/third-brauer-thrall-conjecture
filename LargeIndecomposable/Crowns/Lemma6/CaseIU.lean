module

public import LargeIndecomposable.Crowns.Lemma6.Figure63
public import LargeIndecomposable.Cleaving.Shapes.ShapeS5m
public import LargeIndecomposable.Cleaving.Shapes.ShapeS5p
public import LargeIndecomposable.Cleaving.Shapes.ShapeS4s
public import LargeIndecomposable.Cleaving.Shapes.ShapeS65

/-!
# BO13a Lemma 6, case I.2.c: `ρₙ = ρₙ' ≫ u₂`

Instantiations of the trees used when `ρₙ` factors through `u₂`:
* `l6_s5m`: `D̃₅` `σₙ', u₂, u₂', w₂', η` (`σₙ = ρₙ' ≫ σₙ'`, `ρₙ' ≫ u₂' = 0`);
* `l6_s4s`: the `D̃₄` star `ρₙ', ψ, u₂, d` (`u₂' = d ≫ a`);
* `l6_s5p`: `D̃₅` `ψ₂, u₂, u₂', w₂', η` (`ψ = ψ₁ ≫ ψ₂`);
* `l6_s65`: figure 6.5 (`D̃₅` `w₁, ψ, w₁', ρₙ', σ₂'`, `σ₂ = σ₂' ≫ u₂'`).
The quotient is a parameter `τ` where BO13a's choice may fail.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- A long morphism does not divide a proper middle factor of itself. -/
lemma not_ftm_mid {a b c d : P} {f : a ⟶ d} (hf0 : f ≠ 0) {p : a ⟶ b} {g : b ⟶ c} {q : c ⟶ d}
    (hp : ¬IsIso p) (h : p ≫ g ≫ q = f) : ¬FactorsThroughMorphism f g := by
  rintro ⟨u, v, rfl⟩
  have h2 : f = (p ≫ u) ≫ f ≫ (v ≫ q) := by
    calc f = p ≫ (u ≫ f ≫ v) ≫ q := h.symm
      _ = (p ≫ u) ≫ f ≫ (v ≫ q) := by simp
  obtain ⟨hpu, -⟩ := IsRayCategory.eq_id_of_two_sided f hf0 _ _ h2
  exact hp (isIso_of_isIso_comp p u (fun h0 ↦ IsRayCategory.id_ne_zero a
    (by rw [← hpu, h0, zero_comp])) (by rw [hpu]; infer_instance))

variable [IsFiniteRayCategory P]

/-- Two long morphisms `σ : x → y₀` and `μ : x'' → y₁` with a morphism `ρ : x → y₁`
incomparable with both from the respective sides do not divide each other. -/
lemma l6_μσ (hQ : OneSidedCyclic P) {x y₀ y₁ x'' : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} {μ : x'' ⟶ y₁}
    (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0) (hμ : IsLong μ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ) :
    ¬FactorsThroughMorphism μ σ := by
  intro h
  obtain ⟨hx, hy, he'⟩ := hμ.2.2.2 σ hσ0 h
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he'
  rw [← he'] at hm1 hm2
  exact not_parallel hQ σ ρ hσ0 hρ0 hv1 hv2 hm1 hm2

lemma l6_σμ (hQ : OneSidedCyclic P) {x y₀ y₁ x'' : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} {μ : x'' ⟶ y₁}
    (hσ : IsLong σ) (hρ0 : ρ ≠ 0) (hμ0 : μ ≠ 0) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ) :
    ¬FactorsThroughMorphism σ μ := by
  intro h
  obtain ⟨hx, hy, he'⟩ := hσ.2.2.2 μ hμ0 h
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he'
  rw [he'] at hm1 hm2
  exact not_parallel hQ σ ρ hσ.1 hρ0 hv1 hv2 hm1 hm2

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- `D̃₅` `σₙ', u₂, u₂', w₂', η` in `P/τ`. -/
theorem l6_s5m
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) {x' zn : P} (ρn : x' ⟶ y₀) (σn : x' ⟶ zn) (hσn0 : σn ≠ 0)
    (hq1 : ¬∃ c, σn ≫ c = ρn) (hq2 : ¬∃ c, ρn ≫ c = σn)
    (r : x' ⟶ D.m.out) (s : D.m.out ⟶ zn) (hr : r ≫ D.U = ρn) (hs : r ≫ s = σn)
    (hrU' : r ≫ D.U' = 0) {te : P} (e : te ⟶ y₁) (he : IsIrreducible e)
    (hpk : ¬∃ g, g ≫ e = ρ) (hsU' : ¬∃ g, s ≫ g = D.U')
    {a b : P} (τ : a ⟶ b) (hτ : IsLong τ) (h0s : ¬FactorsThroughMorphism τ s)
    (h0U : ¬FactorsThroughMorphism τ D.U) (h0U' : ¬FactorsThroughMorphism τ D.U')
    (h0W' : ¬FactorsThroughMorphism τ D.W') : False := by
  have hρ0 := hρ.1
  have hiW' := D.W'_not_isIso hρ.2.2.1
  have hWU' := D.W'_U' hL hR hρ0 hρ.2.2.1
  refine B.not_s5m hmin hL hR τ hτ.2.1 hτ.1 s D.U D.U' D.W' e h0s h0U h0U' h0W'
    (not_factorsThrough_irr hτ.2.1 hτ.1 hτ.2.2.1 he) ?_ D.U_not_isIso D.U'_not_isIso hiW'
    he.2.1 ?_ hsU' ?_ (D.U_U' hv1) ?_ (D.U'_U hv2) hWU'.2 ?_ hWU'.1 ?_ ?_ ?_
  · exact fun h ↦ hq1 ⟨inv s ≫ D.U, by rw [← hs, Category.assoc, IsIso.hom_inv_id_assoc, hr]⟩
  · exact fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hs, Category.assoc, hg, hr]⟩
  · exact fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hr, Category.assoc, hg, hs]⟩
  · exact fun ⟨g, hg⟩ ↦ hσn0 (by rw [← hs, ← hg, ← Category.assoc, hrU', zero_comp])
  · rintro ⟨g, hg⟩
    rcases he.2.2 _ g D.U' hg.symm with h | h
    · exact hpk ⟨D.ψ ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.ψU']⟩
    · exact D.U'_not_isIso h
  · rintro ⟨g, hg⟩
    rcases he.2.2 _ g D.W' hg.symm with h | h
    · exact hpk ⟨D.β'.1 ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.βW']⟩
    · exact hiW' h
  · exact fun ⟨g, hg⟩ ↦ hpk ⟨D.ψ ≫ g, by rw [Category.assoc, hg, D.ψU']⟩
  · exact fun ⟨g, hg⟩ ↦ hpk ⟨D.β'.1 ≫ g, by rw [Category.assoc, hg, D.βW']⟩

include B in
/-- The `D̃₄` star `ρₙ', ψ, u₂, d` in `P/τ`, for a prefix `d` of `u₂'`. -/
theorem l6_s4s
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hv1 : ¬∃ c, σ ≫ c = ρ) (D : L6Data σ ρ) {x' c : P} (ρn : x' ⟶ y₀)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (r : x' ⟶ D.m.out) (hr : r ≫ D.U = ρn) (d : D.m.out ⟶ c) (a' : c ⟶ y₁)
    (hd : d ≫ a' = D.U') (hid : ¬IsIso d)
    {a b : P} (τ : a ⟶ b) (hτ : IsLong τ) (h0r : ¬FactorsThroughMorphism τ r)
    (h0U : ¬FactorsThroughMorphism τ D.U) (h0d : ¬FactorsThroughMorphism τ d)
    (h0rU : ¬FactorsThroughMorphism τ ρn) (h0rd : ¬FactorsThroughMorphism τ (r ≫ d))
    (h0ψ : ¬FactorsThroughMorphism τ D.ψ) (h0σ : ¬FactorsThroughMorphism τ σ)
    (h0ψd : ¬FactorsThroughMorphism τ (D.ψ ≫ d)) : False := by
  have hσ0 := hσ.1
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.ψ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.ψU]⟩
  refine B.not_s4s hmin hL hR τ hτ.2.1 hτ.1 r D.ψ D.U d h0U h0d h0r (by rw [hr]; exact h0rU)
    h0rd h0ψ (by rw [D.ψU]; exact h0σ) h0ψd hir D.ψ_not_isIso D.U_not_isIso hid ?_ ?_ ?_ ?_
  · exact fun ⟨g, hg⟩ ↦ hv1 ⟨g ≫ a', by rw [← D.ψU, Category.assoc, ← Category.assoc D.U, hg, hd,
      D.ψU']⟩
  · rintro ⟨g, hg⟩
    have hle := D.hmax ⟨_, D.ψ ≫ d⟩ ⟨pathVal D.χ ≫ d, by
      change D.α.1 ≫ pathVal D.χ ≫ d = D.ψ ≫ d
      simp only [L6Data.ψ]
      rw [pathVal_comp D.α.toPath D.χ, pathVal_toPath, Category.assoc]⟩
      ⟨g, by change (D.ψ ≫ d) ≫ g = σ; rw [Category.assoc, hg, D.ψU]⟩
      ⟨a', by change (D.ψ ≫ d) ≫ a' = ρ; rw [Category.assoc, hd, D.ψU']⟩
    obtain ⟨k', hk'⟩ := hle
    change (D.ψ ≫ d) ≫ k' = D.ψ at hk'
    have hdk : d ≫ k' = 𝟙 _ := hL D.ψ _ _ (by rw [Category.comp_id, ← Category.assoc, hk'])
      (by rw [← Category.assoc, hk']; exact fun h ↦ hσ0 (by rw [← D.ψU, h, zero_comp]))
    exact not_split_mono hid ⟨k', hdk⟩
  · exact fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← D.ψU, ← hg, Category.assoc, hr]⟩
  · exact fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, D.ψU]⟩

include B in
/-- `D̃₅` `ψ₂, u₂, u₂', w₂', η` in `P/ρ`, for a factorization `ψ = ψ₁ ≫ ψ₂`. -/
theorem l6_s5p
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) {m₁ : P} (p₁ : x ⟶ m₁) (p : m₁ ⟶ D.m.out) (hpp : p₁ ≫ p = D.ψ)
    (hip₁ : ¬IsIso p₁) (hip : ¬IsIso p) {te : P} (e : te ⟶ y₁) (he : IsIrreducible e)
    (hpk : ¬∃ g, g ≫ e = ρ) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hiW' := D.W'_not_isIso hρ.2.2.1
  have hWU' := D.W'_U' hL hR hρ0 hρ.2.2.1
  have hp₁0 : p₁ ≠ 0 := fun h ↦ hρ0 (by rw [← D.ψU', ← hpp, h, zero_comp, zero_comp])
  have hp0 : p ≠ 0 := fun h ↦ hρ0 (by rw [← D.ψU', ← hpp, h, comp_zero, zero_comp])
  -- the contour through `ψ₁ ψ₂ u₂'`
  obtain ⟨P₁, hP₁⟩ := RayCat.exists_path p₁ hp₁0
  obtain ⟨P₂, hP₂⟩ := RayCat.exists_path p hp0
  have hcross : ¬∃ g, g ≫ D.W' = p ≫ D.U' := by
    have hV : pathVal (P₁.comp (P₂.comp D.u₂')) = ρ := by
      rw [pathVal_comp, pathVal_comp, hP₁, hP₂, ← Category.assoc, hpp, D.ψU']
    have hint : Interlaced (P₁.comp (P₂.comp D.u₂')) ((D.α.toPath.comp D.χ).comp D.u₂') := by
      rw [← Quiver.Path.comp_assoc]
      refine .rel _ _ (interStep_suffix _ _ _ D.hu₂' ?_ ?_)
      · rw [pathVal_comp, hP₁, hP₂, hpp]
      · rw [pathVal_comp, hP₁, hP₂, hpp]
        exact fun h ↦ hρ0 (by rw [← D.ψU', h, zero_comp])
    have hni : ¬Interlaced (P₁.comp (P₂.comp D.u₂')) (D.β'.toPath.comp D.w') := fun h ↦
      D.hniρ (hint.symm.trans _ _ _ h)
    have := (contour_cross hL hR P₁ (P₂.comp D.u₂') D.β'.toPath D.w' (by rw [hV, D.hρw])
      (by rw [hV]; exact hρ0) hni (pos_length_of_not_isIso P₁ (by rw [hP₁]; exact hip₁))
      (pos_length_of_not_isIso D.w' hiW')).1
    rwa [pathVal_comp, hP₂] at this
  have hρpU : p₁ ≫ p ≫ D.U' = ρ := by rw [← Category.assoc, hpp, D.ψU']
  have hσpU : p₁ ≫ p ≫ D.U = σ := by rw [← Category.assoc, hpp, D.ψU]
  refine B.not_s5p hmin hL hR ρ hρ.2.1 hρ0 p D.U D.U' D.W' e
    (fun h ↦ not_ftm_long_dom hρ hσ0 hv2 (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _))
    (not_ftm_suffix hρ0 D.ψ_not_isIso D.ψU')
    (not_ftm_mid hρ0 hip₁ hρpU)
    (fun h ↦ not_ftm_long_dom hρ hσ0 hv2 (by rw [← hσpU]; exact FactorsThroughMorphism.comp_left h _))
    (not_ftm_suffix hρ0 hip₁ hρpU) (not_ftm_suffix hρ0 D.β'.2.2.1 D.βW')
    (not_factorsThrough_irr hρ.2.1 hρ0 hρ.2.2.1 he) hip D.U_not_isIso D.U'_not_isIso hiW'
    he.2.1 (D.U_U' hv1) (D.U'_U hv2) hWU'.2 ?_ hWU'.1 hcross ?_ ?_ ?_ ?_
  · rintro ⟨g, hg⟩
    rcases he.2.2 _ g D.U' hg.symm with h | h
    · exact hpk ⟨D.ψ ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.ψU']⟩
    · exact D.U'_not_isIso h
  · rintro ⟨g, hg⟩
    rcases he.2.2 _ g D.W' hg.symm with h | h
    · exact hpk ⟨D.β'.1 ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, D.βW']⟩
    · exact hiW' h
  · exact fun ⟨g, hg⟩ ↦ hpk ⟨D.ψ ≫ g, by rw [Category.assoc, hg, D.ψU']⟩
  · exact fun ⟨g, hg⟩ ↦ hpk ⟨p₁ ≫ g, by rw [Category.assoc, hg, hρpU]⟩
  · exact fun ⟨g, hg⟩ ↦ hpk ⟨D.β'.1 ≫ g, by rw [Category.assoc, hg, D.βW']⟩

include B in
/-- **BO13a figure 6.5**: `D̃₅` `w₁, ψ, w₁', ρₙ', σ₂'` in `P/σ`. -/
theorem l6_s65
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) {x'' : P} (μ : x'' ⟶ y₁) (hμ : IsLong μ)
    (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ) {x' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0)
    (hρnl : ¬IsLong ρn) (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (r : x' ⟶ D.m.out) (hr : r ≫ D.U = ρn) (hrU' : r ≫ D.U' = 0) (t : x'' ⟶ D.m.out)
    (ht : t ≫ D.U' = μ) (htr : ¬∃ g, g ≫ t = r) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρβ := B.l6_ρβ hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hσβ' := B.l6_σβ' hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hσμ := l6_σμ hQ hσ hρ0 hμ.1 hv1 hv2 hm1 hm2
  refine B.not_s65 hmin hL hR σ hσ.2.1 hσ0 D.β.1 D.ψ D.β'.1 r t
    (not_ftm_prefix hσ0 (D.W_not_isIso hσ.2.2.1) D.βW) (not_ftm_prefix hσ0 D.U_not_isIso D.ψU)
    (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
      rw [← D.βW']; exact FactorsThroughMorphism.comp_right h _))
    (fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (fun h ↦ hσμ (by rw [← ht]; exact FactorsThroughMorphism.comp_right h _))
    D.β.2.2.1 D.ψ_not_isIso D.β'.2.2.1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htr
  · exact fun h ↦ hp2 ⟨D.ψ ≫ inv r, by rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.ψU]⟩
  · exact fun h ↦ hm1 ⟨D.ψ ≫ inv t, by rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc, D.ψU']⟩
  · exact fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩
  · exact fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.W', by rw [← Category.assoc, hg, D.βW']⟩
  · rintro ⟨g, hg⟩
    rcases D.β.2.2.2 _ D.ψ g hg.symm with h | h
    · exact D.ψ_not_isIso h
    · exact hρβ ⟨inv g ≫ D.U', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU']⟩
  · rintro ⟨g, hg⟩
    rcases D.β'.2.2.2 _ D.ψ g hg.symm with h | h
    · exact D.ψ_not_isIso h
    · exact hσβ' ⟨inv g ≫ D.U, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU]⟩
  · exact fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.W, by rw [← Category.assoc, hg, D.βW]⟩
  · exact fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩
  · exact fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, D.ψU]⟩
  · exact fun ⟨g, hg⟩ ↦ hm2 ⟨g, by rw [← ht, ← hg, Category.assoc, D.ψU']⟩
  · exact fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← D.ψU, ← hg, Category.assoc, hr]⟩
  · exact fun ⟨g, hg⟩ ↦ hμ.1 (by rw [← ht, ← hg, Category.assoc, hrU', comp_zero])
  · exact fun ⟨g, hg⟩ ↦ hm1 ⟨g, by rw [← D.ψU', ← hg, Category.assoc, ht]⟩

end MulBasis

end RayQuiver

end LargeIndecomposable
