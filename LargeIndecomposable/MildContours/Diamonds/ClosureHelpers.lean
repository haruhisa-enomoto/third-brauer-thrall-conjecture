module

public import LargeIndecomposable.MildContours.Diamonds.RadicalGenerator
public import LargeIndecomposable.MildContours.Basic.Global

/-!
# Diamond: the closure of `P_x`, helpers

* `τω'_zero`: `τ ≫ ω' = 0`.
* `eq_τ_of_ftm`: a nonzero morphism out of `x` in `(τ)` is `τ ≫ v`.
* `not_ftm_ω`: if `τ ≫ ζ ≠ 0` then `ω ≫ ζ ∉ (τ)`.
* `tail`: if `τ ≫ v ≠ 0` then `v` is (up to an isomorphism) a prefix of `ω'`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

/-- **Simple socle on both sides gives `ProjInjAt`.** -/
theorem projInjAt_of_div {x z : P} (μ₀ : x ⟶ z) (h0 : μ₀ ≠ 0)
    (hR : ∀ {w : P} (μ : x ⟶ w), μ ≠ 0 → ∃ g, μ ≫ g = μ₀)
    (hL : ∀ {w : P} (ν : w ⟶ z), ν ≠ 0 → ∃ g, g ≫ ν = μ₀) : ProjInjAt μ₀ := by
  refine ⟨h0, ?_, ?_, ?_, ?_⟩
  · intro w ζ hζ
    by_contra h
    obtain ⟨g, hg⟩ := hR (μ₀ ≫ ζ) h
    obtain ⟨-, h2⟩ := IsRayCategory.eq_id_of_two_sided μ₀ h0 (𝟙 _) (ζ ≫ g)
      (by rw [Category.id_comp, ← Category.assoc, hg])
    have : IsIso (ζ ≫ g) := by rw [h2]; infer_instance
    exact hζ (ray_isIso_factors ζ g).1
  · intro w ζ hζ
    by_contra h
    obtain ⟨g, hg⟩ := hL (ζ ≫ μ₀) h
    obtain ⟨h2, -⟩ := IsRayCategory.eq_id_of_two_sided μ₀ h0 (g ≫ ζ) (𝟙 _)
      (by rw [Category.comp_id, Category.assoc, hg])
    have : IsIso (g ≫ ζ) := by rw [h2]; infer_instance
    exact hζ (ray_isIso_factors g ζ).2
  · intro w μ hμ hdeep
    obtain ⟨g, hg⟩ := hR μ hμ
    by_cases hgi : IsIso g
    · obtain ⟨hh, he⟩ := RayQuiver.eq_id_of_isIso g
      exact ⟨hh, by rw [← hg, he]⟩
    · exact absurd (by rw [← hg, hdeep g hgi]) h0
  · intro w ν hν hdeep
    obtain ⟨g, hg⟩ := hL ν hν
    by_cases hgi : IsIso g
    · obtain ⟨hh, he⟩ := RayQuiver.eq_id_of_isIso g
      exact ⟨hh.symm, by rw [← hg, he]⟩
    · exact absurd (by rw [← hg, hdeep g hgi]) h0

namespace DiamondData

variable (D : DiamondData P)

lemma τ_σω : D.τ = (D.γ ≫ D.η) ≫ D.γ ≫ D.α := by rw [D.τ_η]; simp

/-- **`τ ≫ ω' = 0`.** -/
theorem τω'_zero (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) : D.τ ≫ D.ω' = 0 := by
  obtain ⟨u, v, huv⟩ := D.zero
  have h : D.τ ≫ D.ω' = ((D.γ ≫ D.α) ≫ u) ≫ D.τ ≫ v ≫ D.γ := by
    calc D.τ ≫ D.ω' = (D.γ ≫ D.α) ≫ D.ω' ≫ (D.α ≫ D.ω') := by
          change (D.γ ≫ D.α ≫ D.ω' ≫ D.α) ≫ D.ω' = _; simp
      _ = (D.γ ≫ D.α) ≫ (D.ω' ≫ D.η) ≫ D.γ := by rw [D.hD]; simp
      _ = _ := by rw [huv]; simp
  rw [h, ← Category.assoc _ D.τ, D.rad_τ hMo hG _
    (not_isIso_comp_left' _ (not_isIso_comp_left' _ D.hγ.2.1)), zero_comp]

/-- A nonzero morphism out of `x` lying in `(τ)` is `τ ≫ v`. -/
lemma eq_τ_of_ftm (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) {w : P} (μ : D.x ⟶ w) (h0 : μ ≠ 0)
    (h : FactorsThroughMorphism D.τ μ) : ∃ v, μ = D.τ ≫ v := by
  obtain ⟨u, v, rfl⟩ := h
  by_cases hu : IsIso u
  · obtain ⟨hh, he⟩ := RayQuiver.eq_id_of_isIso u
    exact ⟨v, by rw [he]; simp⟩
  · exact absurd (by rw [← Category.assoc, D.rad_τ hMo hG u hu, zero_comp]) h0

/-- If `τ ≫ ζ ≠ 0`, then `ω ≫ ζ` does not lie in `(τ)`. -/
lemma not_ftm_ω (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) {w : P} (ζ : D.y ⟶ w)
    (h : D.τ ≫ ζ ≠ 0) : ¬FactorsThroughMorphism D.τ ((D.γ ≫ D.α) ≫ ζ) := by
  rintro ⟨u, v, huv⟩
  apply h
  rw [D.τ_σω, Category.assoc, huv, ← Category.assoc (D.γ ≫ D.η) u, ← Category.assoc _ D.τ,
    D.rad_τ hMo hG _ (not_isIso_comp_left' _ (not_isIso_comp_left' _ D.hγ.2.1)), zero_comp]

/-- **The tail**: if `τ ≫ v ≠ 0`, then `v` is a prefix of `ω'` up to an isomorphism. -/
theorem tail (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) {w : P} (v : D.y ⟶ w)
    (h : D.τ ≫ v ≠ 0) : ∃ (c : P) (ν : D.y ⟶ c) (ν' : c ⟶ D.a) (hc : c = w),
      ν ≫ ν' = D.ω' ∧ v = ν ≫ eqToHom hc := by
  by_cases hv : IsIso v
  · obtain ⟨hh, he⟩ := RayQuiver.eq_id_of_isIso v
    exact ⟨D.y, 𝟙 _, D.ω', hh, by simp, by rw [he]; simp⟩
  have hv0 : v ≠ 0 := fun h' ↦ h (by rw [h', comp_zero])
  obtain ⟨c, f, v₂, hf, hfv⟩ := exists_first_arrow' v hv0 hv
  have hτf : D.τ ≫ f ≠ 0 := fun h' ↦ h (by rw [hfv, ← Category.assoc, h', zero_comp])
  obtain ⟨hh, hfh⟩ := D.X4 hM f hf (D.not_ftm_ω hMo hG f hτf)
  by_cases hv₂ : IsIso v₂
  · obtain ⟨hc, he⟩ := RayQuiver.eq_id_of_isIso v₂
    exact ⟨c, f, hh, hc, hfh, by rw [hfv, he]⟩
  exfalso
  have hv₂0 : v₂ ≠ 0 := fun h' ↦ hv0 (by rw [hfv, h', comp_zero])
  obtain ⟨d, f₂, v₃, hf₂, hfv₂⟩ := exists_first_arrow' v₂ hv₂0 hv₂
  have hτff : D.τ ≫ f ≫ f₂ ≠ 0 := fun h' ↦ h (by
    rw [hfv, hfv₂, show D.τ ≫ f ≫ f₂ ≫ v₃ = (D.τ ≫ f ≫ f₂) ≫ v₃ by simp, h', zero_comp])
  have hhn : ¬IsIso hh := by
    intro hi
    apply hτf
    have : D.τ ≫ f = (D.τ ≫ D.ω') ≫ inv hh := by rw [← hfh]; simp
    rw [this, D.τω'_zero hMo hG, zero_comp]
  have hhi : IsIrreducible hh := by
    by_contra hni
    have hh0 : hh ≠ 0 := fun h' ↦ D.hτ0 (by rw [← hfh, h']; simp)
    obtain ⟨d', e₂, r, he₂, hr⟩ := exists_first_arrow' hh hh0 hhn
    have hrn : ¬IsIso r := fun h' ↦ hni (by rw [hr]; exact isIrreducible_comp_iso he₂ r)
    exact D.t_le_two hMo f e₂ r hf he₂ hrn (by rw [← hfh, hr])
  obtain ⟨h₃, hh₃⟩ := D.X6 hM f hh hf hhi hfh.symm f₂ hf₂ (by
    have := D.not_ftm_ω hMo hG (f ≫ f₂) hτff
    simpa using this)
  rcases hf₂.2.2 _ hh h₃ hh₃.symm with h' | h'
  · exact hhn h'
  · apply hτff
    rw [← hh₃, ← Category.assoc f, hfh, ← Category.assoc, D.τω'_zero hMo hG, zero_comp]

/-- `η` is not a product of two non-invertible factors one of which is not an arrow. -/
lemma η_two (hM : MildHyp k P) {c : P} (A : D.a ⟶ c) (B : c ⟶ D.x) (hA : ¬IsIso A)
    (hB : ¬IsIso B) (hirr : ¬IsIrreducible A ∨ ¬IsIrreducible B) (hη : D.η = A ≫ B) : False := by
  have hη0 : D.η ≠ 0 := fun h ↦ D.hτ0 (by rw [show D.γ ≫ D.α ≫ D.ω' ≫ D.α = D.τ from rfl, D.τ_η, h]; simp)
  have hB0 : B ≠ 0 := fun h ↦ hη0 (by rw [hη, h, comp_zero])
  have hA0 : A ≠ 0 := fun h ↦ hη0 (by rw [hη, h, zero_comp])
  obtain ⟨c₂, p₂, e₂, hp₂⟩ := MildContour.exists_last_arrow B hB0 hB
  by_cases hB₀ : IsIso (pathVal p₂)
  · have hBi : IsIrreducible B := by rw [hp₂]; exact isIrreducible_iso_comp _ e₂.2
    have hAn : ¬IsIrreducible A := by rcases hirr with h | h; exact h; exact absurd hBi h
    obtain ⟨c₁, p₁, e₁, hp₁⟩ := MildContour.exists_last_arrow A hA0 hA
    have hp₁n : ¬IsIso (pathVal p₁) := fun h ↦ hAn (by rw [hp₁]; exact isIrreducible_iso_comp _ e₁.2)
    exact D.s_le_two hM (pathVal p₁) e₁.1 B hp₁n e₁.2 hBi (by rw [hη, hp₁]; simp)
  · have hB₀0 : pathVal p₂ ≠ 0 := fun h ↦ hB0 (by rw [hp₂, h, zero_comp])
    obtain ⟨c₁, p₁, e₁, hp₁⟩ := MildContour.exists_last_arrow (pathVal p₂) hB₀0 hB₀
    exact D.s_le_two hM (A ≫ pathVal p₁) e₁.1 e₂.1 (not_isIso_comp_left' _ hA) e₁.2 e₂.2
      (by rw [hη, hp₂, hp₁]; simp)

/-- `ω'` is not a product of two non-invertible factors one of which is not an arrow. -/
lemma ω_two (hMo : MildHyp k Pᵒᵖ) {c : P} (A : D.y ⟶ c) (B : c ⟶ D.a) (hA : ¬IsIso A)
    (hB : ¬IsIso B) (hirr : ¬IsIrreducible A ∨ ¬IsIrreducible B) (hω : D.ω' = A ≫ B) :
    False := by
  have hω0 : D.ω' ≠ 0 := fun h ↦ D.hτ0 (by simp [h])
  have hB0 : B ≠ 0 := fun h ↦ hω0 (by rw [hω, h, comp_zero])
  have hA0 : A ≠ 0 := fun h ↦ hω0 (by rw [hω, h, zero_comp])
  obtain ⟨c₁, e₁, A₁, he₁, hA₁⟩ := exists_first_arrow' A hA0 hA
  by_cases hA₁i : IsIso A₁
  · have hAi : IsIrreducible A := by rw [hA₁]; exact isIrreducible_comp_iso he₁ A₁
    have hBn : ¬IsIrreducible B := by rcases hirr with h | h; exact absurd hAi h; exact h
    obtain ⟨c₂, e₂, B₁, he₂, hB₁⟩ := exists_first_arrow' B hB0 hB
    have hB₁n : ¬IsIso B₁ := fun h ↦ hBn (by rw [hB₁]; exact isIrreducible_comp_iso he₂ B₁)
    exact D.t_le_two hMo e₁ (A₁ ≫ e₂) B₁ he₁ (isIrreducible_iso_comp _ he₂) hB₁n
      (by rw [hω, hA₁, hB₁]; simp)
  · have hA₁0 : A₁ ≠ 0 := fun h ↦ hA0 (by rw [hA₁, h, comp_zero])
    obtain ⟨c₂, e₂, A₂, he₂, hA₂⟩ := exists_first_arrow' A₁ hA₁0 hA₁i
    exact D.t_le_two hMo e₁ e₂ (A₂ ≫ B) he₁ he₂ (not_isIso_comp_right' _ hB)
      (by rw [hω, hA₁, hA₂]; simp)

/-- The positions of `P_x`. -/
def IsPos {w : P} (μ : D.x ⟶ w) : Prop :=
  (∃ h : D.x = w, μ = eqToHom h) ∨
  (∃ h : D.a = w, μ = D.γ ≫ eqToHom h) ∨
  (∃ h : D.b = w, μ = D.δ ≫ eqToHom h) ∨
  (∃ (c : P) (ν : D.a ⟶ c) (ν' : c ⟶ D.x) (h : c = w),
    ¬IsIso ν ∧ ν ≫ ν' = D.η ∧ μ = D.γ ≫ ν ≫ eqToHom h) ∨
  (∃ (c : P) (ν : D.y ⟶ c) (ν' : c ⟶ D.a) (h : c = w),
    ν ≫ ν' = D.ω' ∧ μ = (D.γ ≫ D.α) ≫ ν ≫ eqToHom h) ∨
  (∃ h : D.b = w, μ = (D.γ ≫ D.η) ≫ D.δ ≫ eqToHom h) ∨
  (∃ (c : P) (ν : D.y ⟶ c) (ν' : c ⟶ D.a) (h : c = w),
    ν ≫ ν' = D.ω' ∧ μ = D.τ ≫ ν ≫ eqToHom h)

lemma pos_ω {w : P} (ν : D.y ⟶ w) (ν' : w ⟶ D.a) (h : ν ≫ ν' = D.ω') :
    D.IsPos ((D.γ ≫ D.α) ≫ ν) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨w, ν, ν', rfl, h, by simp⟩))))

lemma pos_ω_of {w : P} {μ : D.x ⟶ w} (ν : D.y ⟶ w) (ν' : w ⟶ D.a) (h : ν ≫ ν' = D.ω')
    (hμ : μ = (D.γ ≫ D.α) ≫ ν) : D.IsPos μ := by
  rw [hμ]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨w, ν, ν', rfl, h, by simp⟩))))

lemma pos_τ {w : P} (ν : D.y ⟶ w) (ν' : w ⟶ D.a) (h : ν ≫ ν' = D.ω') :
    D.IsPos (D.τ ≫ ν) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w, ν, ν', rfl, h, by simp⟩)))))

lemma pos_γν {w : P} (ν : D.a ⟶ w) (ν' : w ⟶ D.x) (hν : ¬IsIso ν) (h : ν ≫ ν' = D.η) :
    D.IsPos (D.γ ≫ ν) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨w, ν, ν', rfl, hν, h, by simp⟩)))

lemma pos_iso {w w' : P} {μ : D.x ⟶ w} (hμ : D.IsPos μ) (g : w ⟶ w') [IsIso g] :
    D.IsPos (μ ≫ g) := by
  obtain ⟨hh, he⟩ := RayQuiver.eq_id_of_isIso g
  subst hh; rw [he, eqToHom_refl, Category.comp_id]; exact hμ

lemma pos_γ : D.IsPos D.γ := Or.inr (Or.inl ⟨rfl, by simp⟩)

lemma pos_δ : D.IsPos D.δ := Or.inr (Or.inr (Or.inl ⟨rfl, by simp⟩))

lemma pos_σδ : D.IsPos ((D.γ ≫ D.η) ≫ D.δ) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp⟩)))))

lemma ftm_of_eq_τ {w : P} {μ : D.x ⟶ w} (v : D.y ⟶ w) (h : μ = D.τ ≫ v) :
    FactorsThroughMorphism D.τ μ := ⟨𝟙 _, v, by rw [h]; simp⟩

/-- An arrow `k ≫ h = e` between arrows forces `h` invertible. -/
lemma iso_of_arrow {s t t' : P} {k : s ⟶ t} {e : s ⟶ t'} (hk : IsIrreducible k)
    (he : IsIrreducible e) (h : t ⟶ t') (hh : k ≫ h = e) : IsIso h := by
  rcases he.2.2 _ k h hh.symm with h' | h'
  · exact absurd h' hk.2.1
  · exact h'

/-- **The step of the closure of `P_x`.** -/
theorem pos_step (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) {w w' : P}
    (μ : D.x ⟶ w) (hμ : D.IsPos μ) (e : w ⟶ w') (he : IsIrreducible e) (h0 : μ ≫ e ≠ 0) :
    D.IsPos (μ ≫ e) := by
  by_cases hn : FactorsThroughMorphism D.τ (μ ≫ e)
  · obtain ⟨v, hv⟩ := D.eq_τ_of_ftm hMo hG _ h0 hn
    obtain ⟨c, ν, ν', hc, hνν, hvν⟩ := D.tail hM hMo hG v (by rw [← hv]; exact h0)
    subst hc
    rw [hv, hvν, eqToHom_refl, Category.comp_id]; exact D.pos_τ ν ν' hνν
  rcases hμ with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨c, ν, ν', h, hν, hνη, rfl⟩ |
    ⟨c, ν, ν', h, hνω, rfl⟩ | ⟨h, rfl⟩ | ⟨c, ν, ν', h, hνω, rfl⟩ <;> subst h <;>
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hn h0 ⊢
  · -- `𝟙`
    rcases D.X1 hM hMo e he with ⟨g, hg⟩ | ⟨g, hg⟩
    · have := iso_of_arrow D.hγ he g hg
      rw [← hg]; exact D.pos_iso D.pos_γ g
    · have := iso_of_arrow D.hδ he g hg
      rw [← hg]; exact D.pos_iso D.pos_δ g
  · -- `γ`
    rcases D.X2 hM e he hn with ⟨g, hg⟩ | ⟨g, hg⟩
    · have := iso_of_arrow he D.hα g hg
      exact D.pos_ω_of (inv g) (g ≫ D.ω') (by simp) (by rw [← hg]; simp)
    · exact D.pos_γν e g he.2.1 hg
  · -- `δ`
    obtain ⟨g, hg⟩ := D.X3 hM e he hn
    have := iso_of_arrow D.hβ he g hg
    exact D.pos_ω_of g (inv g ≫ D.ω') (by simp) (by rw [← hg, ← Category.assoc, D.hval])
  · -- `γ ν` with `ν ν' = η`
    by_cases hν' : IsIso ν'
    · have hirr : IsIrreducible (inv ν' ≫ e) := isIrreducible_iso_comp _ he
      have hνe : ν = D.η ≫ inv ν' := by rw [← hνη]; simp
      rcases D.X1 hM hMo _ hirr with ⟨g, hg⟩ | ⟨g, hg⟩
      · have := iso_of_arrow D.hγ hirr g hg
        refine D.pos_ω_of (D.ω' ≫ g) (inv g) (by simp) ?_
        calc (D.γ ≫ ν) ≫ e = D.γ ≫ D.η ≫ (inv ν' ≫ e) := by rw [hνe]; simp
          _ = D.γ ≫ (D.η ≫ D.γ) ≫ g := by rw [← hg]; simp
          _ = (D.γ ≫ D.α) ≫ D.ω' ≫ g := by rw [← D.hD]; simp
      · have := iso_of_arrow D.hδ hirr g hg
        have h1 : (D.γ ≫ ν) ≫ e = ((D.γ ≫ D.η) ≫ D.δ) ≫ g := by
          calc (D.γ ≫ ν) ≫ e = D.γ ≫ D.η ≫ (inv ν' ≫ e) := by rw [hνe]; simp
            _ = _ := by rw [← hg]; simp
        rw [h1]; exact D.pos_iso D.pos_σδ g
    · have hν0 : ν ≠ 0 := fun h ↦ D.hτ0 (by
        rw [show D.γ ≫ D.α ≫ D.ω' ≫ D.α = D.τ from rfl, D.τ_η, ← hνη, h]; simp)
      have hνi : IsIrreducible ν := by
        by_contra h; exact D.η_two hM ν ν' hν hν' (Or.inl h) hνη.symm
      have hν'i : IsIrreducible ν' := by
        by_contra h; exact D.η_two hM ν ν' hν hν' (Or.inr h) hνη.symm
      obtain ⟨g, hg⟩ := D.X5 hM hMo ν ν' hνi hν'i hνη.symm e he (by simpa using hn)
      have := iso_of_arrow hν'i he g hg
      have h1 : (D.γ ≫ ν) ≫ e = D.γ ≫ (D.η ≫ g) := by rw [← hg, ← hνη]; simp
      rw [h1]
      exact D.pos_γν (D.η ≫ g) (inv g) (not_isIso_comp_left' _ D.hη) (by simp)
  · -- `ω ν` with `ν ν' = ω'`
    by_cases hνi : IsIso ν
    · have hirr : IsIrreducible (ν ≫ e) := isIrreducible_iso_comp _ he
      obtain ⟨g, hg⟩ := D.X4 hM (ν ≫ e) hirr (by simpa using hn)
      exact D.pos_ω_of (ν ≫ e) g hg (by simp)
    by_cases hν'i : IsIso ν'
    · exfalso
      have hirr : IsIrreducible (inv ν' ≫ e) := isIrreducible_iso_comp _ he
      have hνe : ν = D.ω' ≫ inv ν' := by rw [← hνω]; simp
      have h1 : ((D.γ ≫ D.α) ≫ ν) ≫ e = (D.γ ≫ D.η) ≫ D.γ ≫ (inv ν' ≫ e) := by
        rw [hνe, show (D.γ ≫ D.η) ≫ D.γ ≫ (inv ν' ≫ e) = D.γ ≫ (D.η ≫ D.γ) ≫ inv ν' ≫ e by simp,
          ← D.hD]; simp
      rw [h1] at hn
      rcases D.X2 hM _ hirr (fun h ↦ hn (ftm_comp_left h _)) with ⟨g, hg⟩ | ⟨g, hg⟩
      · have := iso_of_arrow hirr D.hα g hg
        exact hn (D.ftm_of_eq_τ (inv g) (by rw [D.τ_σω, ← hg]; simp))
      · have hz := D.zero₁ hM (inv ν' ≫ e) hirr g hg.symm
        apply hn
        have := ftm_comp_left hz (D.γ ≫ D.α)
        rw [show (D.γ ≫ D.η) ≫ D.γ ≫ (inv ν' ≫ e) = (D.γ ≫ D.α) ≫ D.ω' ≫ (inv ν' ≫ e) by
          rw [show (D.γ ≫ D.η) ≫ D.γ ≫ (inv ν' ≫ e) = D.γ ≫ (D.η ≫ D.γ) ≫ inv ν' ≫ e by simp,
            ← D.hD]; simp]
        exact this
    · have hνi' : IsIrreducible ν := by
        by_contra h; exact D.ω_two hMo ν ν' hνi hν'i (Or.inl h) hνω.symm
      have hν'i' : IsIrreducible ν' := by
        by_contra h; exact D.ω_two hMo ν ν' hνi hν'i (Or.inr h) hνω.symm
      obtain ⟨g, hg⟩ := D.X6 hM ν ν' hνi' hν'i' hνω.symm e he (by simpa using hn)
      have := iso_of_arrow hν'i' he g hg
      exact D.pos_ω_of (D.ω' ≫ g) (inv g) (by simp) (by rw [← hg, ← hνω]; simp)
  · -- `σ δ`
    obtain ⟨g, hg⟩ := D.X3 hM e he (fun h ↦ hn (by simpa using ftm_comp_left h (D.γ ≫ D.η)))
    exact absurd (D.ftm_of_eq_τ g (by rw [← hg, D.τ_ηδ]; simp)) hn
  · -- `τ ν`
    exact absurd (D.ftm_of_eq_τ (ν ≫ e) (by simp)) hn

/-- **Every nonzero morphism out of `x` is in a position.** -/
theorem pos_path (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) {z : RayVert P}
    (p : Quiver.Path (RayVert.mk D.x) z) : pathVal p ≠ 0 → D.IsPos (pathVal p) := by
  induction p with
  | nil => exact fun _ ↦ Or.inl ⟨rfl, rfl⟩
  | cons p e ih =>
      intro h
      exact D.pos_step hM hMo hG (pathVal p)
        (ih (fun h' ↦ h (by change pathVal p ≫ e.1 = 0; rw [h', zero_comp]))) e.1 e.2 h

theorem pos_all (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) {w : P} (μ : D.x ⟶ w)
    (hμ : μ ≠ 0) : D.IsPos μ := by
  obtain ⟨p, hp⟩ := exists_path μ hμ
  rw [← hp]; exact D.pos_path hM hMo hG p (by rw [hp]; exact hμ)

/-- Each position divides `τ`, except the tail positions `τ ν` with `ν` not invertible. -/
theorem pos_div (hM : MildHyp k P) {w : P} (μ : D.x ⟶ w) (hμ : D.IsPos μ) :
    (∃ g, μ ≫ g = D.τ) ∨ ∃ (ν : D.y ⟶ w) (ν' : w ⟶ D.a), ¬IsIso ν ∧ ν ≫ ν' = D.ω' ∧ μ = D.τ ≫ ν := by
  rcases hμ with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨c, ν, ν', h, hν, hνη, rfl⟩ |
    ⟨c, ν, ν', h, hνω, rfl⟩ | ⟨h, rfl⟩ | ⟨c, ν, ν', h, hνω, rfl⟩ <;> subst h <;>
    simp only [eqToHom_refl, Category.comp_id]
  · exact Or.inl ⟨D.τ, by simp⟩
  · exact Or.inl ⟨D.α ≫ D.ω' ≫ D.α, rfl⟩
  · exact Or.inl ⟨D.β ≫ D.ω' ≫ D.α, D.τ_w.symm⟩
  · exact Or.inl ⟨ν' ≫ D.γ ≫ D.α, by rw [D.τ_η, ← hνη]; simp⟩
  · exact Or.inl ⟨ν' ≫ D.α, by simp only [Category.assoc]; rw [← Category.assoc ν, hνω]⟩
  · exact Or.inl ⟨D.β, by rw [D.τ_ηδ]; simp⟩
  · by_cases hνi : IsIso ν
    · exact Or.inl ⟨inv ν, by simp⟩
    · exact Or.inr ⟨ν, ν', hνi, hνω, rfl⟩

/-- The **exceptional case**: `τ ≫ f ≠ 0` for the first arrow `f` of `ω'` (`ω'` of length
two). -/
def Exc : Prop :=
  ∃ (c : P) (f : D.y ⟶ c) (f' : c ⟶ D.a), IsIrreducible f ∧ f ≫ f' = D.ω' ∧ ¬IsIso f' ∧
    D.τ ≫ f ≠ 0

/-- **Outside the exceptional case, every nonzero morphism out of `x` divides `τ`.** -/
theorem div_τ (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) (hE : ¬D.Exc) {w : P}
    (μ : D.x ⟶ w) (hμ : μ ≠ 0) : ∃ g, μ ≫ g = D.τ := by
  rcases D.pos_div hM μ (D.pos_all hM hMo hG μ hμ) with h | ⟨ν, ν', hν, hνω, rfl⟩
  · exact h
  · exfalso
    by_cases hν' : IsIso ν'
    · apply hμ
      rw [show ν = D.ω' ≫ inv ν' by rw [← hνω]; simp, ← Category.assoc, D.τω'_zero hMo hG,
        zero_comp]
    · have hνi : IsIrreducible ν := by
        by_contra h; exact D.ω_two hMo ν ν' hν hν' (Or.inl h) hνω.symm
      exact hE ⟨w, ν, ν', hνi, hνω, hν', hμ⟩

/-- **Outside the exceptional case on both sides, `P_x` is projective-injective.** -/
theorem projInjAt_τ (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) (hE : ¬D.Exc)
    (hE' : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; ¬D.op.Exc) : ProjInjAt D.τ := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have hMoo : MildHyp k Pᵒᵖᵒᵖ := hMo.op
  refine projInjAt_of_div D.τ D.τ_ne_zero (fun μ hμ ↦ D.div_τ hM hMo hG hE μ hμ) ?_
  intro w ν hν
  obtain ⟨g, hg⟩ := D.op.div_τ hMo hMoo hG.op hE' ν.op
    (fun h ↦ hν (Quiver.Hom.op_inj (by rw [h]; rfl)))
  rw [D.op_τ] at hg
  exact ⟨g.unop, Quiver.Hom.op_inj hg⟩

end DiamondData

end RayCat

end LargeIndecomposable
