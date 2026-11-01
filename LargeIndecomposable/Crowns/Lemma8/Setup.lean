module

public import LargeIndecomposable.Crowns.Lemma7.Statement
public import LargeIndecomposable.Cleaving.Shapes.ShapeF81
public import LargeIndecomposable.Cleaving.Shapes.ShapeF82
public import LargeIndecomposable.Cleaving.Shapes.ShapeF83
public import LargeIndecomposable.Cleaving.Shapes.ShapeF84

/-!
# BO13a Lemma 8: set-up

* `MulBasis.no_crown4`: a minimal crown of length at least six excludes crowns of
  length four.
* `MulBasis.no_fig21`: **BO13a figure 2.1** — two morphisms `γ, δ` into `m`
  incomparable from the right and two morphisms `α, β` out of `m` incomparable
  from the left, with nonzero composites, give the crown
  `(γ ≫ α, δ ≫ α, δ ≫ β, γ ≫ β)` of length four.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- No crown of length four. -/
def NoCrown4 (P : Type) [Category.{0} P] [HasZeroMorphisms P] : Prop :=
  ∀ {a₀ a₁ b₀ b₁ : P} {f₀ : a₀ ⟶ b₀} {f₁ : a₁ ⟶ b₀} {f₂ : a₁ ⟶ b₁} {f₃ : a₀ ⟶ b₁},
    (¬∃ c, c ≫ f₁ = f₀) → (¬∃ c, c ≫ f₀ = f₁) → (¬∃ c, f₁ ≫ c = f₂) → (¬∃ c, f₂ ≫ c = f₁) →
      (¬∃ c, c ≫ f₃ = f₂) → (¬∃ c, c ≫ f₂ = f₃) → (¬∃ c, f₃ ≫ c = f₀) →
        (¬∃ c, f₀ ≫ c = f₃) → f₀ ≠ 0 → f₁ ≠ 0 → f₂ ≠ 0 → f₃ ≠ 0 → False

/-- A minimal crown of length at least six excludes crowns of length four. -/
lemma Crown.noCrown4 {C : Crown P} (hC : C.IsMin) (hn : 2 < C.n) : NoCrown4 P := by
  intro a₀ a₁ b₀ b₁ f₀ f₁ f₂ f₃ p1 p2 v1 v2 p3 p4 v3 v4 h0 h1 h2 h3
  rcases hC (Crown.mk4 f₀ f₁ f₂ f₃ p1 p2 v1 v2 p3 p4 v3 v4 h0 h1 h2 h3) with h | h
  · exact absurd h (by change ¬C.n < 2; omega)
  · exact absurd h.1 (by change C.n ≠ 2; omega)

/-- **BO13a figure 2.1** is not cleaving without crowns of length four. -/
lemma no_fig21 (hL : LeftCancel P) (hR : RightCancel P) (h4 : NoCrown4 P)
    {a₁ a₂ m c₁ c₂ : P} (γ : a₁ ⟶ m) (δ : a₂ ⟶ m) (α : m ⟶ c₁) (β : m ⟶ c₂)
    (hγδ : ¬∃ g, g ≫ γ = δ) (hδγ : ¬∃ g, g ≫ δ = γ) (hαβ : ¬∃ g, α ≫ g = β)
    (hβα : ¬∃ g, β ≫ g = α) (h1 : γ ≫ α ≠ 0) (h2 : δ ≫ α ≠ 0) (h3 : δ ≫ β ≠ 0)
    (h4' : γ ≫ β ≠ 0) : False := by
  refine h4 (f₀ := γ ≫ α) (f₁ := δ ≫ α) (f₂ := δ ≫ β) (f₃ := γ ≫ β)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h1 h2 h3 h4'
  · exact fun ⟨c, hc⟩ ↦ hδγ ⟨c, hR _ _ _ (by rw [Category.assoc, hc])
      (by rw [Category.assoc, hc]; exact h1)⟩
  · exact fun ⟨c, hc⟩ ↦ hγδ ⟨c, hR _ _ _ (by rw [Category.assoc, hc])
      (by rw [Category.assoc, hc]; exact h2)⟩
  · exact fun ⟨c, hc⟩ ↦ hαβ ⟨c, hL _ _ _ (by rw [← Category.assoc, hc])
      (by rw [← Category.assoc, hc]; exact h3)⟩
  · exact fun ⟨c, hc⟩ ↦ hβα ⟨c, hL _ _ _ (by rw [← Category.assoc, hc])
      (by rw [← Category.assoc, hc]; exact h2)⟩
  · exact fun ⟨c, hc⟩ ↦ hγδ ⟨c, hR _ _ _ (by rw [Category.assoc, hc])
      (by rw [Category.assoc, hc]; exact h3)⟩
  · exact fun ⟨c, hc⟩ ↦ hδγ ⟨c, hR _ _ _ (by rw [Category.assoc, hc])
      (by rw [Category.assoc, hc]; exact h4')⟩
  · exact fun ⟨c, hc⟩ ↦ hβα ⟨c, hL _ _ _ (by rw [← Category.assoc, hc])
      (by rw [← Category.assoc, hc]; exact h1)⟩
  · exact fun ⟨c, hc⟩ ↦ hαβ ⟨c, hL _ _ _ (by rw [← Category.assoc, hc])
      (by rw [← Category.assoc, hc]; exact h4')⟩

variable [IsRayCategory P]

/-- A long morphism divides no proper suffix of a nonzero composite. -/
lemma not_ftm_suffix_of_long {a b X Y Z : P} {τ : a ⟶ b} (hτ : IsLong τ) {p : X ⟶ Y}
    {f : Y ⟶ Z} (hp : ¬IsIso p) (h0 : p ≫ f ≠ 0) : ¬FactorsThroughMorphism τ f := by
  intro h
  have hf0 : f ≠ 0 := fun h' ↦ h0 (by rw [h', comp_zero])
  have hfl := hτ.of_factorsThrough hf0 h
  obtain ⟨hx, hy, he⟩ := hfl.2.2.2 (p ≫ f) h0 ⟨p, 𝟙 _, by simp⟩
  subst hx
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  obtain ⟨hp1, -⟩ := IsRayCategory.eq_id_of_two_sided f hf0 p (𝟙 _) (by rw [Category.comp_id, he])
  exact hp (by rw [hp1]; infer_instance)

/-- A long morphism divides no proper prefix of a nonzero composite. -/
lemma not_ftm_prefix_of_long {a b X Y Z : P} {τ : a ⟶ b} (hτ : IsLong τ) {f : X ⟶ Y}
    {q : Y ⟶ Z} (hq : ¬IsIso q) (h0 : f ≫ q ≠ 0) : ¬FactorsThroughMorphism τ f := by
  intro h
  have hf0 : f ≠ 0 := fun h' ↦ h0 (by rw [h', zero_comp])
  have hfl := hτ.of_factorsThrough hf0 h
  obtain ⟨hx, hy, he⟩ := hfl.2.2.2 (f ≫ q) h0 ⟨𝟙 _, q, by simp⟩
  subst hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  obtain ⟨-, hq1⟩ := IsRayCategory.eq_id_of_two_sided f hf0 (𝟙 _) q (by rw [Category.id_comp, he])
  exact hq (by rw [hq1]; infer_instance)

variable [IsFiniteRayCategory P]

/-- A long `σ` does not divide the neighbour `μ` of its neighbour `ρ` (valley `σ, ρ`, peak
`ρ, μ`). -/
lemma not_ftm_valley_peak (hQ : OneSidedCyclic P) {x y₀ y₁ x₂ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    {μ : x₂ ⟶ y₁} (hσ : IsLong σ) (hρ0 : ρ ≠ 0) (hμ0 : μ ≠ 0) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ) :
    ¬FactorsThroughMorphism σ μ := by
  intro h
  obtain ⟨hx, hy, he⟩ := hσ.2.2.2 μ hμ0 h
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  rw [he] at hm1 hm2
  exact not_parallel hQ σ ρ hσ.1 hρ0 hv1 hv2 hm1 hm2

/-- In a chain without crowns of length four, a long `σ t` does not divide `σ (t+2)`. -/
lemma ZChain.not_ftm_σ_add_two (h4 : NoCrown4 P) (Z : ZChain P) (t : ℕ) (hσ : IsLong (Z.σ t)) :
    ¬FactorsThroughMorphism (Z.σ t) (Z.σ (t + 2)) := by
  intro h
  obtain ⟨hx, hy, he⟩ := hσ.2.2.2 (Z.σ (t + 2)) (Z.σ_ne _) h
  have hf₃ : eqToHom hx.symm ≫ Z.σ (t + 2) = Z.σ t ≫ eqToHom hy.symm := by rw [he]; simp
  refine h4 (f₀ := Z.ρ (t + 1)) (f₁ := Z.σ (t + 1)) (f₂ := Z.ρ (t + 2))
    (f₃ := eqToHom hx.symm ≫ Z.σ (t + 2)) (Z.peak₁ (t + 1)) (Z.peak₂ (t + 1)) (Z.valley₁ (t + 1))
    (Z.valley₂ (t + 1)) ?_ ?_ ?_ ?_ (Z.ρ_ne _) (Z.σ_ne _) (Z.ρ_ne _) ?_
  · rintro ⟨c, hc⟩
    exact Z.peak₁ (t + 2) ⟨c ≫ eqToHom hx.symm, by rw [← hc, Category.assoc]⟩
  · rintro ⟨c, hc⟩
    exact Z.peak₂ (t + 2) ⟨eqToHom hx ≫ c, by rw [Category.assoc, hc]; simp⟩
  · rintro ⟨c, hc⟩
    exact Z.valley₁ t ⟨eqToHom hy.symm ≫ c, by rw [← hc, hf₃, Category.assoc]⟩
  · rintro ⟨c, hc⟩
    exact Z.valley₂ t ⟨c ≫ eqToHom hy, by
      rw [← Category.assoc, hc, hf₃, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]⟩
  · intro h0
    apply Z.σ_ne (t + 2)
    have e : Z.σ (t + 2) = eqToHom hx ≫ (eqToHom hx.symm ≫ Z.σ (t + 2)) := by simp
    rw [e, h0, comp_zero]

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a figure 8.1** (`Ẽ₇`): `ρ₂` does not factor through `σ₂'`. -/
theorem l8_f81
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {x x₂ x₃ xn y₀ y₁ z₂ a b : P} {σ₁ : x ⟶ y₀} {ρ₁ : x ⟶ y₁} {σ₂ : x₂ ⟶ y₁} {ρ₂ : x₂ ⟶ z₂}
    {σ₃ : x₃ ⟶ z₂} {ρn : xn ⟶ y₀}
    (hp1 : ¬∃ c, c ≫ σ₂ = ρ₁) (hp2 : ¬∃ c, c ≫ ρ₁ = σ₂) (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂)
    (hs1 : ¬∃ c, c ≫ σ₃ = ρ₂) (hs2 : ¬∃ c, c ≫ ρ₂ = σ₃) (hq1 : ¬∃ c, c ≫ σ₁ = ρn)
    (hq2 : ¬∃ c, c ≫ ρn = σ₁) (hv2 : ¬∃ c, ρ₁ ≫ c = σ₁)
    (hiρ₂ : ¬IsIso ρ₂) (hiσ₃ : ¬IsIso σ₃)
    (V₁ : x ⟶ a) (V₂ : a ⟶ y₀) (hV : V₁ ≫ V₂ = σ₁) (hiV₁ : ¬IsIso V₁)
    (W₁ : x ⟶ b) (W₂ : b ⟶ y₀) (hW : W₁ ≫ W₂ = σ₁) (hiW₁ : ¬IsIso W₁)
    (hWV : ¬∃ g, W₁ ≫ g = V₁) (hVW : ¬∃ g, V₁ ≫ g = W₁) (hWρ : ¬∃ g, W₁ ≫ g = ρ₁)
    (ρ₁' : a ⟶ y₁) (hρ₁' : V₁ ≫ ρ₁' = ρ₁) (σ₂' : x₂ ⟶ a) (hσ₂' : σ₂' ≫ ρ₁' = σ₂)
    (r : xn ⟶ b) (hr : r ≫ W₂ = ρn) (hP1 : ¬∃ g, σ₂' ≫ g = ρ₂)
    {a' b' : P} (τ : a' ⟶ b') (hτ : IsLong τ)
    (h0ρ₁' : ¬FactorsThroughMorphism τ ρ₁') (h0W₁ : ¬FactorsThroughMorphism τ W₁)
    (h0V₁ : ¬FactorsThroughMorphism τ V₁) (h0ρ₁ : ¬FactorsThroughMorphism τ ρ₁)
    (h0r : ¬FactorsThroughMorphism τ r) (h0σ₂' : ¬FactorsThroughMorphism τ σ₂')
    (h0σ₂ : ¬FactorsThroughMorphism τ σ₂) (h0ρ₂ : ¬FactorsThroughMorphism τ ρ₂)
    (h0σ₃ : ¬FactorsThroughMorphism τ σ₃) : False := by
  refine B.not_f81 hmin hL hR τ hτ.2.1 hτ.1 r W₁ V₁ ρ₁' σ₂' ρ₂ σ₃ h0ρ₁' h0W₁ h0V₁
    (by rw [hρ₁']; exact h0ρ₁) h0r h0σ₂' (by rw [hσ₂']; exact h0σ₂) h0ρ₂ h0σ₃
    (fun h ↦ hq2 ⟨W₁ ≫ inv r, by rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, hW]⟩) hiW₁
    hiV₁ (fun h ↦ hv2 ⟨inv ρ₁' ≫ V₂, by rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc, hV]⟩)
    (fun h ↦ hp1 ⟨V₁ ≫ inv σ₂', by rw [← hρ₁', ← hσ₂']; simp⟩) hiρ₂ hiσ₃ hWV
    (by rw [hρ₁']; exact hWρ) hVW hP1
    (fun ⟨g, hg⟩ ↦ hw2 ⟨g ≫ ρ₁', by rw [← Category.assoc, hg, hσ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [hg, hσ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
    (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
    (fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hW, ← hg, ← hr, Category.assoc]⟩)
    (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hr, ← hg, Category.assoc, hW]⟩) hs2 hs1

include B in
/-- **BO13a figure 8.2** (`D̃₆`): `σₙ = ρₙ' ≫ σₙ'`. -/
theorem l8_f82
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {x x₂ xn y₀ y₁ z₂ yn a b : P} {σ₁ : x ⟶ y₀} {ρ₁ : x ⟶ y₁} {σ₂ : x₂ ⟶ y₁} {ρ₂ : x₂ ⟶ z₂}
    {ρn : xn ⟶ y₀} {σn : xn ⟶ yn}
    (hv1 : ¬∃ c, σ₁ ≫ c = ρ₁) (hv2 : ¬∃ c, ρ₁ ≫ c = σ₁) (hw1 : ¬∃ c, σ₂ ≫ c = ρ₂)
    (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂) (hq2 : ¬∃ c, c ≫ ρn = σ₁) (hu1 : ¬∃ c, σn ≫ c = ρn)
    (hu2 : ¬∃ c, ρn ≫ c = σn) (hσ₁0 : σ₁ ≠ 0) (hρ₂0 : ρ₂ ≠ 0)
    (V₁ : x ⟶ a) (V₂ : a ⟶ y₀) (hV : V₁ ≫ V₂ = σ₁) (hiV₂ : ¬IsIso V₂)
    (W₁ : x ⟶ b) (W₂ : b ⟶ y₀) (hW : W₁ ≫ W₂ = σ₁) (hiW₂ : ¬IsIso W₂)
    (hWV₂ : ¬∃ g, g ≫ W₂ = V₂) (hVW₂ : ¬∃ g, g ≫ V₂ = W₂) (hρnV₂ : ¬∃ g, g ≫ V₂ = ρn)
    (ρ₁' : a ⟶ y₁) (hρ₁' : V₁ ≫ ρ₁' = ρ₁) (σ₂' : x₂ ⟶ a) (hσ₂' : σ₂' ≫ ρ₁' = σ₂)
    (ρ₂' : a ⟶ z₂) (hρ₂' : σ₂' ≫ ρ₂' = ρ₂) (hz : σ₂' ≫ V₂ = 0) (hz' : V₁ ≫ ρ₂' = 0)
    (r : xn ⟶ b) (hr : r ≫ W₂ = ρn) (s : b ⟶ yn) (hs : r ≫ s = σn)
    {a' b' : P} (τ : a' ⟶ b') (hτ : IsLong τ)
    (h0s : ¬FactorsThroughMorphism τ s) (h0W₂ : ¬FactorsThroughMorphism τ W₂)
    (h0r : ¬FactorsThroughMorphism τ r) (h0σn : ¬FactorsThroughMorphism τ σn)
    (h0ρn : ¬FactorsThroughMorphism τ ρn) (h0V₂ : ¬FactorsThroughMorphism τ V₂)
    (h0ρ₁' : ¬FactorsThroughMorphism τ ρ₁') (h0ρ₂' : ¬FactorsThroughMorphism τ ρ₂') : False := by
  refine B.not_f82 hmin hL hR τ hτ.2.1 hτ.1 r s W₂ V₂ ρ₁' ρ₂' h0s h0W₂ h0r
    (by rw [hs]; exact h0σn) (by rw [hr]; exact h0ρn) h0V₂ h0ρ₁' h0ρ₂'
    (fun h ↦ hq2 ⟨W₁ ≫ inv r, by rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, hW]⟩)
    (fun h ↦ hu1 ⟨inv s ≫ W₂, by rw [← hs, Category.assoc, IsIso.hom_inv_id_assoc, hr]⟩)
    hiW₂ hiV₂
    (fun h ↦ hv2 ⟨inv ρ₁' ≫ V₂, by rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc, hV]⟩)
    (fun h ↦ hw2 ⟨inv ρ₂' ≫ ρ₁', by rw [← hρ₂', Category.assoc, IsIso.hom_inv_id_assoc, hσ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hu1 ⟨g, by rw [← hs, Category.assoc, hg, hr]⟩)
    (fun ⟨g, hg⟩ ↦ hu2 ⟨g, by rw [← hr, Category.assoc, hg, hs]⟩)
    (fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hV, Category.assoc, hg, hρ₁']⟩)
    (fun ⟨g, hg⟩ ↦ hρ₂0 (by rw [← hρ₂', ← hg, ← Category.assoc, hz, zero_comp]))
    (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ₁', Category.assoc, hg, hV]⟩)
    (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂', Category.assoc, hg, hρ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hσ₁0 (by rw [← hV, ← hg, ← Category.assoc, hz', zero_comp]))
    (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂']⟩)
    hWV₂ hVW₂ (by rw [hr]; exact hρnV₂)

include B in
/-- **BO13a figure 8.3** (`Ẽ₈` type with `σ₂' ≫ v₂ = 0`): `σ₃` does not factor through
`ρ₂'`. -/
theorem l8_f83
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {x x₂ x₃ xn y₀ y₁ z₂ a b t : P} {σ₁ : x ⟶ y₀} {ρ₁ : x ⟶ y₁} {σ₂ : x₂ ⟶ y₁}
    {ρ₂ : x₂ ⟶ z₂} {σ₃ : x₃ ⟶ z₂} {ρn : xn ⟶ y₀}
    (hv1 : ¬∃ c, σ₁ ≫ c = ρ₁) (hv2 : ¬∃ c, ρ₁ ≫ c = σ₁) (hw1 : ¬∃ c, σ₂ ≫ c = ρ₂)
    (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂) (hs1 : ¬∃ c, c ≫ σ₃ = ρ₂) (hq2 : ¬∃ c, c ≫ ρn = σ₁)
    (hp1 : ¬∃ c, c ≫ σ₂ = ρ₁) (hσ₁0 : σ₁ ≠ 0) (hρ₂0 : ρ₂ ≠ 0) (hiσ₃ : ¬IsIso σ₃)
    (V₁ : x ⟶ a) (V₂ : a ⟶ y₀) (hV : V₁ ≫ V₂ = σ₁) (hiV₂ : ¬IsIso V₂)
    (W₁ : x ⟶ b) (W₂ : b ⟶ y₀) (hW : W₁ ≫ W₂ = σ₁) (hiW₂ : ¬IsIso W₂)
    (hWV₂ : ¬∃ g, g ≫ W₂ = V₂) (hVW₂ : ¬∃ g, g ≫ V₂ = W₂) (hρnV₂ : ¬∃ g, g ≫ V₂ = ρn)
    (ρ₁' : a ⟶ y₁) (hρ₁' : V₁ ≫ ρ₁' = ρ₁) (σ₂' : x₂ ⟶ a) (hσ₂' : σ₂' ≫ ρ₁' = σ₂)
    (ρ₂' : a ⟶ z₂) (hρ₂' : σ₂' ≫ ρ₂' = ρ₂) (hz : σ₂' ≫ V₂ = 0) (hz' : V₁ ≫ ρ₂' = 0)
    (r : xn ⟶ b) (hr : r ≫ W₂ = ρn) (φ : xn ⟶ t) (hiφ : ¬IsIso φ)
    (hrφ : ¬∃ g, r ≫ g = φ) (hφρ : ¬∃ g, φ ≫ g = ρn) (hP2b : ¬∃ g, g ≫ ρ₂' = σ₃)
    {a' b' : P} (τ : a' ⟶ b') (hτ : IsLong τ)
    (h0W₂ : ¬FactorsThroughMorphism τ W₂) (h0V₂ : ¬FactorsThroughMorphism τ V₂)
    (h0ρ₁' : ¬FactorsThroughMorphism τ ρ₁') (h0ρ₂' : ¬FactorsThroughMorphism τ ρ₂')
    (h0r : ¬FactorsThroughMorphism τ r) (h0φ : ¬FactorsThroughMorphism τ φ)
    (h0ρn : ¬FactorsThroughMorphism τ ρn) (h0σ₂' : ¬FactorsThroughMorphism τ σ₂')
    (h0σ₂ : ¬FactorsThroughMorphism τ σ₂) (h0ρ₂ : ¬FactorsThroughMorphism τ ρ₂)
    (h0σ₃ : ¬FactorsThroughMorphism τ σ₃)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F83.thin) k)) : False := by
  refine B.not_f83 hmin hL hR τ hτ.2.1 hτ.1 φ r W₂ V₂ ρ₁' σ₂' ρ₂' σ₃ hD hz h0W₂ h0V₂ h0ρ₁'
    h0ρ₂' h0r h0φ (by rw [hr]; exact h0ρn) h0σ₂' (by rw [hσ₂']; exact h0σ₂)
    (by rw [hρ₂']; exact h0ρ₂) h0σ₃ hiφ
    (fun h ↦ hq2 ⟨W₁ ≫ inv r, by rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, hW]⟩)
    hiW₂ hiV₂
    (fun h ↦ hv2 ⟨inv ρ₁' ≫ V₂, by rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc, hV]⟩)
    (fun h ↦ hp1 ⟨V₁ ≫ inv σ₂', by rw [← hρ₁', ← hσ₂']; simp⟩)
    (fun h ↦ hw2 ⟨inv ρ₂' ≫ ρ₁', by rw [← hρ₂', Category.assoc, IsIso.hom_inv_id_assoc, hσ₂']⟩)
    hiσ₃
    (fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hV, Category.assoc, hg, hρ₁']⟩)
    (fun ⟨g, hg⟩ ↦ hρ₂0 (by rw [← hρ₂', ← hg, ← Category.assoc, hz, zero_comp]))
    (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ₁', Category.assoc, hg, hV]⟩)
    (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂', Category.assoc, hg, hρ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hσ₁0 (by rw [← hV, ← hg, ← Category.assoc, hz', zero_comp]))
    (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂']⟩)
    hrφ (fun ⟨g, hg⟩ ↦ hφρ ⟨g ≫ W₂, by rw [← Category.assoc, hg, hr]⟩)
    (fun ⟨g, hg⟩ ↦ hφρ ⟨g, by rw [hg, hr]⟩) hWV₂ (by rw [hr]; exact hρnV₂) hVW₂ hP2b
    (fun ⟨g, hg⟩ ↦ hs1 ⟨σ₂' ≫ g, by rw [Category.assoc, hg, hρ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hs1 ⟨g, by rw [hg, hρ₂']⟩)

include B in
/-- **BO13a figure 8.4**: `σ₃ = σ₃' ≫ ρ₂'` with `v₁ ≫ ρ₂' = σ₃' ≫ ρ₁' = 0`. -/
theorem l8_f84
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {x x₂ x₃ xn y₀ y₁ z₂ a b t : P} {σ₁ : x ⟶ y₀} {ρ₁ : x ⟶ y₁} {σ₂ : x₂ ⟶ y₁}
    {ρ₂ : x₂ ⟶ z₂} {σ₃ : x₃ ⟶ z₂} {ρn : xn ⟶ y₀}
    (hv2 : ¬∃ c, ρ₁ ≫ c = σ₁) (hp1 : ¬∃ c, c ≫ σ₂ = ρ₁) (hp2 : ¬∃ c, c ≫ ρ₁ = σ₂)
    (hw1 : ¬∃ c, σ₂ ≫ c = ρ₂) (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂) (hs1 : ¬∃ c, c ≫ σ₃ = ρ₂)
    (hs2 : ¬∃ c, c ≫ ρ₂ = σ₃) (hq1 : ¬∃ c, c ≫ σ₁ = ρn) (hq2 : ¬∃ c, c ≫ ρn = σ₁)
    (hρ₁0 : ρ₁ ≠ 0) (hσ₃0 : σ₃ ≠ 0)
    (V₁ : x ⟶ a) (V₂ : a ⟶ y₀) (hV : V₁ ≫ V₂ = σ₁) (hiV₁ : ¬IsIso V₁)
    (W₁ : x ⟶ b) (W₂ : b ⟶ y₀) (hW : W₁ ≫ W₂ = σ₁) (hiW₁ : ¬IsIso W₁)
    (hWV : ¬∃ g, W₁ ≫ g = V₁) (hVW : ¬∃ g, V₁ ≫ g = W₁) (hWρ : ¬∃ g, W₁ ≫ g = ρ₁)
    (ρ₁' : a ⟶ y₁) (hρ₁' : V₁ ≫ ρ₁' = ρ₁) (σ₂' : x₂ ⟶ a) (hσ₂' : σ₂' ≫ ρ₁' = σ₂)
    (ρ₂' : a ⟶ z₂) (hρ₂' : σ₂' ≫ ρ₂' = ρ₂) (hz' : V₁ ≫ ρ₂' = 0)
    (σ₃' : x₃ ⟶ a) (hσ₃' : σ₃' ≫ ρ₂' = σ₃) (hz₃ : σ₃' ≫ ρ₁' = 0)
    (r : xn ⟶ b) (hr : r ≫ W₂ = ρn) (φ : xn ⟶ t) (hiφ : ¬IsIso φ)
    (hrφ : ¬∃ g, r ≫ g = φ) (hφρ : ¬∃ g, φ ≫ g = ρn)
    {a' b' : P} (τ : a' ⟶ b') (hτ : IsLong τ)
    (h0ρ₁' : ¬FactorsThroughMorphism τ ρ₁') (h0ρ₂' : ¬FactorsThroughMorphism τ ρ₂')
    (h0W₁ : ¬FactorsThroughMorphism τ W₁) (h0V₁ : ¬FactorsThroughMorphism τ V₁)
    (h0ρ₁ : ¬FactorsThroughMorphism τ ρ₁) (h0r : ¬FactorsThroughMorphism τ r)
    (h0φ : ¬FactorsThroughMorphism τ φ) (h0σ₂' : ¬FactorsThroughMorphism τ σ₂')
    (h0σ₂ : ¬FactorsThroughMorphism τ σ₂) (h0ρ₂ : ¬FactorsThroughMorphism τ ρ₂)
    (h0σ₃' : ¬FactorsThroughMorphism τ σ₃') (h0σ₃ : ¬FactorsThroughMorphism τ σ₃)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F84.thin) k)) : False := by
  refine B.not_f84 hmin hL hR τ hτ.2.1 hτ.1 φ r W₁ V₁ σ₂' σ₃' ρ₁' ρ₂' hD hz' hz₃ h0ρ₁' h0ρ₂'
    h0W₁ h0V₁ (by rw [hρ₁']; exact h0ρ₁) h0r h0φ h0σ₂' (by rw [hσ₂']; exact h0σ₂)
    (by rw [hρ₂']; exact h0ρ₂) h0σ₃' (by rw [hσ₃']; exact h0σ₃) hiφ
    (fun h ↦ hq2 ⟨W₁ ≫ inv r, by rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, hW]⟩) hiW₁
    hiV₁ (fun h ↦ hp1 ⟨V₁ ≫ inv σ₂', by rw [← hρ₁', ← hσ₂']; simp⟩)
    (fun h ↦ hs1 ⟨σ₂' ≫ inv σ₃', by rw [← hρ₂', ← hσ₃']; simp⟩)
    (fun h ↦ hv2 ⟨inv ρ₁' ≫ V₂, by rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc, hV]⟩)
    (fun h ↦ hw2 ⟨inv ρ₂' ≫ ρ₁', by rw [← hρ₂', Category.assoc, IsIso.hom_inv_id_assoc, hσ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hw1 ⟨g, by rw [← hσ₂', Category.assoc, hg, hρ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂']⟩) hWV
    (by rw [hρ₁']; exact hWρ) hVW hrφ
    (fun ⟨g, hg⟩ ↦ hφρ ⟨g ≫ W₂, by rw [← Category.assoc, hg, hr]⟩)
    (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hr, ← hg, Category.assoc, hW]⟩)
    (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
    (fun ⟨g, hg⟩ ↦ hσ₃0 (by rw [← hσ₃', ← hg, Category.assoc, hz', comp_zero]))
    (fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hW, ← hg, ← hr, Category.assoc]⟩)
    (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hρ₁', ← hσ₂', ← hg, Category.assoc]⟩)
    (fun ⟨g, hg⟩ ↦ hs2 ⟨g, by rw [← hσ₃', ← hg, Category.assoc, hρ₂']⟩)
    (fun ⟨g, hg⟩ ↦ hρ₁0 (by rw [← hρ₁', ← hg, Category.assoc, hz₃, comp_zero]))
    (fun ⟨g, hg⟩ ↦ hs1 ⟨g, by rw [← hρ₂', ← hg, Category.assoc, hσ₃']⟩)

end MulBasis

end RayQuiver

end LargeIndecomposable
