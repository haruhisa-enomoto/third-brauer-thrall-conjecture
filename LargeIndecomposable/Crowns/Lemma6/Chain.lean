module

public import LargeIndecomposable.Crowns.Lemma6.Figure6466
public import LargeIndecomposable.Crowns.Basic.CrownFour
public import LargeIndecomposable.Crowns.Lemma5.LongCase

/-!
# Chain facts for BO13a Lemma 6

* `Crown.ftm_of_rayMor_eq`, `Crown.long_meets`: every long morphism divides an
  entry of the chain of a crown (`crown_meets`).
* `Crown.ρ_add_two_mul`, `Crown.σ_add_two_mul`, `Crown.weight_chain`: for
  crowns of length four.
* `MulBasis.l6_caseI_i`: case I.2.c with `ρₙ' ≫ u₂' ≠ 0` (then `n = 2`),
  abstractly: from `depth σ₂ ≤ depth (ρₙ' ≫ u₂')` and the fact that long
  morphisms divide crown entries.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma ftm_of_rayMor_eq {a b : P} {μ : a ⟶ b} {f g : RayMor P} (h : f = g)
    (hf : FactorsThroughMorphism μ f.2.2) : FactorsThroughMorphism μ g.2.2 := h ▸ hf

lemma rayMor_eq_of_eqToHom' (g : RayMor P) {X Y : P} (h1 : X = g.1) (h2 : g.2.1 = Y) :
    (⟨X, Y, eqToHom h1 ≫ g.2.2 ≫ eqToHom h2⟩ : RayMor P) = g := by
  obtain ⟨g1, g2, g3⟩ := g
  change X = g1 at h1
  change g2 = Y at h2
  subst h1 h2
  simp

lemma depth_of_rayMor_eq {f g : RayMor P} (h : f = g) : depth f.2.2 = depth g.2.2 := h ▸ rfl

section TSEF

variable [IsRayCategory P]

/-- A two-sided multiple of `f` of depth at most that of `f` is `f`. -/
lemma eq_of_tsef_depth {X Y : P} {f g : X ⟶ Y} (hg0 : g ≠ 0)
    (h : TwoSidedEndomorphismFactors f g) (hd : depth g ≤ depth f) : g = f := by
  obtain ⟨a₀, b₀, hab₀⟩ := h
  obtain ⟨a, ha'⟩ : ∃ a : X ⟶ X, a = a₀ := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b : Y ⟶ Y, b = b₀ := ⟨_, rfl⟩
  have hab : g = a ≫ f ≫ b := by rw [hab₀, ha', hb', Category.assoc]
  have ha0 : (a ≫ f ≫ b) ≠ 0 := by rw [← hab]; exact hg0
  have hfb0 : f ≫ b ≠ 0 := fun h0 ↦ ha0 (by rw [h0, comp_zero])
  have hai : IsIso a := by
    by_contra ha
    have h1 := depth_lt_comp_left a (f ≫ b) ha0 ha
    have h2 := depth_le_comp_right f b hfb0
    rw [← hab] at h1
    omega
  have hbi : IsIso b := by
    by_contra hb
    have h1 := depth_lt_comp_right f b hfb0 hb
    have h2 := depth_le_comp_left a (f ≫ b) ha0
    rw [← hab] at h2
    omega
  obtain ⟨_, ha⟩ := eq_eqToHom_of_isIso a
  obtain ⟨_, hb⟩ := eq_eqToHom_of_isIso b
  rw [hab, ha, hb]
  simp

end TSEF

namespace Crown

variable [IsRayCategory P] (C : Crown P)

lemma ρ_add_two_mul (hn : C.n = 2) (t k : ℕ) :
    (⟨_, _, C.toZChain.ρ (t + 2 * k)⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ t⟩ := by
  rw [toZChain_ρ, toZChain_ρ, show 2 * (t + 2 * k) = 2 * t + 2 * C.n * k by rw [hn]; ring,
    C.f_add_mul]

lemma σ_add_two_mul (hn : C.n = 2) (t k : ℕ) :
    (⟨_, _, C.toZChain.σ (t + 2 * k)⟩ : RayMor P) = ⟨_, _, C.toZChain.σ t⟩ := by
  rw [toZChain_σ, toZChain_σ, show 2 * (t + 2 * k) + 1 = 2 * t + 1 + 2 * C.n * k by
    rw [hn]; ring, C.f_add_mul]

/-- For a crown of length four, every `ρ` is one of two. -/
lemma ρ_n2 (hn : C.n = 2) (r t : ℕ) :
    (⟨_, _, C.toZChain.ρ t⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ (r + 1)⟩ ∨
      (⟨_, _, C.toZChain.ρ t⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ (r + 2)⟩ := by
  have e1 := C.ρ_add_two_mul hn (t % 2) (t / 2)
  rw [show t % 2 + 2 * (t / 2) = t by omega] at e1
  rcases Nat.lt_or_ge (t % 2) 2 with h | h
  · rcases Nat.mod_two_eq_zero_or_one (r + 1) with hr | hr
    · rcases Nat.mod_two_eq_zero_or_one t with ht | ht
      · left
        have e2 := C.ρ_add_two_mul hn ((r + 1) % 2) ((r + 1) / 2)
        rw [show (r + 1) % 2 + 2 * ((r + 1) / 2) = r + 1 by omega] at e2
        rw [e1, e2, ht, hr]
      · right
        have e2 := C.ρ_add_two_mul hn ((r + 2) % 2) ((r + 2) / 2)
        rw [show (r + 2) % 2 + 2 * ((r + 2) / 2) = r + 2 by omega] at e2
        rw [e1, e2, ht, show (r + 2) % 2 = 1 by omega]
    · rcases Nat.mod_two_eq_zero_or_one t with ht | ht
      · right
        have e2 := C.ρ_add_two_mul hn ((r + 2) % 2) ((r + 2) / 2)
        rw [show (r + 2) % 2 + 2 * ((r + 2) / 2) = r + 2 by omega] at e2
        rw [e1, e2, ht, show (r + 2) % 2 = 0 by omega]
      · left
        have e2 := C.ρ_add_two_mul hn ((r + 1) % 2) ((r + 1) / 2)
        rw [show (r + 1) % 2 + 2 * ((r + 1) / 2) = r + 1 by omega] at e2
        rw [e1, e2, ht, hr]
  · omega

/-- For a crown of length four, every `σ` is one of two. -/
lemma σ_n2 (hn : C.n = 2) (r t : ℕ) :
    (⟨_, _, C.toZChain.σ t⟩ : RayMor P) = ⟨_, _, C.toZChain.σ (r + 1)⟩ ∨
      (⟨_, _, C.toZChain.σ t⟩ : RayMor P) = ⟨_, _, C.toZChain.σ (r + 2)⟩ := by
  have e1 := C.σ_add_two_mul hn (t % 2) (t / 2)
  rw [show t % 2 + 2 * (t / 2) = t by omega] at e1
  rcases Nat.mod_two_eq_zero_or_one (r + 1) with hr | hr
  · rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · left
      have e2 := C.σ_add_two_mul hn ((r + 1) % 2) ((r + 1) / 2)
      rw [show (r + 1) % 2 + 2 * ((r + 1) / 2) = r + 1 by omega] at e2
      rw [e1, e2, ht, hr]
    · right
      have e2 := C.σ_add_two_mul hn ((r + 2) % 2) ((r + 2) / 2)
      rw [show (r + 2) % 2 + 2 * ((r + 2) / 2) = r + 2 by omega] at e2
      rw [e1, e2, ht, show (r + 2) % 2 = 1 by omega]
  · rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · right
      have e2 := C.σ_add_two_mul hn ((r + 2) % 2) ((r + 2) / 2)
      rw [show (r + 2) % 2 + 2 * ((r + 2) / 2) = r + 2 by omega] at e2
      rw [e1, e2, ht, show (r + 2) % 2 = 0 by omega]
    · left
      have e2 := C.σ_add_two_mul hn ((r + 1) % 2) ((r + 1) / 2)
      rw [show (r + 1) % 2 + 2 * ((r + 1) / 2) = r + 1 by omega] at e2
      rw [e1, e2, ht, hr]

/-- The weight of a crown of length four in terms of its chain. -/
lemma weight_chain (hn : C.n = 2) (r : ℕ) :
    C.weight = depth (C.toZChain.ρ (r + 1)) + depth (C.toZChain.σ (r + 1)) +
      depth (C.toZChain.ρ (r + 2)) + depth (C.toZChain.σ (r + 2)) := by
  rw [C.weight_two hn (2 * (r + 1))]
  have e1 := depth_of_rayMor_eq (C.toZChain_σ (r + 1))
  have e2 := depth_of_rayMor_eq (C.toZChain_σ (r + 2))
  have e3 := depth_of_rayMor_eq (C.toZChain_ρ (r + 2))
  simp only at e1 e2 e3
  rw [e1, e2, e3, show 2 * (r + 1) + 3 = 2 * (r + 2) + 1 by ring]
  rfl

end Crown

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- Every long morphism divides an entry of the chain of a crown. -/
theorem long_meets
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (C : Crown P) {a b : P} (μ : a ⟶ b) (hμ : IsLong μ) :
    ∃ t, FactorsThroughMorphism μ (C.toZChain.ρ t) ∨
      FactorsThroughMorphism μ (C.toZChain.σ t) := by
  rcases B.crown_meets hmin μ hμ.2.1 hμ.1 C.toClosedChain with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact ⟨i.1, Or.inl hi⟩
  · refine ⟨i.1, Or.inr ?_⟩
    have e : (⟨_, _, C.toClosedChain.σ i⟩ : RayMor P) = C.f (2 * i.1 + 1) := by
      unfold Crown.toClosedChain ClosedChain.ofSeq midMor
      dsimp only
      exact rayMor_eq_of_eqToHom' _ _ _
    exact ftm_of_rayMor_eq ((e.trans (C.toZChain_σ i.1).symm)) hi

include B in
/-- **BO13a Lemma 6, case I.2.c with `ρₙ' ≫ u₂' ≠ 0`.** Here `σ₂` is transported
to the common domain `x'` of `ρₙ`; `hdep` comes from the minimality of the crown
and `hlongs` from `long_meets` (both for a crown of length four). -/
theorem l6_caseI_i
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) {x' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0)
    (hρnl : ¬IsLong ρn) (hiρn : ¬IsIso ρn) (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (σ₂ : x' ⟶ y₁) (hσ₂ : IsLong σ₂) (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂)
    (hq1 : ¬∃ c, σ₂ ≫ c = ρn) (hq2 : ¬∃ c, ρn ≫ c = σ₂) (r : x' ⟶ D.m.out)
    (hr : r ≫ D.U = ρn) (hrU0 : r ≫ D.U' ≠ 0) (hdep : depth σ₂ ≤ depth (r ≫ D.U'))
    (hlongs : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → FactorsThroughMorphism μ σ ∨
      FactorsThroughMorphism μ ρ ∨ FactorsThroughMorphism μ σ₂ ∨ FactorsThroughMorphism μ ρn)
    {te : P} (e : te ⟶ y₁) (he : IsIrreducible e) (hpk : ¬∃ g, g ≫ e = ρ) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  -- `σ₂ = ρₙ' ≫ u₂'`
  have hσ₂eq : r ≫ D.U' = σ₂ := by
    rcases IsFiniteRayCategory.factorization_comparable (r ≫ D.U') σ₂ with hT | hT
    · exact (eq_of_tsef_depth hσ₂.1 hT hdep).symm
    · obtain ⟨a, b, hab⟩ := hT
      obtain ⟨hx, hy, he'⟩ := hσ₂.2.2.2 (r ≫ D.U') hrU0 ⟨a, b, by rw [hab, Category.assoc]⟩
      simpa using he'
  -- `ρₙ ≤ μ` for a long `μ`
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.ψ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.ψU]⟩
  have hρnr : ¬IsIrreducible ρn := fun h ↦ by
    rcases h.2.2 _ r D.U hr.symm with h' | h'
    · exact hir h'
    · exact D.U_not_isIso h'
  obtain ⟨_, _, μ, hμ, a₁, b₁, hab₁⟩ := exists_isLong_above hρn0 hiρn hρnr
  -- Option A: `ρₙ ≤ σ`
  have optA : FactorsThroughMorphism ρn σ → False := by
    rintro ⟨c, d, hcd⟩
    obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c_dual hQ hL hp2 D.U D.ψ r D.ψU hr d c hcd.symm
      hσ0
    exact B.l6_s5p hmin hL hR hσ hρ hv1 hv2 D d₁ d₂ hd hd₁ hd₂ e he hpk
  -- Option C: `ρₙ ≤ σ₂`
  have optC : FactorsThroughMorphism ρn σ₂ → False := by
    rintro ⟨c, d, hcd⟩
    obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR hq2 r D.U' D.U hσ₂eq hr c d hcd.symm
      hσ₂.1
    have hμσ := l6_μσ hQ hσ0 hρ0 hσ₂ hv1 hv2 hm1 hm2
    refine B.l6_s4s hmin hL hR hσ hv1 D ρn hp1 hp2 r hr d₁ d₂ hd hd₁ σ₂ hσ₂ ?_ ?_ ?_ ?_ ?_ ?_ hμσ ?_
    · exact fun h ↦ hρnl (hσ₂.of_factorsThrough hρn0 (by
        rw [← hr]; exact FactorsThroughMorphism.comp_right h _))
    · exact fun h ↦ hμσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _)
    · exact fun h ↦ not_ftm_long_cod hσ₂ hρ0 hm1 (by
        rw [← D.ψU', ← hd]; exact FactorsThroughMorphism.comp_left
          (FactorsThroughMorphism.comp_right h _) _)
    · exact fun h ↦ hρnl (hσ₂.of_factorsThrough hρn0 h)
    · exact not_ftm_prefix hσ₂.1 hd₂ (by rw [Category.assoc, hd, hσ₂eq])
    · exact fun h ↦ hμσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_right h _)
    · exact fun h ↦ not_ftm_long_cod hσ₂ hρ0 hm1 (by
        rw [← D.ψU', ← hd, ← Category.assoc]; exact FactorsThroughMorphism.comp_right h _)
  have hρnμ : FactorsThroughMorphism ρn μ := ⟨a₁, b₁, hab₁⟩
  have trans : ∀ {X Y : P} {f : X ⟶ Y}, FactorsThroughMorphism μ f →
      FactorsThroughMorphism ρn f := by
    rintro X Y f ⟨c, d, rfl⟩
    exact ⟨c ≫ a₁, b₁ ≫ d, by rw [hab₁]; simp⟩
  rcases hlongs μ hμ with h | h | h | h
  · exact optA (trans h)
  · -- `ρₙ ≤ ρ` is impossible
    obtain ⟨c, d, hcd⟩ := trans h
    have hd0 : ρn ≫ d ≠ 0 := fun h0 ↦ hρ0 (by rw [hcd, h0, comp_zero])
    rcases IsFiniteRayCategory.factorization_comparable (ρn ≫ d) σ₂ with hT | hT
    · obtain ⟨a, b, hab⟩ := hT
      exact optC ⟨a, d ≫ b, by rw [hab]; simp⟩
    · obtain ⟨a, b, hab⟩ := hT
      refine not_ftm_long_cod hσ₂ hρ0 hm1 ⟨c ≫ a, b, ?_⟩
      have e : ρn ≫ d = a ≫ σ₂ ≫ b := by rw [hab]; simp
      rw [hcd, e]
      simp
  · exact optC (trans h)
  · exact hρnl (hμ.of_factorsThrough hρn0 h)

end MulBasis

end RayQuiver

end LargeIndecomposable
