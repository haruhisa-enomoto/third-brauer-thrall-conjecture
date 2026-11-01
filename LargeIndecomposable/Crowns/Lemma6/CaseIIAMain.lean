module

public import LargeIndecomposable.Crowns.Lemma6.CaseIIA

/-!
# BO13a Lemma 6, case II.A: assembly

`σ, ρ` long neighbours, `ρₙ`, `σ₂` not long, `ρₙ` factors through the last
arrow of `w` (`MulBasis.l6_caseIIA`). The symmetric case (`σ₂` through the last
arrow of `w'`) is the same statement for `D.swap`.
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

/-- A maximal split of the contour path `β w` for a morphism factoring through
its last arrow. -/
theorem l6_max_split {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (D : L6Data σ ρ) {x' : P}
    (ρn : x' ⟶ y₀) (hp1 : ¬∃ c, c ≫ σ = ρn) {c : RayVert P} (w'' : Quiver.Path D.b c)
    (e : c ⟶ RayVert.mk y₀) (hw : D.w = w''.cons e) (he : ∃ g, g ≫ e.1 = ρn) :
    ∃ (S : L6WSplit D) (r : x' ⟶ S.c.out) (c₀ : RayVert P) (p₁' : Quiver.Path (RayVert.mk x) c₀)
      (e' : c₀ ⟶ S.c), r ≫ S.w₂ = ρn ∧ S.p₁ = p₁'.cons e' ∧
        ¬∃ g, g ≫ e'.1 ≫ S.w₂ = ρn := by
  have hpq : (D.β.toPath.comp w'').comp e.toPath = D.β.toPath.comp D.w := by rw [hw]; rfl
  obtain ⟨w₁', w', p₁', e', p₂, hsplit, hp₂, ⟨r, hr⟩, hmax⟩ := exists_max_suffix (x := RayVert.mk x) (y := RayVert.mk y₀) ρn
    (D.β.toPath.comp w'') e.toPath (by simp) (by
      obtain ⟨g, hg⟩ := he; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩)
    (by rw [hpq, D.hσw]; exact hp1)
  exact ⟨⟨w', p₁'.cons e', p₂, hsplit.trans hpq, by simp, hp₂⟩, r, w₁', p₁', e', hr, rfl, hmax⟩

/-- `ρₙ ≤ σ` when all long morphisms divide `σ` or `ρ` (BO13a's use of Lemma 5 d)). -/
theorem l6_le_σ {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    {x' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hiρn : ¬IsIso ρn) (hρnr : ¬IsIrreducible ρn)
    (h2 : ∀ {a b : P} (τ : a ⟶ b), IsLong τ → FactorsThroughMorphism τ σ ∨
      FactorsThroughMorphism τ ρ) (hρ : IsLong ρ) : FactorsThroughMorphism ρn σ := by
  obtain ⟨_, _, μ, hμ, a₁, b₁, hab₁⟩ := exists_isLong_above hρn0 hiρn hρnr
  have trans : ∀ {X Y : P} {f : X ⟶ Y}, FactorsThroughMorphism μ f →
      FactorsThroughMorphism ρn f := by
    rintro X Y f ⟨c, d, rfl⟩
    exact ⟨c ≫ a₁, b₁ ≫ d, by rw [hab₁]; simp⟩
  rcases h2 μ hμ with h | h
  · exact trans h
  · obtain ⟨c, d, hcd⟩ := trans h
    have hc0 : c ≫ ρn ≠ 0 := fun h0 ↦ hρ.1 (by rw [hcd, ← Category.assoc, h0, zero_comp])
    rcases IsFiniteRayCategory.factorization_comparable (c ≫ ρn) σ with hT | hT
    · obtain ⟨a, b, hab⟩ := hT
      exact ⟨a ≫ c, b, by rw [hab]; simp⟩
    · obtain ⟨a, b, hab⟩ := hT
      refine absurd ⟨a, b ≫ d, ?_⟩ (not_ftm_long_dom hσ hρ.1 hv1)
      rw [hcd, ← Category.assoc, hab]; simp

include B in
/-- **BO13a Lemma 6, case II.A**: `ρₙ` factors through the last arrow of `w`. -/
theorem l6_caseIIA
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ)
    {x' x'' zn z₂ : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn) (hiρn : ¬IsIso ρn)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (σn : x' ⟶ zn) (hσn0 : σn ≠ 0) (hiσn : ¬IsIso σn) (hq1 : ¬∃ c, σn ≫ c = ρn)
    (hq2 : ¬∃ c, ρn ≫ c = σn)
    (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂) (hiσ₂ : ¬IsIso σ₂)
    (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂)
    (ρ₂ : x'' ⟶ z₂) (hρ₂0 : ρ₂ ≠ 0) (hiρ₂ : ¬IsIso ρ₂) (hs1 : ¬∃ c, σ₂ ≫ c = ρ₂)
    (hs2 : ¬∃ c, ρ₂ ≫ c = σ₂)
    {c₀ : RayVert P} (w₀ : Quiver.Path D.b c₀) (e₀ : c₀ ⟶ RayVert.mk y₀) (hw₀ : D.w = w₀.cons e₀)
    (hρne : ∃ g, g ≫ e₀.1 = ρn)
    (hσ₂f : (∃ (c : RayVert P) (u'' : Quiver.Path D.m c) (eu : c ⟶ RayVert.mk y₁),
        D.u₂' = u''.cons eu ∧ ∃ g, g ≫ eu.1 = σ₂) ∨
      (∃ (c : RayVert P) (w'' : Quiver.Path D.b' c) (e : c ⟶ RayVert.mk y₁),
        D.w' = w''.cons e ∧ ∃ g, g ≫ e.1 = σ₂))
    (hD67 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F67.thin) k))
    (hD68 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F68.thin) k))
    (hD610 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F610.thin) k))
    (hD611 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F611.thin) k))
    (hD612 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F612.thin) k)) :
    False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  obtain ⟨S, r, c₁, p₁', e', hr, hS, hmax⟩ := l6_max_split D ρn hp1 w₀ e₀ hw₀ hρne
  -- claim 1: `u₂'` is an arrow
  obtain ⟨c₂, u'', eu, hu⟩ := exists_last_arrow D.u₂' D.U'_not_isIso
  have hu0 : u''.length = 0 := by
    by_contra h
    exact B.l6_f67 hmin hL hR hσ hρ hv1 hv2 D S ρn hρn0 hρnl hp1 hp2 r hr u'' eu hu (by omega)
      hD67
  rcases hσ₂f with ⟨c, u₃, eu₃, hu₃, g₃, hg₃⟩ | ⟨c, w'', e, hw', g₃, hg₃⟩
  · -- (b) `σ₂` through `u₂'`
    have hlen : u₃.length = 0 := by
      have h1 : (u''.cons eu).length = (u₃.cons eu₃).length := by rw [← hu, ← hu₃]
      simp only [Quiver.Path.length_cons] at h1
      omega
    cases u₃ with
    | cons _ _ => simp at hlen
    | nil =>
    have hU'eu : D.U' = eu₃.1 := by
      change pathVal D.u₂' = _; rw [hu₃]; exact Category.id_comp _
    set t := g₃ with ht'
    have ht : t ≫ D.U' = σ₂ := by rw [hU'eu]; exact hg₃
    have hit : ¬IsIso t := fun h ↦ hm1 ⟨D.ψ ≫ inv t, by
      rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc, D.ψU']⟩
    have htU : t ≫ D.U = 0 := by
      by_contra h
      exact B.l6_f610 hmin hL hR hQ hσ hρ hv1 hv2 D S ρn hρn0 hρnl hp1 hp2 r hr σ₂ hσ₂0 hσ₂l hm1
        hm2 t ht h hD610
    obtain ⟨_, w₁'', β₁, hβw⟩ := exists_last_arrow D.w' (D.W'_not_isIso hρ.2.2.1)
    let S' : L6WSplit D.swap := ⟨_, D.β'.toPath.comp w₁'', β₁.toPath,
      by change _ = D.β'.toPath.comp D.w'; rw [hβw]; rfl, by simp, by simp⟩
    by_cases hσρ₂ : FactorsThroughMorphism σ ρ₂
    · -- `ρ₂ ≅ σ`: `φ` an arrow of a contour of `σ`
      obtain ⟨hx, hy, he⟩ := hσ.2.2.2 ρ₂ hρ₂0 hσρ₂
      subst hx hy
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
      rw [he] at hs1 hs2
      obtain ⟨T, φ, hφ, hφ2⟩ := B.exists_first_not hmin hL hR hσ (hcont _ hσ) σ₂ hσ₂0 hs2 hs1
      refine B.l6_f611 hmin hL hR hσ hρ hv1 hv2 D S S' ρn hρn0 hρnl hp1 hp2 r hr σ₂ hσ₂0 hσ₂l
        hm1 hm2 t ht φ (not_factorsThrough_irr hσ.2.1 hσ0 hσ.2.2.1 hφ) hφ.2.1 ?_ hφ2 hD611
      rintro ⟨g, hg⟩
      rcases hφ.2.2 _ t g hg.symm with h | h
      · exact hit h
      · exact hφ2 ⟨inv g ≫ D.U', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, ht]⟩
    by_cases hρ₂t : ∃ q, t ≫ q = ρ₂
    · obtain ⟨q, hq⟩ := hρ₂t
      have hψq : D.ψ ≫ q = 0 := by
        by_contra h
        exact B.l6_star_t hmin hL hR hσ hρ hv1 D σ₂ hσ₂0 hσ₂l hm1 hm2 ρ₂ hρ₂0 hs1 hs2 hσρ₂ t ht
          htU q hq h
      by_cases hs : ∃ s, r ≫ s = σn
      · obtain ⟨s, hs⟩ := hs
        exact B.l6_f613 hmin hL hR hQ hσ hρ hv1 hv2 D S ρn hρn0 hρnl hp1 hp2 r hr σn hσn0 hq1
          hq2 s hs σ₂ ρ₂ hρ₂0 hs1 hs2 hσρ₂ t ht htU q hq hψq
      · exact B.l6_f612 hmin hL hR hQ hσ hρ hv1 hv2 D S S' ρn hρn0 hρnl hp1 hp2 r hr σn hσn0
          hiσn hq1 hq2 hs σ₂ hσ₂0 hσ₂l hm1 hm2 ρ₂ hρ₂0 hs1 hs2 hσρ₂ t ht htU q hq hψq hD612
    · exact B.l6_f611 hmin hL hR hσ hρ hv1 hv2 D S S' ρn hρn0 hρnl hp1 hp2 r hr σ₂ hσ₂0 hσ₂l
        hm1 hm2 t ht ρ₂ hσρ₂ hiρ₂ hρ₂t hs2 hD611
  · -- (a) `σ₂` through `w'`
    obtain ⟨S', t, c₁', q₁', e₁', ht, hS', hmax'⟩ := l6_max_split D.swap σ₂ hm2 w'' e hw'
      ⟨g₃, hg₃⟩
    by_cases h3 : ∃ (a b : P) (τ : a ⟶ b), IsLong τ ∧ ¬FactorsThroughMorphism τ σ ∧
        ¬FactorsThroughMorphism τ ρ
    · obtain ⟨_, _, τ, hτ, hτσ, hτρ⟩ := h3
      exact B.l6_f68 hmin hL hR hσ hρ hv1 hv2 D S S' ρn hρn0 hρnl hp1 hp2 r hr σ₂ hσ₂0 hσ₂l hm1
        hm2 t ht τ hτ hτσ hτρ hD68
    · have h2 : ∀ {a b : P} (τ : a ⟶ b), IsLong τ → FactorsThroughMorphism τ σ ∨
          FactorsThroughMorphism τ ρ := by
        intro a b τ hτ
        by_contra h
        push Not at h
        exact h3 ⟨a, b, τ, hτ, h.1, h.2⟩
      have hρnr : ¬IsIrreducible ρn := fun h ↦ by
        rcases h.2.2 _ r S.w₂ hr.symm with h' | h'
        · exact hp2 ⟨S.w₁ ≫ inv r, by rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc,
            S.w₁w₂]⟩
        · exact S.w₂_not_isIso h'
      have hσ₂r : ¬IsIrreducible σ₂ := fun h ↦ by
        rcases h.2.2 _ t S'.w₂ ht.symm with h' | h'
        · exact hm1 ⟨S'.w₁ ≫ inv t, by rw [← ht, Category.assoc, IsIso.inv_hom_id_assoc,
            S'.w₁w₂]⟩
        · exact S'.w₂_not_isIso h'
      obtain ⟨a₁, b₁, hab₁⟩ := l6_le_σ hσ hv1 ρn hρn0 hiρn hρnr h2 hρ
      obtain ⟨a₂, b₂, hab₂⟩ := l6_le_σ hρ hv2 σ₂ hσ₂0 hiσ₂ hσ₂r
        (fun τ hτ ↦ (h2 τ hτ).symm) hσ
      -- `w₁ = f₁ ≫ a` with `a` a nonempty path ending in `e'`
      obtain ⟨_, d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c_dual hQ hL hp2 S.w₂ S.w₁ r S.w₁w₂ hr b₁ a₁
        hab₁.symm hσ0
      obtain ⟨_, d₁', d₂', hd', hd₁', hd₂'⟩ := lemma4c_dual hQ hL hm1 S'.w₂ S'.w₁ t S'.w₁w₂ ht b₂
        a₂ hab₂.symm hρ0
      have hne : 0 < p₁'.length := by
        by_contra h0
        have hp : p₁'.length = 0 := by omega
        cases p₁' with
        | nil =>
          have hirr : IsIrreducible S.w₁ := by
            change IsIrreducible (pathVal S.p₁); rw [hS]
            have : pathVal (Quiver.Path.nil.cons e') = e'.1 := Category.id_comp _
            rw [this]; exact e'.2
          rcases hirr.2.2 _ d₁ d₂ hd.symm with h | h
          · exact hd₁ h
          · exact hd₂ h
        | cons _ _ => simp at hp
      have hne' : 0 < q₁'.length := by
        by_contra h0
        have hp : q₁'.length = 0 := by omega
        cases q₁' with
        | nil =>
          have hirr : IsIrreducible S'.w₁ := by
            change IsIrreducible (pathVal S'.p₁); rw [hS']
            have : pathVal (Quiver.Path.nil.cons e₁') = e₁'.1 := Category.id_comp _
            rw [this]; exact e₁'.2
          rcases hirr.2.2 _ d₁' d₂' hd'.symm with h | h
          · exact hd₁' h
          · exact hd₂' h
        | cons _ _ => simp at hp
      obtain ⟨_, f₁, q₀, hq₀⟩ := exists_first_arrow p₁' (not_isIso_pathVal p₁' hne)
      obtain ⟨_, f₁', q₀', hq₀'⟩ := exists_first_arrow q₁' (not_isIso_pathVal q₁' hne')
      refine B.l6_f69 hmin hL hR hσ hρ hv1 hv2 D S S' ρn hρn0 hρnl hp1 hp2 r hr σ₂ hσ₂0 hσ₂l hm1
        hm2 t ht f₁ (q₀.cons e') (by rw [hS, hq₀]; rfl) (by simp) ?_ f₁' (q₀'.cons e₁')
        (by rw [hS', hq₀']; rfl) (by simp) ?_
      · rintro ⟨g, hg⟩
        refine hmax ⟨g ≫ pathVal q₀, ?_⟩
        have e1 : pathVal (q₀.cons e') = pathVal q₀ ≫ e'.1 := rfl
        rw [← hr, ← hg, e1]
        simp only [Category.assoc]
      · rintro ⟨g, hg⟩
        refine hmax' ⟨g ≫ pathVal q₀', ?_⟩
        have e1 : pathVal (q₀'.cons e₁') = pathVal q₀' ≫ e₁'.1 := rfl
        rw [← ht, ← hg, e1]
        simp only [Category.assoc]

end MulBasis

end RayQuiver

end LargeIndecomposable
