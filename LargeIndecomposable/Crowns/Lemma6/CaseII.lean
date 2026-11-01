module

public import LargeIndecomposable.Crowns.Lemma6.CaseIIC
public import LargeIndecomposable.Crowns.Lemma6.CaseIUMain

/-!
# BO13a Lemma 6, case II

Neither `ρₙ` nor `σ₂` is long (`MulBasis.l6_caseII`). By Lemma 5 a), `ρₙ`
factors through the last arrow of `u₂` or of `w`, and `σ₂` through the last
arrow of `u₂'` or of `w'`:
* `ρₙ` through `w`: case II.A (`l6_caseIIA`); `σ₂` through `w'`: case II.A for
  `L6Data.swap`;
* otherwise case II.C: figure 6.1 if neither factors through all of `u₂`
  resp. `u₂'`; `l6_IIC_β` (or its swap) if exactly one does; if both do
  (`l6_IIC_α`), figure 6.14, whose failure gives a crown of length four, so
  `n = 2` by minimality and `l6_IIC_αend` applies.
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
/-- In a crown of length four whose `ρₙ = ρ (r+1)` and `σ₂ = σ (r+2)` are not long,
every long morphism divides `σ (r+1)` or `ρ (r+2)`. -/
theorem l6_n2_longs
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (C : Crown P) (hn : C.n = 2) (r : ℕ) (hρnl : ¬IsLong (C.toZChain.ρ (r + 1)))
    (hσ₂l : ¬IsLong (C.toZChain.σ (r + 2))) {a b : P} (τ : a ⟶ b) (hτ : IsLong τ) :
    FactorsThroughMorphism τ (C.toZChain.σ (r + 1)) ∨
      FactorsThroughMorphism τ (C.toZChain.ρ (r + 2)) := by
  obtain ⟨t, ht⟩ := B.long_meets hmin C τ hτ
  rcases ht with h | h
  · rcases C.ρ_n2 hn r t with e' | e'
    · exact absurd (hτ.of_factorsThrough (C.toZChain.ρ_ne _) (ftm_of_rayMor_eq e' h)) hρnl
    · exact Or.inr (ftm_of_rayMor_eq e' h)
  · rcases C.σ_n2 hn r t with e' | e'
    · exact Or.inl (ftm_of_rayMor_eq e' h)
    · exact absurd (hτ.of_factorsThrough (C.toZChain.σ_ne _) (ftm_of_rayMor_eq e' h)) hσ₂l

include B in
/-- **BO13a Lemma 6, case II.C (α)**: `ρₙ = ρₙ' ≫ u₂` and `σ₂ = σ₂' ≫ u₂'`. -/
theorem l6_IIC_α
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (C : Crown P) (hC : C.IsMin) (r : ℕ)
    (hσ : IsLong (C.toZChain.σ (r + 1))) (hρ : IsLong (C.toZChain.ρ (r + 2)))
    (hρnl : ¬IsLong (C.toZChain.ρ (r + 1))) (hσ₂l : ¬IsLong (C.toZChain.σ (r + 2)))
    (D : L6Data (C.toZChain.σ (r + 1)) (C.toZChain.ρ (r + 2)))
    (r' : C.toZChain.x (r + 1) ⟶ D.m.out) (hr' : r' ≫ D.U = C.toZChain.ρ (r + 1))
    (t : C.toZChain.x (r + 3) ⟶ D.m.out) (ht : t ≫ D.U' = C.toZChain.σ (r + 2)) : False := by
  have hv1 : ¬∃ c, C.toZChain.σ (r + 1) ≫ c = C.toZChain.ρ (r + 2) := C.toZChain.valley₁ (r + 1)
  have hv2 : ¬∃ c, C.toZChain.ρ (r + 2) ≫ c = C.toZChain.σ (r + 1) := C.toZChain.valley₂ (r + 1)
  have hp1 : ¬∃ c, c ≫ C.toZChain.σ (r + 1) = C.toZChain.ρ (r + 1) := C.toZChain.peak₁ (r + 1)
  have hp2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 1) = C.toZChain.σ (r + 1) := C.toZChain.peak₂ (r + 1)
  have hm1 : ¬∃ c, c ≫ C.toZChain.σ (r + 2) = C.toZChain.ρ (r + 2) := C.toZChain.peak₁ (r + 2)
  have hm2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 2) = C.toZChain.σ (r + 2) := C.toZChain.peak₂ (r + 2)
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρn0 := C.toZChain.ρ_ne (r + 1)
  have hσ₂0 := C.toZChain.σ_ne (r + 2)
  have hiρn := C.toZChain.ρ_not_isIso (r + 1)
  have hiσ₂ := C.toZChain.σ_not_isIso (r + 2)
  have h2n := Crown.two_le_n hQ C
  by_cases hrt : ∃ g, g ≫ r' = t
  · -- the crown `(ρ₁, ρₙ' ≫ u₂', ρₙ, σ₁)`
    obtain ⟨g, hg⟩ := hrt
    have hrU0 : r' ≫ D.U' ≠ 0 := fun h0 ↦ hσ₂0 (by
      rw [← ht, ← hg, Category.assoc, h0, comp_zero])
    have p1 : ¬∃ c, c ≫ (r' ≫ D.U') = C.toZChain.ρ (r + 2) := by
      rintro ⟨c, hc⟩
      have h := hR (c ≫ r') D.ψ D.U' (by rw [Category.assoc, hc, D.ψU']) (by
        rw [Category.assoc, hc]; exact hρ0)
      exact hp2 ⟨c, by rw [← hr', ← Category.assoc, h, D.ψU]⟩
    have p2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 2) = r' ≫ D.U' := by
      rintro ⟨c, hc⟩
      have h := hR (c ≫ D.ψ) r' D.U' (by rw [Category.assoc, D.ψU', hc]) (by
        rw [Category.assoc, D.ψU']; exact fun h ↦ hrU0 (by rw [← hc, h]))
      exact hp1 ⟨c, by rw [← hr', ← h, Category.assoc, D.ψU]⟩
    have v1 : ¬∃ c, (r' ≫ D.U') ≫ c = C.toZChain.ρ (r + 1) := by
      rintro ⟨c, hc⟩
      have h := hL r' (D.U' ≫ c) D.U (by rw [← Category.assoc, hc, hr']) (by
        rw [← Category.assoc, hc]; exact hρn0)
      exact hv2 ⟨c, by rw [← D.ψU', Category.assoc, h, D.ψU]⟩
    have v2 : ¬∃ c, C.toZChain.ρ (r + 1) ≫ c = r' ≫ D.U' := by
      rintro ⟨c, hc⟩
      have h := hL r' (D.U ≫ c) D.U' (by rw [← Category.assoc, hr', hc]) (by
        rw [← Category.assoc, hr', hc]; exact hrU0)
      exact hv1 ⟨c, by rw [← D.ψU, Category.assoc, h, D.ψU']⟩
    let C' := Crown.mk4 (C.toZChain.ρ (r + 2)) (r' ≫ D.U') (C.toZChain.ρ (r + 1))
      (C.toZChain.σ (r + 1)) p1 p2 v1 v2 hp1 hp2 hv1 hv2 hρ0 hrU0 hρn0 hσ0
    have hn : C.n = 2 := by
      rcases hC C' with h | h
      · exact absurd h (by change ¬C.n < 2; omega)
      · exact h.1
    exact B.l6_IIC_αend hmin hL hR hQ hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) hρn0 hρnl hiρn
      hp1 hp2 r' hr' hrU0 (fun τ hτ ↦ B.l6_n2_longs hmin C hn r hρnl hσ₂l τ hτ)
  by_cases htr : ∃ g, g ≫ t = r'
  · -- the crown `(ρ₁, σ₂, σ₂' ≫ u₂, σ₁)`
    obtain ⟨g, hg⟩ := htr
    have htU0 : t ≫ D.U ≠ 0 := fun h0 ↦ hρn0 (by
      rw [← hr', ← hg, Category.assoc, h0, comp_zero])
    have v1 : ¬∃ c, C.toZChain.σ (r + 2) ≫ c = t ≫ D.U := by
      rintro ⟨c, hc⟩
      have h := hL t (D.U' ≫ c) D.U (by rw [← Category.assoc, ht, hc]) (by
        rw [← Category.assoc, ht, hc]; exact htU0)
      exact D.U'_U hv2 ⟨c, h⟩
    have v2 : ¬∃ c, (t ≫ D.U) ≫ c = C.toZChain.σ (r + 2) := by
      rintro ⟨c, hc⟩
      have h := hL t (D.U ≫ c) D.U' (by rw [← Category.assoc, hc, ht]) (by
        rw [← Category.assoc, hc]; exact hσ₂0)
      exact D.U_U' hv1 ⟨c, h⟩
    have p3 : ¬∃ c, c ≫ C.toZChain.σ (r + 1) = t ≫ D.U := fun ⟨c, hc⟩ ↦
      hp1 ⟨g ≫ c, by rw [Category.assoc, hc, ← Category.assoc, hg, hr']⟩
    have p4 : ¬∃ c, c ≫ (t ≫ D.U) = C.toZChain.σ (r + 1) := by
      rintro ⟨c, hc⟩
      have h := hR (c ≫ t) D.ψ D.U (by rw [Category.assoc, hc, D.ψU]) (by
        rw [Category.assoc, hc]; exact hσ0)
      exact hm1 ⟨c, by rw [← ht, ← Category.assoc, h, D.ψU']⟩
    let C' := Crown.mk4 (C.toZChain.ρ (r + 2)) (C.toZChain.σ (r + 2)) (t ≫ D.U)
      (C.toZChain.σ (r + 1)) hm1 hm2 v1 v2 p3 p4 hv1 hv2 hρ0 hσ₂0 htU0 hσ0
    have hn : C.n = 2 := by
      rcases hC C' with h | h
      · exact absurd h (by change ¬C.n < 2; omega)
      · exact h.1
    exact B.l6_IIC_αend hmin hL hR hQ hρ hσ hv2 hv1 D.swap (C.toZChain.σ (r + 2)) hσ₂0 hσ₂l
      hiσ₂ hm2 hm1 t ht htU0 (fun τ hτ ↦ (B.l6_n2_longs hmin C hn r hρnl hσ₂l τ hτ).symm)
  exact B.l6_s614 hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.σ (r + 2)) hσ₂0 hσ₂l hm1 hm2
    (C.toZChain.ρ (r + 1)) hρn0 hρnl hp1 hp2 r' hr' t ht hrt htr

include B in
/-- **BO13a Lemma 6, case II**: `σ₁ = σ (r+1)`, `ρ₁ = ρ (r+2)` long with
`ρₙ = ρ (r+1)` and `σ₂ = σ (r+2)` not long in a minimal crown is impossible. -/
theorem l6_caseII
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (r : ℕ)
    (hσ : IsLong (C.toZChain.σ (r + 1))) (hρ : IsLong (C.toZChain.ρ (r + 2)))
    (hρnl : ¬IsLong (C.toZChain.ρ (r + 1))) (hσ₂l : ¬IsLong (C.toZChain.σ (r + 2)))
    (hD67 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F67.thin) k))
    (hD68 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F68.thin) k))
    (hD610 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F610.thin) k))
    (hD611 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F611.thin) k))
    (hD612 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F612.thin) k))
    (hD617 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F617.thin) k)) :
    False := by
  have hv1 : ¬∃ c, C.toZChain.σ (r + 1) ≫ c = C.toZChain.ρ (r + 2) := C.toZChain.valley₁ (r + 1)
  have hv2 : ¬∃ c, C.toZChain.ρ (r + 2) ≫ c = C.toZChain.σ (r + 1) := C.toZChain.valley₂ (r + 1)
  have hp1 : ¬∃ c, c ≫ C.toZChain.σ (r + 1) = C.toZChain.ρ (r + 1) := C.toZChain.peak₁ (r + 1)
  have hp2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 1) = C.toZChain.σ (r + 1) := C.toZChain.peak₂ (r + 1)
  have hq1 : ¬∃ c, C.toZChain.σ r ≫ c = C.toZChain.ρ (r + 1) := C.toZChain.valley₁ r
  have hq2 : ¬∃ c, C.toZChain.ρ (r + 1) ≫ c = C.toZChain.σ r := C.toZChain.valley₂ r
  have hm1 : ¬∃ c, c ≫ C.toZChain.σ (r + 2) = C.toZChain.ρ (r + 2) := C.toZChain.peak₁ (r + 2)
  have hm2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 2) = C.toZChain.σ (r + 2) := C.toZChain.peak₂ (r + 2)
  have hs1 : ¬∃ c, C.toZChain.σ (r + 2) ≫ c = C.toZChain.ρ (r + 3) := C.toZChain.valley₁ (r + 2)
  have hs2 : ¬∃ c, C.toZChain.ρ (r + 3) ≫ c = C.toZChain.σ (r + 2) := C.toZChain.valley₂ (r + 2)
  have hρn0 := C.toZChain.ρ_ne (r + 1)
  have hσn0 := C.toZChain.σ_ne r
  have hσ₂0 := C.toZChain.σ_ne (r + 2)
  have hρ₂0 := C.toZChain.ρ_ne (r + 3)
  have hiρn := C.toZChain.ρ_not_isIso (r + 1)
  have hiσn := C.toZChain.σ_not_isIso r
  have hiσ₂ := C.toZChain.σ_not_isIso (r + 2)
  have hiρ₂ := C.toZChain.ρ_not_isIso (r + 3)
  obtain ⟨D⟩ := B.exists_l6Data hmin hL hR hσ hρ (hcont _ hσ) (hcont _ hρ) hv1 hv2
  obtain ⟨_, u₁, eu, hu⟩ := exists_last_arrow D.u₂ D.U_not_isIso
  obtain ⟨_, w₁, ew, hw⟩ := exists_last_arrow D.w (D.W_not_isIso hσ.2.2.1)
  obtain ⟨_, u₃, eu', hu'⟩ := exists_last_arrow D.u₂' D.U'_not_isIso
  obtain ⟨_, w₃, ew', hw'⟩ := exists_last_arrow D.w' (D.W'_not_isIso hρ.2.2.1)
  -- Lemma 5 a) for the contours of `σ₁` and `ρ₁`
  have hρnf : (∃ g, g ≫ eu.1 = C.toZChain.ρ (r + 1)) ∨
      (∃ g, g ≫ ew.1 = C.toZChain.ρ (r + 1)) := by
    by_contra h
    refine B.lemma5a_last hmin hL hR hQ hcont C (r + 1) hσ eu ew
      ((D.α.toPath.comp D.χ).comp u₁) (D.β.toPath.comp w₁) ?_ ?_ ?_
      (fun h' ↦ h (Or.inl h')) (fun h' ↦ h (Or.inr h'))
    · have := D.hσu; rw [hu] at this; exact this
    · have := D.hσw; rw [hw] at this; exact this
    · have := D.hniσ; rw [hu, hw] at this; exact this
  have hσ₂f : (∃ g, g ≫ eu'.1 = C.toZChain.σ (r + 2)) ∨
      (∃ g, g ≫ ew'.1 = C.toZChain.σ (r + 2)) := by
    by_contra h
    refine B.lemma5a_rho_last hmin hL hR hQ hcont C (r + 2) hρ eu' ew'
      ((D.α.toPath.comp D.χ).comp u₃) (D.β'.toPath.comp w₃) ?_ ?_ ?_
      (fun h' ↦ h (Or.inl h')) (fun h' ↦ h (Or.inr h'))
    · have := D.hρu; rw [hu'] at this; exact this
    · have := D.hρw; rw [hw'] at this; exact this
    · have := D.hniρ; rw [hu', hw'] at this; exact this
  by_cases hρw : ∃ g, g ≫ ew.1 = C.toZChain.ρ (r + 1)
  · -- case II.A
    refine B.l6_caseIIA hmin hL hR hQ hcont hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) hρn0 hρnl
      hiρn hp1 hp2 (C.toZChain.σ r) hσn0 hiσn hq1 hq2 (C.toZChain.σ (r + 2)) hσ₂0 hσ₂l hiσ₂
      hm1 hm2 (C.toZChain.ρ (r + 3)) hρ₂0 hiρ₂ hs1 hs2 w₁ ew hw hρw ?_ hD67 hD68 hD610 hD611
      hD612
    rcases hσ₂f with h | h
    · exact Or.inl ⟨_, u₃, eu', hu', h⟩
    · exact Or.inr ⟨_, w₃, ew', hw', h⟩
  have hρu : ∃ g, g ≫ eu.1 = C.toZChain.ρ (r + 1) := hρnf.resolve_right hρw
  by_cases hσw : ∃ g, g ≫ ew'.1 = C.toZChain.σ (r + 2)
  · -- case II.A for the swapped data
    exact B.l6_caseIIA hmin hL hR hQ hcont hρ hσ hv2 hv1 D.swap (C.toZChain.σ (r + 2)) hσ₂0
      hσ₂l hiσ₂ hm2 hm1 (C.toZChain.ρ (r + 3)) hρ₂0 hiρ₂ hs2 hs1 (C.toZChain.ρ (r + 1)) hρn0
      hρnl hiρn hp2 hp1 (C.toZChain.σ r) hσn0 hiσn hq2 hq1 w₃ ew' hw' hσw
      (Or.inl ⟨_, u₁, eu, hu, hρu⟩) hD67 hD68 hD610 hD611 hD612
  have hσu : ∃ g, g ≫ eu'.1 = C.toZChain.σ (r + 2) := hσ₂f.resolve_right hσw
  have hW : D.W = pathVal w₁ ≫ ew.1 := by change pathVal D.w = _; rw [hw]; rfl
  have hW' : D.W' = pathVal w₃ ≫ ew'.1 := by change pathVal D.w' = _; rw [hw']; rfl
  have hρnW : ¬∃ g, g ≫ D.W = C.toZChain.ρ (r + 1) := fun ⟨g, hg⟩ ↦
    hρw ⟨g ≫ pathVal w₁, by rw [Category.assoc, ← hW]; exact hg⟩
  have hσ₂W' : ¬∃ g, g ≫ D.W' = C.toZChain.σ (r + 2) := fun ⟨g, hg⟩ ↦
    hσw ⟨g ≫ pathVal w₃, by rw [Category.assoc, ← hW']; exact hg⟩
  by_cases hU : ∃ g, g ≫ D.U = C.toZChain.ρ (r + 1)
  · by_cases hU' : ∃ g, g ≫ D.U' = C.toZChain.σ (r + 2)
    · obtain ⟨r', hr'⟩ := hU
      obtain ⟨t, ht⟩ := hU'
      exact B.l6_IIC_α hmin hL hR hQ C hC r hσ hρ hρnl hσ₂l D r' hr' t ht
    · obtain ⟨r', hr'⟩ := hU
      exact B.l6_IIC_β hmin hL hR hQ hcont hρ hσ hv2 hv1 D.swap (C.toZChain.σ (r + 2)) hσ₂0
        hσ₂l hm2 hm1 (C.toZChain.ρ (r + 3)) hρ₂0 hiρ₂ hs2 hs1 (C.toZChain.ρ (r + 1)) hρn0 hρnl
        hp2 hp1 (C.toZChain.σ r) hσn0 hiσn hq2 hq1 r' hr' hρnW hσ₂W' u₃ eu' hu' hσu hU' hD617
  · by_cases hU' : ∃ g, g ≫ D.U' = C.toZChain.σ (r + 2)
    · obtain ⟨t, ht⟩ := hU'
      exact B.l6_IIC_β hmin hL hR hQ hcont hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) hρn0 hρnl
        hp1 hp2 (C.toZChain.σ r) hσn0 hiσn hq1 hq2 (C.toZChain.σ (r + 2)) hσ₂0 hσ₂l hm1 hm2
        (C.toZChain.ρ (r + 3)) hρ₂0 hiρ₂ hs1 hs2 t ht hσ₂W' hρnW u₁ eu hu hρu hU hD617
    · -- figure 6.1 with `ρₙ` and `σ₂`
      exact B.l6_fig61 hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) (C.toZChain.σ (r + 2))
        (not_factorsThrough_of_not_isLong hσ hρn0 hρnl)
        (not_factorsThrough_of_not_isLong hσ hσ₂0 hσ₂l) hiρn hiσ₂ hp2 hm1 hρnW hU hσ₂W' hU'

end MulBasis

end RayQuiver

end LargeIndecomposable
