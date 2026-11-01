module

public import LargeIndecomposable.Crowns.Lemma6.Helpers

/-!
# BO13a Lemma 6, case I.2.c at the level of a minimal crown

`σ₁ = σ (r+1)`, `ρ₁ = ρ (r+2)` and `σ₂ = σ (r+2)` long, `ρₙ = ρ (r+1)` not long,
and `ρₙ = ρₙ' ≫ u₂`. Part (i): `ρₙ' ≫ u₂' ≠ 0` (`MulBasis.l6_caseI_U_i`).
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
/-- **Lemma 6, case I.2.c (i).** -/
theorem l6_caseI_U_i
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (C : Crown P) (hC : C.IsMin) (r : ℕ)
    (hσ : IsLong (C.toZChain.σ (r + 1))) (hρ : IsLong (C.toZChain.ρ (r + 2)))
    (hσ₂ : IsLong (C.toZChain.σ (r + 2))) (hρnl : ¬IsLong (C.toZChain.ρ (r + 1)))
    (D : L6Data (C.toZChain.σ (r + 1)) (C.toZChain.ρ (r + 2)))
    {Te : P} (e : Te ⟶ C.toZChain.z (r + 2)) (he : IsIrreducible e)
    (hpk : ¬∃ g, g ≫ e = C.toZChain.ρ (r + 2))
    (r' : C.toZChain.x (r + 1) ⟶ D.m.out) (hr' : r' ≫ D.U = C.toZChain.ρ (r + 1))
    (hrU0 : r' ≫ D.U' ≠ 0) : False := by
  have hv1 : ¬∃ c, C.toZChain.σ (r + 1) ≫ c = C.toZChain.ρ (r + 2) := C.toZChain.valley₁ (r + 1)
  have hv2 : ¬∃ c, C.toZChain.ρ (r + 2) ≫ c = C.toZChain.σ (r + 1) := C.toZChain.valley₂ (r + 1)
  have hp1 : ¬∃ c, c ≫ C.toZChain.σ (r + 1) = C.toZChain.ρ (r + 1) := C.toZChain.peak₁ (r + 1)
  have hp2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 1) = C.toZChain.σ (r + 1) := C.toZChain.peak₂ (r + 1)
  have hm1 : ¬∃ c, c ≫ C.toZChain.σ (r + 2) = C.toZChain.ρ (r + 2) := C.toZChain.peak₁ (r + 2)
  have hm2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 2) = C.toZChain.σ (r + 2) := C.toZChain.peak₂ (r + 2)
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρn0 := C.toZChain.ρ_ne (r + 1)
  -- the crown `(ρ₁, ρₙ' u₂', ρₙ, σ₁)`
  have p1 : ¬∃ c, c ≫ (r' ≫ D.U') = C.toZChain.ρ (r + 2) := by
    rintro ⟨c, hc⟩
    have h := hR (c ≫ r') D.ψ D.U' (by rw [Category.assoc, hc, D.ψU']) (by
      rw [Category.assoc, hc]; exact hρ0)
    exact hp2 ⟨c, by rw [← hr', ← Category.assoc, h, D.ψU]⟩
  have p2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 2) = r' ≫ D.U' := by
    rintro ⟨c, hc⟩
    have h := hR (c ≫ D.ψ) r' D.U' (by rw [Category.assoc, D.ψU', hc]) (by
      rw [Category.assoc, D.ψU']; exact fun h0 ↦ hrU0 (by rw [← hc, h0]))
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
  let C' := Crown.mk4 (C.toZChain.ρ (r + 2)) (r' ≫ D.U') (C.toZChain.ρ (r + 1)) (C.toZChain.σ (r + 1)) p1 p2 v1 v2 hp1 hp2
    hv1 hv2 hρ0 hrU0 hρn0 hσ0
  have hmin' := hC C'
  have h2n := Crown.two_le_n hQ C
  obtain ⟨hn, hw⟩ : C.n = 2 ∧ C.weight ≤ C'.weight := by
    rcases hmin' with h | h
    · exact absurd h (by change ¬C.n < 2; omega)
    · exact h
  rw [Crown.weight_chain C hn r, Crown.weight_mk4] at hw
  have hdep0 : depth (C.toZChain.σ (r + 2)) ≤ depth (r' ≫ D.U') := by omega
  -- transport `σ₂` to the domain of `ρₙ`
  obtain ⟨hx, hy, hρeq⟩ := eq_of_rayMor_eq (C.ρ_add_two_mul hn (r + 1) 1)
  set σ₂' := eqToHom hx.symm ≫ C.toZChain.σ (r + 2) with hσ₂'
  have e2 : (⟨_, _, σ₂'⟩ : RayMor P) = ⟨_, _, C.toZChain.σ (r + 2)⟩ := by
    have := rayMor_eq_of_eqToHom' (⟨_, _, C.toZChain.σ (r + 2)⟩ : RayMor P) hx.symm rfl
    simpa using this
  have hρeq' : C.toZChain.ρ (r + 3) = eqToHom hx ≫ C.toZChain.ρ (r + 1) ≫ eqToHom hy.symm := hρeq
  refine B.l6_caseI_i hmin hL hR hQ hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) hρn0 hρnl
    (C.toZChain.ρ_not_isIso _) hp1 hp2 σ₂' (isLong_of_rayMor_eq e2.symm hσ₂) ?_ ?_ ?_ ?_ r' hr' hrU0
    (by rw [depth_of_rayMor_eq e2]; exact hdep0) ?_ e he hpk
  · rintro ⟨c, hc⟩
    exact hm1 ⟨c ≫ eqToHom hx.symm, by rw [Category.assoc]; exact hc⟩
  · rintro ⟨c, hc⟩
    exact hm2 ⟨eqToHom hx ≫ c, by rw [Category.assoc, hc, hσ₂']; simp⟩
  · rintro ⟨c, hc⟩
    apply C.toZChain.valley₁ (r + 2)
    refine ⟨c ≫ eqToHom hy.symm, ?_⟩
    have h1 : C.toZChain.σ (r + 2) ≫ c = eqToHom hx ≫ C.toZChain.ρ (r + 1) := by
      rw [← hc, hσ₂']; simp
    change _ = C.toZChain.ρ (r + 3)
    rw [hρeq', ← Category.assoc, h1, Category.assoc]
  · rintro ⟨c, hc⟩
    apply C.toZChain.valley₂ (r + 2)
    refine ⟨eqToHom hy ≫ c, ?_⟩
    change C.toZChain.ρ (r + 3) ≫ _ = _
    rw [hρeq']
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hc, hσ₂']
    simp
  · intro a b μ hμ
    obtain ⟨t, ht⟩ := B.long_meets hmin C μ hμ
    rcases ht with h | h
    · rcases C.ρ_n2 hn r t with e' | e'
      · exact Or.inr (Or.inr (Or.inr (ftm_of_rayMor_eq e' h)))
      · exact Or.inr (Or.inl (ftm_of_rayMor_eq e' h))
    · rcases C.σ_n2 hn r t with e' | e'
      · exact Or.inl (ftm_of_rayMor_eq e' h)
      · exact Or.inr (Or.inr (Or.inl (ftm_of_rayMor_eq (e'.trans e2.symm) h)))

include B in
/-- **Lemma 6, case I.2.c (ii).** -/
theorem l6_caseI_U_ii
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (r : ℕ)
    (hσ : IsLong (C.toZChain.σ (r + 1))) (hρ : IsLong (C.toZChain.ρ (r + 2)))
    (hσ₂ : IsLong (C.toZChain.σ (r + 2))) (hρnl : ¬IsLong (C.toZChain.ρ (r + 1)))
    (D : L6Data (C.toZChain.σ (r + 1)) (C.toZChain.ρ (r + 2)))
    {Te : P} (e : Te ⟶ C.toZChain.z (r + 2)) (he : IsIrreducible e)
    (hpk : ¬∃ g, g ≫ e = C.toZChain.ρ (r + 2))
    (r' : C.toZChain.x (r + 1) ⟶ D.m.out) (hr' : r' ≫ D.U = C.toZChain.ρ (r + 1))
    (hrU' : r' ≫ D.U' = 0)
    (hD64 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F64.thin) k))
    (hD66 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F66.thin) k)) :
    False := by
  have hv1 : ¬∃ c, C.toZChain.σ (r + 1) ≫ c = C.toZChain.ρ (r + 2) := C.toZChain.valley₁ (r + 1)
  have hv2 : ¬∃ c, C.toZChain.ρ (r + 2) ≫ c = C.toZChain.σ (r + 1) := C.toZChain.valley₂ (r + 1)
  have hp1 : ¬∃ c, c ≫ C.toZChain.σ (r + 1) = C.toZChain.ρ (r + 1) := C.toZChain.peak₁ (r + 1)
  have hp2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 1) = C.toZChain.σ (r + 1) := C.toZChain.peak₂ (r + 1)
  have hq1 : ¬∃ c, C.toZChain.σ r ≫ c = C.toZChain.ρ (r + 1) := C.toZChain.valley₁ r
  have hq2 : ¬∃ c, C.toZChain.ρ (r + 1) ≫ c = C.toZChain.σ r := C.toZChain.valley₂ r
  have hm1 : ¬∃ c, c ≫ C.toZChain.σ (r + 2) = C.toZChain.ρ (r + 2) := C.toZChain.peak₁ (r + 2)
  have hm2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 2) = C.toZChain.σ (r + 2) := C.toZChain.peak₂ (r + 2)
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hσ₂0 := hσ₂.1
  have hρn0 := C.toZChain.ρ_ne (r + 1)
  have hσn0 := C.toZChain.σ_ne r
  have hiσn := C.toZChain.σ_not_isIso r
  have hμσ := l6_μσ hQ hσ0 hρ0 hσ₂ hv1 hv2 hm1 hm2
  have hσ₂ρ : ¬FactorsThroughMorphism (C.toZChain.σ (r + 2)) (C.toZChain.ρ (r + 2)) :=
    not_ftm_long_cod hσ₂ hρ0 hm1
  have hρσ₂ : ¬FactorsThroughMorphism (C.toZChain.ρ (r + 2)) (C.toZChain.σ (r + 2)) :=
    not_ftm_long_cod hρ hσ₂0 hm2
  have hρσ : ¬FactorsThroughMorphism (C.toZChain.ρ (r + 2)) (C.toZChain.σ (r + 1)) :=
    not_ftm_long_dom hρ hσ0 hv2
  have h2n := Crown.two_le_n hQ C
  by_cases hs : ∃ s, r' ≫ s = C.toZChain.σ r
  · -- (ii-a): `σₙ = ρₙ' ≫ σₙ'`
    obtain ⟨s, hs⟩ := hs
    have hsU' : ¬∃ g, s ≫ g = D.U' := by
      rintro ⟨g, hg⟩
      by_cases hgi : IsIso g
      · exact hσn0 (by rw [← hs, show s = D.U' ≫ inv g by rw [← hg]; simp, ← Category.assoc, hrU',
          zero_comp])
      · have hρψ : (D.ψ ≫ s) ≫ g = C.toZChain.ρ (r + 2) := by rw [Category.assoc, hg, D.ψU']
        have hψs0 : D.ψ ≫ s ≠ 0 := fun h0 ↦ hρ0 (by rw [← hρψ, h0, zero_comp])
        have p1 : ¬∃ c, c ≫ C.toZChain.σ r = D.ψ ≫ s := by
          rintro ⟨c, hc⟩
          have h := hR (c ≫ r') D.ψ s (by rw [Category.assoc, hs, hc]) (by
            rw [Category.assoc, hs, hc]; exact hψs0)
          exact hp2 ⟨c, by rw [← hr', ← Category.assoc, h, D.ψU]⟩
        have p2 : ¬∃ c, c ≫ (D.ψ ≫ s) = C.toZChain.σ r := by
          rintro ⟨c, hc⟩
          have h := hR (c ≫ D.ψ) r' s (by rw [Category.assoc, hc, hs]) (by
            rw [Category.assoc, hc]; exact hσn0)
          exact hp1 ⟨c, by rw [← hr', ← h, Category.assoc, D.ψU]⟩
        have v3 : ¬∃ c, C.toZChain.σ (r + 1) ≫ c = D.ψ ≫ s := by
          rintro ⟨c, hc⟩
          have h := hL D.ψ (D.U ≫ c) s (by rw [← Category.assoc, D.ψU, hc]) (by
            rw [← Category.assoc, D.ψU, hc]; exact hψs0)
          exact hq2 ⟨c, by rw [← hr', Category.assoc, h, hs]⟩
        have v4 : ¬∃ c, (D.ψ ≫ s) ≫ c = C.toZChain.σ (r + 1) := by
          rintro ⟨c, hc⟩
          have h := hL D.ψ (s ≫ c) D.U (by rw [← Category.assoc, hc, D.ψU]) (by
            rw [← Category.assoc, hc]; exact hσ0)
          exact hq1 ⟨c, by rw [← hs, Category.assoc, h, hr']⟩
        let C' := Crown.mk4 (D.ψ ≫ s) (C.toZChain.σ r) (C.toZChain.ρ (r + 1))
          (C.toZChain.σ (r + 1)) p1 p2 hq1 hq2 hp1 hp2 v3 v4 hψs0 hσn0 hρn0 hσ0
        obtain ⟨hn, hw⟩ : C.n = 2 ∧ C.weight ≤ C'.weight := by
          rcases hC C' with h | h
          · exact absurd h (by change ¬C.n < 2; omega)
          · exact h
        rw [Crown.weight_chain C hn r, Crown.weight_mk4] at hw
        have e1 : depth (C.toZChain.σ (r + 2)) = depth (C.toZChain.σ r) :=
          depth_of_rayMor_eq (C.σ_add_two_mul hn r 1)
        have e2 := depth_lt_comp_right (D.ψ ≫ s) g (by rw [hρψ]; exact hρ0) hgi
        rw [hρψ] at e2
        omega
    by_cases hσσn : FactorsThroughMorphism (C.toZChain.σ (r + 1)) (C.toZChain.σ r)
    · refine B.l6_s5m hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) (C.toZChain.σ r) hσn0
        hq1 hq2 r' s hr' hs hrU' e he hpk hsU' (C.toZChain.σ (r + 2)) hσ₂ ?_ ?_ ?_ ?_
      · exact fun h ↦ hμσ (ftm_trans_long hσ hσn0 hσσn (by
          rw [← hs]; exact FactorsThroughMorphism.comp_left h _))
      · exact fun h ↦ hμσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _)
      · exact fun h ↦ hσ₂ρ (by rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _)
      · exact fun h ↦ hσ₂ρ (by rw [← D.βW']; exact FactorsThroughMorphism.comp_left h _)
    · refine B.l6_s5m hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) (C.toZChain.σ r) hσn0
        hq1 hq2 r' s hr' hs hrU' e he hpk hsU' (C.toZChain.σ (r + 1)) hσ ?_
        (not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU) ?_ ?_
      · exact fun h ↦ hσσn (by rw [← hs]; exact FactorsThroughMorphism.comp_left h _)
      · exact fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
          rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _)
      · exact fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
          rw [← D.βW']; exact FactorsThroughMorphism.comp_left h _)
  · -- (ii-b): `σ₂` through a last arrow of the contour `(ψ u₂', β' w')` of `ρ₁`
    obtain ⟨c₁, u'', eu, hu⟩ := exists_last_arrow D.u₂' D.U'_not_isIso
    obtain ⟨d₁, w'', ew, hw⟩ := exists_last_arrow D.w' (D.W'_not_isIso hρ.2.2.1)
    have hρu : pathVal (((D.α.toPath.comp D.χ).comp u'').cons eu) = C.toZChain.ρ (r + 2) := by
      have := D.hρu; rw [hu] at this; exact this
    have hρw : pathVal ((D.β'.toPath.comp w'').cons ew) = C.toZChain.ρ (r + 2) := by
      have := D.hρw; rw [hw] at this; exact this
    have hUeu : pathVal u'' ≫ eu.1 = D.U' := by
      change _ = pathVal D.u₂'; rw [hu]; rfl
    have hWew : pathVal w'' ≫ ew.1 = D.W' := by
      change _ = pathVal D.w'; rw [hw]; rfl
    by_cases hβe : ∃ t, t ≫ ew.1 = C.toZChain.σ (r + 2)
    · -- figure 6.4
      obtain ⟨t, ht⟩ := hβe
      have hρ1 : (D.β'.1 ≫ pathVal w'') ≫ ew.1 = C.toZChain.ρ (r + 2) := by
        rw [Category.assoc, hWew, D.βW']
      have hq : w''.comp ew.toPath = D.w' := by rw [hw]; rfl
      by_cases hρσn : FactorsThroughMorphism (C.toZChain.ρ (r + 2)) (C.toZChain.σ r)
      · refine B.l6_f64 hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.σ (r + 2)) hm1 hm2
          (C.toZChain.ρ (r + 1)) (C.toZChain.σ r) hρn0 hp1 hp2 hq1 hq2 hiσn r' hr' hs w''
          ew.toPath hq (by simp) t (by rw [pathVal_toPath]; exact ht) (C.toZChain.σ (r + 2)) hσ₂
          (fun h ↦ hσ₂ρ (ftm_trans_long hρ hσn0 hρσn h)) ?_ ?_ hμσ
          (not_factorsThrough_of_not_isLong hσ₂ hρn0 hρnl) hD64
        · exact fun h ↦ hσ₂ρ (by rw [← hρ1]; exact FactorsThroughMorphism.comp_right h _)
        · exact not_ftm_prefix hσ₂0 ew.2.2.1 ht
      · refine B.l6_f64 hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.σ (r + 2)) hm1 hm2
          (C.toZChain.ρ (r + 1)) (C.toZChain.σ r) hρn0 hp1 hp2 hq1 hq2 hiσn r' hr' hs w''
          ew.toPath hq (by simp) t (by rw [pathVal_toPath]; exact ht) (C.toZChain.ρ (r + 2)) hρ
          hρσn (not_ftm_prefix hρ0 ew.2.2.1 hρ1) ?_ hρσ
          (not_factorsThrough_of_not_isLong hρ hρn0 hρnl) hD64
        exact fun h ↦ hρσ₂ (by rw [← ht]; exact FactorsThroughMorphism.comp_right h _)
    by_cases hαe : ∃ t, t ≫ eu.1 = C.toZChain.σ (r + 2)
    · obtain ⟨t, ht⟩ := hαe
      by_cases hU' : ∃ g, g ≫ D.U' = C.toZChain.σ (r + 2)
      · -- figure 6.5
        obtain ⟨t', ht'⟩ := hU'
        have htr : ¬∃ g, g ≫ t' = r' := by
          rintro ⟨g, hg⟩
          by_cases hgi : IsIso g
          · exact hσ₂0 (by rw [← ht', show t' = inv g ≫ r' by rw [← hg]; simp, Category.assoc,
              hrU', comp_zero])
          · have hρn' : g ≫ (t' ≫ D.U) = C.toZChain.ρ (r + 1) := by
              rw [← Category.assoc, hg, hr']
            have htU0 : t' ≫ D.U ≠ 0 := fun h0 ↦ hρn0 (by rw [← hρn', h0, comp_zero])
            have p1 : ¬∃ c, c ≫ (t' ≫ D.U) = C.toZChain.σ (r + 1) := by
              rintro ⟨c, hc⟩
              have h := hR (c ≫ t') D.ψ D.U (by rw [Category.assoc, hc, D.ψU]) (by
                rw [Category.assoc, hc]; exact hσ0)
              exact hm1 ⟨c, by rw [← D.ψU', ← h, Category.assoc, ht']⟩
            have p2 : ¬∃ c, c ≫ C.toZChain.σ (r + 1) = t' ≫ D.U := by
              rintro ⟨c, hc⟩
              have h := hR (c ≫ D.ψ) t' D.U (by rw [Category.assoc, D.ψU, hc]) (by
                rw [Category.assoc, D.ψU, hc]; exact htU0)
              exact hm2 ⟨c, by rw [← ht', ← h, Category.assoc, D.ψU']⟩
            have v1 : ¬∃ c, (t' ≫ D.U) ≫ c = C.toZChain.σ (r + 2) := by
              rintro ⟨c, hc⟩
              have h := hL t' (D.U ≫ c) D.U' (by rw [← Category.assoc, hc, ht']) (by
                rw [← Category.assoc, hc]; exact hσ₂0)
              exact hv1 ⟨c, by rw [← D.ψU, Category.assoc, h, D.ψU']⟩
            have v2 : ¬∃ c, C.toZChain.σ (r + 2) ≫ c = t' ≫ D.U := by
              rintro ⟨c, hc⟩
              have h := hL t' (D.U' ≫ c) D.U (by rw [← Category.assoc, ht', hc]) (by
                rw [← Category.assoc, ht', hc]; exact htU0)
              exact hv2 ⟨c, by rw [← D.ψU', Category.assoc, h, D.ψU]⟩
            let C' := Crown.mk4 (C.toZChain.σ (r + 1)) (t' ≫ D.U) (C.toZChain.σ (r + 2))
              (C.toZChain.ρ (r + 2)) p1 p2 v1 v2 hm2 hm1 hv2 hv1 hσ0 htU0 hσ₂0 hρ0
            obtain ⟨hn, hw⟩ : C.n = 2 ∧ C.weight ≤ C'.weight := by
              rcases hC C' with h | h
              · exact absurd h (by change ¬C.n < 2; omega)
              · exact h
            rw [Crown.weight_chain C hn r, Crown.weight_mk4] at hw
            have e2 := depth_lt_comp_left g (t' ≫ D.U) (by rw [hρn']; exact hρn0) hgi
            rw [hρn'] at e2
            omega
        exact B.l6_s65 hmin hL hR hQ hσ hρ hv1 hv2 D (C.toZChain.σ (r + 2)) hσ₂ hm1 hm2
          (C.toZChain.ρ (r + 1)) hρn0 hρnl hp1 hp2 r' hr' hrU' t' ht' htr
      · -- figure 6.6
        have hiu : ¬IsIso (pathVal u'') := fun h ↦ hU' ⟨t ≫ inv (pathVal u''), by
          rw [← hUeu, Category.assoc, IsIso.inv_hom_id_assoc, ht]⟩
        have hρd : D.ψ ≫ pathVal u'' ≫ eu.1 = C.toZChain.ρ (r + 2) := by rw [hUeu, D.ψU']
        have hrd : r' ≫ pathVal u'' = 0 := by
          by_contra hrd0
          by_cases hρrd : FactorsThroughMorphism (C.toZChain.ρ (r + 2)) (r' ≫ pathVal u'')
          · refine B.l6_s4s hmin hL hR hσ hv1 D (C.toZChain.ρ (r + 1)) hp1 hp2 r' hr'
              (pathVal u'') eu.1 hUeu hiu (C.toZChain.σ (r + 2)) hσ₂ ?_ ?_ ?_
              (not_factorsThrough_of_not_isLong hσ₂ hρn0 hρnl)
              (fun h ↦ hσ₂ρ (ftm_trans_long hρ hrd0 hρrd h)) ?_ hμσ ?_
            · exact fun h ↦ hρnl (hσ₂.of_factorsThrough hρn0 (by
                rw [← hr']; exact FactorsThroughMorphism.comp_right h _))
            · exact fun h ↦ hμσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _)
            · exact fun h ↦ hσ₂ρ (by
                rw [← hρd]; exact FactorsThroughMorphism.comp_left
                  (FactorsThroughMorphism.comp_right h _) _)
            · exact fun h ↦ hμσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_right h _)
            · exact fun h ↦ hσ₂ρ (by
                rw [← hρd, ← Category.assoc]; exact FactorsThroughMorphism.comp_right h _)
          · refine B.l6_s4s hmin hL hR hσ hv1 D (C.toZChain.ρ (r + 1)) hp1 hp2 r' hr'
              (pathVal u'') eu.1 hUeu hiu (C.toZChain.ρ (r + 2)) hρ ?_ ?_
              (not_ftm_mid hρ0 D.ψ_not_isIso hρd)
              (not_factorsThrough_of_not_isLong hρ hρn0 hρnl) hρrd
              (not_ftm_prefix hρ0 D.U'_not_isIso D.ψU') hρσ
              (not_ftm_prefix hρ0 eu.2.2.1 (by rw [Category.assoc]; exact hρd))
            · exact fun h ↦ hρnl (hρ.of_factorsThrough hρn0 (by
                rw [← hr']; exact FactorsThroughMorphism.comp_right h _))
            · exact fun h ↦ hρσ (by rw [← D.ψU]; exact FactorsThroughMorphism.comp_left h _)
        have hdap : u''.comp eu.toPath = D.u₂' := by rw [hu]; rfl
        have hdp : 0 < u''.length := pos_length_of_not_isIso u'' hiu
        by_cases hρσn : FactorsThroughMorphism (C.toZChain.ρ (r + 2)) (C.toZChain.σ r)
        · refine B.l6_f66 hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.σ (r + 2)) hm1 hm2
            (C.toZChain.ρ (r + 1)) (C.toZChain.σ r) hρn0 hp1 hp2 hq1 hq2 hiσn r' hr' hs u''
            eu.toPath hdap hdp (by simp) hrd t (by rw [pathVal_toPath]; exact ht) hU'
            (C.toZChain.σ (r + 2)) hσ₂ (fun h ↦ hσ₂ρ (ftm_trans_long hρ hσn0 hρσn h)) ?_ ?_ ?_
            (not_ftm_prefix hσ₂0 eu.2.2.1 ht) hμσ
            (not_factorsThrough_of_not_isLong hσ₂ hρn0 hρnl) hD66
          · exact fun h ↦ hσ₂ρ (by rw [← D.βW']; exact FactorsThroughMorphism.comp_right h _)
          · exact fun h ↦ hσ₂ρ (by
              rw [← hρd]; exact FactorsThroughMorphism.comp_left
                (FactorsThroughMorphism.comp_right h _) _)
          · exact fun h ↦ hσ₂ρ (by
              rw [← hρd, ← Category.assoc]
              exact FactorsThroughMorphism.comp_right h _)
        · refine B.l6_f66 hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.σ (r + 2)) hm1 hm2
            (C.toZChain.ρ (r + 1)) (C.toZChain.σ r) hρn0 hp1 hp2 hq1 hq2 hiσn r' hr' hs u''
            eu.toPath hdap hdp (by simp) hrd t (by rw [pathVal_toPath]; exact ht) hU'
            (C.toZChain.ρ (r + 2)) hρ hρσn (not_ftm_prefix hρ0 (D.W'_not_isIso hρ.2.2.1) D.βW')
            (not_ftm_mid hρ0 D.ψ_not_isIso hρd)
            (not_ftm_prefix hρ0 eu.2.2.1 (by rw [Category.assoc]; exact hρd)) ?_ hρσ
            (not_factorsThrough_of_not_isLong hρ hρn0 hρnl) hD66
          exact fun h ↦ hρσ₂ (by rw [← ht]; exact FactorsThroughMorphism.comp_right h _)
    · exact B.lemma5a_rho_last hmin hL hR hQ hcont C (r + 2) hρ eu ew
        ((D.α.toPath.comp D.χ).comp u'') (D.β'.toPath.comp w'') hρu hρw
        (by have := D.hniρ; rw [hu, hw] at this; exact this) hαe hβe

include B in
/-- **BO13a Lemma 6, case I**: `σ₁ = σ (r+1)`, `ρ₁ = ρ (r+2)` and `σ₂ = σ (r+2)`
long in a minimal crown is impossible. -/
theorem l6_caseI
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (r : ℕ)
    (hσ : IsLong (C.toZChain.σ (r + 1))) (hρ : IsLong (C.toZChain.ρ (r + 2)))
    (hσ₂ : IsLong (C.toZChain.σ (r + 2)))
    (hD63 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F63.thin) k))
    (hD64 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F64.thin) k))
    (hD66 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F66.thin) k)) :
    False := by
  have hv1 : ¬∃ c, C.toZChain.σ (r + 1) ≫ c = C.toZChain.ρ (r + 2) := C.toZChain.valley₁ (r + 1)
  have hv2 : ¬∃ c, C.toZChain.ρ (r + 2) ≫ c = C.toZChain.σ (r + 1) := C.toZChain.valley₂ (r + 1)
  have hp1 : ¬∃ c, c ≫ C.toZChain.σ (r + 1) = C.toZChain.ρ (r + 1) := C.toZChain.peak₁ (r + 1)
  have hp2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 1) = C.toZChain.σ (r + 1) := C.toZChain.peak₂ (r + 1)
  have hq1 : ¬∃ c, C.toZChain.σ r ≫ c = C.toZChain.ρ (r + 1) := C.toZChain.valley₁ r
  have hq2 : ¬∃ c, C.toZChain.ρ (r + 1) ≫ c = C.toZChain.σ r := C.toZChain.valley₂ r
  have hm1 : ¬∃ c, c ≫ C.toZChain.σ (r + 2) = C.toZChain.ρ (r + 2) := C.toZChain.peak₁ (r + 2)
  have hm2 : ¬∃ c, c ≫ C.toZChain.ρ (r + 2) = C.toZChain.σ (r + 2) := C.toZChain.peak₂ (r + 2)
  have hρn0 := C.toZChain.ρ_ne (r + 1)
  have hσn0 := C.toZChain.σ_ne r
  have hiσn := C.toZChain.σ_not_isIso r
  obtain ⟨D⟩ := B.exists_l6Data hmin hL hR hσ hρ (hcont _ hσ) (hcont _ hρ) hv1 hv2
  obtain ⟨Te, e, he, hpk⟩ := B.exists_last_not hmin hL hR hσ₂ (hcont _ hσ₂)
    (C.toZChain.ρ (r + 2)) hρ.1 hm1 hm2
  have hy₁ := D.irr_y₁ hρ.2.2.1 he hpk
  have h0e := not_factorsThrough_irr hσ.2.1 hσ.1 hσ.2.2.1 he
  by_cases hρnl : IsLong (C.toZChain.ρ (r + 1))
  · -- I.1: figure 6.1 with `θ`
    obtain ⟨T, θ, hθ, hpkθ⟩ := B.exists_last_not hmin hL hR hρnl (hcont _ hρnl)
      (C.toZChain.σ (r + 1)) hσ.1 hp2 hp1
    have hy₀ := D.irr_y₀ hσ.2.2.1 hθ hpkθ
    exact B.l6_fig61 hmin hL hR hσ hρ hv1 hv2 D θ e
      (not_factorsThrough_irr hσ.2.1 hσ.1 hσ.2.2.1 hθ) h0e hθ.2.1 he.2.1 hpkθ hpk hy₀.1 hy₀.2
      hy₁.1 hy₁.2
  by_cases hW : ∃ g, g ≫ D.W = C.toZChain.ρ (r + 1)
  · -- I.2.b
    obtain ⟨r', hr'⟩ := hW
    by_cases hs : ∃ s, r' ≫ s = C.toZChain.σ r
    · obtain ⟨s, hs⟩ := hs
      exact B.l6_fig62 hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) (C.toZChain.σ r) hρn0
        hσn0 hρnl hp1 hp2 hq1 hq2 r' s hr' hs e he hpk
    · have hir' : ¬IsIso r' := fun h ↦ hp2 ⟨D.β.1 ≫ inv r', by
        rw [← hr', Category.assoc, IsIso.inv_hom_id_assoc, D.βW]⟩
      by_cases hσ₂σn : FactorsThroughMorphism (C.toZChain.σ (r + 2)) (C.toZChain.σ r)
      · have hσnl : IsLong (C.toZChain.σ r) := hσ₂.of_factorsThrough hσn0 hσ₂σn
        obtain ⟨T, φ, hφ, hφρ⟩ := B.exists_first_not hmin hL hR hσnl (hcont _ hσnl)
          (C.toZChain.ρ (r + 1)) hρn0 hq1 hq2
        refine B.l6_fig63 hmin hL hR hQ hσ hρ hv1 hv2 D (C.toZChain.σ (r + 2)) hσ₂ hm1 hm2
          (C.toZChain.ρ (r + 1)) hρn0 hρnl hp1 hp2 r' hr' φ
          (not_factorsThrough_irr hσ₂.2.1 hσ₂.1 hσ₂.2.2.1 hφ) hφ.2.1 ?_ ?_ hφρ e he hpk hD63
        · rintro ⟨g, hg⟩
          rcases hφ.2.2 _ r' g hg.symm with h | h
          · exact hir' h
          · exact hφρ ⟨inv g ≫ D.W, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hr']⟩
        · exact fun ⟨g, hg⟩ ↦ hφρ ⟨g ≫ D.W, by rw [← Category.assoc, hg, hr']⟩
      · refine B.l6_fig63 hmin hL hR hQ hσ hρ hv1 hv2 D (C.toZChain.σ (r + 2)) hσ₂ hm1 hm2
          (C.toZChain.ρ (r + 1)) hρn0 hρnl hp1 hp2 r' hr' (C.toZChain.σ r) hσ₂σn hiσn hs ?_ hq1
          e he hpk hD63
        exact fun ⟨g, hg⟩ ↦ hq1 ⟨g ≫ D.W, by rw [← Category.assoc, hg, hr']⟩
  by_cases hU : ∃ g, g ≫ D.U = C.toZChain.ρ (r + 1)
  · -- I.2.c
    obtain ⟨r', hr'⟩ := hU
    by_cases hrU' : r' ≫ D.U' = 0
    · exact B.l6_caseI_U_ii hmin hL hR hQ hcont C hC r hσ hρ hσ₂ hρnl D e he hpk r' hr' hrU' hD64
        hD66
    · exact B.l6_caseI_U_i hmin hL hR hQ C hC r hσ hρ hσ₂ hρnl D e he hpk r' hr' hrU'
  · -- I.2.a: figure 6.1 with `ρₙ`
    exact B.l6_fig61 hmin hL hR hσ hρ hv1 hv2 D (C.toZChain.ρ (r + 1)) e
      (not_factorsThrough_of_not_isLong hσ hρn0 hρnl) h0e (C.toZChain.ρ_not_isIso _) he.2.1 hp2
      hpk hW hU hy₁.1 hy₁.2

end MulBasis

end RayQuiver

end LargeIndecomposable
