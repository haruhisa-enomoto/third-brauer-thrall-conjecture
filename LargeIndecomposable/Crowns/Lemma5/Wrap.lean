module

public import LargeIndecomposable.Crowns.Lemma5.SoleCase
public import LargeIndecomposable.RayCategories.Contours.ContourFirst

/-!
# BO13a Lemma 5 a)

Let `σ s` be long in a chain `Z`, let `(α v', β w')` be a contour of `σ s`, and
suppose every long morphism occurs in a contour. If `ρ (s+1)` factors through
neither first arrow `α`, `β`, we get a contradiction (`MulBasis.lemma5a`).

Following BO13a, we walk along the chain to the next long morphism `τ`
(`Nat.find`). If `τ = ρ (s+1)`, four first arrows leave `x (s+1)`. Otherwise `τ`
is some `ρ (s+1+L+1)` (case A) or `σ (s+1+L)` (case B). If some long morphism
does not divide `τ`, we quotient by it (`lemma5a_caseA`, `lemma5a_caseB`);
otherwise `τ` is the only long morphism up to the factorization order and the
top states `lemma5a_top`, `lemma5a_topB` apply.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- **The last arrows of a contour are incomparable.** -/
lemma not_last_of_contour (hR : RightCancel P) {x a b y : RayVert P} (α : a ⟶ y) (β : b ⟶ y)
    (v' : Quiver.Path x a) (w' : Quiver.Path x b)
    (hval : pathVal (v'.cons α) = pathVal (w'.cons β)) (h0 : pathVal (v'.cons α) ≠ 0)
    (hni : ¬Interlaced (v'.cons α) (w'.cons β)) : ¬∃ χ : a.out ⟶ b.out, χ ≫ β.1 = α.1 := by
  rintro ⟨χ, hχ⟩
  have hiso : IsIso χ := by
    rcases α.2.2.2 _ χ β.1 hχ.symm with h | h
    · exact h
    · exact absurd h β.2.2.1
  obtain ⟨hab, rfl⟩ := RayQuiver.eq_id_of_isIso χ
  change a.out = b.out at hab
  have hab' : a = b := hab
  subst hab'
  have hαβ : α = β := Subtype.ext (by
    change eqToHom hab ≫ β.1 = α.1 at hχ
    simpa using hχ.symm)
  subst hαβ
  apply hni
  change Interlaced (v'.comp α.toPath) (w'.comp α.toPath)
  refine Relation.EqvGen.rel _ _ (interStep_suffix _ _ _ (by simp) ?_ ?_)
  · exact hR (pathVal v') (pathVal w') α.1 hval h0
  · intro h
    apply h0
    change pathVal v' ≫ α.1 = 0
    rw [h, zero_comp]

/-- A path whose value is not invertible starts with an arrow. -/
lemma exists_first_arrow {x y : RayVert P} (v : Quiver.Path x y) (hv : ¬IsIso (pathVal v)) :
    ∃ (c : RayVert P) (α : x ⟶ c) (v' : Quiver.Path c y), v = α.toPath.comp v' := by
  have hl : 0 < v.length := by
    cases v with
    | nil => exact absurd (IsIso.id _) hv
    | cons _ _ => simp
  obtain ⟨c, α, v', -, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ v
    (n := v.length - 1) (by omega)
  exact ⟨c, α, v', rfl⟩

/-- A path whose value is not invertible ends with an arrow. -/
lemma exists_last_arrow {x y : RayVert P} (v : Quiver.Path x y) (hv : ¬IsIso (pathVal v)) :
    ∃ (c : RayVert P) (v' : Quiver.Path x c) (α : c ⟶ y), v = v'.cons α := by
  cases v with
  | nil => exact absurd (IsIso.id _) hv
  | cons v' α => exact ⟨_, v', α, rfl⟩

/-- A contour of a long morphism occurring in a contour, by first arrows. -/
lemma exists_contour_first {a b : P} {μ : a ⟶ b} (hμ : IsLong μ) (hc : ¬NotInContour μ) :
    ∃ (c d : RayVert P) (α : RayVert.mk a ⟶ c) (β : RayVert.mk a ⟶ d)
      (v' : Quiver.Path c (RayVert.mk b)) (w' : Quiver.Path d (RayVert.mk b)),
      pathVal (α.toPath.comp v') = μ ∧ pathVal (β.toPath.comp w') = μ ∧
        ¬Interlaced (α.toPath.comp v') (β.toPath.comp w') := by
  obtain ⟨v, w, hv, hw, hni⟩ : ∃ v w : Quiver.Path (RayVert.mk a) (RayVert.mk b),
      pathVal v = μ ∧ pathVal w = μ ∧ ¬Interlaced v w := by
    by_contra h
    exact hc fun v w hv hw ↦ by
      by_contra hi
      exact h ⟨v, w, hv, hw, hi⟩
  obtain ⟨c, α, v', rfl⟩ := exists_first_arrow v (by rw [hv]; exact hμ.2.1)
  obtain ⟨d, β, w', rfl⟩ := exists_first_arrow w (by rw [hw]; exact hμ.2.1)
  exact ⟨c, d, α, β, v', w', hv, hw, hni⟩

/-- A contour of a long morphism occurring in a contour, by last arrows. -/
lemma exists_contour_last {a b : P} {μ : a ⟶ b} (hμ : IsLong μ) (hc : ¬NotInContour μ) :
    ∃ (c d : RayVert P) (α : c ⟶ RayVert.mk b) (β : d ⟶ RayVert.mk b)
      (v' : Quiver.Path (RayVert.mk a) c) (w' : Quiver.Path (RayVert.mk a) d),
      pathVal (v'.cons α) = μ ∧ pathVal (w'.cons β) = μ ∧ ¬Interlaced (v'.cons α) (w'.cons β) := by
  obtain ⟨v, w, hv, hw, hni⟩ : ∃ v w : Quiver.Path (RayVert.mk a) (RayVert.mk b),
      pathVal v = μ ∧ pathVal w = μ ∧ ¬Interlaced v w := by
    by_contra h
    exact hc fun v w hv hw ↦ by
      by_contra hi
      exact h ⟨v, w, hv, hw, hi⟩
  obtain ⟨c, v', α, rfl⟩ := exists_last_arrow v (by rw [hv]; exact hμ.2.1)
  obtain ⟨d, w', β, rfl⟩ := exists_last_arrow w (by rw [hw]; exact hμ.2.1)
  exact ⟨c, d, α, β, v', w', hv, hw, hni⟩

variable [Fintype P] [IsFiniteRayCategory P]

/-- Every reducible morphism lies below a long morphism. -/
lemma exists_isLong_above {x y : P} {f : x ⟶ y} (hf0 : f ≠ 0) (hfi : ¬IsIso f)
    (hfr : ¬IsIrreducible f) :
    ∃ (a b : P) (μ : a ⟶ b), IsLong μ ∧ FactorsThroughMorphism f μ := by
  classical
  let S : Set (RayMor P) := {g | g.2.2 ≠ 0 ∧ FactorsThroughMorphism f g.2.2}
  have hS : S.Finite := Set.toFinite _
  have hne : S.Nonempty := ⟨⟨x, y, f⟩, hf0, 𝟙 _, 𝟙 _, by simp⟩
  obtain ⟨⟨a, b, g⟩, ⟨hg0, α, β, hg⟩, hmax⟩ := Set.exists_max_image S (fun μ ↦ depth μ.2.2) hS hne
  simp only at hg0 hg hmax
  have hα0 : α ≠ 0 := fun h ↦ hg0 (by rw [hg, h, zero_comp])
  have hfβ0 : f ≫ β ≠ 0 := fun h ↦ hg0 (by rw [hg, h, comp_zero])
  refine ⟨a, b, g, ⟨hg0, fun hi ↦ ?_, fun hirr ↦ ?_, ?_⟩, α, β, hg⟩
  · rw [hg] at hi
    have := isIso_of_isIso_comp α (f ≫ β) hα0 hi
    have : IsIso (f ≫ β) := by
      have : f ≫ β = inv α ≫ α ≫ f ≫ β := by simp
      rw [this]; infer_instance
    exact hfi (isIso_of_isIso_comp f β hf0 this)
  · have hfr' : ∃ (z : P) (f₁ : x ⟶ z) (f₂ : z ⟶ y), f = f₁ ≫ f₂ ∧ ¬IsIso f₁ ∧ ¬IsIso f₂ := by
      by_contra h
      exact hfr ⟨hf0, hfi, fun z f₁ f₂ he ↦ by
        by_contra h'
        exact h ⟨z, f₁, f₂, he, fun h1 ↦ h' (Or.inl h1), fun h2 ↦ h' (Or.inr h2)⟩⟩
    obtain ⟨z, f₁, f₂, hf, h1, h2⟩ := hfr'
    rcases hirr.2.2 _ (α ≫ f₁) (f₂ ≫ β) (by rw [hg, hf]; simp) with h | h
    · have := isIso_of_isIso_comp α f₁ hα0 h
      apply h1
      have : f₁ = inv α ≫ α ≫ f₁ := by simp
      rw [this]; infer_instance
    · exact h2 (isIso_of_isIso_comp f₂ β (fun h0 ↦ hf0 (by rw [hf, h0, comp_zero])) h)
  · intro x' y' h hh0 ⟨a', b', hh⟩
    have hmem : (⟨x', y', h⟩ : RayMor P) ∈ S := ⟨hh0, a' ≫ α, β ≫ b', by rw [hh, hg]; simp⟩
    have hle := hmax _ hmem
    simp only at hle
    have hgb0 : g ≫ b' ≠ 0 := fun h0 ↦ hh0 (by rw [hh, h0, comp_zero])
    have ha' : IsIso a' := by
      by_contra ha
      have h1 := depth_lt_comp_left a' (g ≫ b') (by rw [← hh]; exact hh0) ha
      have h2 := depth_le_comp_right g b' hgb0
      rw [← hh] at h1
      omega
    have hb' : IsIso b' := by
      by_contra hb
      have h1 := depth_lt_comp_right g b' hgb0 hb
      have h2 := depth_le_comp_left a' (g ≫ b') (by rw [← hh]; exact hh0)
      rw [← hh] at h2
      omega
    obtain ⟨h1, rfl⟩ := eq_eqToHom_of_isIso a'
    obtain ⟨h2, rfl⟩ := eq_eqToHom_of_isIso b'
    exact ⟨h1, h2.symm, hh⟩

end RayCat

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a).** If every long morphism occurs in a contour, `σ s` is
long with contour `(α v', β w')`, and a long morphism follows in the chain, then
`ρ (s+1)` factors through `α` or `β`. -/
theorem lemma5a
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (Z : ZChain P) (s : ℕ) (hσ : IsLong (Z.σ s)) (hnext : ∃ j, IsLong (Z.σ (s + 1 + j)))
    {a₁ b₁ : RayVert P} (α : RayVert.mk (Z.x (s + 1)) ⟶ a₁) (β : RayVert.mk (Z.x (s + 1)) ⟶ b₁)
    (v' : Quiver.Path a₁ (RayVert.mk (Z.z s))) (w' : Quiver.Path b₁ (RayVert.mk (Z.z s)))
    (hv : pathVal (α.toPath.comp v') = Z.σ s) (hw : pathVal (β.toPath.comp w') = Z.σ s)
    (hni : ¬Interlaced (α.toPath.comp v') (β.toPath.comp w'))
    (hα : ¬∃ g, α.1 ≫ g = Z.ρ (s + 1)) (hβ : ¬∃ g, β.1 ≫ g = Z.ρ (s + 1)) : False := by
  classical
  -- the two first arrows of the contour of `σ s`
  let F : Fin 2 → BMor (Z.x (s + 1)) := ![arrB α, arrB β]
  have hFi : ∀ i, IsIrreducible (F i).2 := by
    intro i; fin_cases i
    exacts [α.2, β.2]
  have hF01 : F 0 ≠ F 1 := fun h ↦ not_bLe_first_of_contour hL α β v' w' (by rw [hv, hw])
    (by rw [hv]; exact hσ.1) hni (by
      change arrB α = arrB β at h
      exact h ▸ ⟨𝟙 _, Category.comp_id _⟩)
  have hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ (s + 1) := by
    intro i; fin_cases i
    exacts [hα, hβ]
  -- the next long morphism of the chain
  obtain ⟨K, hK, hKmin⟩ : ∃ K, ((K % 2 = 0 ∧ IsLong (Z.ρ (s + 1 + K / 2))) ∨
      (K % 2 = 1 ∧ IsLong (Z.σ (s + 1 + K / 2)))) ∧ ∀ k < K, ¬((k % 2 = 0 ∧
        IsLong (Z.ρ (s + 1 + k / 2))) ∨ (k % 2 = 1 ∧ IsLong (Z.σ (s + 1 + k / 2)))) := by
    have hex : ∃ K, (K % 2 = 0 ∧ IsLong (Z.ρ (s + 1 + K / 2))) ∨
        (K % 2 = 1 ∧ IsLong (Z.σ (s + 1 + K / 2))) := by
      obtain ⟨j, hj⟩ := hnext
      exact ⟨2 * j + 1, Or.inr ⟨by omega, by rwa [show (2 * j + 1) / 2 = j by omega]⟩⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk ↦ Nat.find_min hex hk⟩
  have hρn : ∀ j, 2 * j < K → ¬IsLong (Z.ρ (s + 1 + j)) := fun j hj h ↦
    hKmin _ hj (Or.inl ⟨by omega, by rwa [show 2 * j / 2 = j by omega]⟩)
  have hσn : ∀ j, 2 * j + 1 < K → ¬IsLong (Z.σ (s + 1 + j)) := fun j hj h ↦
    hKmin _ hj (Or.inr ⟨by omega, by rwa [show (2 * j + 1) / 2 = j by omega]⟩)
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' K
  · have hτ' : IsLong (Z.ρ (s + 1 + m)) := by
      rcases hK with ⟨-, h⟩ | ⟨h, -⟩
      · rwa [show 2 * m / 2 = m by omega] at h
      · omega
    rcases m with _ | L
    · -- `τ = ρ (s+1)`: four first arrows out of `x (s+1)`
      obtain ⟨c, d, α', β', v'', w'', hv', hw', hni'⟩ := exists_contour_first hτ' (hcont _ hτ')
      exact B.not_contours_out hmin hL hR α β v' w' (by rw [hv, hw]) (by rw [hv]; exact hσ.1) hni
        (by rw [hv]; exact hσ.2.1) (by rw [hv]; exact hσ.2.2.1) α' β' v'' w'' (by rw [hv', hw'])
        (by rw [hv']; exact hτ'.1) hni' (by rw [hv']; exact hα) (by rw [hv']; exact hβ)
    · -- case A: `τ = ρ (s+1+L+1)`
      have hτ : IsLong (Z.ρ (s + 1 + L + 1)) := hτ'
      have hnρ : ∀ j ≤ L, ¬IsLong (Z.ρ (s + 1 + j)) := fun j hj ↦ hρn j (by omega)
      have hnσ : ∀ j ≤ L, ¬IsLong (Z.σ (s + 1 + j)) := fun j hj ↦ hσn j (by omega)
      obtain ⟨c, d, α', β', v'', w'', hv', hw', hni'⟩ := exists_contour_first hτ (hcont _ hτ)
      let G : Fin 2 → BMor (Z.x (s + 1 + L + 1)) := ![arrB α', arrB β']
      have hGi : ∀ i, IsIrreducible (G i).2 := by
        intro i; fin_cases i
        exacts [α'.2, β'.2]
      have hG01 : G 0 ≠ G 1 := fun h ↦ not_bLe_first_of_contour hL α' β' v'' w''
        (by rw [hv', hw']) (by rw [hv']; exact hτ.1) hni' (by
          change arrB α' = arrB β' at h
          exact h ▸ ⟨𝟙 _, Category.comp_id _⟩)
      have hGτ : ∀ i, ∃ t, (G i).2 ≫ t = Z.ρ (s + 1 + L + 1) := by
        intro i; fin_cases i
        · exact ⟨pathVal v'', by rw [← hv', pathVal_comp, pathVal_toPath]; rfl⟩
        · exact ⟨pathVal w'', by rw [← hw', pathVal_comp, pathVal_toPath]; rfl⟩
      by_cases hother : ∃ (a b : P) (μ : a ⟶ b), IsLong μ ∧
          ¬FactorsThroughMorphism μ (Z.ρ (s + 1 + L + 1))
      · obtain ⟨_, _, μ, hμ, hτμ⟩ := hother
        exact B.lemma5a_caseA hmin hL hR hμ Z (s + 1) L hnρ hnσ F hFi hF01 hFρ G hGi hG01 hGτ
          hτμ hτ.2.2.1
      · -- `τ` is the only long morphism
        push Not at hother
        by_cases hσG : ∃ i, ∃ g, (G i).2 ≫ g = Z.σ (s + 1 + L)
        · have key : ∀ {e : RayVert P} (γ : RayVert.mk (Z.x (s + 1 + L + 1)) ⟶ e)
              (u : Quiver.Path e (RayVert.mk (Z.z (s + 1 + L + 1)))),
              pathVal (γ.toPath.comp u) = Z.ρ (s + 1 + L + 1) →
              ∀ S : e.out ⟶ Z.z (s + 1 + L), γ.1 ≫ S = Z.σ (s + 1 + L) → False := by
            intro e γ u hγu S hS
            have hγu' : γ.1 ≫ pathVal u = Z.ρ (s + 1 + L + 1) := by
              rw [← hγu, pathVal_comp, pathVal_toPath]
            have hSi : ¬IsIso S := fun h ↦ Z.valley₁ (s + 1 + L) ⟨inv S ≫ pathVal u, by
              rw [← hS, Category.assoc, IsIso.hom_inv_id_assoc, hγu']⟩
            have hσr : ¬IsIrreducible (Z.σ (s + 1 + L)) := fun h ↦ by
              rcases h.2.2 _ γ.1 S hS.symm with h' | h'
              · exact γ.2.2.1 h'
              · exact hSi h'
            obtain ⟨_, _, μ', hμ', a, b, hab⟩ := exists_isLong_above (Z.σ_ne _)
              (Z.σ_not_isIso _) hσr
            obtain ⟨a', b', hab'⟩ := hother _ _ μ' hμ'
            exact B.lemma5a_top hmin hL hR hQ Z (s + 1) L hτ hnρ hnσ F hFi hF01 hFρ
              ⟨a' ≫ a, b ≫ b', by rw [hab', hab]; simp⟩ u.length γ.toPath u rfl (by simp)
              (by rw [pathVal_toPath]; exact hγu') S (by rw [pathVal_toPath]; exact hS)
          obtain ⟨i, S, hS⟩ := hσG
          fin_cases i
          · exact key α' v'' hv' S hS
          · exact key β' w'' hw' S hS
        · push Not at hσG
          exact B.not_zigzag_arrow_forks hmin hL hR _ hτ.2.1 hτ.1 hτ.2.2.1 Z (s + 1) L F G hFi
            hGi hF01 hG01
            (fun j hj ↦ not_factorsThrough_of_not_isLong hτ (Z.ρ_ne _) (hnρ j hj))
            (fun j hj ↦ not_factorsThrough_of_not_isLong hτ (Z.σ_ne _) (hnσ j hj)) hFρ
            (fun i ⟨g, hg⟩ ↦ hσG i g hg)
  · -- case B: `τ = σ (s+1+m)`
    have hτ : IsLong (Z.σ (s + 1 + m)) := by
      rcases hK with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · rwa [show (2 * m + 1) / 2 = m by omega] at h
    have hnρ : ∀ j ≤ m, ¬IsLong (Z.ρ (s + 1 + j)) := fun j hj ↦ hρn j (by omega)
    have hnσ : ∀ j < m, ¬IsLong (Z.σ (s + 1 + j)) := fun j hj ↦ hσn j (by omega)
    obtain ⟨c, d, α', β', v'', w'', hv', hw', hni'⟩ := exists_contour_last hτ (hcont _ hτ)
    let G : Fin 2 → Σ y : P, y ⟶ Z.z (s + 1 + m) := ![⟨c.out, α'.1⟩, ⟨d.out, β'.1⟩]
    have hGi : ∀ i, IsIrreducible (G i).2 := by
      intro i; fin_cases i
      exacts [α'.2, β'.2]
    have hG01 : G 0 ≠ G 1 := by
      intro h
      apply not_last_of_contour hR α' β' v'' w'' (by rw [hv', hw']) (by rw [hv']; exact hτ.1) hni'
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      change c = d at h1
      subst h1
      exact ⟨𝟙 _, by rw [Category.id_comp]; exact (eq_of_heq h2).symm⟩
    have hGτ : ∀ i, ∃ t, t ≫ (G i).2 = Z.σ (s + 1 + m) := by
      intro i; fin_cases i
      · exact ⟨pathVal v'', hv'⟩
      · exact ⟨pathVal w'', hw'⟩
    by_cases hother : ∃ (a b : P) (μ : a ⟶ b), IsLong μ ∧
        ¬FactorsThroughMorphism μ (Z.σ (s + 1 + m))
    · obtain ⟨_, _, μ, hμ, hτμ⟩ := hother
      exact B.lemma5a_caseB hmin hL hR hμ Z (s + 1) m hnρ hnσ F hFi hF01 hFρ G hGi hG01 hGτ
        hτμ hτ.2.2.1
    · push Not at hother
      by_cases hρG : ∃ i, ∃ g, g ≫ (G i).2 = Z.ρ (s + 1 + m)
      · have key : ∀ {e : RayVert P} (u : Quiver.Path (RayVert.mk (Z.x (s + 1 + m + 1))) e)
            (γ : e ⟶ RayVert.mk (Z.z (s + 1 + m))), pathVal (u.cons γ) = Z.σ (s + 1 + m) →
            ∀ R' : Z.x (s + 1 + m) ⟶ e.out, R' ≫ γ.1 = Z.ρ (s + 1 + m) → False := by
          intro e u γ huγ R' hR'
          have huγ' : pathVal u ≫ γ.1 = Z.σ (s + 1 + m) := huγ
          have hRi : ¬IsIso R' := fun h ↦ Z.peak₂ (s + 1 + m) ⟨pathVal u ≫ inv R', by
            rw [← hR', Category.assoc, IsIso.inv_hom_id_assoc, huγ']⟩
          have hρr : ¬IsIrreducible (Z.ρ (s + 1 + m)) := fun h ↦ by
            rcases h.2.2 _ R' γ.1 hR'.symm with h' | h'
            · exact hRi h'
            · exact γ.2.2.1 h'
          obtain ⟨_, _, μ', hμ', a, b, hab⟩ := exists_isLong_above (Z.ρ_ne _)
            (Z.ρ_not_isIso _) hρr
          obtain ⟨a', b', hab'⟩ := hother _ _ μ' hμ'
          exact B.lemma5a_topB hmin hL hR hQ Z (s + 1) m hτ hnρ hnσ F hFi hF01 hFρ
            ⟨a' ≫ a, b ≫ b', by rw [hab', hab]; simp⟩ u.length u γ.toPath rfl (by simp)
            (by rw [pathVal_toPath]; exact huγ') R' (by rw [pathVal_toPath]; exact hR')
        obtain ⟨i, R', hR'⟩ := hρG
        fin_cases i
        · exact key v'' α' hv' R' hR'
        · exact key w'' β' hw' R' hR'
      · push Not at hρG
        have hGG : ∀ i i', i ≠ i' → ¬∃ g, g ≫ (G i).2 = (G i').2 := fun i i' hii' hg ↦ by
          have := eq_of_suffix_irr (hGi i) (hGi i') hg
          fin_cases i <;> fin_cases i' <;> simp_all
        have hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2 := fun i i' hii' hg ↦ by
          have := eq_of_bLe_irr (hFi i) (hFi i') hg
          fin_cases i <;> fin_cases i' <;> simp_all
        exact B.not_zigzag_forks_in hmin hL hR _ hτ.2.1 hτ.1 Z (s + 1) m F G
          (fun j hj ↦ not_factorsThrough_of_not_isLong hτ (Z.ρ_ne _) (hnρ j hj))
          (fun j hj ↦ not_factorsThrough_of_not_isLong hτ (Z.σ_ne _) (hnσ j hj))
          (fun i ↦ not_factorsThrough_irr hτ.2.1 hτ.1 hτ.2.2.1 (hFi i))
          (fun i ↦ not_factorsThrough_irr hτ.2.1 hτ.1 hτ.2.2.1 (hGi i)) (fun i ↦ (hFi i).2.1)
          (fun i ↦ (hGi i).2.1) hFF hGG hFρ
          (fun i ↦ not_comp_eq_irr (hFi i) (Z.ρ_not_isIso _) (hFρ i))
          (fun i ⟨g, hg⟩ ↦ hρG i g hg)
          (fun i ↦ not_comp_eq_irr' (hGi i) (Z.ρ_not_isIso _) (fun ⟨g, hg⟩ ↦ hρG i g hg))

end MulBasis

end RayQuiver

end LargeIndecomposable
