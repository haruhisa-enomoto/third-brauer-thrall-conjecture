module

public import LargeIndecomposable.Crowns.Basic.CrownLongs
public import LargeIndecomposable.Cleaving.Shapes.ShapeF7A
public import LargeIndecomposable.Cleaving.Shapes.ShapeF7B
public import LargeIndecomposable.Cleaving.Shapes.ShapeF7C

/-!
# BO13a Lemma 7: the contour paths are short

For a long `σ`, a non-long `ρ ≤ σ` with the same domain (a valley), a long
`μ ≠ σ` forming a peak with `ρ`, and a contour `(α v', β w')` of `σ` with `ρ`
through `α`, the trees of BO13a figure 7.2 (in `P/μ`) force `v'` to have two
arrows and `w'` at most three (`MulBasis.l7_short`).

* `RayCat.exists_max_prefix`: a longest prefix through which a morphism
  factors.
* `RayCat.prefix_cross`: proper prefixes of the two paths of a contour are
  incomparable.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- **A maximal prefix through which `f` factors.** -/
lemma exists_max_prefix {x y : RayVert P} {z : P} (f : x.out ⟶ z) :
    ∀ {w : RayVert P} (q : Quiver.Path w y) (p : Quiver.Path x w), 0 < p.length →
      (∃ g, pathVal p ≫ g = f) → (¬∃ g, pathVal (p.comp q) ≫ g = f) →
      ∃ (w' w'' : RayVert P) (p₁ : Quiver.Path x w') (e : w' ⟶ w'') (p₂ : Quiver.Path w'' y),
        p₁.comp (e.toPath.comp p₂) = p.comp q ∧ 0 < p₁.length ∧ (∃ g, pathVal p₁ ≫ g = f) ∧
          ¬∃ g, (pathVal p₁ ≫ e.1) ≫ g = f := by
  intro w q
  induction q with
  | nil =>
    intro p _ hp hpq
    exact absurd (by simpa using hp) hpq
  | cons q' e' ih =>
    intro p hpl hp hpq
    by_cases h : ∃ g, pathVal (p.comp q') ≫ g = f
    · exact ⟨_, _, p.comp q', e', Quiver.Path.nil, rfl,
        by rw [Quiver.Path.length_comp]; omega, h, fun ⟨g, hg⟩ ↦ hpq ⟨g, hg⟩⟩
    · obtain ⟨w', w'', p₁, e, p₂, h1, h2, h3, h4⟩ := ih p hpl hp h
      refine ⟨w', w'', p₁, e, p₂.cons e', ?_, h2, h3, h4⟩
      rw [show p₁.comp (e.toPath.comp (p₂.cons e')) = (p₁.comp (e.toPath.comp p₂)).cons e' from
        rfl, h1]
      rfl

variable [IsRayCategory P]

/-- Proper prefixes of the two paths of a contour are incomparable. -/
lemma prefix_cross (hL : LeftCancel P) (hR : RightCancel P) {x y : RayVert P}
    (V W : Quiver.Path x y) (hval : pathVal V = pathVal W) (h0 : pathVal V ≠ 0)
    (hni : ¬Interlaced V W) {m m' : RayVert P} (u₁ : Quiver.Path x m) (u₂ : Quiver.Path m y)
    (t₁ : Quiver.Path x m') (t₂ : Quiver.Path m' y) (hu : u₁.comp u₂ = V) (ht : t₁.comp t₂ = W)
    (hu₁ : 0 < u₁.length) (ht₂ : 0 < t₂.length) : ¬∃ g, pathVal u₁ ≫ g = pathVal t₁ := by
  subst hu ht
  exact (contour_cross hL hR u₁ u₂ t₁ t₂ hval h0 hni hu₁ ht₂).2

omit [IsRayCategory P] in
/-- A long morphism divides no nonzero morphism different from it. -/
lemma not_ftm_of_ne {a b x y : P} {μ : a ⟶ b} (hμ : IsLong μ) {σ : x ⟶ y} (hσ0 : σ ≠ 0)
    (hne : (⟨x, y, σ⟩ : RayMor P) ≠ ⟨a, b, μ⟩) : ¬FactorsThroughMorphism μ σ := by
  intro h
  obtain ⟨hx, hy, he⟩ := hμ.2.2.2 σ hσ0 h
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  exact hne (by rw [he])

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a figures 7.1, 7.2**: the contour paths of `σ` are short. -/
theorem l7_short
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    {x y₀ y₁ x₂ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ0 : ρ ≠ 0)
    (hρl : ¬IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (hle : FactorsThroughMorphism ρ σ) {μ : x₂ ⟶ y₁} (hμ : IsLong μ)
    (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ)
    (hne : (⟨x, y₀, σ⟩ : RayMor P) ≠ ⟨x₂, y₁, μ⟩)
    {c d : RayVert P} (α : RayVert.mk x ⟶ c) (β : RayVert.mk x ⟶ d)
    (v' : Quiver.Path c (RayVert.mk y₀)) (w' : Quiver.Path d (RayVert.mk y₀))
    (hv : pathVal (α.toPath.comp v') = σ) (hw : pathVal (β.toPath.comp w') = σ)
    (hni : ¬Interlaced (α.toPath.comp v') (β.toPath.comp w')) (hα : ∃ g, α.1 ≫ g = ρ) :
    v'.length = 2 ∧ w'.length ≤ 3 := by
  have hσ0 := hσ.1
  -- `η`: an arrow into `y₁` of a contour of `μ` through which `ρ` does not factor
  obtain ⟨Te, η, hη, hηρ⟩ := B.exists_last_not hmin hL hR hμ (hcont _ hμ) ρ hρ0 hm1 hm2
  have h0η : ¬FactorsThroughMorphism μ η := not_factorsThrough_irr hμ.2.1 hμ.1 hμ.2.2.1 hη
  -- segments of `σ` and of `ρ` are not divisible by `μ`
  have segσ : ∀ {X Y : P} (L : x ⟶ X) (s : X ⟶ Y) (R : Y ⟶ y₀), L ≫ s ≫ R = σ →
      ¬FactorsThroughMorphism μ s := fun L s R hs h ↦ not_ftm_of_ne hμ hσ0 hne (by
    rw [← hs]; exact FactorsThroughMorphism.comp_left (FactorsThroughMorphism.comp_right h R) L)
  have segρ : ∀ {X Y : P} (L : x ⟶ X) (s : X ⟶ Y) (R : Y ⟶ y₁), L ≫ s ≫ R = ρ →
      ¬FactorsThroughMorphism μ s := fun L s R hs h ↦ hρl (hμ.of_factorsThrough hρ0 (by
    rw [← hs]; exact FactorsThroughMorphism.comp_left (FactorsThroughMorphism.comp_right h R) L))
  -- `ρ` does not factor through `β`
  have hβρ : ¬∃ g, β.1 ≫ g = ρ := fun hβ ↦ B.not_factors_both hmin hL hR α β v' w'
    (by rw [hv, hw]) (by rw [hv]; exact hσ0) hni ⟨_, ρ⟩ hρ0
    (by rintro ⟨c, hc⟩; rw [hv] at hc; exact hv1 ⟨c, hc⟩)
    (by rintro ⟨c, hc⟩; change ρ ≫ c = _ at hc; rw [hv] at hc; exact hv2 ⟨c, hc⟩) hα hβ
  -- the longest prefix of `α v'` through which `ρ` factors
  obtain ⟨_, _, p₁, e, p₂, hsplit, hp₁, ⟨ρ', hρ'⟩, hmx⟩ := exists_max_prefix
    (x := RayVert.mk x) (y := RayVert.mk y₀) ρ v' α.toPath (by simp)
    (by obtain ⟨g, hg⟩ := hα; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩)
    (by rintro ⟨g, hg⟩; rw [hv] at hg; exact hv1 ⟨g, hg⟩)
  have hσ3 : pathVal p₁ ≫ e.1 ≫ pathVal p₂ = σ := by
    rw [← hv, ← hsplit, pathVal_comp, pathVal_comp, pathVal_toPath]
  have hir' : ¬IsIso ρ' := fun h ↦ hv2 ⟨inv ρ' ≫ e.1 ≫ pathVal p₂, by
    rw [← hρ', Category.assoc, IsIso.hom_inv_id_assoc]; exact hσ3⟩
  -- Lemma 4 c): the rest of the path has at least two arrows
  have hp₂ : 0 < p₂.length := by
    by_contra h0
    have hl : p₂.length = 0 := by omega
    cases p₂ with
    | cons _ _ => simp at hl
    | nil =>
      obtain ⟨c', d', hcd⟩ := hle
      obtain ⟨_, d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR hv2 (pathVal p₁) e.1 ρ'
        (by rw [← hσ3]; exact congrArg (pathVal p₁ ≫ ·) (Category.comp_id _).symm) hρ' c' d'
        hcd.symm hσ0
      rcases e.2.2.2 _ d₁ d₂ hd.symm with h | h
      · exact hd₁ h
      · exact hd₂ h
  have hlen : p₁.length + 1 + p₂.length = 1 + v'.length := by
    have := congrArg Quiver.Path.length hsplit
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at this
    omega
  have hval : pathVal (α.toPath.comp v') = pathVal (β.toPath.comp w') := by rw [hv, hw]
  have h0v : pathVal (α.toPath.comp v') ≠ 0 := by rw [hv]; exact hσ0
  have hwσ : β.1 ≫ pathVal w' = σ := by rw [← hw, pathVal_comp, pathVal_toPath]
  have hw' : 0 < w'.length := by
    by_contra h0
    have hl : w'.length = 0 := by omega
    cases w' with
    | cons _ _ => simp at hl
    | nil =>
      apply hσ.2.2.1
      rw [← hwσ]
      exact (Category.comp_id β.1).symm ▸ β.2
  have hρη : ∀ {X : P} (L : x ⟶ X) (s : X ⟶ y₁), L ≫ s = ρ → ¬∃ g, g ≫ η = s :=
    fun L s hs ⟨g, hg⟩ ↦ hηρ ⟨L ≫ g, by rw [Category.assoc, hg, hs]⟩
  have hrη : ¬∃ g, g ≫ ρ' = η := by
    rintro ⟨g, hg⟩
    rcases hη.2.2 _ g ρ' hg.symm with h | h
    · exact hηρ ⟨pathVal p₁ ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, hρ']⟩
    · exact hir' h
  have hV₂r : ¬∃ g, e.1 ≫ g = ρ' := fun ⟨g, hg⟩ ↦ hmx ⟨g, by rw [Category.assoc, hg, hρ']⟩
  have hrV₂ : ¬∃ g, ρ' ≫ g = e.1 := by
    rintro ⟨g, hg⟩
    rcases e.2.2.2 _ ρ' g hg.symm with h | h
    · exact hir' h
    · exact hmx ⟨inv g, by
        rw [Category.assoc, ← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id, hρ']⟩
  -- figure 7.2, first tree: the prefix is one arrow
  have hp₁1 : p₁.length = 1 := by
    by_contra h1
    obtain ⟨_, p₀, q₁, hq₁⟩ := exists_last_arrow p₁ (not_isIso_pathVal p₁ hp₁)
    subst hq₁
    have hp₀ : 0 < p₀.length := by simp only [Quiver.Path.length_cons] at h1; omega
    have hσ4 : pathVal p₀ ≫ q₁.1 ≫ e.1 ≫ pathVal p₂ = σ := by
      rw [← hσ3]; change _ = (pathVal p₀ ≫ q₁.1) ≫ _; simp only [Category.assoc]
    have hρ3 : pathVal p₀ ≫ q₁.1 ≫ ρ' = ρ := by
      rw [← hρ']; change _ = (pathVal p₀ ≫ q₁.1) ≫ _; simp only [Category.assoc]
    exact B.not_f7a hmin hL hR μ hμ.2.1 hμ.1 (pathVal p₀) q₁.1 e.1 (pathVal p₂) ρ' η
      (segσ (pathVal p₀ ≫ q₁.1) e.1 (pathVal p₂) (by simp only [Category.assoc]; exact hσ4))
      (segσ (pathVal p₀ ≫ q₁.1) (e.1 ≫ pathVal p₂) (𝟙 _) (by
        simp only [Category.assoc, Category.comp_id]; exact hσ4))
      (segρ (pathVal p₀ ≫ q₁.1) ρ' (𝟙 _) (by simp only [Category.assoc, Category.comp_id]; exact hρ3))
      (segσ (pathVal p₀) q₁.1 (e.1 ≫ pathVal p₂) hσ4)
      (segσ (pathVal p₀) (q₁.1 ≫ e.1) (pathVal p₂) (by simp only [Category.assoc]; exact hσ4))
      (segσ (pathVal p₀) ((q₁.1 ≫ e.1) ≫ pathVal p₂) (𝟙 _) (by
        simp only [Category.assoc, Category.comp_id]; exact hσ4))
      (segρ (pathVal p₀) (q₁.1 ≫ ρ') (𝟙 _) (by simp only [Category.assoc, Category.comp_id]; exact hρ3))
      (segσ (𝟙 _) (pathVal p₀) (q₁.1 ≫ e.1 ≫ pathVal p₂) (by
        simp only [Category.id_comp]; exact hσ4))
      (segσ (𝟙 _) (pathVal p₀ ≫ q₁.1) (e.1 ≫ pathVal p₂) (by
        simp only [Category.assoc, Category.id_comp]; exact hσ4))
      (segσ (𝟙 _) ((pathVal p₀ ≫ q₁.1) ≫ e.1) (pathVal p₂) (by
        simp only [Category.assoc, Category.id_comp]; exact hσ4))
      (segσ (𝟙 _) (((pathVal p₀ ≫ q₁.1) ≫ e.1) ≫ pathVal p₂) (𝟙 _) (by
        simp only [Category.assoc, Category.id_comp, Category.comp_id]; exact hσ4))
      (segρ (𝟙 _) ((pathVal p₀ ≫ q₁.1) ≫ ρ') (𝟙 _) (by
        simp only [Category.assoc, Category.id_comp, Category.comp_id]; exact hρ3))
      (segσ (pathVal p₀ ≫ q₁.1 ≫ e.1) (pathVal p₂) (𝟙 _) (by
        simp only [Category.assoc, Category.comp_id]; exact hσ4)) h0η
      (not_isIso_pathVal p₀ hp₀) q₁.2.2.1 e.2.2.1 (not_isIso_pathVal p₂ hp₂) hir' hη.2.1
      hV₂r hrV₂ (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ', Category.assoc, hg]; exact hσ3⟩) hrη
      (hρη _ _ hρ') (hρη (pathVal p₀) _ hρ3) (hρη (𝟙 _) _ (by
        simp only [Category.assoc, Category.id_comp]; exact hρ3))
  -- the crossings of the contour at proper prefixes
  have crossVW : ∀ {m m' : RayVert P} (u₁ : Quiver.Path (RayVert.mk x) m)
      (u₂ : Quiver.Path m (RayVert.mk y₀)) (t₁ : Quiver.Path (RayVert.mk x) m')
      (t₂ : Quiver.Path m' (RayVert.mk y₀)), u₁.comp u₂ = α.toPath.comp v' →
      t₁.comp t₂ = β.toPath.comp w' → 0 < u₁.length → 0 < t₂.length →
      ¬∃ g, pathVal u₁ ≫ g = pathVal t₁ :=
    fun u₁ u₂ t₁ t₂ hu ht hu₁ ht₂ ↦ prefix_cross hL hR _ _ hval h0v hni u₁ u₂ t₁ t₂ hu ht hu₁ ht₂
  have crossWV : ∀ {m m' : RayVert P} (u₁ : Quiver.Path (RayVert.mk x) m)
      (u₂ : Quiver.Path m (RayVert.mk y₀)) (t₁ : Quiver.Path (RayVert.mk x) m')
      (t₂ : Quiver.Path m' (RayVert.mk y₀)), u₁.comp u₂ = β.toPath.comp w' →
      t₁.comp t₂ = α.toPath.comp v' → 0 < u₁.length → 0 < t₂.length →
      ¬∃ g, pathVal u₁ ≫ g = pathVal t₁ :=
    fun u₁ u₂ t₁ t₂ hu ht hu₁ ht₂ ↦ prefix_cross hL hR _ _ hval.symm (by rw [← hval]; exact h0v)
      (fun h ↦ hni h.symm) u₁ u₂ t₁ t₂ hu ht hu₁ ht₂
  have hV₁W₁ : ¬∃ g, pathVal p₁ ≫ g = β.1 := by
    have := crossVW p₁ (e.toPath.comp p₂) β.toPath w' hsplit rfl hp₁ hw'
    rwa [pathVal_toPath] at this
  have hW₁V : ∀ {m : RayVert P} (t₁ : Quiver.Path (RayVert.mk x) m)
      (t₂ : Quiver.Path m (RayVert.mk y₀)), t₁.comp t₂ = α.toPath.comp v' → 0 < t₂.length →
      ¬∃ g, β.1 ≫ g = pathVal t₁ := by
    intro m t₁ t₂ ht ht₂
    have := crossWV β.toPath w' t₁ t₂ rfl ht (by simp) ht₂
    rwa [pathVal_toPath] at this
  -- figure 7.2, second tree: the rest after the second arrow is one arrow
  have hp₂1 : p₂.length = 1 := by
    by_contra h1
    obtain ⟨_, e₂, p₃, he₂⟩ := exists_first_arrow p₂ (not_isIso_pathVal p₂ hp₂)
    subst he₂
    have hp₃ : 0 < p₃.length := by
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at h1; omega
    have hσ5 : pathVal p₁ ≫ e.1 ≫ e₂.1 ≫ pathVal p₃ = σ := by
      rw [← hσ3, pathVal_comp, pathVal_toPath]
    exact B.not_f7b hmin hL hR μ hμ.2.1 hμ.1 (pathVal p₁) β.1 e.1 e₂.1 ρ' η
      (segσ (pathVal p₁) e.1 (e₂.1 ≫ pathVal p₃) hσ5)
      (segσ (pathVal p₁) (e.1 ≫ e₂.1) (pathVal p₃) (by simp only [Category.assoc]; exact hσ5))
      (segρ (pathVal p₁) ρ' (𝟙 _) (by simp only [Category.comp_id]; exact hρ'))
      (segσ (𝟙 _) (pathVal p₁) (e.1 ≫ e₂.1 ≫ pathVal p₃) (by
        simp only [Category.id_comp]; exact hσ5))
      (segσ (𝟙 _) (pathVal p₁ ≫ e.1) (e₂.1 ≫ pathVal p₃) (by
        simp only [Category.assoc, Category.id_comp]; exact hσ5))
      (segσ (𝟙 _) ((pathVal p₁ ≫ e.1) ≫ e₂.1) (pathVal p₃) (by
        simp only [Category.assoc, Category.id_comp]; exact hσ5))
      (segρ (𝟙 _) (pathVal p₁ ≫ ρ') (𝟙 _) (by
        simp only [Category.id_comp, Category.comp_id]; exact hρ'))
      (segσ (𝟙 _) β.1 (pathVal w') (by simp only [Category.id_comp]; exact hwσ))
      (segσ (pathVal p₁ ≫ e.1) e₂.1 (pathVal p₃) (by simp only [Category.assoc]; exact hσ5)) h0η
      (not_isIso_pathVal p₁ hp₁) β.2.2.1 e.2.2.1 e₂.2.2.1 hir' hη.2.1 hV₂r hrV₂
      (fun ⟨g, hg⟩ ↦ hv2 ⟨g ≫ pathVal p₃, by
        rw [← hρ', Category.assoc, ← Category.assoc ρ', hg]; simp only [Category.assoc]
        exact hσ5⟩)
      hV₁W₁ (hW₁V p₁ (e.toPath.comp (e₂.toPath.comp p₃)) hsplit (by simp))
      (by
        have := hW₁V (p₁.comp e.toPath) (e₂.toPath.comp p₃)
          (by rw [Quiver.Path.comp_assoc]; exact hsplit) (by simp)
        rwa [pathVal_comp, pathVal_toPath] at this)
      (by
        have := hW₁V ((p₁.comp e.toPath).comp e₂.toPath) p₃
          (by simp only [Quiver.Path.comp_assoc]; exact hsplit) hp₃
        simpa only [pathVal_comp, pathVal_toPath, Category.assoc] using this)
      (fun ⟨g, hg⟩ ↦ hβρ ⟨g, by rw [hg]; exact hρ'⟩) hrη (hρη _ _ hρ')
      (hρη (𝟙 _) _ (by simp only [Category.id_comp]; exact hρ'))
  -- figure 7.2, third tree: `w` has at most four arrows
  have hw4 : w'.length ≤ 3 := by
    by_contra h4
    obtain ⟨_, e₂, w₁', rfl⟩ := exists_first_arrow w' (not_isIso_pathVal w' hw')
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at h4
    obtain ⟨_, e₃, w₂', rfl⟩ := exists_first_arrow w₁' (not_isIso_pathVal w₁' (by omega))
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at h4
    obtain ⟨_, e₄, w₃', rfl⟩ := exists_first_arrow w₂' (not_isIso_pathVal w₂' (by omega))
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at h4
    have hw₃ : 0 < w₃'.length := by omega
    have hσw : β.1 ≫ e₂.1 ≫ e₃.1 ≫ e₄.1 ≫ pathVal w₃' = σ := by
      rw [← hwσ]; simp only [pathVal_comp, pathVal_toPath]
    have hσv : pathVal p₁ ≫ e.1 ≫ pathVal p₂ = σ := hσ3
    have pre : ∀ {m : RayVert P} (t₁ : Quiver.Path (RayVert.mk x) m)
        (t₂ : Quiver.Path m (RayVert.mk y₀)),
        t₁.comp t₂ = β.toPath.comp (e₂.toPath.comp (e₃.toPath.comp (e₄.toPath.comp w₃'))) →
        0 < t₂.length → ¬∃ g, pathVal p₁ ≫ g = pathVal t₁ :=
      fun t₁ t₂ ht ht₂ ↦ crossVW p₁ (e.toPath.comp p₂) t₁ t₂ hsplit ht hp₁ ht₂
    exact B.not_f7c hmin hL hR μ hμ.2.1 hμ.1 (pathVal p₁) β.1 e₂.1 e₃.1 e₄.1 e.1 ρ' η
      (segσ (pathVal p₁) e.1 (pathVal p₂) hσv)
      (segρ (pathVal p₁) ρ' (𝟙 _) (by simp only [Category.comp_id]; exact hρ'))
      (segσ (𝟙 _) (pathVal p₁) (e.1 ≫ pathVal p₂) (by simp only [Category.id_comp]; exact hσv))
      (segσ (𝟙 _) (pathVal p₁ ≫ e.1) (pathVal p₂) (by
        simp only [Category.assoc, Category.id_comp]; exact hσv))
      (segρ (𝟙 _) (pathVal p₁ ≫ ρ') (𝟙 _) (by
        simp only [Category.id_comp, Category.comp_id]; exact hρ'))
      (segσ (𝟙 _) β.1 (e₂.1 ≫ e₃.1 ≫ e₄.1 ≫ pathVal w₃') (by
        simp only [Category.id_comp]; exact hσw))
      (segσ (𝟙 _) (β.1 ≫ e₂.1) (e₃.1 ≫ e₄.1 ≫ pathVal w₃') (by
        simp only [Category.assoc, Category.id_comp]; exact hσw))
      (segσ (𝟙 _) ((β.1 ≫ e₂.1) ≫ e₃.1) (e₄.1 ≫ pathVal w₃') (by
        simp only [Category.assoc, Category.id_comp]; exact hσw))
      (segσ (𝟙 _) (((β.1 ≫ e₂.1) ≫ e₃.1) ≫ e₄.1) (pathVal w₃') (by
        simp only [Category.assoc, Category.id_comp]; exact hσw))
      (segσ β.1 e₂.1 (e₃.1 ≫ e₄.1 ≫ pathVal w₃') hσw)
      (segσ β.1 (e₂.1 ≫ e₃.1) (e₄.1 ≫ pathVal w₃') (by simp only [Category.assoc]; exact hσw))
      (segσ β.1 ((e₂.1 ≫ e₃.1) ≫ e₄.1) (pathVal w₃') (by
        simp only [Category.assoc]; exact hσw))
      (segσ (β.1 ≫ e₂.1) e₃.1 (e₄.1 ≫ pathVal w₃') (by simp only [Category.assoc]; exact hσw))
      (segσ (β.1 ≫ e₂.1) (e₃.1 ≫ e₄.1) (pathVal w₃') (by
        simp only [Category.assoc]; exact hσw))
      (segσ (β.1 ≫ e₂.1 ≫ e₃.1) e₄.1 (pathVal w₃') (by simp only [Category.assoc]; exact hσw))
      h0η (not_isIso_pathVal p₁ hp₁) β.2.2.1 e₂.2.2.1 e₃.2.2.1 e₄.2.2.1 e.2.2.1 hir' hη.2.1
      hV₂r hrV₂
      (by simpa only [pathVal_toPath] using pre β.toPath _ rfl (by simp))
      (by
        simpa only [pathVal_comp, pathVal_toPath] using
          pre (β.toPath.comp e₂.toPath) (e₃.toPath.comp (e₄.toPath.comp w₃'))
            (by simp only [Quiver.Path.comp_assoc]) (by simp))
      (by
        simpa only [pathVal_comp, pathVal_toPath, Category.assoc] using
          pre ((β.toPath.comp e₂.toPath).comp e₃.toPath) (e₄.toPath.comp w₃')
            (by simp only [Quiver.Path.comp_assoc]) (by simp))
      (by
        simpa only [pathVal_comp, pathVal_toPath, Category.assoc] using
          pre (((β.toPath.comp e₂.toPath).comp e₃.toPath).comp e₄.toPath) w₃'
            (by simp only [Quiver.Path.comp_assoc]) hw₃)
      (hW₁V p₁ (e.toPath.comp p₂) hsplit (by simp))
      (by
        have := hW₁V (p₁.comp e.toPath) p₂ (by rw [Quiver.Path.comp_assoc]; exact hsplit) hp₂
        rwa [pathVal_comp, pathVal_toPath] at this)
      (fun ⟨g, hg⟩ ↦ hβρ ⟨g, by rw [hg]; exact hρ'⟩) hrη (hρη _ _ hρ')
      (hρη (𝟙 _) _ (by simp only [Category.id_comp]; exact hρ'))
  exact ⟨by omega, hw4⟩

end MulBasis

end RayQuiver

end LargeIndecomposable
