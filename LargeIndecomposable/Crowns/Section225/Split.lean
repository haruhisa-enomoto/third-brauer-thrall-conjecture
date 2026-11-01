module

public import LargeIndecomposable.Crowns.Section225.Orientations

/-!
# BO13a §2.2.5: a reflecting contour splits at one point

* `Quiver.Path.comp_eq_comp`: two factorizations of one path (Levi's lemma).
* `RayCat.split_or_gap`: a path whose first arrow is a prefix of `ρ` and whose last
  arrow is a suffix of `ρₙ` splits as `v₁ v₂` with `ρ` through `v₁` and `ρₙ` through
  `v₂`, or has a gap `v₁ m v₂` between the longest such prefix and suffix.
* `MulBasis.s225_split`: for a long `σ₁` with a reflecting contour `v`, the gap gives the
  `D̃₅` tree `F8R1A` in `P/τ`; so `v = v₁ v₂` with `ρ₁ = V₁ ≫ ρ₁'`, `ρₙ = ρₙ' ≫ V₂`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- **Levi's lemma for paths.** -/
lemma comp_eq_comp {x : V} : ∀ {y b : V} (w₂ : Path b y) {a : V} (u₁ : Path x a)
    (u₂ : Path a y) (w₁ : Path x b), u₁.comp u₂ = w₁.comp w₂ →
      (∃ m : Path a b, w₁ = u₁.comp m ∧ u₂ = m.comp w₂) ∨
        (∃ m : Path b a, u₁ = w₁.comp m ∧ w₂ = m.comp u₂) := by
  intro y b w₂
  induction w₂ with
  | nil =>
    intro a u₁ u₂ w₁ h
    exact Or.inl ⟨u₂, h.symm, (comp_nil _).symm⟩
  | cons w₂' e ih =>
    intro a u₁ u₂ w₁ h
    cases u₂ with
    | nil => exact Or.inr ⟨w₂'.cons e, h, (comp_nil _).symm⟩
    | cons u₂' e' =>
      simp only [comp_cons, cons.injEq] at h
      obtain ⟨rfl, h2, h3⟩ := h
      obtain rfl := eq_of_heq h3
      rcases ih u₁ u₂' w₁ (eq_of_heq h2) with ⟨m, hw, hu⟩ | ⟨m, hu, hw⟩
      · exact Or.inl ⟨m, hw, by rw [hu]; rfl⟩
      · exact Or.inr ⟨m, hu, by rw [hw]; rfl⟩

end Quiver.Path

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- **Split or gap.** -/
lemma split_or_gap {x y b c : RayVert P} {Y₁ Xn : P} (ρ : x.out ⟶ Y₁) (ρn : Xn ⟶ y.out)
    (α : x ⟶ b) (v' : Quiver.Path b y) (u : Quiver.Path x c) (ω : c ⟶ y)
    (hvu : α.toPath.comp v' = u.cons ω) (hα : ∃ g, α.1 ≫ g = ρ) (hω : ∃ g, g ≫ ω.1 = ρn)
    (h1 : ¬∃ g, pathVal (α.toPath.comp v') ≫ g = ρ)
    (h2 : ¬∃ g, g ≫ pathVal (α.toPath.comp v') = ρn) :
    (∃ (a : RayVert P) (v₁ : Quiver.Path x a) (v₂ : Quiver.Path a y),
      v₁.comp v₂ = α.toPath.comp v' ∧ 0 < v₁.length ∧ 0 < v₂.length ∧
        (∃ g, pathVal v₁ ≫ g = ρ) ∧ (∃ g, g ≫ pathVal v₂ = ρn) ∧
          ∃ (d : RayVert P) (e : a ⟶ d) (p₂ : Quiver.Path d y), v₂ = e.toPath.comp p₂ ∧
            ¬∃ g, (pathVal v₁ ≫ e.1) ≫ g = ρ) ∨
    ∃ (a d : RayVert P) (v₁ : Quiver.Path x a) (m : Quiver.Path a d) (v₂ : Quiver.Path d y),
      v₁.comp (m.comp v₂) = α.toPath.comp v' ∧ 0 < v₁.length ∧ 0 < m.length ∧
        0 < v₂.length ∧ (∃ g, pathVal v₁ ≫ g = ρ) ∧ (∃ g, g ≫ pathVal v₂ = ρn) ∧
          (¬∃ g, pathVal (v₁.comp m) ≫ g = ρ) ∧ ¬∃ g, g ≫ pathVal (m.comp v₂) = ρn := by
  obtain ⟨w', w'', p₁, e, p₂, k1, k2, k3, k4⟩ := exists_max_prefix ρ v' α.toPath (by simp)
    (by obtain ⟨g, hg⟩ := hα; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩) h1
  have h2' : ¬∃ g, g ≫ pathVal (u.comp ω.toPath) = ρn := by
    change ¬∃ g, g ≫ pathVal (u.cons ω) = ρn
    rw [← hvu]; exact h2
  obtain ⟨w₁, w₂, q₁, f, q₂, l1, l2, l3, l4⟩ := exists_max_suffix ρn u ω.toPath (by simp)
    (by obtain ⟨g, hg⟩ := hω; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩) h2'
  have hv : p₁.comp (e.toPath.comp p₂) = (q₁.cons f).comp q₂ := by
    rw [k1, l1, hvu]; rfl
  rcases Quiver.Path.comp_eq_comp q₂ p₁ (e.toPath.comp p₂) (q₁.cons f) hv with
    ⟨m, hm1, hm2⟩ | ⟨m, hm1, hm2⟩
  · cases m with
    | nil =>
      refine Or.inl ⟨_, p₁, q₂, by rw [← k1, hm2, Quiver.Path.nil_comp], k2, l2, k3, l3, _, e,
        p₂, by rw [hm2, Quiver.Path.nil_comp], k4⟩
    | cons m' f' =>
      refine Or.inr ⟨_, _, p₁, m'.cons f', q₂, by rw [← k1, hm2], k2, by simp, l2, k3, l3, ?_, ?_⟩
      · -- `m` starts with `e`
        rintro ⟨g, hg⟩
        rcases Quiver.Path.comp_eq_comp q₂ e.toPath p₂ (m'.cons f') hm2 with
          ⟨n, hn1, -⟩ | ⟨n, hn1, -⟩
        · refine k4 ⟨pathVal n ≫ g, ?_⟩
          rw [← hg, hn1, pathVal_comp, pathVal_comp, pathVal_toPath]
          simp
        · have hl := congrArg Quiver.Path.length hn1
          simp only [Quiver.Path.length_toPath, Quiver.Path.length_comp,
            Quiver.Path.length_cons] at hl
          cases n with
          | cons _ _ => simp only [Quiver.Path.length_cons] at hl; omega
          | nil =>
            simp only [Quiver.Path.comp_nil] at hn1
            refine k4 ⟨g, ?_⟩
            rw [← hg, pathVal_comp, ← hn1, pathVal_toPath]
      · -- `m` ends with `f`
        rintro ⟨g, hg⟩
        have hf : (p₁.comp m').cons f' = q₁.cons f := hm1.symm
        simp only [Quiver.Path.cons.injEq] at hf
        obtain ⟨rfl, -, hf2⟩ := hf
        obtain rfl := eq_of_heq hf2
        refine l4 ⟨g ≫ pathVal m', ?_⟩
        rw [← hg, pathVal_comp]
        change (g ≫ pathVal m') ≫ f'.1 ≫ pathVal q₂ = g ≫ (pathVal m' ≫ f'.1) ≫ pathVal q₂
        simp
  · refine Or.inl ⟨_, p₁, e.toPath.comp p₂, k1, k2, by simp, k3, ?_, _, e, p₂, rfl, k4⟩
    obtain ⟨g, hg⟩ := l3
    exact ⟨g ≫ pathVal m, by rw [Category.assoc, ← pathVal_comp, ← hm2]; exact hg⟩

/-- **Split or gap**, with the longest suffix. -/
lemma split_or_gap_suf {x y b c : RayVert P} {Y₁ Xn : P} (ρ : x.out ⟶ Y₁) (ρn : Xn ⟶ y.out)
    (α : x ⟶ b) (v' : Quiver.Path b y) (u : Quiver.Path x c) (ω : c ⟶ y)
    (hvu : α.toPath.comp v' = u.cons ω) (hα : ∃ g, α.1 ≫ g = ρ) (hω : ∃ g, g ≫ ω.1 = ρn)
    (h1 : ¬∃ g, pathVal (α.toPath.comp v') ≫ g = ρ)
    (h2 : ¬∃ g, g ≫ pathVal (α.toPath.comp v') = ρn) :
    (∃ (a : RayVert P) (v₁ : Quiver.Path x a) (v₂ : Quiver.Path a y),
      v₁.comp v₂ = α.toPath.comp v' ∧ 0 < v₁.length ∧ 0 < v₂.length ∧
        (∃ g, pathVal v₁ ≫ g = ρ) ∧ (∃ g, g ≫ pathVal v₂ = ρn) ∧
          ∃ (d : RayVert P) (u₁ : Quiver.Path x d) (f : d ⟶ a), v₁ = u₁.cons f ∧
            ¬∃ g, g ≫ f.1 ≫ pathVal v₂ = ρn) ∨
    ∃ (a d : RayVert P) (v₁ : Quiver.Path x a) (m : Quiver.Path a d) (v₂ : Quiver.Path d y),
      v₁.comp (m.comp v₂) = α.toPath.comp v' ∧ 0 < v₁.length ∧ 0 < m.length ∧
        0 < v₂.length ∧ (∃ g, pathVal v₁ ≫ g = ρ) ∧ (∃ g, g ≫ pathVal v₂ = ρn) ∧
          (¬∃ g, pathVal (v₁.comp m) ≫ g = ρ) ∧ ¬∃ g, g ≫ pathVal (m.comp v₂) = ρn := by
  obtain ⟨w', w'', p₁, e, p₂, k1, k2, k3, k4⟩ := exists_max_prefix ρ v' α.toPath (by simp)
    (by obtain ⟨g, hg⟩ := hα; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩) h1
  have h2' : ¬∃ g, g ≫ pathVal (u.comp ω.toPath) = ρn := by
    change ¬∃ g, g ≫ pathVal (u.cons ω) = ρn
    rw [← hvu]; exact h2
  obtain ⟨w₁, w₂, q₁, f, q₂, l1, l2, l3, l4⟩ := exists_max_suffix ρn u ω.toPath (by simp)
    (by obtain ⟨g, hg⟩ := hω; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩) h2'
  have hv : p₁.comp (e.toPath.comp p₂) = (q₁.cons f).comp q₂ := by
    rw [k1, l1, hvu]; rfl
  rcases Quiver.Path.comp_eq_comp q₂ p₁ (e.toPath.comp p₂) (q₁.cons f) hv with
    ⟨m, hm1, hm2⟩ | ⟨m, hm1, hm2⟩
  · cases m with
    | nil =>
      refine Or.inl ⟨_, p₁, q₂, by rw [← k1, hm2, Quiver.Path.nil_comp], k2, l2, k3, l3, _, q₁,
        f, hm1.symm, l4⟩
    | cons m' f' =>
      refine Or.inr ⟨_, _, p₁, m'.cons f', q₂, by rw [← k1, hm2], k2, by simp, l2, k3, l3, ?_, ?_⟩
      · -- `m` starts with `e`
        rintro ⟨g, hg⟩
        rcases Quiver.Path.comp_eq_comp q₂ e.toPath p₂ (m'.cons f') hm2 with
          ⟨n, hn1, -⟩ | ⟨n, hn1, -⟩
        · refine k4 ⟨pathVal n ≫ g, ?_⟩
          rw [← hg, hn1, pathVal_comp, pathVal_comp, pathVal_toPath]
          simp
        · have hl := congrArg Quiver.Path.length hn1
          simp only [Quiver.Path.length_toPath, Quiver.Path.length_comp,
            Quiver.Path.length_cons] at hl
          cases n with
          | cons _ _ => simp only [Quiver.Path.length_cons] at hl; omega
          | nil =>
            simp only [Quiver.Path.comp_nil] at hn1
            refine k4 ⟨g, ?_⟩
            rw [← hg, pathVal_comp, ← hn1, pathVal_toPath]
      · -- `m` ends with `f`
        rintro ⟨g, hg⟩
        have hf : (p₁.comp m').cons f' = q₁.cons f := hm1.symm
        simp only [Quiver.Path.cons.injEq] at hf
        obtain ⟨rfl, -, hf2⟩ := hf
        obtain rfl := eq_of_heq hf2
        refine l4 ⟨g ≫ pathVal m', ?_⟩
        rw [← hg, pathVal_comp]
        change (g ≫ pathVal m') ≫ f'.1 ≫ pathVal q₂ = g ≫ (pathVal m' ≫ f'.1) ≫ pathVal q₂
        simp
  · refine Or.inl ⟨_, q₁.cons f, q₂, by rw [l1, hvu]; rfl, by simp, l2, ?_, l3, _, q₁, f, rfl,
      l4⟩
    obtain ⟨g, hg⟩ := k3
    exact ⟨pathVal m ≫ g, by rw [← Category.assoc, ← pathVal_comp, ← hm1]; exact hg⟩

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **A reflecting contour splits at one point** (the gap gives the `D̃₅` tree `F8R1A` in
`P/τ`; figure 2.1 at the split point gives the zero relation). Here `ρ` is the valley
neighbour and `ρn` the peak neighbour of the long `σ`. -/
theorem split_refl
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (h4 : NoCrown4 P)
    {X Y₀ Y₁ Xn : P} (σ : X ⟶ Y₀) (ρ : X ⟶ Y₁) (ρn : Xn ⟶ Y₀) (hσ : IsLong σ)
    (hρl : ¬IsLong ρ) (hρnl : ¬IsLong ρn) (hρ0 : ρ ≠ 0) (hρn0 : ρn ≠ 0)
    (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ) (hq1 : ¬∃ c, c ≫ σ = ρn)
    (hq2 : ¬∃ c, c ≫ ρn = σ) {a' b' : P} (τ : a' ⟶ b') (hτ : IsLong τ)
    (hτσ : ¬FactorsThroughMorphism τ σ) {b c : RayVert P} (α : RayVert.mk X ⟶ b)
    (v' : Quiver.Path b (RayVert.mk Y₀)) (u : Quiver.Path (RayVert.mk X) c)
    (ω : c ⟶ RayVert.mk Y₀) (hvu : α.toPath.comp v' = u.cons ω)
    (hv : pathVal (α.toPath.comp v') = σ) (hα : ∃ g, α.1 ≫ g = ρ) (hω : ∃ g, g ≫ ω.1 = ρn) :
    ∃ (a : RayVert P) (v₁ : Quiver.Path (RayVert.mk X) a) (v₂ : Quiver.Path a (RayVert.mk Y₀))
      (ρ' : a.out ⟶ Y₁) (ρn' : Xn ⟶ a.out), v₁.comp v₂ = α.toPath.comp v' ∧ 0 < v₁.length ∧
        0 < v₂.length ∧ pathVal v₁ ≫ ρ' = ρ ∧ ρn' ≫ pathVal v₂ = ρn ∧ ρn' ≫ ρ' = 0 ∧
          ∃ (d : RayVert P) (e : a ⟶ d) (p₂ : Quiver.Path d (RayVert.mk Y₀)),
            v₂ = e.toPath.comp p₂ ∧ ¬∃ g, (pathVal v₁ ≫ e.1) ≫ g = ρ := by
  have hσ0 := hσ.1
  rcases split_or_gap ρ ρn α v' u ω hvu hα hω (by rw [hv]; exact hv1) (by rw [hv]; exact hq1) with
    ⟨a, v₁, v₂, e, h1, h2, ⟨ρ', hρ'⟩, ⟨ρn', hρn'⟩, hmax⟩ |
      ⟨a, d, v₁, m, v₂, e, h1, hm, h2, ⟨ρ', hρ'⟩, ⟨ρn', hρn'⟩, hpre, hsuf⟩
  · have hV : pathVal v₁ ≫ pathVal v₂ = σ := by rw [← pathVal_comp v₁ v₂, e, hv]
    refine ⟨a, v₁, v₂, ρ', ρn', e, h1, h2, hρ', hρn', ?_, hmax⟩
    -- figure 2.1 at `a`
    by_contra h0
    refine no_fig21 hL hR h4 (pathVal v₁) ρn' ρ' (pathVal v₂) ?_ ?_ ?_ ?_
      (by rw [hρ']; exact hρ0) h0 (by rw [hρn']; exact hρn0) (by rw [hV]; exact hσ0)
    · exact fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hV, ← Category.assoc, hg, hρn']⟩
    · exact fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hρn', ← Category.assoc, hg, hV]⟩
    · exact fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ', Category.assoc, hg, hV]⟩
    · exact fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hV, Category.assoc, hg, hρ']⟩
  · exfalso
    have hV : pathVal v₁ ≫ pathVal m ≫ pathVal v₂ = σ := by
      rw [← pathVal_comp m v₂, ← pathVal_comp v₁ (m.comp v₂), e, hv]
    have hiV₁ := not_isIso_pathVal v₁ h1
    have hiA := not_isIso_pathVal m hm
    have hiBm := not_isIso_pathVal v₂ h2
    have hAB0 : pathVal m ≫ pathVal v₂ ≠ 0 := fun h ↦ hσ0 (by rw [← hV, h, comp_zero])
    have hrA : ¬∃ g, g ≫ ρn' = pathVal m := fun ⟨g, hg⟩ ↦
      hq2 ⟨pathVal v₁ ≫ g, by rw [← hV, ← hρn', ← hg]; simp⟩
    have hρA : ¬∃ g, ρ' ≫ g = pathVal m := fun ⟨g, hg⟩ ↦
      hv2 ⟨g ≫ pathVal v₂, by rw [← hV, ← hρ', ← hg]; simp⟩
    exact B.not_f8r1a hmin hL hR τ hτ.2.1 hτ.1 (pathVal v₁) (pathVal m) (pathVal v₂) ρn' ρ'
      (h0_a_c := not_ftm_prefix_of_long hτ hiBm hAB0)
      (h0_a_y₀ := not_ftm_suffix_of_long hτ hiV₁ (by rw [hV]; exact hσ0))
      (h0_a_y₁ := not_ftm_suffix_of_long hτ hiV₁ (by rw [hρ']; exact hρ0))
      (h0_x_a := not_ftm_prefix_of_long hτ hiA
        (fun h ↦ hσ0 (by rw [← hV, ← Category.assoc, h, zero_comp])))
      (h0_x_c := not_ftm_prefix_of_long hτ hiBm (by rw [Category.assoc, hV]; exact hσ0))
      (h0_x_y₀ := by rw [Category.assoc, hV]; exact hτσ)
      (h0_x_y₁ := by rw [hρ']; exact not_factorsThrough_of_not_isLong hτ hρ0 hρl)
      (h0_c_y₀ := not_ftm_suffix_of_long hτ hiA hAB0)
      (h0_xn_c := not_ftm_prefix_of_long hτ hiBm (by rw [hρn']; exact hρn0))
      (h0_xn_y₀ := by rw [hρn']; exact not_factorsThrough_of_not_isLong hτ hρn0 hρnl)
      (hi_V₁ := hiV₁) (hi_A := hiA) (hi_Bm := hiBm)
      (hi_r := fun _ ↦ hrA ⟨pathVal m ≫ inv ρn', by simp⟩)
      (hi_ρ₁' := fun _ ↦ hρA ⟨inv ρ' ≫ pathVal m, by simp⟩)
      (hl_A_ρ₁'_y₁ := fun ⟨g, hg⟩ ↦ hpre ⟨g, by rw [pathVal_comp v₁ m, Category.assoc, hg, hρ']⟩)
      (hl_ρ₁'_A_c := hρA)
      (hl_ρ₁'_A_y₀ := fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ', Category.assoc, hg, hV]⟩)
      (hr_A_r_xn := fun ⟨g, hg⟩ ↦ hsuf ⟨g, by rw [pathVal_comp m v₂, ← Category.assoc, hg, hρn']⟩)
      (hr_r_A_a := hrA)
      (hr_r_A_x := fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hρn', ← Category.assoc, hg, Category.assoc, hV]⟩)

include B in
/-- **A reflecting contour splits at one point**, with the longest suffix (the gap gives the `D̃₅` tree `F8R1A` in
`P/τ`; figure 2.1 at the split point gives the zero relation). Here `ρ` is the valley
neighbour and `ρn` the peak neighbour of the long `σ`. -/
theorem split_refl_suf
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (h4 : NoCrown4 P)
    {X Y₀ Y₁ Xn : P} (σ : X ⟶ Y₀) (ρ : X ⟶ Y₁) (ρn : Xn ⟶ Y₀) (hσ : IsLong σ)
    (hρl : ¬IsLong ρ) (hρnl : ¬IsLong ρn) (hρ0 : ρ ≠ 0) (hρn0 : ρn ≠ 0)
    (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ) (hq1 : ¬∃ c, c ≫ σ = ρn)
    (hq2 : ¬∃ c, c ≫ ρn = σ) {a' b' : P} (τ : a' ⟶ b') (hτ : IsLong τ)
    (hτσ : ¬FactorsThroughMorphism τ σ) {b c : RayVert P} (α : RayVert.mk X ⟶ b)
    (v' : Quiver.Path b (RayVert.mk Y₀)) (u : Quiver.Path (RayVert.mk X) c)
    (ω : c ⟶ RayVert.mk Y₀) (hvu : α.toPath.comp v' = u.cons ω)
    (hv : pathVal (α.toPath.comp v') = σ) (hα : ∃ g, α.1 ≫ g = ρ) (hω : ∃ g, g ≫ ω.1 = ρn) :
    ∃ (a : RayVert P) (v₁ : Quiver.Path (RayVert.mk X) a) (v₂ : Quiver.Path a (RayVert.mk Y₀))
      (ρ' : a.out ⟶ Y₁) (ρn' : Xn ⟶ a.out), v₁.comp v₂ = α.toPath.comp v' ∧ 0 < v₁.length ∧
        0 < v₂.length ∧ pathVal v₁ ≫ ρ' = ρ ∧ ρn' ≫ pathVal v₂ = ρn ∧ ρn' ≫ ρ' = 0 ∧
          ∃ (d : RayVert P) (u₁ : Quiver.Path (RayVert.mk X) d) (f : d ⟶ a),
            v₁ = u₁.cons f ∧ ¬∃ g, g ≫ f.1 ≫ pathVal v₂ = ρn := by
  have hσ0 := hσ.1
  rcases split_or_gap_suf ρ ρn α v' u ω hvu hα hω (by rw [hv]; exact hv1) (by rw [hv]; exact hq1) with
    ⟨a, v₁, v₂, e, h1, h2, ⟨ρ', hρ'⟩, ⟨ρn', hρn'⟩, hmax⟩ |
      ⟨a, d, v₁, m, v₂, e, h1, hm, h2, ⟨ρ', hρ'⟩, ⟨ρn', hρn'⟩, hpre, hsuf⟩
  · have hV : pathVal v₁ ≫ pathVal v₂ = σ := by rw [← pathVal_comp v₁ v₂, e, hv]
    refine ⟨a, v₁, v₂, ρ', ρn', e, h1, h2, hρ', hρn', ?_, hmax⟩
    -- figure 2.1 at `a`
    by_contra h0
    refine no_fig21 hL hR h4 (pathVal v₁) ρn' ρ' (pathVal v₂) ?_ ?_ ?_ ?_
      (by rw [hρ']; exact hρ0) h0 (by rw [hρn']; exact hρn0) (by rw [hV]; exact hσ0)
    · exact fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hV, ← Category.assoc, hg, hρn']⟩
    · exact fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hρn', ← Category.assoc, hg, hV]⟩
    · exact fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ', Category.assoc, hg, hV]⟩
    · exact fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hV, Category.assoc, hg, hρ']⟩
  · exfalso
    have hV : pathVal v₁ ≫ pathVal m ≫ pathVal v₂ = σ := by
      rw [← pathVal_comp m v₂, ← pathVal_comp v₁ (m.comp v₂), e, hv]
    have hiV₁ := not_isIso_pathVal v₁ h1
    have hiA := not_isIso_pathVal m hm
    have hiBm := not_isIso_pathVal v₂ h2
    have hAB0 : pathVal m ≫ pathVal v₂ ≠ 0 := fun h ↦ hσ0 (by rw [← hV, h, comp_zero])
    have hrA : ¬∃ g, g ≫ ρn' = pathVal m := fun ⟨g, hg⟩ ↦
      hq2 ⟨pathVal v₁ ≫ g, by rw [← hV, ← hρn', ← hg]; simp⟩
    have hρA : ¬∃ g, ρ' ≫ g = pathVal m := fun ⟨g, hg⟩ ↦
      hv2 ⟨g ≫ pathVal v₂, by rw [← hV, ← hρ', ← hg]; simp⟩
    exact B.not_f8r1a hmin hL hR τ hτ.2.1 hτ.1 (pathVal v₁) (pathVal m) (pathVal v₂) ρn' ρ'
      (h0_a_c := not_ftm_prefix_of_long hτ hiBm hAB0)
      (h0_a_y₀ := not_ftm_suffix_of_long hτ hiV₁ (by rw [hV]; exact hσ0))
      (h0_a_y₁ := not_ftm_suffix_of_long hτ hiV₁ (by rw [hρ']; exact hρ0))
      (h0_x_a := not_ftm_prefix_of_long hτ hiA
        (fun h ↦ hσ0 (by rw [← hV, ← Category.assoc, h, zero_comp])))
      (h0_x_c := not_ftm_prefix_of_long hτ hiBm (by rw [Category.assoc, hV]; exact hσ0))
      (h0_x_y₀ := by rw [Category.assoc, hV]; exact hτσ)
      (h0_x_y₁ := by rw [hρ']; exact not_factorsThrough_of_not_isLong hτ hρ0 hρl)
      (h0_c_y₀ := not_ftm_suffix_of_long hτ hiA hAB0)
      (h0_xn_c := not_ftm_prefix_of_long hτ hiBm (by rw [hρn']; exact hρn0))
      (h0_xn_y₀ := by rw [hρn']; exact not_factorsThrough_of_not_isLong hτ hρn0 hρnl)
      (hi_V₁ := hiV₁) (hi_A := hiA) (hi_Bm := hiBm)
      (hi_r := fun _ ↦ hrA ⟨pathVal m ≫ inv ρn', by simp⟩)
      (hi_ρ₁' := fun _ ↦ hρA ⟨inv ρ' ≫ pathVal m, by simp⟩)
      (hl_A_ρ₁'_y₁ := fun ⟨g, hg⟩ ↦ hpre ⟨g, by rw [pathVal_comp v₁ m, Category.assoc, hg, hρ']⟩)
      (hl_ρ₁'_A_c := hρA)
      (hl_ρ₁'_A_y₀ := fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ', Category.assoc, hg, hV]⟩)
      (hr_A_r_xn := fun ⟨g, hg⟩ ↦ hsuf ⟨g, by rw [pathVal_comp m v₂, ← Category.assoc, hg, hρn']⟩)
      (hr_r_A_a := hrA)
      (hr_r_A_x := fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hρn', ← Category.assoc, hg, Category.assoc, hV]⟩)

end MulBasis

end RayQuiver

end LargeIndecomposable
