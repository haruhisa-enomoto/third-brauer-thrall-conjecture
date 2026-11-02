module

public import LargeIndecomposable.MildContours.Contours.Lemma21
public import LargeIndecomposable.Cleaving.Shapes.ShapeD4B
public import LargeIndecomposable.Cleaving.Shapes.ShapeD5
public import LargeIndecomposable.FundamentalGroups.Basic.Fundamental

/-!
# [mild] Lemma 2.2

If `ρ = π(y)` factors through `α`, it does not factor through `β`
(`MildContour.not_ρ_factor_both`). [mild] refers this to the end of the proof
of Lemma 2.1, whose argument assumes that `ρ` factors through neither arrow;
we argue instead with the first point where paths for the two factorizations
part (a cleaving `D̃₄` or `D̃₅` in `P/τ`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- A nonempty path starts with an arrow. -/
lemma path_first_arrow {a : RayVert P} : ∀ {b : RayVert P} (r : Quiver.Path a b), r.length ≠ 0 →
    ∃ (c : RayVert P) (e : a ⟶ c) (r' : Quiver.Path c b), r = (Quiver.Path.nil.cons e).comp r'
  | _, .nil, h => absurd rfl h
  | _, .cons .nil e₀, _ => ⟨_, e₀, .nil, rfl⟩
  | _, .cons (.cons r₁ e₁) e₀, _ => by
      obtain ⟨c, e, r', hr⟩ := path_first_arrow (r₁.cons e₁) (by simp)
      exact ⟨c, e, r'.cons e₀, by rw [Quiver.Path.comp_cons, ← hr]⟩

/-- Arrows out of the same vertex either coincide or are apart. -/
lemma arrows_eq_or_apart_out {m u₁ u₂ : RayVert P} (e₁ : m ⟶ u₁) (e₂ : m ⟶ u₂) :
    (∃ h : u₁ = u₂, HEq e₁ e₂) ∨ ((¬∃ g, e₁.1 ≫ g = e₂.1) ∧ ¬∃ g, e₂.1 ≫ g = e₁.1) := by
  by_cases h1 : ∃ g, e₁.1 ≫ g = e₂.1
  · left
    obtain ⟨g, hg⟩ := h1
    have hiso : IsIso g := by
      rcases e₂.2.2.2 _ e₁.1 g hg.symm with h | h
      · exact absurd h e₁.2.2.1
      · exact h
    obtain ⟨hab, rfl⟩ := RayQuiver.eq_id_of_isIso g
    have hab' : u₁ = u₂ := hab
    subst hab'
    refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
    change e₁.1 ≫ eqToHom hab = e₂.1 at hg
    simpa using hg
  by_cases h2 : ∃ g, e₂.1 ≫ g = e₁.1
  · left
    obtain ⟨g, hg⟩ := h2
    have hiso : IsIso g := by
      rcases e₁.2.2.2 _ e₂.1 g hg.symm with h | h
      · exact absurd h e₂.2.2.1
      · exact h
    exact absurd ⟨inv g, by rw [← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id]⟩ h1
  · exact Or.inr ⟨h1, h2⟩

/-- **Two paths from the same vertex**: one extends the other, or they part at a
first pair of different arrows. -/
lemma path_diverge {a : RayVert P} : ∀ {b₁ b₂ : RayVert P} (p : Quiver.Path a b₁)
    (q : Quiver.Path a b₂),
    (∃ r : Quiver.Path b₁ b₂, q = p.comp r) ∨ (∃ r : Quiver.Path b₂ b₁, p = q.comp r) ∨
      ∃ (m u₁ u₂ : RayVert P) (c : Quiver.Path a m) (e₁ : m ⟶ u₁) (e₂ : m ⟶ u₂)
        (r₁ : Quiver.Path u₁ b₁) (r₂ : Quiver.Path u₂ b₂),
        ¬(∃ h : u₁ = u₂, HEq e₁ e₂) ∧ p = (c.cons e₁).comp r₁ ∧ q = (c.cons e₂).comp r₂
  | _, _, .nil, q => Or.inl ⟨q, (Quiver.Path.nil_comp q).symm⟩
  | b₁, _, .cons p₀ e, q => by
      rcases path_diverge p₀ q with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨m, u₁, u₂, c, e₁, e₂, r₁, r₂, hne, h1, h2⟩
      · by_cases hl : r.length = 0
        · cases r with
          | nil =>
              exact Or.inr (Or.inl ⟨Quiver.Path.nil.cons e, by
                rw [hr, Quiver.Path.comp_nil, Quiver.Path.comp_cons, Quiver.Path.comp_nil]⟩)
          | cons _ _ => simp at hl
        · obtain ⟨c, e', r', hr'⟩ := path_first_arrow r hl
          by_cases he : ∃ h : b₁ = c, HEq e e'
          · obtain ⟨h, he⟩ := he
            subst h
            have he' : e = e' := eq_of_heq he
            subst he'
            refine Or.inl ⟨r', ?_⟩
            rw [hr, hr', ← Quiver.Path.comp_assoc, Quiver.Path.comp_cons, Quiver.Path.comp_nil]
          · refine Or.inr (Or.inr ⟨_, _, _, p₀, e, e', .nil, r', he, rfl, ?_⟩)
            rw [hr, hr', ← Quiver.Path.comp_assoc, Quiver.Path.comp_cons, Quiver.Path.comp_nil]
      · exact Or.inr (Or.inl ⟨r.cons e, by rw [hr, Quiver.Path.comp_cons]⟩)
      · exact Or.inr (Or.inr ⟨m, u₁, u₂, c, e₁, e₂, r₁.cons e, r₂, hne,
          by rw [h1, Quiver.Path.comp_cons], h2⟩)

namespace MildContour

variable {x y : P} (C : MildContour x y)
variable [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

/-- **[mild] Lemma 2.2, first claim**: `ρ` does not factor through both `α` and `β`. -/
theorem not_ρ_factor_both (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : C.ρ = ω' ≫ C.α.1)
    {ω'' : y ⟶ C.sw} (hω'' : C.ρ = ω'' ≫ C.β.1) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hρ0 : C.ρ ≠ 0 := fun h ↦ C.τ_ne_zero (by change C.ω ≫ C.ρ = 0; rw [h, comp_zero])
  have hω'0 : ω' ≠ 0 := fun h ↦ hρ0 (by rw [hω', h, zero_comp])
  have hω''0 : ω'' ≠ 0 := fun h ↦ hρ0 (by rw [hω'', h, zero_comp])
  obtain ⟨p', hp'⟩ := exists_path ω' hω'0
  obtain ⟨p'', hp''⟩ := exists_path ω'' hω''0
  have hγα : ¬IsIso (C.γ ≫ C.α.1) := not_isIso_comp_of_right _ _ C.α.2.2.1
  rcases path_diverge p' p'' with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨m, u₁, u₂, c, e₁, e₂, r₁, r₂, hne, h1, h2⟩
  · -- `ω'' = ω' ≫ r̄`, so `α = r̄ ≫ β`
    have e : ω' ≫ (pathVal r ≫ C.β.1) = ω' ≫ C.α.1 := by
      rw [← Category.assoc, ← hp', ← pathVal_comp, ← hr, hp'', ← hω'', hω', hp']
    exact hap.1 ⟨pathVal r, hL _ _ _ e (by rw [e, ← hω']; exact hρ0)⟩
  · have e : ω'' ≫ (pathVal r ≫ C.α.1) = ω'' ≫ C.β.1 := by
      rw [← Category.assoc, ← hp'', ← pathVal_comp, ← hr, hp', ← hω', hω'', hp'']
    exact hap.2 ⟨pathVal r, hL _ _ _ e (by rw [e, ← hω'']; exact hρ0)⟩
  · have hab := (arrows_eq_or_apart_out e₁ e₂).resolve_left hne
    have hρ1 : C.ρ = pathVal c ≫ e₁.1 ≫ pathVal r₁ ≫ C.α.1 := by
      rw [hω', ← hp', h1, pathVal_comp]
      change ((pathVal c ≫ e₁.1) ≫ pathVal r₁) ≫ C.α.1 = _; simp only [Category.assoc]
    have hρ2 : C.ρ = pathVal c ≫ e₂.1 ≫ pathVal r₂ ≫ C.β.1 := by
      rw [hω'', ← hp'', h2, pathVal_comp]
      change ((pathVal c ≫ e₂.1) ≫ pathVal r₂) ≫ C.β.1 = _; simp only [Category.assoc]
    have hτ1 : C.τ = C.γ ≫ C.α.1 ≫ pathVal c ≫ e₁.1 ≫ pathVal r₁ ≫ C.α.1 := by
      rw [C.τ_eq_v, hρ1]
    have hτ2 : C.τ = C.γ ≫ C.α.1 ≫ pathVal c ≫ e₂.1 ≫ pathVal r₂ ≫ C.β.1 := by
      rw [C.τ_eq_v, hρ2]
    have hτ3 : C.τ = C.δ ≫ C.β.1 ≫ pathVal c ≫ e₁.1 ≫ pathVal r₁ ≫ C.α.1 := by
      rw [C.τ_eq_w, hρ1]
    have hτ4 : C.τ = C.δ ≫ C.β.1 ≫ pathVal c ≫ e₂.1 ≫ pathVal r₂ ≫ C.β.1 := by
      rw [C.τ_eq_w, hρ2]
    have hγ := C.γ_not_isIso hR
    have hδ := C.δ_not_isIso hR
    have hτ0 := C.τ_ne_zero
    cases c with
    | nil =>
        have hn : pathVal (Quiver.Path.nil : Quiver.Path (RayVert.mk y) (RayVert.mk y)) = 𝟙 y := rfl
        simp only [hn, Category.id_comp] at hτ1 hτ2 hτ3 hτ4
        refine hM.not_md4b C.τ C.τ_not_isIso hτ0 C.α.1 C.β.1 e₁.1 e₂.1
          (not_ftm_mid (q := pathVal r₁ ≫ C.α.1) hτ0 hγα (by rw [hτ1]; simp))
          (not_ftm_mid (q := pathVal r₂ ≫ C.β.1) hτ0 hγα (by rw [hτ2]; simp))
          (C.ftm_α hR)
          (not_ftm_mid (q := pathVal r₁ ≫ C.α.1) hτ0 hγ (by rw [hτ1]; simp))
          (not_ftm_mid (q := pathVal r₂ ≫ C.β.1) hτ0 hγ (by rw [hτ2]; simp))
          (C.ftm_β hR)
          (not_ftm_mid (q := pathVal r₁ ≫ C.α.1) hτ0 hδ (by rw [hτ3]; simp))
          (not_ftm_mid (q := pathVal r₂ ≫ C.β.1) hτ0 hδ (by rw [hτ4]; simp))
          C.α.2.2.1 C.β.2.2.1 e₁.2.2.1 e₂.2.2.1 hab.1 hab.2 hap.2 hap.1
    | cons c₀ e₀ =>
        have hq : ¬IsIso (pathVal (c₀.cons e₀)) := not_isIso_pathVal _ (by simp)
        refine hM.not_md5 C.τ C.τ_not_isIso hτ0 C.α.1 C.β.1 (pathVal (c₀.cons e₀)) e₁.1 e₂.1
          (not_ftm_mid (q := e₁.1 ≫ pathVal r₁ ≫ C.α.1) hτ0 hγα (by rw [hτ1]; simp))
          (not_ftm_mid (q := pathVal r₁ ≫ C.α.1) hτ0 hγα (by rw [hτ1]; simp))
          (not_ftm_mid (q := pathVal r₂ ≫ C.β.1) hτ0 hγα (by rw [hτ2]; simp))
          (C.ftm_α hR)
          (not_ftm_mid (q := e₁.1 ≫ pathVal r₁ ≫ C.α.1) hτ0 hγ (by rw [hτ1]; simp))
          (not_ftm_mid (q := pathVal r₁ ≫ C.α.1) hτ0 hγ (by rw [hτ1]; simp))
          (not_ftm_mid (q := pathVal r₂ ≫ C.β.1) hτ0 hγ (by rw [hτ2]; simp))
          (C.ftm_β hR)
          (not_ftm_mid (q := e₁.1 ≫ pathVal r₁ ≫ C.α.1) hτ0 hδ (by rw [hτ3]; simp))
          (not_ftm_mid (q := pathVal r₁ ≫ C.α.1) hτ0 hδ (by rw [hτ3]; simp))
          (not_ftm_mid (q := pathVal r₂ ≫ C.β.1) hτ0 hδ (by rw [hτ4]; simp))
          (not_ftm_mid (q := pathVal r₁ ≫ C.α.1) hτ0
            (not_isIso_comp_of_left (C.γ ≫ C.α.1) (pathVal (c₀.cons e₀)) hγα)
            (by rw [hτ1]; simp))
          (not_ftm_mid (q := pathVal r₂ ≫ C.β.1) hτ0
            (not_isIso_comp_of_left (C.γ ≫ C.α.1) (pathVal (c₀.cons e₀)) hγα)
            (by rw [hτ2]; simp))
          C.α.2.2.1 C.β.2.2.1 hq e₁.2.2.1 e₂.2.2.1 hab.1 hab.2 hap.2 hap.1

/-- A middle factor of `f ≠ 0` with a non-invertible right part does not factor
through `f`. -/
lemma not_ftm_mid_right {a b c d : P} {f : a ⟶ d} (hf0 : f ≠ 0) {p : a ⟶ b} {g : b ⟶ c}
    {q : c ⟶ d} (hq : ¬IsIso q) (h : p ≫ g ≫ q = f) : ¬FactorsThroughMorphism f g := by
  rintro ⟨u, v, rfl⟩
  have e : f = (p ≫ u) ≫ f ≫ (v ≫ q) := by
    conv_lhs => rw [← h]
    simp only [Category.assoc]
  obtain ⟨-, hvq⟩ := IsRayCategory.eq_id_of_two_sided _ hf0 _ (v ≫ q) e
  haveI : IsIso (v ≫ q) := by rw [hvq]; infer_instance
  exact hq (ray_isIso_factors v q).2

/-- **[mild] Lemma 2.2, loop case**: if `α` is a loop at `y` with `ρ = α`, the arrow
of `v` before `α` is `α` (penny-farthing) or `β` (dumb-bell). -/
theorem loop_prev (hM : MildHyp k P) {x y s t : P} (v'' : Quiver.Path (RayVert.mk x) (RayVert.mk s))
    (e : (RayVert.mk s : RayVert P) ⟶ RayVert.mk y) (α : (RayVert.mk y : RayVert P) ⟶ RayVert.mk y)
    (w' : Quiver.Path (RayVert.mk x) (RayVert.mk t)) (β : (RayVert.mk t : RayVert P) ⟶ RayVert.mk y)
    (hval : pathVal ((v''.cons e).cons α) = pathVal (w'.cons β))
    (h0 : pathVal ((v''.cons e).cons α) ≠ 0)
    (hni : ¬Interlaced ((v''.cons e).cons α) (w'.cons β))
    (hρ : ∀ f : y ⟶ y, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow α.1 n)
    (hωρ : pathVal ((v''.cons e).cons α) ≫ α.1 ≠ 0) :
    (∃ h : s = y, HEq e α) ∨ (∃ h : s = t, HEq e β) := by
  let C : MildContour x y := ⟨y, t, v''.cons e, α, w', β, hval, h0, hni, α.1, hρ, hωρ⟩
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  rcases arrows_eq_or_apart e α with ⟨h, he⟩ | hea
  · exact Or.inl ⟨congrArg RayVert.out h, by subst h; exact he⟩
  rcases arrows_eq_or_apart e β with ⟨h, he⟩ | heb
  · exact Or.inr ⟨congrArg RayVert.out h, by subst h; exact he⟩
  exfalso
  have hτe : pathVal v'' ≫ e.1 ≫ (α.1 ≫ C.ρ) = C.τ := by
    change pathVal v'' ≫ e.1 ≫ α.1 ≫ α.1 = ((pathVal v'' ≫ e.1) ≫ α.1) ≫ α.1
    simp only [Category.assoc]
  have hτe' : pathVal v'' ≫ (e.1 ≫ α.1) ≫ C.ρ = C.τ := by
    change pathVal v'' ≫ (e.1 ≫ α.1) ≫ α.1 = ((pathVal v'' ≫ e.1) ≫ α.1) ≫ α.1
    simp only [Category.assoc]
  exact hM.not_in3 C.τ C.τ_not_isIso hτ0 α.1 β.1 e.1 C.ρ C.ftm_ρ (C.ftm_α hR) (C.ftm_αρ hR)
    (C.ftm_β hR) (C.ftm_βρ hR)
    (not_ftm_mid_right hτ0 (not_isIso_comp_of_right _ _ C.ρ_not_isIso) hτe)
    (not_ftm_mid_right hτ0 C.ρ_not_isIso hτe')
    α.2.2.1 β.2.2.1 e.2.2.1 C.ρ_not_isIso hap.2 hea.1 hap.1 heb.1 hea.2 heb.2

end MildContour

end RayCat

end LargeIndecomposable
