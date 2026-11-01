module

public import LargeIndecomposable.Cleaving.Shapes.ShapeIn3
public import LargeIndecomposable.Crowns.Lemma6.CaseIU
public import LargeIndecomposable.Crowns.Lemma5.Wrap
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# [mild] Lemma 1.1: the paths of a mild contour are unique

For a contour `v, w : x ⇝ y` (equal nonzero values, not interlaced) and a
non-invertible `ρ : y ⟶ y` with `v̄ ≫ ρ ≠ 0`, every path `u` with `ū = v̄` is
`v` or `w` (`MildHyp.path_unique`). The contradictions are `D̃₄` diagrams
`MildHyp.not_in3` in `P/(v̄ ≫ ρ)`.
Reconstruction: `notes/2026-10-30-142400-mild-contours-reconstruction.md`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- Distinct-arrow condition: neither arrow factors through the other. -/
def ArrowsApart {a b y : RayVert P} (e : a ⟶ y) (f : b ⟶ y) : Prop :=
  (¬∃ g : a.out ⟶ b.out, g ≫ f.1 = e.1) ∧ ¬∃ g : b.out ⟶ a.out, g ≫ e.1 = f.1

/-- Arrows into the same vertex either coincide or are apart. -/
lemma arrows_eq_or_apart {a b y : RayVert P} (e : a ⟶ y) (f : b ⟶ y) :
    (∃ h : a = b, HEq e f) ∨ ArrowsApart e f := by
  by_cases h1 : ∃ g : a.out ⟶ b.out, g ≫ f.1 = e.1
  · left
    obtain ⟨g, hg⟩ := h1
    have hiso : IsIso g := by
      rcases e.2.2.2 _ g f.1 hg.symm with h | h
      · exact h
      · exact absurd h f.2.2.1
    obtain ⟨hab, rfl⟩ := RayQuiver.eq_id_of_isIso g
    have hab' : a = b := hab
    subst hab'
    refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
    change eqToHom hab ≫ f.1 = e.1 at hg
    simpa using hg.symm
  by_cases h2 : ∃ g : b.out ⟶ a.out, g ≫ e.1 = f.1
  · left
    obtain ⟨g, hg⟩ := h2
    have hiso : IsIso g := by
      rcases f.2.2.2 _ g e.1 hg.symm with h | h
      · exact h
      · exact absurd h e.2.2.1
    exact absurd ⟨inv g, by rw [← hg, IsIso.inv_hom_id_assoc]⟩ h1
  · exact Or.inr ⟨h1, h2⟩

lemma isIso_pathVal_nil {x : RayVert P} : IsIso (pathVal (Quiver.Path.nil : Quiver.Path x x)) := by
  change IsIso (𝟙 _)
  infer_instance

/-- **Splitting two different paths with equal nonzero value** at their maximal
common final segment. -/
lemma path_split (hR : RightCancel P) {x : RayVert P} :
    ∀ (n : ℕ) {y : RayVert P} (u v : Quiver.Path x y), u.length ≤ n →
      pathVal u = pathVal v → pathVal u ≠ 0 → u ≠ v →
      ∃ (m su sv : RayVert P) (u₀ : Quiver.Path x su) (eu : su ⟶ m) (v₀ : Quiver.Path x sv)
        (ev : sv ⟶ m) (σ : Quiver.Path m y),
        u = (u₀.cons eu).comp σ ∧ v = (v₀.cons ev).comp σ ∧ ArrowsApart eu ev := by
  intro n
  induction n with
  | zero =>
      intro y u v hl huv h0 hne
      cases u with
      | nil =>
          cases v with
          | nil => exact absurd rfl hne
          | cons v' d =>
              exact absurd (by rw [← huv]; exact isIso_pathVal_nil)
                (not_isIso_pathVal _ (by simp))
      | cons u' c => simp at hl
  | succ n ih =>
      intro y u v hl huv h0 hne
      cases u with
      | nil =>
          cases v with
          | nil => exact absurd rfl hne
          | cons v' d =>
              exact absurd (by rw [← huv]; exact isIso_pathVal_nil)
                (not_isIso_pathVal _ (by simp))
      | cons u' c =>
          cases v with
          | nil =>
              exact absurd (by rw [huv]; exact isIso_pathVal_nil)
                (not_isIso_pathVal _ (by simp))
          | cons v' d =>
              rcases arrows_eq_or_apart c d with ⟨hab, hcd⟩ | hap
              · subst hab
                have hcd' : c = d := eq_of_heq hcd
                subst hcd'
                have hne' : u' ≠ v' := fun h ↦ hne (by rw [h])
                have hval : pathVal u' = pathVal v' :=
                  hR (pathVal u') (pathVal v') c.1 huv h0
                have h0' : pathVal u' ≠ 0 := fun h ↦ h0 (by
                  change pathVal u' ≫ c.1 = 0; rw [h, zero_comp])
                obtain ⟨m, su, sv, u₀, eu, v₀, ev, σ, hu, hv, hap⟩ :=
                  ih u' v' (by simp at hl; omega) hval h0' hne'
                exact ⟨m, su, sv, u₀, eu, v₀, ev, σ.cons c, by rw [hu]; rfl, by rw [hv]; rfl, hap⟩
              · exact ⟨_, _, _, u', c, v', d, .nil, rfl, rfl, hap⟩

/-- A path of length one has irreducible value. -/
lemma length_pos_of_not_irreducible {x z y : RayVert P} (p : Quiver.Path x z) (e : z ⟶ y)
    (h : ¬IsIrreducible (pathVal (p.cons e))) : 0 < p.length := by
  cases p with
  | nil => exact absurd (by change IsIrreducible (𝟙 _ ≫ e.1); simpa using e.2) h
  | cons _ _ => simp

/-- A path with irreducible value `p̄ ≫ e` has empty `p`. -/
lemma length_eq_zero_of_irreducible_cons {x z y : RayVert P} (p : Quiver.Path x z) (e : z ⟶ y)
    (h : IsIrreducible (pathVal p ≫ e.1)) : p.length = 0 := by
  by_contra hp
  rcases h.2.2 _ (pathVal p) e.1 rfl with h1 | h1
  · exact not_isIso_pathVal p (by omega) h1
  · exact e.2.2.1 h1

variable [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

lemma not_isIso_comp_of_right {a b c : P} (f : a ⟶ b) (g : b ⟶ c) (hg : ¬IsIso g) :
    ¬IsIso (f ≫ g) := fun h ↦ hg (ray_isIso_factors f g).2

lemma not_isIso_comp_of_left {a b c : P} (f : a ⟶ b) (g : b ⟶ c) (hf : ¬IsIso f) :
    ¬IsIso (f ≫ g) := fun h ↦ hf (ray_isIso_factors f g).1

/-- **Case of three apart last arrows** (first diagram of [mild] Figure 1.3). -/
lemma MildHyp.l11_caseA (hM : MildHyp k P) {x y : RayVert P} {su sv sw : RayVert P}
    (u' : Quiver.Path x su) (eu : su ⟶ y) (v' : Quiver.Path x sv) (ev : sv ⟶ y)
    (w' : Quiver.Path x sw) (ew : sw ⟶ y)
    (huv : pathVal (u'.cons eu) = pathVal (v'.cons ev))
    (hvw : pathVal (v'.cons ev) = pathVal (w'.cons ew)) {ρ : y.out ⟶ y.out} (hρ : ¬IsIso ρ)
    (hωρ : pathVal (v'.cons ev) ≫ ρ ≠ 0) (h1 : ArrowsApart eu ev) (h2 : ArrowsApart eu ew)
    (h3 : ArrowsApart ev ew) : False := by
  set τ := pathVal (v'.cons ev) ≫ ρ
  have hτ : ¬IsIso τ := not_isIso_comp_of_right _ _ hρ
  -- the value is not irreducible, so all three prefixes are nonempty
  have hnirr : ¬IsIrreducible (pathVal (v'.cons ev)) := by
    intro hirr
    have hv0 := length_eq_zero_of_irreducible_cons v' ev hirr
    have hw0 := length_eq_zero_of_irreducible_cons w' ew (by
      change IsIrreducible (pathVal (w'.cons ew)); rw [← hvw]; exact hirr)
    cases v' with
    | cons _ _ => simp at hv0
    | nil =>
      cases w' with
      | cons _ _ => simp at hw0
      | nil =>
        apply h3.1
        refine ⟨𝟙 _, ?_⟩
        have e1 : 𝟙 _ ≫ ev.1 = 𝟙 _ ≫ ew.1 := hvw
        simpa using e1.symm
  have hu0 : 0 < u'.length := length_pos_of_not_irreducible u' eu (by rw [huv]; exact hnirr)
  have hv0 : 0 < v'.length := length_pos_of_not_irreducible v' ev hnirr
  have hw0 : 0 < w'.length := length_pos_of_not_irreducible w' ew (by rw [← hvw]; exact hnirr)
  have eV : pathVal v' ≫ ev.1 ≫ ρ = τ := by
    change pathVal v' ≫ ev.1 ≫ ρ = (pathVal v' ≫ ev.1) ≫ ρ; rw [Category.assoc]
  have eW : pathVal w' ≫ ew.1 ≫ ρ = τ := by
    change pathVal w' ≫ ew.1 ≫ ρ = pathVal (v'.cons ev) ≫ ρ
    rw [hvw, ← Category.assoc]; rfl
  have eU : pathVal u' ≫ eu.1 ≫ ρ = τ := by
    change pathVal u' ≫ eu.1 ≫ ρ = pathVal (v'.cons ev) ≫ ρ
    rw [← huv, ← Category.assoc]; rfl
  exact hM.not_in3 τ hτ hωρ ev.1 ew.1 eu.1 ρ
    (not_ftm_mid hωρ (p := pathVal (v'.cons ev)) (q := 𝟙 _) (not_isIso_pathVal _ (by simp))
      (by rw [Category.comp_id]))
    (not_ftm_mid hωρ (not_isIso_pathVal _ hv0) eV)
    (not_ftm_mid hωρ (q := 𝟙 _) (not_isIso_pathVal _ hv0) (by rw [Category.comp_id, eV]))
    (not_ftm_mid hωρ (not_isIso_pathVal _ hw0) eW)
    (not_ftm_mid hωρ (q := 𝟙 _) (not_isIso_pathVal _ hw0) (by rw [Category.comp_id, eW]))
    (not_ftm_mid hωρ (not_isIso_pathVal _ hu0) eU)
    (not_ftm_mid hωρ (q := 𝟙 _) (not_isIso_pathVal _ hu0) (by rw [Category.comp_id, eU]))
    ev.2.2.1 ew.2.2.1 eu.2.2.1 hρ h3.2 h1.1 h3.1 h2.1 h1.2 h2.2

/-- A factorization `g ≫ ew = ev ≫ σ̄` interlaces `v₀ ev σ` with `w' ew`. -/
lemma interlaced_of_factor (hR : RightCancel P) {x sv m y sw : RayVert P} (v₀ : Quiver.Path x sv)
    (hv₀ : 0 < v₀.length) (ev : sv ⟶ m) (σ : Quiver.Path m y) (w' : Quiver.Path x sw) (ew : sw ⟶ y)
    (hvw : pathVal ((v₀.cons ev).comp σ) = pathVal (w'.cons ew))
    (h0 : pathVal ((v₀.cons ev).comp σ) ≠ 0) (g : sv.out ⟶ sw.out)
    (hg : g ≫ ew.1 = ev.1 ≫ pathVal σ) : Interlaced ((v₀.cons ev).comp σ) (w'.cons ew) := by
  have hV : pathVal ((v₀.cons ev).comp σ) = pathVal v₀ ≫ ev.1 ≫ pathVal σ := by
    rw [pathVal_comp]; change (pathVal v₀ ≫ ev.1) ≫ pathVal σ = _; rw [Category.assoc]
  have hgne : g ≫ ew.1 ≠ 0 := by
    rw [hg]; intro h; apply h0; rw [hV, h, comp_zero]
  have hg0 : g ≠ 0 := fun h ↦ hgne (by rw [h, zero_comp])
  let π := pathOf g hg0
  have hπ : pathVal π = g := pathVal_pathOf g hg0
  have hcancel : pathVal (v₀.comp π) = pathVal w' := by
    rw [pathVal_comp, hπ]
    apply hR _ _ ew.1
    · rw [Category.assoc, hg, ← hV, hvw]; rfl
    · rw [Category.assoc, hg, ← hV]; exact h0
  have hne1 : pathVal (v₀.comp π) ≠ 0 := by
    rw [hcancel]; intro h; apply h0; rw [hvw]; change pathVal w' ≫ ew.1 = 0; rw [h, zero_comp]
  have s1 : InterStep ((v₀.comp π).comp ew.toPath) (w'.comp ew.toPath) :=
    interStep_suffix _ _ _ (by simp) hcancel hne1
  have hinner : pathVal (π.comp ew.toPath) = pathVal (ev.toPath.comp σ) := by
    rw [pathVal_comp, pathVal_comp, hπ, pathVal_toPath, pathVal_toPath, hg]
  have hne2 : pathVal (π.comp ew.toPath) ≠ 0 := by
    rw [pathVal_comp, hπ, pathVal_toPath]; exact hgne
  have s2 : InterStep (v₀.comp (π.comp ew.toPath)) (v₀.comp (ev.toPath.comp σ)) :=
    interStep_prefix v₀ hv₀ _ _ hinner hne2
  have e1 : (v₀.cons ev).comp σ = v₀.comp (ev.toPath.comp σ) := by
    rw [← Quiver.Path.comp_assoc]; rfl
  have e2 : (v₀.comp π).comp ew.toPath = v₀.comp (π.comp ew.toPath) := Quiver.Path.comp_assoc _ _ _
  have e3 : w'.cons ew = w'.comp ew.toPath := rfl
  rw [e1, e3]
  refine Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ s2)) ?_
  rw [← e2]
  exact Relation.EqvGen.rel _ _ s1

/-- **Case of a common nonempty final segment** (second diagram of [mild]
Figure 1.3). -/
lemma MildHyp.l11_caseB (hM : MildHyp k P) {x y m su sv sw : RayVert P}
    (u₀ : Quiver.Path x su) (eu : su ⟶ m) (v₀ : Quiver.Path x sv) (ev : sv ⟶ m)
    (σ : Quiver.Path m y) (hσ : 0 < σ.length) (w' : Quiver.Path x sw) (ew : sw ⟶ y)
    (huv : pathVal ((u₀.cons eu).comp σ) = pathVal ((v₀.cons ev).comp σ))
    (hvw : pathVal ((v₀.cons ev).comp σ) = pathVal (w'.cons ew))
    (h0 : pathVal ((v₀.cons ev).comp σ) ≠ 0)
    (hni : ¬Interlaced ((v₀.cons ev).comp σ) (w'.cons ew)) {ρ : y.out ⟶ y.out} (hρ : ¬IsIso ρ)
    (hωρ : pathVal ((v₀.cons ev).comp σ) ≫ ρ ≠ 0) (hap : ArrowsApart eu ev) : False := by
  set τ := pathVal ((v₀.cons ev).comp σ) ≫ ρ
  have hτ : ¬IsIso τ := not_isIso_comp_of_right _ _ hρ
  have hV : pathVal ((v₀.cons ev).comp σ) = pathVal v₀ ≫ ev.1 ≫ pathVal σ := by
    rw [pathVal_comp]; change (pathVal v₀ ≫ ev.1) ≫ pathVal σ = _; rw [Category.assoc]
  have hU : pathVal ((u₀.cons eu).comp σ) = pathVal u₀ ≫ eu.1 ≫ pathVal σ := by
    rw [pathVal_comp]; change (pathVal u₀ ≫ eu.1) ≫ pathVal σ = _; rw [Category.assoc]
  have hσi : ¬IsIso (pathVal σ) := not_isIso_pathVal σ hσ
  have hin : pathVal u₀ ≫ eu.1 = pathVal v₀ ≫ ev.1 := by
    apply hM.right _ _ (pathVal σ)
    · rw [Category.assoc, Category.assoc, ← hU, ← hV, huv]
    · rw [Category.assoc, ← hU, huv]; exact h0
  have hv₀ : 0 < v₀.length := by
    cases v₀ with
    | cons _ _ => simp
    | nil =>
      exact absurd ⟨pathVal u₀, by rw [hin]; exact Category.id_comp _⟩ hap.2
  have hu₀ : 0 < u₀.length := by
    cases u₀ with
    | cons _ _ => simp
    | nil =>
      exact absurd ⟨pathVal v₀, by rw [← hin]; exact Category.id_comp _⟩ hap.1
  have hw' : 0 < w'.length := by
    refine length_pos_of_not_irreducible w' ew ?_
    rw [← hvw, hV]
    intro hirr
    rcases hirr.2.2 _ (pathVal v₀) (ev.1 ≫ pathVal σ) rfl with h1 | h1
    · exact not_isIso_pathVal v₀ hv₀ h1
    · exact not_isIso_comp_of_left _ _ ev.2.2.1 h1
  have eV : pathVal v₀ ≫ (ev.1 ≫ pathVal σ) ≫ ρ = τ := by
    change _ = pathVal ((v₀.cons ev).comp σ) ≫ ρ; rw [hV]; simp only [Category.assoc]
  have eU : pathVal u₀ ≫ (eu.1 ≫ pathVal σ) ≫ ρ = τ := by
    change _ = pathVal ((v₀.cons ev).comp σ) ≫ ρ; rw [← huv, hU]; simp only [Category.assoc]
  have eW : pathVal w' ≫ ew.1 ≫ ρ = τ := by
    change _ = pathVal ((v₀.cons ev).comp σ) ≫ ρ; rw [hvw, ← Category.assoc]; rfl
  have hirrβ : ∀ {s : RayVert P} (e : s ⟶ m), ¬∃ g, g ≫ e.1 ≫ pathVal σ = ew.1 := by
    rintro s e ⟨g, hg⟩
    rcases ew.2.2.2 _ (g ≫ e.1) (pathVal σ) (by rw [← hg, Category.assoc]) with h1 | h1
    · exact not_isIso_comp_of_right _ _ e.2.2.1 h1
    · exact hσi h1
  have hUV : Interlaced ((u₀.cons eu).comp σ) ((v₀.cons ev).comp σ) := by
    refine Relation.EqvGen.rel _ _ (interStep_suffix _ _ _ hσ hin ?_)
    intro h
    apply h0
    rw [pathVal_comp]
    change pathVal (v₀.cons ev) ≫ _ = 0
    rw [show pathVal (v₀.cons ev) = pathVal (u₀.cons eu) from hin.symm, h, zero_comp]
  have hUw : ¬∃ g, g ≫ ew.1 = eu.1 ≫ pathVal σ := by
    rintro ⟨g, hg⟩
    apply hni
    have hUW := interlaced_of_factor hM.right u₀ hu₀ eu σ w' ew (huv.trans hvw)
      (by rw [huv]; exact h0) g hg
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hUV) hUW
  have hVw : ¬∃ g, g ≫ ew.1 = ev.1 ≫ pathVal σ := by
    rintro ⟨g, hg⟩
    exact hni (interlaced_of_factor hM.right v₀ hv₀ ev σ w' ew hvw h0 g hg)
  have hσne : ∀ {s : RayVert P} (p : Quiver.Path x s) (e : s ⟶ m),
      pathVal p ≫ e.1 = pathVal v₀ ≫ ev.1 → e.1 ≫ pathVal σ ≠ 0 := by
    intro s p e he h
    apply h0
    rw [hV, ← Category.assoc, ← he, Category.assoc, h, comp_zero]
  have hvu : ¬∃ g, g ≫ ev.1 ≫ pathVal σ = eu.1 ≫ pathVal σ := by
    rintro ⟨g, hg⟩
    refine hap.1 ⟨g, hM.right _ _ (pathVal σ) (by rw [Category.assoc, hg]) ?_⟩
    rw [Category.assoc, hg]; exact hσne u₀ eu hin
  have huv' : ¬∃ g, g ≫ eu.1 ≫ pathVal σ = ev.1 ≫ pathVal σ := by
    rintro ⟨g, hg⟩
    refine hap.2 ⟨g, hM.right _ _ (pathVal σ) (by rw [Category.assoc, hg]) ?_⟩
    rw [Category.assoc, hg]; exact hσne v₀ ev rfl
  exact hM.not_in3 τ hτ hωρ (ev.1 ≫ pathVal σ) ew.1 (eu.1 ≫ pathVal σ) ρ
    (not_ftm_mid hωρ (p := pathVal ((v₀.cons ev).comp σ)) (q := 𝟙 _)
      (not_isIso_pathVal _ (by simp)) (by rw [Category.comp_id]))
    (not_ftm_mid hωρ (not_isIso_pathVal _ hv₀) eV)
    (not_ftm_mid hωρ (q := 𝟙 _) (not_isIso_pathVal _ hv₀) (by rw [Category.comp_id, eV]))
    (not_ftm_mid hωρ (not_isIso_pathVal _ hw') eW)
    (not_ftm_mid hωρ (q := 𝟙 _) (not_isIso_pathVal _ hw') (by rw [Category.comp_id, eW]))
    (not_ftm_mid hωρ (not_isIso_pathVal _ hu₀) eU)
    (not_ftm_mid hωρ (q := 𝟙 _) (not_isIso_pathVal _ hu₀) (by rw [Category.comp_id, eU]))
    (not_isIso_comp_of_left _ _ ev.2.2.1) ew.2.2.1 (not_isIso_comp_of_left _ _ eu.2.2.1) hρ
    (hirrβ ev) hvu hVw hUw huv' (hirrβ eu)

/-- **[mild] Lemma 1.1**: the paths of a contour `{v, w}` with `v̄ ≫ ρ ≠ 0`
(`ρ` a non-invertible endomorphism of the end) are the only paths with
value `v̄`. -/
theorem MildHyp.path_unique (hM : MildHyp k P) {x y : RayVert P} {v w : Quiver.Path x y}
    (hvw : pathVal v = pathVal w) (h0 : pathVal v ≠ 0) (hni : ¬Interlaced v w)
    {ρ : y.out ⟶ y.out} (hρ : ¬IsIso ρ) (hωρ : pathVal v ≫ ρ ≠ 0) (u : Quiver.Path x y)
    (hu : pathVal u = pathVal v) : u = v ∨ u = w := by
  by_contra hc
  push Not at hc
  obtain ⟨huv, huw⟩ := hc
  have hu0 : pathVal u ≠ 0 := by rw [hu]; exact h0
  have hw0 : pathVal w ≠ 0 := by rw [← hvw]; exact h0
  obtain ⟨m₁, su₁, sv₁, u₁, eu₁, v₁, ev₁, σ₁, hu₁, hv₁, hap₁⟩ :=
    path_split hM.right u.length u v le_rfl hu hu0 huv
  obtain ⟨m₂, su₂, sw₂, u₂, eu₂, w₂, ew₂, σ₂, hu₂, hw₂, hap₂⟩ :=
    path_split hM.right u.length u w le_rfl (hu.trans hvw) hu0 huw
  have hwni : ¬IsIso (pathVal w) := by
    intro hiso
    have hwl : w.length = 0 := by
      by_contra h; exact not_isIso_pathVal w (by omega) hiso
    have hvl : v.length = 0 := by
      by_contra h; exact not_isIso_pathVal v (by omega) (by rw [hvw]; exact hiso)
    cases w with
    | cons _ _ => simp at hwl
    | nil =>
      cases v with
      | cons _ _ => simp at hvl
      | nil => exact hni (Relation.EqvGen.refl _)
  have hvni : ¬IsIso (pathVal v) := by rw [hvw]; exact hwni
  rcases Nat.eq_zero_or_pos σ₁.length with hσ₁ | hσ₁
  swap
  · obtain ⟨sw, w', ew, rfl⟩ := exists_last_arrow w hwni
    subst hv₁
    rw [hu₁] at hu
    exact hM.l11_caseB u₁ eu₁ v₁ ev₁ σ₁ hσ₁ w' ew hu hvw h0 hni hρ hωρ hap₁
  rcases Nat.eq_zero_or_pos σ₂.length with hσ₂ | hσ₂
  swap
  · obtain ⟨sv, v', ev, rfl⟩ := exists_last_arrow v hvni
    subst hw₂
    rw [hu₂] at hu
    exact hM.l11_caseB u₂ eu₂ w₂ ew₂ σ₂ hσ₂ v' ev (hu.trans hvw) hvw.symm hw0
      (fun h ↦ hni (Relation.EqvGen.symm _ _ h)) hρ (by rw [← hvw]; exact hωρ) hap₂
  cases σ₁ with
  | cons _ _ => simp at hσ₁
  | nil =>
    cases σ₂ with
    | cons _ _ => simp at hσ₂
    | nil =>
      simp only [Quiver.Path.comp_nil] at hu₁ hu₂ hv₁ hw₂
      subst hv₁ hw₂
      have hcons : u₁.cons eu₁ = u₂.cons eu₂ := hu₁.symm.trans hu₂
      have hs := Quiver.Path.obj_eq_of_cons_eq_cons hcons
      subst hs
      have he := eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons hcons)
      subst he
      rw [hu₁] at hu
      have h3 : ArrowsApart ev₁ ew₂ :=
        ⟨not_last_of_contour hM.right ev₁ ew₂ v₁ w₂ hvw h0 hni,
          not_last_of_contour hM.right ew₂ ev₁ w₂ v₁ hvw.symm hw0
            (fun h ↦ hni (Relation.EqvGen.symm _ _ h))⟩
      exact hM.l11_caseA u₁ eu₁ v₁ ev₁ w₂ ew₂ hu hvw hρ hωρ hap₁ hap₂ h3

end RayCat

end LargeIndecomposable
