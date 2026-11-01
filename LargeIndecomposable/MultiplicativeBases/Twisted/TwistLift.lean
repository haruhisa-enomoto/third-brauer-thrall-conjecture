module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift

/-!
# Twisting one arrow of a path realization by a unit

Let `F₁` assign to each arrow `a : i ⟶ j` of a quiver a morphism `F₀ j ⟶ F₀ i`
(the reversed realization). We twist one arrow `a` by a unit:
on the target side (`twistTgt`, the morphism becomes `W j ≫ F₁ a`) or on the
source side (`twistSrc`, it becomes `F₁ a ≫ W i`). If the unit commutes with the
loop `ℓ` at that vertex and every other arrow at that vertex kills `a` (through
any endomorphism), then a path vanishes after the twist exactly when it vanished
before (`pathMap_twistTgt_eq_zero_iff`, `pathMap_twistSrc_eq_zero_iff`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace LargeIndecomposable.TwistLift

open LargeIndecomposable.LinearPathCategory

universe u v w z

variable {Q : Type v} [Quiver.{w} Q] {C : Type z} [Category.{u} C] [HasZeroMorphisms C]
  (F₀ : Q → C) (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
  {i₀ j₀ : Q} (a : i₀ ⟶ j₀) (W : ∀ v : Q, F₀ v ⟶ F₀ v)

/-- `e` is the arrow `a`. -/
def IsA {i j : Q} (e : i ⟶ j) : Prop := ∃ (_ : i = i₀) (_ : j = j₀), HEq e a

open Classical in
/-- Twist `a` on its target side by `W`. -/
def twistTgt {i j : Q} (e : i ⟶ j) : F₀ j ⟶ F₀ i :=
  if IsA a e then W j ≫ F₁ e else F₁ e

open Classical in
/-- Twist `a` on its source side by `W`. -/
def twistSrc {i j : Q} (e : i ⟶ j) : F₀ j ⟶ F₀ i :=
  if IsA a e then F₁ e ≫ W i else F₁ e

lemma twistTgt_a : twistTgt F₀ F₁ a W a = W j₀ ≫ F₁ a := by
  rw [twistTgt, if_pos ⟨rfl, rfl, HEq.rfl⟩]

lemma twistTgt_of_not {i j : Q} (e : i ⟶ j) (h : ¬IsA a e) : twistTgt F₀ F₁ a W e = F₁ e := by
  rw [twistTgt, if_neg h]

lemma twistSrc_a : twistSrc F₀ F₁ a W a = F₁ a ≫ W i₀ := by
  rw [twistSrc, if_pos ⟨rfl, rfl, HEq.rfl⟩]

lemma twistSrc_of_not {i j : Q} (e : i ⟶ j) (h : ¬IsA a e) : twistSrc F₀ F₁ a W e = F₁ e := by
  rw [twistSrc, if_neg h]

/-- The twisted target-side arrow is `V ≫ F₁ e` with `V = W j` or `V = 𝟙`. -/
lemma twistTgt_eq {i j : Q} (e : i ⟶ j) :
    twistTgt F₀ F₁ a W e = W j ≫ F₁ e ∨ twistTgt F₀ F₁ a W e = F₁ e := by
  by_cases h : IsA a e
  · left; rw [twistTgt, if_pos h]
  · right; rw [twistTgt, if_neg h]

lemma twistSrc_eq {i j : Q} (e : i ⟶ j) :
    twistSrc F₀ F₁ a W e = F₁ e ≫ W i ∨ twistSrc F₀ F₁ a W e = F₁ e := by
  by_cases h : IsA a e
  · left; rw [twistSrc, if_pos h]
  · right; rw [twistSrc, if_neg h]

section Tgt

variable (ℓ : j₀ ⟶ j₀) (hW : ∀ v, IsIso (W v)) (hcomm : W j₀ ≫ F₁ ℓ = F₁ ℓ ≫ W j₀)
  (hK : ∀ {m : Q} (e : j₀ ⟶ m), ¬(∃ _ : m = j₀, HEq e ℓ) →
    ∀ u : F₀ j₀ ⟶ F₀ j₀, F₁ e ≫ u ≫ F₁ a = 0)

/-- The invariant at a path ending at `j₀`: a commuting unit, and killing by every
other arrow out of `j₀`. -/
def GoodTgt {s : Q} (p : Quiver.Path s j₀) : Prop :=
  (∃ U : F₀ j₀ ⟶ F₀ j₀, IsIso U ∧ U ≫ F₁ ℓ = F₁ ℓ ≫ U ∧
      pathMap F₀ (twistTgt F₀ F₁ a W) p = U ≫ pathMap F₀ F₁ p) ∧
    ∀ {m : Q} (e : j₀ ⟶ m), ¬(∃ _ : m = j₀, HEq e ℓ) →
      ∀ u : F₀ j₀ ⟶ F₀ j₀, F₁ e ≫ u ≫ pathMap F₀ F₁ p = 0

include hW hcomm hK in
lemma invTgt {s : Q} : ∀ {v : Q} (p : Quiver.Path s v),
    (pathMap F₀ (twistTgt F₀ F₁ a W) p = 0 ∧ pathMap F₀ F₁ p = 0) ∨
      pathMap F₀ (twistTgt F₀ F₁ a W) p = pathMap F₀ F₁ p ∨
      ∃ h : v = j₀, GoodTgt F₀ F₁ a W ℓ (h ▸ p) := by
  intro v p
  induction p with
  | nil => exact Or.inr (Or.inl (by simp))
  | @cons v' v'' p e ih =>
    rcases ih with ⟨h1, h2⟩ | h | ⟨hv', hB⟩
    · left
      simp only [pathMap_cons, h1, h2, comp_zero, and_self]
    · by_cases hA : IsA a e
      · obtain ⟨h₁, h₂, he⟩ := hA
        subst v' v''
        have he' := eq_of_heq he
        subst he'
        right; right
        refine ⟨rfl, ⟨W _, hW _, hcomm, ?_⟩, fun e' he' u ↦ ?_⟩
        · simp only [pathMap_cons, twistTgt_a, h, Category.assoc]
        · simp only [pathMap_cons]
          rw [← Category.assoc u, ← Category.assoc, ← Category.assoc, Category.assoc (F₁ e'),
            hK e' he' u, zero_comp]
      · right; left
        simp only [pathMap_cons, twistTgt_of_not F₀ F₁ a W e hA, h]
    · subst v'
      obtain ⟨⟨U, hU, hUc, hpU⟩, hkill⟩ := hB
      simp only at hpU hkill
      by_cases hl : ∃ _ : v'' = j₀, HEq e ℓ
      · obtain ⟨hv'', he⟩ := hl
        subst v''
        have he' := eq_of_heq he
        subst he'
        right; right
        have hV : ∃ V : F₀ j₀ ⟶ F₀ j₀, IsIso V ∧ V ≫ F₁ e = F₁ e ≫ V ∧
            twistTgt F₀ F₁ a W e = V ≫ F₁ e := by
          rcases twistTgt_eq F₀ F₁ a W e with h | h
          · exact ⟨W _, hW _, hcomm, h⟩
          · exact ⟨𝟙 _, inferInstance, by simp, by rw [h]; simp⟩
        obtain ⟨V, hV, hVc, hVe⟩ := hV
        refine ⟨rfl, ⟨V ≫ U, inferInstance, ?_, ?_⟩, fun e' he' u ↦ ?_⟩
        · rw [Category.assoc, hUc, ← Category.assoc, hVc, Category.assoc]
        · simp only [pathMap_cons, hVe, hpU, Category.assoc]
          rw [← Category.assoc (F₁ e) U, ← hUc, Category.assoc]
        · simp only [pathMap_cons]
          rw [← Category.assoc u]
          exact hkill e' he' _
      · left
        have hz : F₁ e ≫ U ≫ pathMap F₀ F₁ p = 0 := hkill e hl U
        have hz' : F₁ e ≫ pathMap F₀ F₁ p = 0 := by
          have := hkill e hl (𝟙 _); simpa using this
        refine ⟨?_, by simpa using hz'⟩
        simp only [pathMap_cons, hpU]
        rcases twistTgt_eq F₀ F₁ a W e with h | h
        · rw [h, Category.assoc, hz, comp_zero]
        · rw [h, hz]

include hW hcomm hK in
/-- **Twisting on the target side keeps the zero paths.** -/
theorem pathMap_twistTgt_eq_zero_iff {s v : Q} (p : Quiver.Path s v) :
    pathMap F₀ (twistTgt F₀ F₁ a W) p = 0 ↔ pathMap F₀ F₁ p = 0 := by
  rcases invTgt F₀ F₁ a W ℓ hW hcomm hK p with ⟨h1, h2⟩ | h | ⟨rfl, ⟨U, hU, -, hpU⟩, -⟩
  · exact ⟨fun _ ↦ h2, fun _ ↦ h1⟩
  · rw [h]
  · simp only at hpU
    rw [hpU]
    constructor
    · intro h0
      have := congrArg (fun f ↦ inv U ≫ f) h0
      simpa using this
    · intro h0; rw [h0, comp_zero]

end Tgt

section Src

variable (ℓ : i₀ ⟶ i₀) (hW : ∀ v, IsIso (W v)) (hcomm : W i₀ ≫ F₁ ℓ = F₁ ℓ ≫ W i₀)
  (hK : ∀ {m : Q} (e : m ⟶ i₀), ¬(∃ _ : m = i₀, HEq e ℓ) →
    ∀ u : F₀ i₀ ⟶ F₀ i₀, F₁ a ≫ u ≫ F₁ e = 0)

/-- The invariant at a path ending at `i₀`: `a` is killed after it, or the path
commutes with the unit. -/
def GoodSrc {s : Q} (p : Quiver.Path s i₀) : Prop :=
  (∀ u : F₀ i₀ ⟶ F₀ i₀, F₁ a ≫ u ≫ pathMap F₀ F₁ p = 0) ∨
    W i₀ ≫ pathMap F₀ F₁ p = pathMap F₀ F₁ p ≫ W s

include hW hcomm hK in
lemma invSrc {s : Q} : ∀ {v : Q} (p : Quiver.Path s v),
    (pathMap F₀ (twistSrc F₀ F₁ a W) p = 0 ∧ pathMap F₀ F₁ p = 0) ∨
      ((∃ U : F₀ s ⟶ F₀ s, IsIso U ∧
          pathMap F₀ (twistSrc F₀ F₁ a W) p = pathMap F₀ F₁ p ≫ U) ∧
        ∀ h : v = i₀, GoodSrc F₀ F₁ a W (h ▸ p)) := by
  intro v p
  induction p with
  | nil =>
    refine Or.inr ⟨⟨𝟙 _, inferInstance, by simp⟩, fun h ↦ ?_⟩
    subst h
    right; simp
  | @cons v' v'' p e ih =>
    rcases ih with ⟨h1, h2⟩ | ⟨⟨U, hU, hpU⟩, hD⟩
    · left
      simp only [pathMap_cons, h1, h2, comp_zero, and_self]
    · by_cases hA : IsA a e
      · obtain ⟨h₁, h₂, he⟩ := hA
        subst v' v''
        have he' := eq_of_heq he
        subst he'
        have hpe : pathMap F₀ (twistSrc F₀ F₁ e W) (p.cons e) =
            F₁ e ≫ W i₀ ≫ pathMap F₀ F₁ p ≫ U := by
          simp only [pathMap_cons, twistSrc_a, hpU, Category.assoc]
        rcases hD rfl with hD1 | hD2
        · left
          simp only at hD1
          constructor
          · rw [hpe, ← Category.assoc (W i₀), ← Category.assoc, hD1, zero_comp]
          · simpa using hD1 (𝟙 _)
        · right
          simp only at hD2
          refine ⟨⟨W s ≫ U, inferInstance, ?_⟩, fun h ↦ ?_⟩
          · rw [hpe, ← Category.assoc (W i₀), hD2]; simp
          · subst j₀
            by_cases hl : ∃ _ : i₀ = i₀, HEq e ℓ
            · obtain ⟨-, hel⟩ := hl
              have hel' := eq_of_heq hel
              subst hel'
              right
              simp only [pathMap_cons]
              rw [← Category.assoc, hcomm, Category.assoc, hD2, Category.assoc]
            · left
              intro u
              simp only [pathMap_cons]
              rw [← Category.assoc u, ← Category.assoc, ← Category.assoc, Category.assoc (F₁ e),
                hK e hl u, zero_comp]
      · right
        refine ⟨⟨U, hU, ?_⟩, fun h ↦ ?_⟩
        · simp only [pathMap_cons, twistSrc_of_not F₀ F₁ a W e hA, hpU, Category.assoc]
        · subst v''
          by_cases hl : ∃ _ : v' = i₀, HEq e ℓ
          · obtain ⟨hv, hel⟩ := hl
            subst v'
            have hel' := eq_of_heq hel
            subst hel'
            rcases hD rfl with hD1 | hD2
            · left
              intro u
              simp only [pathMap_cons]
              rw [← Category.assoc u]
              exact hD1 _
            · right
              simp only at hD2
              simp only [pathMap_cons]
              rw [← Category.assoc, hcomm, Category.assoc, hD2, Category.assoc]
          · left
            intro u
            simp only [pathMap_cons]
            rw [← Category.assoc u, ← Category.assoc, ← Category.assoc, Category.assoc (F₁ a),
              hK e hl u, zero_comp]

include hW hcomm hK in
/-- **Twisting on the source side keeps the zero paths.** -/
theorem pathMap_twistSrc_eq_zero_iff {s v : Q} (p : Quiver.Path s v) :
    pathMap F₀ (twistSrc F₀ F₁ a W) p = 0 ↔ pathMap F₀ F₁ p = 0 := by
  rcases invSrc F₀ F₁ a W ℓ hW hcomm hK p with ⟨h1, h2⟩ | ⟨⟨U, hU, hpU⟩, -⟩
  · exact ⟨fun _ ↦ h2, fun _ ↦ h1⟩
  · rw [hpU]
    constructor
    · intro h0
      have := congrArg (fun f ↦ f ≫ inv U) h0
      simpa using this
    · intro h0; rw [h0, zero_comp]

end Src

end LargeIndecomposable.TwistLift
