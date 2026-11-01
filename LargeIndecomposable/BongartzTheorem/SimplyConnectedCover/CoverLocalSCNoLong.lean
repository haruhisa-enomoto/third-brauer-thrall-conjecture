module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.CoverLocalSC

/-!
# Local simple connectivity without long morphisms

If `P` has no long morphisms, nonzero paths of the cover have length at most one
(`length_le_one_of_noLong`), so every weight on the cover is a cocycle, hence a coboundary, and
the cover is locally simply connected (`coverLocalSC_of_not_hasLong`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

/-- Two irreducible morphisms compose to zero without long morphisms. -/
lemma comp_irr_eq_zero (h : ¬HasLong P) {a b c : P} {f : a ⟶ b} {g : b ⟶ c}
    (hf : IsIrreducible f) (hg : IsIrreducible g) : f ≫ g = 0 := by
  by_contra h0
  have hni : ¬IsIso (f ≫ g) := by
    intro hiso
    have := (isIso_of_comp_isIso f g hiso).1
    exact hf.2.1 this
  have hirr : IsIrreducible (f ≫ g) := by
    by_contra hni'
    exact h ⟨_, _, _, h0, hni, hni'⟩
  rcases hirr.2.2 b f g rfl with h1 | h1
  · exact hf.2.1 h1
  · exact hg.2.1 h1

/-- **Nonzero paths of the cover have length at most one.** -/
lemma length_le_one_of_noLong (h : ¬HasLong P) {x : RayVert (Cover x₀)} :
    ∀ {y : RayVert (Cover x₀)} (p : Quiver.Path x y), pathVal p ≠ 0 → p.length ≤ 1
  | _, .nil, _ => by simp
  | _, .cons .nil _, _ => by simp
  | _, .cons (.cons q e₁) e₂, hp => by
    exfalso
    apply hp
    change (pathVal q ≫ e₁.1) ≫ e₂.1 = 0
    rw [Category.assoc]
    have h1 : e₁.1 ≫ e₂.1 = 0 := by
      by_contra hne
      have := val_ne_zero hne
      rw [val_comp] at this
      exact this (comp_irr_eq_zero h (isIrreducible_val e₁.2) (isIrreducible_val e₂.2))
    rw [h1, Limits.comp_zero]

lemma pathVal_cons_cons' (h : ¬HasLong P) {x w z y : RayVert (Cover x₀)} (q : Quiver.Path x w)
    (e₁ : w ⟶ z) (e₂ : z ⟶ y) : pathVal ((q.cons e₁).cons e₂) = 0 := by
  by_contra hne
  have := length_le_one_of_noLong h _ hne
  simp at this

lemma pathVal_single' {x y : RayVert (Cover x₀)} (e : x ⟶ y) :
    pathVal ((Quiver.Path.nil : Quiver.Path x x).cons e) = e.1 :=
  Category.id_comp _

lemma not_id_eq' {x : RayVert (Cover x₀)} (e : x ⟶ x) : e.1 ≠ 𝟙 _ := by
  intro h
  apply e.2.2.1
  rw [h]; infer_instance

/-- Without long morphisms, two cover paths with the same nonzero value are equal. -/
lemma path_eq_of_noLong (h : ¬HasLong P) {x : RayVert (Cover x₀)} :
    ∀ {y : RayVert (Cover x₀)} (p q : Quiver.Path x y), pathVal p = pathVal q → pathVal p ≠ 0 → p = q
  | _, .nil, .nil, _, _ => rfl
  | _, .nil, .cons .nil e, hpq, _ => absurd ((pathVal_single' e).symm.trans hpq.symm) (not_id_eq' e)
  | _, .nil, .cons (.cons q e₁) e₂, hpq, h0 => absurd (hpq.trans (pathVal_cons_cons' h q e₁ e₂)) h0
  | _, .cons .nil e, .nil, hpq, _ => absurd ((pathVal_single' e).symm.trans hpq) (not_id_eq' e)
  | _, .cons .nil e, .cons .nil e', hpq, _ => by
    rw [pathVal_single', pathVal_single'] at hpq
    rw [Subtype.ext hpq]
  | _, .cons .nil e, .cons (.cons q e₁) e₂, hpq, h0 =>
    absurd (hpq.trans (pathVal_cons_cons' h q e₁ e₂)) h0
  | _, .cons (.cons p e₁) e₂, _, _, h0 => absurd (pathVal_cons_cons' h p e₁ e₂) h0

/-- **Without long morphisms every weight on the cover is a cocycle.** -/
lemma isCocycle_of_noLong (h : ¬HasLong P) (c : ArrowWeight (Cover x₀)) : IsCocycle c := by
  intro x y p q hpq h0
  rw [path_eq_of_noLong h p q hpq h0]

/-- **Local simple connectivity without long morphisms.** -/
theorem coverLocalSC_of_not_hasLong (h : ¬HasLong P) : CoverLocalSC x₀ := by
  intro D _ _ c _
  obtain ⟨φ, hφ⟩ := isCoboundary_cover c (isCocycle_of_noLong h c)
  exact ⟨fun a ↦ φ (RayVert.mk a), fun e _ _ ↦ hφ e⟩

end LargeIndecomposable.RayCat
