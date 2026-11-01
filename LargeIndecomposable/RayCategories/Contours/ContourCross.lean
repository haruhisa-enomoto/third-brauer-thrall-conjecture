module

public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# Crossing factorizations in a contour

For a contour `(v₁ v₂, w₁ w₂)` with `v₁` and `w₂` nonempty, the tail `v₂` does
not factor as `g ≫ w₂` and the head `w₁` does not factor as `v₁ ≫ g`
(`RayCat.contour_cross`): either factorization would interlace the two paths.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- **Crossing factorizations interlace a contour.** -/
lemma contour_cross (hL : LeftCancel P) (hR : RightCancel P) {x a b y : RayVert P}
    (v₁ : Quiver.Path x a) (v₂ : Quiver.Path a y) (w₁ : Quiver.Path x b) (w₂ : Quiver.Path b y)
    (hval : pathVal (v₁.comp v₂) = pathVal (w₁.comp w₂)) (h0 : pathVal (v₁.comp v₂) ≠ 0)
    (hni : ¬Interlaced (v₁.comp v₂) (w₁.comp w₂)) (hv₁ : 0 < v₁.length) (hw₂ : 0 < w₂.length) :
    (¬∃ g : a.out ⟶ b.out, g ≫ pathVal w₂ = pathVal v₂) ∧
      (¬∃ g : a.out ⟶ b.out, pathVal v₁ ≫ g = pathVal w₁) := by
  rw [pathVal_comp] at hval h0
  rw [pathVal_comp] at hval
  -- a factorization `g` with `v₁ ≫ g = w₁` and `g ≫ w₂ = v₂` interlaces
  have key : ∀ g : a.out ⟶ b.out, pathVal v₁ ≫ g = pathVal w₁ → g ≫ pathVal w₂ = pathVal v₂ →
      False := by
    intro g h1 h2
    have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [← h2, h, zero_comp, comp_zero])
    let p := pathOf g hg0
    have hp : pathVal p = g := pathVal_pathOf g hg0
    apply hni
    have s1 : InterStep (v₁.comp v₂) (v₁.comp (p.comp w₂)) :=
      interStep_prefix v₁ hv₁ v₂ (p.comp w₂) (by rw [pathVal_comp, hp, h2])
        (fun h ↦ h0 (by rw [h, comp_zero]))
    have s2 : InterStep ((v₁.comp p).comp w₂) (w₁.comp w₂) :=
      interStep_suffix (v₁.comp p) w₁ w₂ hw₂ (by rw [pathVal_comp, hp, h1])
        (fun h ↦ h0 (by rw [← h2, ← Category.assoc, ← hp, ← pathVal_comp, h, zero_comp]))
    rw [Quiver.Path.comp_assoc] at s2
    exact (Relation.EqvGen.rel _ _ s1).trans _ _ _ (Relation.EqvGen.rel _ _ s2)
  constructor
  · rintro ⟨g, hg⟩
    refine key g (hR _ _ (pathVal w₂) ?_ ?_) hg
    · rw [Category.assoc, hg, hval]
    · rw [Category.assoc, hg]; exact h0
  · rintro ⟨g, hg⟩
    refine key g hg (hL (pathVal v₁) _ _ ?_ ?_)
    · rw [← Category.assoc, hg, hval]
    · rw [← Category.assoc, hg, ← hval]; exact h0

end RayCat

end LargeIndecomposable
