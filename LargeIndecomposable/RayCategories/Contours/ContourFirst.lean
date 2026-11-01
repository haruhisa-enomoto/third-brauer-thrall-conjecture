module

public import LargeIndecomposable.Crowns.Basic.PosetCrown
public import LargeIndecomposable.RayCategories.Contours.Interlaced

/-!
# First arrows of contours (BO13a, Lemma 4 b))

In a ray category with left cancellation, the two paths of a contour start
with incomparable irreducible morphisms (`RayCat.not_bLe_first_of_contour`):
otherwise the first arrows agree and the paths are interlaced. Hence a
neighbour `ρ` of `σ = val v = val w` in a crown cannot factor through both
paths (`RayQuiver.MulBasis.not_factors_both`, BO13a Lemma 4 b)).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- The morphism out of `x` of an arrow of the quiver. -/
def arrB {x y : RayVert P} (α : x ⟶ y) : BMor x.out := ⟨y.out, α.1⟩

/-- **The first arrows of a contour are incomparable.** -/
lemma not_bLe_first_of_contour (hL : LeftCancel P) {x a b y : RayVert P} (α : x ⟶ a) (β : x ⟶ b)
    (v' : Quiver.Path a y) (w' : Quiver.Path b y)
    (hval : pathVal (α.toPath.comp v') = pathVal (β.toPath.comp w'))
    (h0 : pathVal (α.toPath.comp v') ≠ 0)
    (hni : ¬Interlaced (α.toPath.comp v') (β.toPath.comp w')) : ¬BLe (arrB α) (arrB β) := by
  rintro ⟨χ, hχ⟩
  have hiso : IsIso χ := by
    rcases β.2.2.2 _ α.1 χ hχ.symm with h | h
    · exact absurd h α.2.2.1
    · exact h
  obtain ⟨hab, rfl⟩ := RayQuiver.eq_id_of_isIso χ
  change a.out = b.out at hab
  have hab' : a = b := hab
  subst hab'
  have hαβ : α = β := Subtype.ext (by
    change α.1 ≫ eqToHom hab = β.1 at hχ
    simpa using hχ)
  subst hαβ
  apply hni
  refine Relation.EqvGen.rel _ _ (interStep_prefix _ (by simp) v' w' ?_ ?_)
  · rw [pathVal_comp, pathVal_comp] at hval
    exact hL _ _ _ (by simpa [pathVal] using hval) (by
      rw [pathVal_comp] at h0; simpa [pathVal] using h0)
  · intro h
    apply h0
    rw [pathVal_comp, h, comp_zero]

end RayCat

namespace RayQuiver

namespace MulBasis

open RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [LargeIndecomposable.IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a, Lemma 4 b)**: a morphism `ρ` incomparable with `σ = val v = val w`
from a contour `(v, w)` does not factor through the first arrows of both
paths. -/
theorem not_factors_both
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x a b y : RayVert P} (α : x ⟶ a) (β : x ⟶ b)
    (v' : Quiver.Path a y) (w' : Quiver.Path b y)
    (hval : pathVal (α.toPath.comp v') = pathVal (β.toPath.comp w'))
    (h0 : pathVal (α.toPath.comp v') ≠ 0)
    (hni : ¬Interlaced (α.toPath.comp v') (β.toPath.comp w')) (ρ : BMor x.out) (hρ : ρ.2 ≠ 0)
    (hσρ : ¬BLe ⟨y.out, pathVal (α.toPath.comp v')⟩ ρ)
    (hρσ : ¬BLe ρ ⟨y.out, pathVal (α.toPath.comp v')⟩)
    (hα : BLe (arrB α) ρ) (hβ : BLe (arrB β) ρ) : False := by
  have hσα : BLe (arrB α) ⟨y.out, pathVal (α.toPath.comp v')⟩ :=
    ⟨pathVal v', by
      rw [pathVal_comp]
      change α.1 ≫ pathVal v' = (𝟙 _ ≫ α.1) ≫ pathVal v'
      rw [Category.id_comp]⟩
  have hσβ : BLe (arrB β) ⟨y.out, pathVal (α.toPath.comp v')⟩ :=
    ⟨pathVal w', by
      rw [hval, pathVal_comp]
      change β.1 ≫ pathVal w' = (𝟙 _ ≫ β.1) ≫ pathVal w'
      rw [Category.id_comp]⟩
  exact B.not_four_le hmin hR (arrB α) (arrB β) _ ρ h0 hρ hσα hσβ hα hβ
    (not_bLe_first_of_contour hL α β v' w' hval h0 hni)
    (not_bLe_first_of_contour hL β α w' v' hval.symm (hval ▸ h0)
      fun h ↦ hni (Relation.EqvGen.symm _ _ h)) hσρ hρσ

end MulBasis

end RayQuiver

end LargeIndecomposable
