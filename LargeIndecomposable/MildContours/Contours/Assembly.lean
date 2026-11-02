module

public import LargeIndecomposable.MildContours.Contours.Lemma22
public import LargeIndecomposable.RayCategories.Opposite.Op

/-!
# Mild contours: reduction to the case `ρ = ω' ≫ α`

[mild] Lemma 2.1 and duality reduce "no non-deep contour" to the core case
where `ρ = π(y)` factors through the last arrow `α` of `v`
(`CoreHyp`). If Lemma 2.1 gives the alternative (2) instead, the contour is
also non-deep at `x`, and its reversal in `Pᵒᵖ` is a mild contour; Lemma 2.1
for the reversal gives (1) for it, or the alternative (2') which, combined with
(2), forces `σ = π(x)` to factor through the first arrow of `v` or `w`, which
is (1) for the reversal again (`MildContour.no_mildContour`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

lemma op_rpow {C : Type*} [Category C] {x : C} (e : x ⟶ x) : ∀ n, (rpow e n).op = rpow e.op n
  | 0 => rfl
  | n + 1 => by rw [rpow_succ, op_comp, op_rpow e n, ← rpow_succ']

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

lemma revPath_cons_first {x c y : RayVert P} (a : x ⟶ c) (v₁ : Quiver.Path c y) :
    revPath ((Quiver.Path.nil.cons a).comp v₁) = (revPath v₁).cons (revArr a) := by
  rw [revPath_comp]; rfl

variable [Fintype P] [DecidableEq P] [IsFiniteRayCategory P]

/-- **The reversed contour.** For paths `v = a₁ v₁`, `w = b₁ w₁` from `x` to
`y` with the same nonzero value, not interlaced, and `σ = π(x)` with
`σ ≫ v̄ ≠ 0`, the reversals form a mild contour of `Pᵒᵖ`. -/
def revContour {x y c d : RayVert P} (a : x ⟶ c)
    (v₁ : Quiver.Path c y) (b : x ⟶ d)
    (w₁ : Quiver.Path d y)
    (hval : pathVal ((Quiver.Path.nil.cons a).comp v₁) = pathVal ((Quiver.Path.nil.cons b).comp w₁))
    (h0 : pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
    (hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁))
    (σ : x.out ⟶ x.out) (hσ : ∀ e : x.out ⟶ x.out, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow σ n)
    (hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0) :
    letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
    MildContour (op y.out) (op x.out) :=
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  { sv := op c.out
    sw := op d.out
    v' := revPath v₁
    α := revArr a
    w' := revPath w₁
    β := revArr b
    hval := by
      rw [← revPath_cons_first a v₁, ← revPath_cons_first b w₁, pathVal_revPath, pathVal_revPath,
        hval]
    h0 := by
      rw [← revPath_cons_first a v₁, pathVal_revPath]
      exact fun h ↦ h0 (Quiver.Hom.op_inj (by rw [h, op_zero]))
    hni := fun h ↦ hni (by
      rw [← revPath_cons_first a v₁, ← revPath_cons_first b w₁] at h
      have := interlaced_unrevPath h
      rwa [unrevPath_revPath, unrevPath_revPath] at this)
    ρ := σ.op
    hρ := fun f hf ↦ by
      obtain ⟨n, hn, he⟩ := hσ f.unop (fun h ↦ hf (by
        have : IsIso f.unop.op := inferInstance
        exact this))
      exact ⟨n, hn, by rw [← op_rpow, ← he]; rfl⟩
    hωρ := by
      rw [← revPath_cons_first a v₁, pathVal_revPath]
      intro h
      apply hσω
      apply Quiver.Hom.op_inj
      rw [op_comp, h, op_zero] }

section Dual

variable {x y c d : RayVert P} (a : x ⟶ c) (v₁ : Quiver.Path c y) (b : x ⟶ d)
  (w₁ : Quiver.Path d y)
  (hval : pathVal ((Quiver.Path.nil.cons a).comp v₁) = pathVal ((Quiver.Path.nil.cons b).comp w₁))
  (h0 : pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
  (hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁))
  (σ : x.out ⟶ x.out) (hσ : ∀ e : x.out ⟶ x.out, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow σ n)
  (hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)

lemma revContour_ω :
    letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
    (revContour a v₁ b w₁ hval h0 hni σ hσ hσω).ω =
      (pathVal ((Quiver.Path.nil.cons a).comp v₁)).op := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  change pathVal ((revPath v₁).cons (revArr a)) = _
  rw [← revPath_cons_first a v₁, pathVal_revPath]

variable {k : Type*} [Field k] [Infinite k]

end Dual

namespace MildContour

variable {k : Type*} [Field k] [Infinite k]

/-- Paths of a contour are nonempty. -/
lemma length_pos_of_contour {x y : RayVert P} {v w : Quiver.Path x y}
    (hval : pathVal v = pathVal w) (hni : ¬Interlaced v w) : 0 < v.length := by
  cases v with
  | nil =>
      cases w with
      | nil => exact absurd (Relation.EqvGen.refl _) hni
      | cons w' β =>
          exact absurd (by rw [← hval]; exact isIso_pathVal_nil) (not_isIso_pathVal _ (by simp))
  | cons _ _ => simp

end MildContour

end RayCat

end LargeIndecomposable
