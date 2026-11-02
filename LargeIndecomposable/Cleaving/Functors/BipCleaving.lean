module

public import LargeIndecomposable.Cleaving.Functors.PathCatCleaving

/-!
# Cleaving out of bipartite quivers

If a thin quiver has no path of length two (every vertex is a source or a
sink), the local criterion `PathCat.ArrowCleaving` reduces to the zigzag
conditions: arrow images are nonzero and not invertible, two arrows with a
common source do not factor through each other on the right, and two arrows
with a common target do not factor through each other on the left
(`RayCat.PathCat.arrowCleaving_of_bip`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

namespace RayCat

namespace PathCat

variable {Q : Type} [Quiver.{0} Q] [∀ a b : Q, Subsingleton (a ⟶ b)]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  (F : PathCat Q ⥤ P) [F.PreservesZeroMorphisms]

/-- No paths of length two. -/
def NoTwoPaths (Q : Type) [Quiver.{0} Q] : Prop :=
  ∀ {a b c : Q} (_ : a ⟶ b) (_ : b ⟶ c), False

variable {F}

/-- **The zigzag criterion for bipartite quivers.** -/
theorem arrowCleaving_of_bip (hb : NoTwoPaths Q) (hQ : LargeIndecomposable.Foundations.Quiver.IsAcyclic Q)
    (h0 : ∀ {a b : Q} (e : a ⟶ b), F.map (ofPath e.toPath) ≠ 0)
    (hiso : ∀ {a b : Q} (e : a ⟶ b), ¬IsIso (F.map (ofPath e.toPath)))
    (hl : ∀ {a b b' : Q} (e : a ⟶ b) (e' : a ⟶ b'), b ≠ b' →
      ¬∃ g, F.map (ofPath e.toPath) ≫ g = F.map (ofPath e'.toPath))
    (hr : ∀ {a a' b : Q} (e : a ⟶ b) (e' : a' ⟶ b), a ≠ a' →
      ¬∃ g, g ≫ F.map (ofPath e.toPath) = F.map (ofPath e'.toPath)) :
    ArrowCleaving F where
  ne_zero {a b} p := by
    cases p with
    | nil => rw [map_ofPath_nil]; exact IsRayCategory.id_ne_zero _
    | cons q e =>
      cases q with
      | nil => exact h0 e
      | cons q' e' => exact (hb e' e).elim
  injective {a b} p q _ := by
    cases p with
    | nil => exact (hQ.eq_nil q).symm
    | cons p e =>
      cases p with
      | cons p' e' => exact (hb e' e).elim
      | nil =>
        cases q with
        | nil => exact absurd (hQ.eq_nil (Quiver.Path.nil.cons e)) (fun h ↦ by cases h)
        | cons q f =>
          cases q with
          | cons q' f' => exact (hb f' f).elim
          | nil => rw [Subsingleton.elim e f]
  left {a c b} e p := by
    rintro ⟨g, hg⟩
    cases p with
    | nil =>
      rw [map_ofPath_nil] at hg
      exact (hiso e (isIso_of_isIso_comp _ g (h0 e) (by rw [hg]; infer_instance))).elim
    | cons q e' =>
      cases q with
      | cons q' e'' => exact (hb e'' e').elim
      | nil =>
        by_cases hcb : c = b
        · subst hcb
          exact ⟨Quiver.Path.nil, by rw [Subsingleton.elim e e']; rfl⟩
        · exact (hl e e' hcb ⟨g, hg⟩).elim
  right {a c b} e p := by
    rintro ⟨g, hg⟩
    cases p with
    | nil =>
      rw [map_ofPath_nil] at hg
      have hg0 : g ≠ 0 := fun h ↦ IsRayCategory.id_ne_zero _ (by rw [← hg, h, zero_comp])
      have hc : IsIso (g ≫ F.map (ofPath e.toPath)) := by rw [hg]; infer_instance
      have := isIso_of_isIso_comp g (F.map (ofPath e.toPath)) hg0 hc
      have : IsIso (F.map (ofPath e.toPath)) := IsIso.of_isIso_comp_left g _
      exact (hiso e this).elim
    | cons q e' =>
      cases q with
      | cons q' e'' => exact (hb e'' e').elim
      | nil =>
        by_cases hca : c = a
        · subst hca
          exact ⟨Quiver.Path.nil, by rw [Subsingleton.elim e e']⟩
        · exact (hr e e' hca ⟨g, hg⟩).elim

end PathCat

end RayCat

end LargeIndecomposable
