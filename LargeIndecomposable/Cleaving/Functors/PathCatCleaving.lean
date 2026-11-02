module

public import LargeIndecomposable.Cleaving.PathCategories.PathCatRep
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# A local criterion for cleaving functors out of path categories

If `P` has cancellation, a functor `F : PathCat Q ⥤ P` is cleaving as soon as
it is nonzero and injective on paths and satisfies Gabriel–Roiter's condition
b) of 13.8 for the arrows: if `F p` factors through `F e` on the side of an
arrow `e`, then `p` starts (resp. ends) with `e`
(`RayCat.PathCat.isCleaving_of_arrows`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

namespace RayCat

namespace PathCat

variable {Q : Type} [Quiver.{0} Q] {P : Type} [Category.{0} P] [HasZeroMorphisms P]
  (F : PathCat Q ⥤ P) [F.PreservesZeroMorphisms]

/-- The hypotheses of the local criterion. -/
structure ArrowCleaving : Prop where
  ne_zero : ∀ {a b : Q} (p : Quiver.Path a b), F.map (ofPath p) ≠ 0
  injective : ∀ {a b : Q} (p q : Quiver.Path a b), F.map (ofPath p) = F.map (ofPath q) → p = q
  left : ∀ {a c b : Q} (e : a ⟶ c) (p : Quiver.Path a b),
    (∃ g, F.map (ofPath e.toPath) ≫ g = F.map (ofPath p)) → ∃ q : Quiver.Path c b, p = e.toPath.comp q
  right : ∀ {a c b : Q} (e : c ⟶ b) (p : Quiver.Path a b),
    (∃ g, g ≫ F.map (ofPath e.toPath) = F.map (ofPath p)) → ∃ q : Quiver.Path a c, p = q.cons e

variable {F}

lemma map_ofPath_comp {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    F.map (ofPath (p.comp q)) = F.map (ofPath p) ≫ F.map (ofPath q) := by
  rw [← F.map_comp, ofPath_comp]

lemma map_ofPath_nil (a : Q) : F.map (ofPath (Quiver.Path.nil : Quiver.Path a a)) = 𝟙 _ :=
  F.map_id _

lemma ArrowCleaving.image_aux (hF : ArrowCleaving F) (hL : LeftCancel P) (hR : RightCancel P) :
    ∀ (n : ℕ) {a a' b b' : Q} (p : Quiver.Path a' a) (q : Quiver.Path b b')
      (r : Quiver.Path a' b') (ρ : F.obj ⟨a⟩ ⟶ F.obj ⟨b⟩), p.length + q.length = n →
      F.map (ofPath p) ≫ ρ ≫ F.map (ofPath q) = F.map (ofPath r) →
      ∃ l : (⟨a⟩ : PathCat Q) ⟶ ⟨b⟩, ρ = F.map l := by
  intro n
  induction n with
  | zero =>
    intro a a' b b' p q r ρ hn h
    cases p with
    | cons p e => simp at hn
    | nil =>
      cases q with
      | cons q e => simp at hn
      | nil =>
        rw [map_ofPath_nil, map_ofPath_nil, Category.id_comp, Category.comp_id] at h
        exact ⟨ofPath r, h⟩
  | succ n ih =>
    intro a a' b b' p q r ρ hn h
    cases q with
    | cons q e =>
      obtain ⟨r', rfl⟩ := hF.right e r ⟨F.map (ofPath p) ≫ ρ ≫ F.map (ofPath q), by
        rw [← h, show (q.cons e) = q.comp e.toPath by simp, map_ofPath_comp]; simp⟩
      have h' : (F.map (ofPath p) ≫ ρ ≫ F.map (ofPath q)) ≫ F.map (ofPath e.toPath) =
          F.map (ofPath r') ≫ F.map (ofPath e.toPath) := by
        rw [← map_ofPath_comp, show r'.comp e.toPath = r'.cons e by simp, ← h,
          show (q.cons e) = q.comp e.toPath by simp, map_ofPath_comp]
        simp
      have := hR _ _ _ h' (by rw [h']; rw [← map_ofPath_comp]; exact hF.ne_zero _)
      exact ih p q r' ρ (by simp at hn; omega) this
    | nil =>
      have hp : p.length = n + 1 := by simp at hn; omega
      obtain ⟨c, e, p', hp', rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ p hp
      rw [map_ofPath_comp] at h
      obtain ⟨r', rfl⟩ := hF.left e r ⟨_, (Category.assoc _ _ _).symm.trans h⟩
      rw [map_ofPath_comp, Category.assoc] at h
      have := hL _ _ _ h (by rw [h, ← map_ofPath_comp]; exact hF.ne_zero _)
      exact ih p' Quiver.Path.nil r' ρ (by simp; omega) this

variable [Fintype Q] [DecidableEq Q] [∀ a b : Q, Finite (a ⟶ b)] [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic Q)]
  [IsRayCategory P] [Fintype P] [DecidableEq P]

/-- **The local criterion for cleaving functors.** -/
theorem isCleaving_of_arrows (hF : ArrowCleaving F) (hL : LeftCancel P) (hR : RightCancel P) :
    IsCleaving F where
  map_eq_zero_iff {X Y} f := by
    rcases f with _ | p
    · exact ⟨fun _ ↦ rfl, fun _ ↦ F.map_zero _ _⟩
    · exact ⟨fun h ↦ absurd h (hF.ne_zero p), fun h ↦ by cases h⟩
  map_injective {X Y} f g h := by
    rcases f with _ | p <;> rcases g with _ | q
    · rfl
    · exact absurd ((F.map_zero _ _).symm.trans h).symm (hF.ne_zero q)
    · exact absurd (h.trans (F.map_zero _ _)) (hF.ne_zero p)
    · exact congrArg some (hF.injective p q h)
  image_closed {X X' Y Y'} μ ρ ν κ h hκ := by
    rcases κ with _ | r
    · exact absurd rfl hκ
    rcases μ with _ | p
    · have h0 : F.map (none : Option (Quiver.Path X'.as X.as)) = 0 := F.map_zero X' X
      rw [h0, zero_comp] at h
      exact absurd h.symm (hF.ne_zero r)
    rcases ν with _ | q
    · have h0 : F.map (none : Option (Quiver.Path Y.as Y'.as)) = 0 := F.map_zero Y Y'
      rw [h0, comp_zero, comp_zero] at h
      exact absurd h.symm (hF.ne_zero r)
    exact hF.image_aux hL hR _ p q r ρ rfl h

end PathCat

end RayCat

end LargeIndecomposable
