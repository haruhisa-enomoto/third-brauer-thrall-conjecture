module

public import LargeIndecomposable.Coverings.UniversalCover.PieceKills

/-!
# Arrow-closed parts of convex sets are convex

If `C` is convex and `T ⊆ C` contains, with any point, all points of `C` joined to it by an
irreducible morphism in either direction, then `T` is convex (`convex_of_closed`). This is the
first step in showing that a critical piece is connected.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

lemma reach_trans' {a b c : Cover x₀} (h : Reach a b) (h' : Reach b c) : Reach a c := by
  induction h with
  | refl => exact h'
  | step f hf _ ih => exact Reach.step f hf (ih h')

/-- **Arrow-closed parts of convex sets are convex.** -/
theorem convex_of_closed {C T : Set (Cover x₀)} (hC : Convex C) (hTC : T ⊆ C)
    (hcl : ∀ a b (f : a ⟶ b), IsIrreducible f → a ∈ C → b ∈ C → (a ∈ T ↔ b ∈ T)) :
    Convex T := by
  intro a b c ha hc hab hbc
  induction hab with
  | refl => exact ha
  | step f hf hrest ih =>
    rename_i a' a'' b'
    have ha''C : a'' ∈ C :=
      hC a' a'' c (hTC ha) (hTC hc) (Reach.step f hf (Reach.refl _)) (reach_trans' hrest hbc)
    exact ih ((hcl _ _ f hf (hTC ha) ha''C).1 ha) hbc

end LargeIndecomposable.RayCat
