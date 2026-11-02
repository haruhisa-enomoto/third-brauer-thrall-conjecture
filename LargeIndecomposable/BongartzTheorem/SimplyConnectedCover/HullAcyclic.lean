module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.GabrielPieces

/-!
# Interval-finiteness of the cover for an acyclic quiver

If the quiver of the ray category `P` has no oriented cycle, the number of objects reachable
from `x` by arrows strictly decreases along arrows. Hence an object of the universal cover
reaches only finitely many objects, and every finite set of objects of the cover lies in a
finite convex piece (`hullFinite_of_acyclic`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

lemma Cover.Reach.trans {a b c : Cover x₀} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  induction h1 with
  | refl => exact h2
  | step f hf _ ih => exact Reach.step f hf (ih h2)

end LargeIndecomposable.RayCat
