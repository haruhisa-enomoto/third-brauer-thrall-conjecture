module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceCritical
public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerInterval
public import LargeIndecomposable.DirectedAlgebras.Directing.CornerSurvive
public import LargeIndecomposable.BongartzTheorem.ContourExclusion.ContourPiece

/-!
# Arrows of a piece are full edges of the Euler form of its quotients

In a piece of the cover, parallel paths have equal composites (`ParEq`). An arrow is
irreducible, so no other path joins its ends: no third point lies on a path from its source to
its target (`no_mid`). For a set `T'` of points of the piece containing both ends, the corner of
the arrow survives in the quotient by the idempotents outside `T'` (`qmap_corner_ne'`), and the
interval of the arrow in the quotient has two points. Hence the arrow is a full edge of the Euler
form of the quotient (`eulerForm_c_arrow_quot`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)} {k : Type u} [Field k]

omit [Fintype P] [DecidableEq P] in
/-- **No third point on a path along an arrow.** -/
lemma no_mid (hpar : ParEq S) (α : (pieceQuiver S).A) {z : (pieceQuiver S).V}
    (hz1 : z ≠ (pieceQuiver S).src α) (hz2 : z ≠ (pieceQuiver S).tgt α)
    (h1 : PR ((pieceQuiver S).src α) z) (h2 : PR z ((pieceQuiver S).tgt α)) : False := by
  obtain ⟨l1, hl1⟩ := h1
  obtain ⟨l2, hl2⟩ := h2
  have he := hpar (l1 ++ l2) [α] _ _ (pathFrom_append l1 l2 hl1 hl2) ⟨rfl, rfl⟩
  rw [compD_append l1 l2 hl1 hl2, compD_single] at he
  rcases α.2.2.2.2.2 _ (compD S l1 _ _ hl1) (compD S l2 _ _ hl2) he.symm with h | h
  · exact hz1 (Subtype.ext (IsRayCategory.skeletal ⟨@asIso _ _ _ _ _ h⟩).symm)
  · exact hz2 (Subtype.ext (IsRayCategory.skeletal ⟨@asIso _ _ _ _ _ h⟩))

/-- Points on a path along an arrow are its ends. -/
lemma mid_eq_of_arrow (hpar : ParEq S) (hacyc : ∀ (i : (pieceQuiver S).V)
    (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i) (α : (pieceQuiver S).A)
    (v : (pieceQuiver S).V)
    (h1 : Relation.ReflTransGen (pieceDirData (k := k) hacyc).Arr ((pieceQuiver S).src α) v)
    (h2 : Relation.ReflTransGen (pieceDirData (k := k) hacyc).Arr v ((pieceQuiver S).tgt α)) :
    v = (pieceQuiver S).src α ∨ v = (pieceQuiver S).tgt α := by
  by_contra hv
  push Not at hv
  obtain ⟨l1, hl1⟩ := path_of_rtg h1
  obtain ⟨l2, hl2⟩ := path_of_rtg h2
  exact no_mid hpar α hv.1 hv.2 ⟨l1, hl1⟩ ⟨l2, hl2⟩

/-- The corner element of an arrow is nonzero. -/
lemma arrow_corner_ne (hpar : ParEq S) (α : (pieceQuiver S).A) :
    pev ((pieceQuiver S).tgt α) * pbvec ((pieceQuiver S).src α) ((pieceQuiver S).tgt α) *
      pev ((pieceQuiver S).src α) ≠ (0 : PieceAlg k S) := by
  have hgv : gval ((pieceQuiver S).src α) ((pieceQuiver S).tgt α) ≠ 0 := by
    rw [gval_eq hpar (l := [α]) ⟨rfl, rfl⟩, compD_single]
    exact α.2.2.2.1
  exact cv_ne_zero hpar hgv

end LargeIndecomposable.RayCat
