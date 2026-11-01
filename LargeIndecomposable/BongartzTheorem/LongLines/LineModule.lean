module

public import LargeIndecomposable.BongartzTheorem.LongLines.LinePaths
public import LargeIndecomposable.Coverings.Pieces.PdModule

/-!
# The module of a line

The constant thin representation of the piece `D_{S_L}` of a line `L` (`k` at each point,
identities on the arrows) respects the cover (`respectsCover_lineRep`): paths inside the line have
nonzero value, and parallel paths inside the line are equal. A contour of `P` (two different
paths with the same nonzero value) acts by zero on its push-down (`pdAct_contour_eq_zero`):
lifts of both paths would be two different paths inside the line with the same ends.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover FinQuiver RayQuiver Classical

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

/-- Cover paths of the paths of a piece, inside the piece. -/
lemma cover_of_piece_path' {S : Finset (Cover x₀)} : ∀ (le : List (pieceQuiver S).A)
    {i j : (pieceQuiver S).V} (h : PathFrom i le j),
    ∃ p : Quiver.Path (RayVert.mk (pt S i)) (RayVert.mk (pt S j)),
      PathIn (S : Set (Cover x₀)) p ∧ pathVal p = compD S le i j h
  | [], i, j, h => by
    change i = j at h
    subst h
    exact ⟨Quiver.Path.nil, i.2, rfl⟩
  | e :: le, i, j, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    subst h1
    obtain ⟨p, hpS, hp⟩ := cover_of_piece_path' le h2
    let a : RayVert.mk (pt S e.1) ⟶ RayVert.mk (pt S e.2.1) := ⟨e.2.2.1, e.2.2.2⟩
    refine ⟨(Quiver.Path.nil.cons a).comp p, ?_, ?_⟩
    · exact (pathIn_comp_iff _ _).2 ⟨⟨e.1.2, e.2.1.2⟩, hpS⟩
    · erw [pathVal_comp, hp]
      change (𝟙 _ ≫ e.2.2.1) ≫ compD S le _ j h2 = eqToHom rfl ≫ e.2.2.1 ≫ compD S le _ j h2
      simp

namespace CLine

variable (L : CLine x₀) (k : Type u) [Field k]

/-- **The line representation**: `k` at each point of the line, identities on the arrows. -/
def lineRep : Rep k (pieceQuiver L.finset) where
  obj _ := ModuleCat.of k k
  map _ := 𝟙 _

instance (i : (pieceQuiver L.finset).V) : FiniteDimensional k ((L.lineRep k).obj i) :=
  inferInstanceAs (FiniteDimensional k k)

/-- Paths inside the line have nonzero composite. -/
lemma compD_ne_zero (le : List (pieceQuiver L.finset).A) {i j : (pieceQuiver L.finset).V}
    (h : PathFrom i le j) : compD L.finset le i j h ≠ 0 := by
  obtain ⟨p, hpS, hp⟩ := cover_of_piece_path' le h
  rw [← hp]
  rw [L.coe_finset] at hpS
  exact L.nz p hpS

/-- **The line representation respects the cover.** -/
theorem respectsCover_lineRep : RespectsCover (L.lineRep k) := by
  refine ⟨fun le i j h h0 ↦ absurd h0 (L.compD_ne_zero le h), fun le le' i j h h' _ ↦ ?_⟩
  rw [L.path_unique le le' i j h h']

lemma pdAct_contour_aux {l l' : List (quiver P).A} {x y : P}
    {h : PathFrom (D := quiver P) x l y} {h' : PathFrom (D := quiver P) x l' y}
    (he : pathMor l x y h = pathMor l' x y h') (hν : pathMor l x y h ≠ 0) (hll' : l ≠ l')
    (hl : l ≠ []) :
    (L.lineRep k).pdAct (pieceProj L.finset) (word k (quiver P) l) = 0 := by
  refine Rep.pdAct_word_eq_zero _ _ fun le i j hle hmap ↦ hll' ?_
  obtain ⟨le', hmap', hle', -⟩ := exists_partner L.convex_finset (L.respectsCover_lineRep k) he hν hl
    hmap hle
  rw [← hmap, ← hmap', L.path_unique le le' i j hle hle']

/-- **Contours act by zero on the line module.** -/
theorem pdAct_contour_eq_zero {l l' : List (quiver P).A} {x y : P}
    {h : PathFrom (D := quiver P) x l y} {h' : PathFrom (D := quiver P) x l' y}
    (he : pathMor l x y h = pathMor l' x y h') (hν : pathMor l x y h ≠ 0) (hll' : l ≠ l') :
    (L.lineRep k).pdAct (pieceProj L.finset) (word k (quiver P) l) = 0 := by
  by_cases hl : l = []
  · have hl' : l' ≠ [] := by rintro rfl; exact hll' (hl.trans rfl)
    rw [pdAct_linRel L.convex_finset (L.respectsCover_lineRep k) (LinRel.eq l l' x y h h' he)]
    exact L.pdAct_contour_aux k he.symm (he ▸ hν) (Ne.symm hll') hl'
  · exact L.pdAct_contour_aux k he hν hll' hl

end CLine

end LargeIndecomposable.RayCat
