module

public import LargeIndecomposable.Coverings.Pieces.PieceSepDec
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma42
public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.CoverLocalSC

/-!
# Cover paths and piece paths

In a convex piece `S`, a path of the cover between points of `S` lifts to a path of the piece
with the same composite (`piece_of_cover_path`), and a piece path gives a cover path with the same
value (`cover_of_piece_path`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- **Cover paths inside a convex piece are piece paths.** -/
lemma piece_of_cover_path (hS : Convex (S : Set (Cover x₀))) (i : (pieceQuiver S).V) :
    ∀ {d : RayVert (Cover x₀)} (p : Quiver.Path (RayVert.mk (pt S i)) d) (hd : d.out ∈ S),
      ∃ (le : List (pieceQuiver S).A) (h : PathFrom i le ⟨d.out, hd⟩),
        compD S le i ⟨d.out, hd⟩ h = pathVal p
  | _, .nil, hd => ⟨[], rfl, rfl⟩
  | _, .cons (b := c) q e, hd => by
    have hc : c.out ∈ S := hS _ _ _ i.2 hd (reach_of_path q)
      (Reach.step e.1 e.2 (Reach.refl _))
    obtain ⟨le, hle, he⟩ := piece_of_cover_path hS i q hc
    let α : (pieceQuiver S).A := ⟨⟨c.out, hc⟩, ⟨_, hd⟩, e.1, e.2⟩
    refine ⟨le ++ [α], pathFrom_append le [α] hle ⟨rfl, rfl⟩, ?_⟩
    erw [compD_append le [α] hle ⟨rfl, rfl⟩, he, compD_single]
    rfl

/-- **Piece paths are cover paths.** -/
lemma cover_of_piece_path : ∀ (le : List (pieceQuiver S).A) {i j : (pieceQuiver S).V}
    (h : PathFrom i le j), ∃ p : Quiver.Path (RayVert.mk (pt S i)) (RayVert.mk (pt S j)),
      pathVal p = compD S le i j h
  | [], i, j, h => by
    change i = j at h
    subst h
    exact ⟨Quiver.Path.nil, rfl⟩
  | e :: le, i, j, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    subst h1
    obtain ⟨p, hp⟩ := cover_of_piece_path le h2
    let a : RayVert.mk (pt S e.1) ⟶ RayVert.mk (pt S e.2.1) := ⟨e.2.2.1, e.2.2.2⟩
    refine ⟨(Quiver.Path.nil.cons a).comp p, ?_⟩
    erw [pathVal_comp, hp]
    change (𝟙 _ ≫ e.2.2.1) ≫ compD S le _ j h2 = eqToHom rfl ≫ e.2.2.1 ≫ compD S le _ j h2
    simp

/-- **No closed paths in an acyclic cover.** -/
lemma cycleFree_of_acyclic (h : CoverAcyclic x₀) :
    ∀ (a : Cover x₀) (p : Quiver.Path (RayVert.mk a) (RayVert.mk a)), p.length = 0 := by
  intro a p
  by_contra hp
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 1 := ⟨p.length - 1, by omega⟩
  have key : ∀ {c : RayVert (Cover x₀)} (q : Quiver.Path (RayVert.mk a) c), 0 < q.length →
      ∃ (b : Cover x₀) (f : a ⟶ b), IsIrreducible f ∧ Reach b c.out := by
    intro c q hq
    induction q with
    | nil => exact absurd hq (by simp)
    | cons q e ih =>
      rename_i d
      by_cases hq0 : q.length = 0
      · obtain rfl := Quiver.Path.eq_of_length_zero q hq0
        exact ⟨_, e.1, e.2, Reach.refl _⟩
      · obtain ⟨b, f, hf, hr⟩ := ih (by omega)
        exact ⟨b, f, hf, hr.trans (Reach.step e.1 e.2 (Reach.refl _))⟩
  obtain ⟨b, f, hf, hr⟩ := key p (by omega)
  exact h a b f hf hr

/-- **Interval-finiteness from finite convex hulls.** -/
lemma intervalFinite_of_hull (h : HullFinite x₀) : ∀ a b : Cover x₀, (interval a b).Finite := by
  classical
  intro a b
  obtain ⟨T, hT, hTc⟩ := h {a, b}
  refine (T.finite_toSet).subset fun z ⟨⟨p⟩, ⟨q⟩⟩ ↦ ?_
  exact hTc a z b (hT (by simp)) (hT (by simp)) (reach_of_path p) (reach_of_path q)

/-- **Lemma 4.2 for pieces** from the cover. -/
lemma parEq_of_cover (hacyc : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
    (hsc : CoverLocalSC x₀) : ParEq S := by
  intro l l' i j h h'
  obtain ⟨p, hp⟩ := cover_of_piece_path l h
  obtain ⟨p', hp'⟩ := cover_of_piece_path l' h'
  rw [← hp, ← hp']
  exact pathVal_eq_of_parallel (cycleFree_of_acyclic hacyc) hint hsc _ _ _ rfl p p'

end LargeIndecomposable.RayCat
