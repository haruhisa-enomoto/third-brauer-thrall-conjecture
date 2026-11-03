module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineBandRel

/-!
# Lines carried by a module

A *module line* in a finite set `S` of points of the cover is a line without extra arrows
(`OLine`) inside `S`, with a representation `X` of the piece of `S` that respects the cover,
whose arrows act by nonzero maps only between points of the line, and whose paths along the
line act by nonzero maps (`MLine`). It need not be convex. If `S` is convex, its good pairs are
rigid (`MLine.rigid`): a path with the value of a segment of the line has a partner in `S` with
the same action on `X` (`exists_partner`), so it runs along the line, and paths along the line
with the same ends are equal (`OLine.path_unique`). So a module line with `3 dim k(P)` arrows
gives a band (`exists_lineBandRel`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover FinQuiver RayQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

variable (x₀) in
/-- **A module line** in `S`: a line without extra arrows inside `S`, carried by a
representation `X` of the piece of `S`. -/
structure MLine (S : Finset (Cover x₀)) (k : Type u) [Field k] extends OLine x₀ where
  sub : ∀ a ≤ n, pt a ∈ S
  /-- The representation. -/
  X : Rep k (pieceQuiver S)
  resp : RespectsCover X
  onlyNZ : ∀ e : (pieceQuiver S).A, X.arrOp e ≠ 0 →
    (∃ a ≤ n, pt a = ((pieceQuiver S).src e).1) ∧ ∃ b ≤ n, pt b = ((pieceQuiver S).tgt e).1
  pathNZ : ∀ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V), PathFrom i le j →
    (∀ e ∈ le, (∃ a ≤ n, pt a = ((pieceQuiver S).src e).1) ∧
      ∃ b ≤ n, pt b = ((pieceQuiver S).tgt e).1) → X.pathTot le ≠ 0

omit [Fintype P] [DecidableEq P] in
lemma pathIn_mono {H H' : Set (Cover x₀)} (hH : H ⊆ H') {X : RayVert (Cover x₀)} :
    ∀ {Y : RayVert (Cover x₀)} (q : Quiver.Path X Y), PathIn H q → PathIn H' q
  | _, .nil, h => hH h
  | _, .cons q _, h => ⟨pathIn_mono hH q h.1, hH h.2⟩

/-- A path of the cover inside `H ⊆ S` is a path of the piece of `S` whose arrows join points
of `H`. -/
lemma piecePath_of_pathIn' (S : Finset (Cover x₀)) (H : Set (Cover x₀)) (hHS : H ⊆ S)
    {X : RayVert (Cover x₀)} (hX : X.out ∈ S) :
    ∀ {Y : RayVert (Cover x₀)} (q : Quiver.Path X Y), PathIn H q → (hY : Y.out ∈ S) →
      ∃ le : List (pieceQuiver S).A,
        PathFrom (D := pieceQuiver S) (⟨X.out, hX⟩ : S) le ⟨Y.out, hY⟩ ∧
          le.map (pieceProj S).arr = labs q ∧
          ∀ e ∈ le, ((pieceQuiver S).src e).1 ∈ H ∧ ((pieceQuiver S).tgt e).1 ∈ H
  | _, .nil, _, _ => ⟨[], rfl, rfl, fun e he ↦ absurd he (List.not_mem_nil)⟩
  | _, .cons q e, hq, hY => by
    obtain ⟨le, hle, hmap, hin⟩ := piecePath_of_pathIn' S H hHS hX q hq.1
      (hHS (pathIn_tgt _ q hq.1))
    let α : (pieceQuiver S).A := ⟨⟨_, hHS (pathIn_tgt _ q hq.1)⟩, ⟨_, hY⟩, e.1, e.2⟩
    refine ⟨le ++ [α], pathFrom_append_gen le [α] hle ⟨rfl, rfl⟩, ?_, fun e' he' ↦ ?_⟩
    · rw [List.map_append, hmap]
      rfl
    · rcases List.mem_append.1 he' with h | h
      · exact hin e' h
      · rw [List.mem_singleton.1 h]
        exact ⟨pathIn_tgt _ q hq.1, hq.2⟩

lemma arrOp_ne_zero_of_pathTot {k : Type u} [Field k] {D : FinQuiver} (X : Rep k D) :
    ∀ (le : List D.A), X.pathTot le ≠ 0 → ∀ e ∈ le, X.arrOp e ≠ 0
  | [], _, e, he => absurd he List.not_mem_nil
  | c :: le, h, e, he => by
    have h' : X.pathTot le ∘ₗ X.arrOp c ≠ 0 := h
    rcases List.mem_cons.1 he with rfl | he
    · intro h0; rw [h0, LinearMap.comp_zero] at h'; exact h' rfl
    · refine arrOp_ne_zero_of_pathTot X le (fun h0 ↦ ?_) e he
      rw [h0, LinearMap.zero_comp] at h'; exact h' rfl

namespace MLine

variable {S : Finset (Cover x₀)} {k : Type u} [Field k] (L : MLine x₀ S k)

/-- The transport of an arrow of the piece of `S` with ends on the line to the piece of the
line. -/
def trArr (e : (pieceQuiver S).A) (he : (∃ a ≤ L.n, L.pt a = ((pieceQuiver S).src e).1) ∧
    ∃ b ≤ L.n, L.pt b = ((pieceQuiver S).tgt e).1) : (pieceQuiver L.finset).A :=
  ⟨⟨((pieceQuiver S).src e).1, L.mem_finset.2 he.1⟩,
    ⟨((pieceQuiver S).tgt e).1, L.mem_finset.2 he.2⟩, e.2.2⟩

/-- Transport of a path with all arrows on the line. -/
lemma tr_path : ∀ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V)
    (h : PathFrom i le j) (hle : ∀ e ∈ le, (∃ a ≤ L.n, L.pt a = ((pieceQuiver S).src e).1) ∧
      ∃ b ≤ L.n, L.pt b = ((pieceQuiver S).tgt e).1) (hi : ∃ a ≤ L.n, L.pt a = i.1)
    (hj : ∃ b ≤ L.n, L.pt b = j.1),
    ∃ le' : List (pieceQuiver L.finset).A,
      PathFrom (D := pieceQuiver L.finset) ⟨i.1, L.mem_finset.2 hi⟩ le' ⟨j.1, L.mem_finset.2 hj⟩ ∧
        le'.map (pieceProj L.finset).arr = le.map (pieceProj S).arr
  | [], i, j, h, _, hi, hj => by
    change i = j at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | e :: le, i, j, h, hle, hi, hj => by
    obtain ⟨h1, h2⟩ := h
    have he := hle e (List.mem_cons_self ..)
    obtain ⟨le', hp', hm'⟩ := tr_path le _ j h2 (fun e' he' ↦ hle e' (List.mem_cons_of_mem _ he'))
      he.2 hj
    refine ⟨L.trArr e he :: le', ⟨?_, hp'⟩, ?_⟩
    · change (⟨((pieceQuiver S).src e).1, _⟩ : L.finset) = _
      exact Subtype.ext (by simp only []; exact congrArg (fun z : S ↦ z.1) h1)
    · simp only [List.map_cons, hm']
      rfl

/-- **Good pairs of a module line in a convex set are rigid.** -/
theorem rigid (hS : Convex (S : Set (Cover x₀))) {t t' : ℕ}
    (hg : L.GoodPair t t') : WLine.Rigid hg := by
  intro l l' x y h h' he hl
  obtain ⟨le, i, j, hp, hmap⟩ := hl
  have hν : pathMor l x y h ≠ 0 := by
    intro h0
    exact WLine.cyc_band hg le i j hp (hmap ▸ ⟨x, y, h, h0⟩)
  by_cases hl0 : l = []
  · subst hl0
    change x = y at h
    subst h
    by_contra hll'
    obtain ⟨c, l'', rfl⟩ := List.exists_cons_of_ne_nil (Ne.symm hll')
    refine pathMor_ne_id c l'' x h' ?_
    rw [← he]
    simp [pathMor]
  have hN := WLine.t'_eq hg
  have hn := hg.2.1.1
  have hvi : WLine.vidx t i ≤ L.n := by
    rcases i with _ | j₀
    · change t + 1 ≤ L.n; omega
    · change t + 2 + (j₀ : ℕ) ≤ L.n; have := j₀.2; omega
  obtain ⟨b, q, hq, hlq⟩ := WLine.cover_path hg le i j hp (WLine.vidx t i) hvi
    (by rintro j₀ rfl; rfl)
  have hHS : L.pts ⊆ (S : Set (Cover x₀)) := by
    rintro c ⟨a, ha, rfl⟩; exact L.sub a ha
  obtain ⟨lp, hlp, hlpm, hlin⟩ := piecePath_of_pathIn' S L.pts hHS (L.sub _ hvi) q hq
    (hHS (pathIn_tgt _ q hq))
  have hlpm' : lp.map (pieceProj S).arr = l := hlpm.trans (hlq.trans hmap)
  obtain ⟨lp', hlpm2, hlp', htot⟩ := exists_partner hS L.resp he hν hl0 hlpm' hlp
  have hline : ∀ e ∈ lp, (∃ a ≤ L.n, L.pt a = ((pieceQuiver S).src e).1) ∧
      ∃ b ≤ L.n, L.pt b = ((pieceQuiver S).tgt e).1 := fun e he ↦
    ⟨(hlin e he).1, (hlin e he).2⟩
  have hnz : L.X.pathTot lp ≠ 0 := L.pathNZ lp _ _ hlp hline
  have hline' : ∀ e ∈ lp', (∃ a ≤ L.n, L.pt a = ((pieceQuiver S).src e).1) ∧
      ∃ b ≤ L.n, L.pt b = ((pieceQuiver S).tgt e).1 := fun e he ↦
    L.onlyNZ e (arrOp_ne_zero_of_pathTot L.X lp' (htot ▸ hnz) e he)
  have hi : ∃ a ≤ L.n, L.pt a = (⟨(RayVert.mk (L.pt (WLine.vidx t i))).out, L.sub _ hvi⟩ : S).1 :=
    ⟨_, hvi, rfl⟩
  have hj : ∃ a ≤ L.n, L.pt a = (⟨(RayVert.mk (L.pt b)).out,
      hHS (pathIn_tgt _ q hq)⟩ : S).1 := pathIn_tgt _ q hq
  obtain ⟨m, hm, hmm⟩ := tr_path L lp _ _ hlp hline hi hj
  obtain ⟨m', hm', hmm'⟩ := tr_path L lp' _ _ hlp' hline' hi hj
  rw [← hlpm', ← hlpm2, ← hmm, ← hmm', L.path_unique m m' _ _ hm hm']

end MLine

end LargeIndecomposable.RayCat
