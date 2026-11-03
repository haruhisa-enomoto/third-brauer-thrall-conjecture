module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineBand
public import LargeIndecomposable.BongartzTheorem.LongLines.LineModule
public import LargeIndecomposable.BongartzTheorem.ContourExclusion.RelationPaths
public import LargeIndecomposable.RayCategories.Linearization.RegularRepresentation

/-!
# A band from one line of the cover, without excluding contours

Let `L` be a line of the cover with a good pair of sinks, and call a path of `Q_P` *along the
band* if it is the image of a directed path of the band cycle. A path along the band is a
directed segment of `L`. If another path has the same value, the partner of its lift in the
convex line `L` (`exists_partner`) is a path of `L` with the same ends, so it is the same path
(`CLine.path_unique`). Hence the paths that are not along the band form a set `RelPaths`
(`relPaths_notAlong`), and the kernel of `kQ_P → k(P)` lies in the span of their words. This
gives a monomial-type band (`lineBandRel`) whose cycle has `t' - t` points, with no condition
on contours of `P` (BO23, proof of Theorem 7).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover FinQuiver RayQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
lemma pathFrom_split_gen {D : FinQuiver} : ∀ (l l' : List D.A) {i j : D.V},
    PathFrom i (l ++ l') j → ∃ m, PathFrom i l m ∧ PathFrom m l' j
  | [], _, i, _, h => ⟨i, rfl, h⟩
  | c :: l, l', _, _, h => by
    obtain ⟨m, h1, h2⟩ := pathFrom_split_gen l l' h.2
    exact ⟨m, ⟨h.1, h1⟩, h2⟩

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
lemma pathFrom_append_gen {D : FinQuiver} : ∀ (l l' : List D.A) {i j m : D.V},
    PathFrom i l j → PathFrom j l' m → PathFrom i (l ++ l') m
  | [], l', i, j, m, h, h' => by change i = j at h; subst h; exact h'
  | c :: l, l', i, j, m, h, h' => ⟨h.1, pathFrom_append_gen l l' h.2 h'⟩

omit [Fintype P] [DecidableEq P] in
lemma pathIn_tgt (S : Set (Cover x₀)) {X : RayVert (Cover x₀)} :
    ∀ {Y : RayVert (Cover x₀)} (q : Quiver.Path X Y), PathIn S q → Y.out ∈ S
  | _, .nil, h => h
  | _, .cons _ _, h => h.2

omit [Fintype P] [DecidableEq P] in
lemma pathIn_src (S : Set (Cover x₀)) {X : RayVert (Cover x₀)} :
    ∀ {Y : RayVert (Cover x₀)} (q : Quiver.Path X Y), PathIn S q → X.out ∈ S
  | _, .nil, h => h
  | _, .cons q _, h => pathIn_src S q h.1

/-- A path of the cover inside a finite set `S` is a path of the piece quiver of `S` with the
same labels. -/
lemma piecePath_of_pathIn (S : Finset (Cover x₀)) {X : RayVert (Cover x₀)} (hX : X.out ∈ S) :
    ∀ {Y : RayVert (Cover x₀)} (q : Quiver.Path X Y), PathIn (S : Set (Cover x₀)) q →
      (hY : Y.out ∈ S) → ∃ le : List (pieceQuiver S).A,
        PathFrom (D := pieceQuiver S) (⟨X.out, hX⟩ : S) le ⟨Y.out, hY⟩ ∧
          le.map (pieceProj S).arr = labs q
  | _, .nil, _, _ => ⟨[], rfl, rfl⟩
  | _, .cons q e, hq, hY => by
    obtain ⟨le, hle, hmap⟩ := piecePath_of_pathIn S hX q hq.1 (pathIn_tgt _ q hq.1)
    let α : (pieceQuiver S).A := ⟨⟨_, pathIn_tgt _ q hq.1⟩, ⟨_, hY⟩, e.1, e.2⟩
    refine ⟨le ++ [α], pathFrom_append_gen le [α] hle ⟨rfl, rfl⟩, ?_⟩
    rw [List.map_append, hmap]
    rfl

namespace CLine

variable {L : CLine x₀} {t t' : ℕ} (hg : L.GoodPair t t')

/-- The paths of `Q_P` along the band cycle of a good pair. -/
def Along : Set (List (quiver P).A) :=
  {l | ∃ (le : List (CycArr (nc t t'))) (i j : Option (Fin (nc t t' + 1))),
    PathFrom (D := cycleQuiver (nc t t') (eps L t t')) i le j ∧ le.map (cyc hg).arr = l}

/-- The paths of `Q_P` that are not along the band cycle. -/
def NotAlong : Set (List (quiver P).A) :=
  {l | l ∉ Along hg ∧ ∃ x y, PathFrom (D := quiver P) x l y}

lemma along_take {l l' : List (quiver P).A} (h : l ++ l' ∈ Along hg) : l ∈ Along hg := by
  obtain ⟨le, i, j, hp, hmap⟩ := h
  have hsplit : le = le.take l.length ++ le.drop l.length := (List.take_append_drop _ _).symm
  rw [hsplit] at hp
  obtain ⟨m, h1, -⟩ := pathFrom_split_gen _ _ hp
  refine ⟨le.take l.length, i, m, h1, ?_⟩
  rw [List.map_take, hmap, List.take_left']
  rfl

lemma along_drop {l l' : List (quiver P).A} (h : l' ++ l ∈ Along hg) : l ∈ Along hg := by
  obtain ⟨le, i, j, hp, hmap⟩ := h
  have hsplit : le = le.take l'.length ++ le.drop l'.length := (List.take_append_drop _ _).symm
  rw [hsplit] at hp
  obtain ⟨m, -, h2⟩ := pathFrom_split_gen _ _ hp
  refine ⟨le.drop l'.length, m, j, h2, ?_⟩
  rw [List.map_drop, hmap, List.drop_left']
  rfl

include hg in
/-- **A path along the band shares its value with no other path.** -/
lemma eq_of_along {l l' : List (quiver P).A} {x y : P} (h : PathFrom (D := quiver P) x l y)
    (h' : PathFrom (D := quiver P) x l' y) (he : pathMor l x y h = pathMor l' x y h')
    (hl : l ∈ Along hg) : l = l' := by
  obtain ⟨le, i, j, hp, hmap⟩ := hl
  have hν : pathMor l x y h ≠ 0 := by
    intro h0
    exact cyc_band hg le i j hp (hmap ▸ ⟨x, y, h, h0⟩)
  by_cases hl0 : l = []
  · subst hl0
    change x = y at h
    subst h
    by_contra hll'
    obtain ⟨c, l'', rfl⟩ := List.exists_cons_of_ne_nil (Ne.symm hll')
    refine pathMor_ne_id c l'' x h' ?_
    rw [← he]
    simp [pathMor]
  have hN := t'_eq hg
  have hn := hg.2.1.1
  have hvi : vidx t i ≤ L.n := by
    rcases i with _ | j₀
    · change t + 1 ≤ L.n; omega
    · change t + 2 + (j₀ : ℕ) ≤ L.n; have := j₀.2; omega
  obtain ⟨b, q, hq, hlq⟩ := cover_path hg le i j hp (vidx t i) hvi (by rintro j₀ rfl; rfl)
  rw [← L.coe_finset] at hq
  obtain ⟨lp, hlp, hlpm⟩ := piecePath_of_pathIn L.finset (pathIn_src _ q hq) q hq
    (pathIn_tgt _ q hq)
  have hlpm' : lp.map (pieceProj L.finset).arr = l := hlpm.trans (hlq.trans hmap)
  obtain ⟨lp', hlpm2, hlp', -⟩ := exists_partner L.convex_finset (L.respectsCover_lineRep ℚ) he hν
    hl0 hlpm' hlp
  rw [← hlpm', ← hlpm2, L.path_unique lp lp' _ _ hlp hlp']

/-- **The paths off the band** contain the zero paths and the contours, and are closed under
extension. -/
theorem relPaths_notAlong : RelPaths (NotAlong hg) where
  ne_nil l hl := by
    rintro rfl
    exact hl.1 ⟨[], none, none, rfl, rfl⟩
  path l hl := hl.2
  ext_right l hl l' x z h := ⟨fun h' ↦ hl.1 (along_take hg h'), x, z, h⟩
  ext_left l hl l' x z h := ⟨fun h' ↦ hl.1 (along_drop hg h'), x, z, h⟩
  zero l hl := by
    obtain ⟨x, y, h, h0⟩ := hl
    refine ⟨fun ⟨le, i, j, hp, hmap⟩ ↦ cyc_band hg le i j hp (hmap ▸ ⟨x, y, h, h0⟩), x, y, h⟩
  contour l l' x y h h' he hll := ⟨fun hl ↦ hll (eq_of_along hg h h' he hl), x, y, h⟩

end CLine

section Assemble

open CLine

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- **A band from one line of the cover**, without excluding contours: the cycle of a minimal
good pair, presented by the paths off the band. -/
def lineBandRel (L : CLine x₀) {t t' : ℕ} (hg : L.GoodPair t t')
    (hmin : ∀ u u', L.GoodPair u u' → t' - t ≤ u' - u)
    (e : Linearization P k ≃ₐ[k] B) : Walk.MonomialBand k B where
  n := nc t t'
  ε := eps L t t'
  Q := quiver P
  p := cyc hg
  locInj := cyc_locInj hg
  primitive := cyc_primitive hg hmin
  π := e.toAlgHom.comp (linPres P k)
  surj := e.surjective.comp (linPres_surjective P k)
  P := NotAlong hg
  ker_le z hz := by
    have : linPres P k z = 0 := by
      have h0 : e (linPres P k z) = e 0 := by rw [map_zero]; exact hz
      exact e.injective h0
    exact (relPaths_notAlong hg).ker_linPres_le_of k z this
  band le i j h hmem := hmem.1 ⟨le, i, j, h, rfl⟩

lemma lineBandRel_n (L : CLine x₀) {t t' : ℕ} (hg : L.GoodPair t t')
    (hmin : ∀ u u', L.GoodPair u u' → t' - t ≤ u' - u) (e : Linearization P k ≃ₐ[k] B) :
    (lineBandRel L hg hmin e).n + 2 = t' - t := by
  have := t'_eq hg
  change nc t t' + 2 = t' - t
  omega

/-- **A line with a good pair gives a band** whose cycle has at most `t' - t` points, for any
good pair `(t, t')` of the line. -/
theorem exists_lineBandRel (L : CLine x₀) {t t' : ℕ} (hg : L.GoodPair t t')
    (e : Linearization P k ≃ₐ[k] B) :
    ∃ M : Walk.MonomialBand k B, M.n + 2 ≤ t' - t := by
  obtain ⟨u, u', hu, hmin⟩ := L.exists_minimal_goodPair ⟨t, t', hg⟩
  exact ⟨lineBandRel L hu hmin e, (lineBandRel_n L hu hmin e).le.trans (hmin t t' hg)⟩

end Assemble

end LargeIndecomposable.RayCat
