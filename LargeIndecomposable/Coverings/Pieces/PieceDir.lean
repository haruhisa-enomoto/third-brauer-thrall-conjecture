module

public import LargeIndecomposable.Coverings.Pieces.PieceModRep
public import LargeIndecomposable.Coverings.Pieces.PointPair
public import LargeIndecomposable.Quivers.PathAlgebras.CornerSpan
public import LargeIndecomposable.DirectedAlgebras.Separation.SeparationThm
public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.CoverAcyclic

/-!
# Piece algebras are directed algebras

For a piece `S` of the cover without nonempty closed paths, the piece algebra with its vertex
idempotents and the arrows that are nonzero in it is a directed algebra (`pieceDirData`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

omit [Fintype P] [DecidableEq P] in
lemma reach_of_pathFrom : ∀ (l : List (pieceQuiver S).A) {i j : (pieceQuiver S).V},
    PathFrom i l j → Reach (pt S i) (pt S j)
  | [], i, j, h => by change i = j at h; subst h; exact Reach.refl _
  | c :: l, i, j, h => by
    obtain ⟨h1, h2⟩ := h
    change c.1 = i at h1
    subst h1
    exact Reach.step c.2.2.1 c.2.2.2 (reach_of_pathFrom l h2)

omit [Fintype P] [DecidableEq P] in
/-- **Pieces of an acyclic cover have no closed paths.** -/
lemma piece_acyclic (h : CoverAcyclic x₀) (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A)
    (hl : l ≠ []) : ¬PathFrom i l i := by
  match l, hl with
  | c :: l', _ =>
    rintro ⟨h1, h2⟩
    change c.1 = i at h1
    subst h1
    exact h _ _ c.2.2.1 c.2.2.2 (reach_of_pathFrom l' h2)

/-- The quotient map onto the piece algebra. -/
abbrev pmk : (pieceQuiver S).PathAlgebra k →ₐ[k] PieceAlg k S :=
  RingQuot.mkAlgHom k (fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0)

lemma pmk_surjective : Function.Surjective (pmk (k := k) (S := S)) :=
  RingQuot.mkAlgHom_surjective k _

lemma ev_ne_zero (v : (pieceQuiver S).V) : pev (k := k) v ≠ 0 := by
  intro h
  have h1 := congrArg (pieceAct (Rep.pointRep (k := k) v) (respectsCover_pointRep v)) h
  rw [map_zero, pieceAct_mk, Rep.pdAct_vertex, Rep.pdVert_id] at h1
  let x : (Rep.pointRep (k := k) v).Tot := Pi.single v (fun _ ↦ (1 : k))
  have h2 := LinearMap.congr_fun h1 x
  rw [Rep.idm_apply, LinearMap.zero_apply] at h2
  have h3 := congrFun h2 v
  rw [Pi.single_eq_same, Pi.zero_apply] at h3
  have h4 := congrFun h3 ⟨0, by simp⟩
  rw [show x v = fun _ ↦ (1 : k) from Pi.single_eq_same (M := fun i ↦
    (Rep.pointRep (k := k) v).obj i) v _] at h4
  exact one_ne_zero h4

/-- Nonzero arrows of the piece algebra. -/
def PArr (x y : (pieceQuiver S).V) : Prop :=
  ∃ α : (pieceQuiver S).A, (pieceQuiver S).src α = x ∧ (pieceQuiver S).tgt α = y ∧
    ea (k := k) α ≠ 0

/-- A path whose word is nonzero in the piece algebra runs along nonzero arrows. -/
lemma rtg_of_word : ∀ (l : List (pieceQuiver S).A) {x y : (pieceQuiver S).V},
    PathFrom x l y → pmk (k := k) (word k (pieceQuiver S) l) ≠ 0 →
      Relation.ReflTransGen (PArr (k := k) (S := S)) x y
  | [], x, y, h, _ => by
    change x = y at h
    subst h
    exact Relation.ReflTransGen.refl
  | c :: l, x, y, h, hw => by
    obtain ⟨h1, h2⟩ := h
    have hw' : pmk (k := k) (word k (pieceQuiver S) l) * ea (k := k) c ≠ 0 := by
      rw [← map_mul]; exact hw
    have hc : ea (k := k) c ≠ 0 := fun h0 ↦ hw' (by rw [h0, mul_zero])
    have hl : pmk (k := k) (word k (pieceQuiver S) l) ≠ 0 := fun h0 ↦ hw' (by rw [h0, zero_mul])
    exact Relation.ReflTransGen.head ⟨c, h1, rfl, hc⟩ (rtg_of_word l h2 hl)

/-- Corners of the piece algebra are spanned by the images of the corner generators. -/
lemma corner_piece (a : PieceAlg k S) (x y : (pieceQuiver S).V) :
    pev (k := k) y * a * pev x ∈ Submodule.span k (pmk '' cornerSet k x y) := by
  obtain ⟨p, rfl⟩ := pmk_surjective a
  have h := Submodule.mem_map_of_mem (f := (pmk (k := k) (S := S)).toLinearMap)
    (corner_mem_span k p x y)
  rw [Submodule.map_span] at h
  simpa [map_mul] using h

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
lemma pathFrom_append {D : FinQuiver} : ∀ (l l' : List D.A) {i j m : D.V},
    PathFrom i l j → PathFrom j l' m → PathFrom i (l ++ l') m
  | [], l', i, j, m, h, h' => by change i = j at h; subst h; exact h'
  | c :: l, l', i, j, m, h, h' => ⟨h.1, pathFrom_append l l' h.2 h'⟩

lemma path_of_rtg {x y : (pieceQuiver S).V}
    (h : Relation.ReflTransGen (PArr (k := k) (S := S)) x y) :
    ∃ l, PathFrom x l y := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ h2 ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨α, h1, h2', -⟩ := h2
    refine ⟨l ++ [α], pathFrom_append l [α] hl ⟨h1, h2'⟩⟩

lemma path_of_tg {x y : (pieceQuiver S).V}
    (h : Relation.TransGen (PArr (k := k) (S := S)) x y) :
    ∃ l, l ≠ [] ∧ PathFrom x l y := by
  obtain ⟨z, hxz, ⟨α, h1, h2, -⟩⟩ := Relation.TransGen.tail'_iff.1 h
  obtain ⟨l, hl⟩ := path_of_rtg hxz
  exact ⟨l ++ [α], by simp, pathFrom_append l [α] hl ⟨h1, h2⟩⟩

variable (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] →
  ¬PathFrom i l i)
include hacyc

lemma local_piece (x : (pieceQuiver S).V) (a : PieceAlg k S) :
    ∃ c : k, pev (k := k) x * a * pev x = c • pev x := by
  have h := corner_piece a x x
  have hsub : pmk (k := k) '' cornerSet k x x ⊆ {pev (k := k) x} := by
    rintro _ ⟨r, (⟨-, rfl⟩ | ⟨l, hl, hp, rfl⟩), rfl⟩
    · rfl
    · exact absurd hp (hacyc x l hl)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (Submodule.span_mono hsub h)
  exact ⟨c, hc.symm⟩

lemma hom_piece (x y : (pieceQuiver S).V) (a : PieceAlg k S) (h : pev (k := k) y * a * pev x ≠ 0) :
    Relation.ReflTransGen (PArr (k := k) (S := S)) x y := by
  by_contra hno
  apply h
  have hle : Submodule.span k (pmk (k := k) '' cornerSet k x y) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨r, (⟨rfl, rfl⟩ | ⟨l, hl, hp, rfl⟩), rfl⟩
    · exact absurd Relation.ReflTransGen.refl hno
    · by_contra h0
      exact hno (rtg_of_word l hp h0)
  have := hle (corner_piece a x y)
  rwa [Submodule.mem_bot] at this

lemma acyc_piece (x y : (pieceQuiver S).V) (h : Relation.TransGen (PArr (k := k) (S := S)) x y)
    (h' : Relation.ReflTransGen (PArr (k := k) (S := S)) y x) : False := by
  obtain ⟨l, hl, hp⟩ := path_of_tg h
  obtain ⟨l', hp'⟩ := path_of_rtg h'
  exact hacyc x (l ++ l') (by simp [hl]) (pathFrom_append l l' hp hp')

omit hacyc in
lemma gen_piece (x : (pieceQuiver S).V) (a : PieceAlg k S) :
    (1 - pev (k := k) x) * a * pev x ∈ Submodule.span (PieceAlg k S)
      {r | ∃ y b, PArr (k := k) x y ∧ r = pev y * b * pev x} := by
  classical
  set G : Set (PieceAlg k S) :=
    {r | ∃ y b, PArr (k := k) (S := S) x y ∧ r = pev (k := k) y * b * pev (k := k) x}
  have hword : ∀ l : List (pieceQuiver S).A, l ≠ [] → ∀ y, PathFrom x l y →
      pmk (k := k) (word k (pieceQuiver S) l) ∈ Submodule.span (PieceAlg k S) G := by
    rintro (_ | ⟨c, l'⟩) hl y hp
    · exact absurd rfl hl
    obtain ⟨h1, -⟩ := hp
    have he : ea (k := k) c = pev ((pieceQuiver S).tgt c) * ea c * pev x := by
      rw [ev_tgt_mul_ea, ea_mul_ev, if_pos h1.symm]
    change pmk (k := k) (word k (pieceQuiver S) l' * arrow k (pieceQuiver S) c) ∈ _
    rw [map_mul]
    change pmk (k := k) (word k (pieceQuiver S) l') * ea c ∈ _
    by_cases hc : ea (k := k) c = 0
    · rw [hc, mul_zero]; exact Submodule.zero_mem _
    · rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨_, ea c, ⟨c, h1, rfl, hc⟩, rfl⟩)
  have hsum : (1 - pev (k := k) x) * a * pev x = ∑ y ∈ Finset.univ.erase x, pev y * a * pev x := by
    rw [← sum_ev (k := k) (S := S), ← Finset.add_sum_erase _ _ (Finset.mem_univ x),
      add_sub_cancel_left (pev (k := k) x), Finset.sum_mul, Finset.sum_mul]
  rw [hsum]
  refine Submodule.sum_mem _ fun y hy ↦ ?_
  have hxy : x ≠ y := (Finset.ne_of_mem_erase hy).symm
  have hle : Submodule.span k (pmk (k := k) '' cornerSet k x y) ≤
      (Submodule.span (PieceAlg k S) G).restrictScalars k := by
    rw [Submodule.span_le]
    rintro _ ⟨r, (⟨h, -⟩ | ⟨l, hl, hp, rfl⟩), rfl⟩
    · exact absurd h hxy
    · exact hword l hl y hp
  exact hle (corner_piece a x y)

/-- **The piece algebra is a directed algebra.** -/
def pieceDirData : AR.DirData k (PieceAlg k S) where
  ι := (pieceQuiver S).V
  e := pev
  idem v := by
    change pev v * pev v = pev v
    rw [ev_mul_ev, if_pos rfl]
  orth v w h := by rw [ev_mul_ev, if_neg h]
  sum := sum_ev
  T := Set.univ
  zero v hv := absurd (Set.mem_univ v) hv
  ne v _ := ev_ne_zero v
  local_ := local_piece hacyc
  Arr := PArr
  arrT _ _ _ := ⟨Set.mem_univ _, Set.mem_univ _⟩
  hom := hom_piece hacyc
  acyc := acyc_piece hacyc
  gen := gen_piece
  arrNe x y h := by
    obtain ⟨α, h1, h2, hα⟩ := h
    refine ⟨ea α, ?_⟩
    rw [← h1, ← h2, ev_tgt_mul_ea, ea_mul_ev, if_pos rfl]
    exact hα

end LargeIndecomposable.RayCat
