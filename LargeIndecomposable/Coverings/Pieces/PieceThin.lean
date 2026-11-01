module

public import LargeIndecomposable.Coverings.Pieces.PieceDir

/-!
# The thin representation from a point

Assume parallel paths of a piece have equal composites (Lemma 4.2). For a point `x`, let
`gval y : x → y` be the composite of any path from `x` to `y` (zero if there is none). The
representation `thinRep x` has `k` at every point, and an arrow `e` acts by `1` if
`gval (src e) ≫ e ≠ 0` and by `0` otherwise. It respects the cover (`respectsCover_thinRep`), and a
path from `x` with nonzero composite acts nonzero on it, so its word is nonzero in the piece
algebra (`pmk_word_ne_zero`).
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
/-- **Composites of concatenated paths.** -/
lemma compD_append : ∀ (l l' : List (pieceQuiver S).A) {i j m : (pieceQuiver S).V}
    (h : PathFrom i l j) (h' : PathFrom j l' m),
    compD S (l ++ l') i m (pathFrom_append l l' h h') = compD S l i j h ≫ compD S l' j m h'
  | [], l', i, j, m, h, h' => by
    change i = j at h
    subst h
    change compD S l' i m _ = eqToHom rfl ≫ compD S l' i m h'
    rw [eqToHom_refl, Category.id_comp]
  | e :: l, l', i, j, m, h, h' => by
    change eqToHom _ ≫ e.2.2.1 ≫ compD S (l ++ l') _ m _ =
      (eqToHom _ ≫ e.2.2.1 ≫ compD S l _ j h.2) ≫ compD S l' j m h'
    erw [compD_append l l' h.2 h']
    simp only [Category.assoc]
    rfl

variable (S) in
/-- Lemma 4.2 for the piece: parallel paths have equal composites. -/
def ParEq : Prop :=
  ∀ (l l' : List (pieceQuiver S).A) (i j : (pieceQuiver S).V) (h : PathFrom i l j)
    (h' : PathFrom i l' j), compD S l i j h = compD S l' i j h'

variable (x : (pieceQuiver S).V)

open Classical in
/-- The composite of a path from `x` to `y`. -/
def gval (y : (pieceQuiver S).V) : pt S x ⟶ pt S y :=
  if h : ∃ l, PathFrom x l y then compD S h.choose x y h.choose_spec else 0

variable {x}

lemma gval_eq (hpar : ParEq S) {y : (pieceQuiver S).V} {l : List (pieceQuiver S).A}
    (h : PathFrom x l y) : gval x y = compD S l x y h := by
  have hex : ∃ l, PathFrom x l y := ⟨l, h⟩
  unfold gval
  rw [dif_pos hex]
  exact hpar _ _ _ _ _ _

lemma gval_self (hpar : ParEq S) : gval x x = 𝟙 _ := by
  rw [gval_eq hpar (l := []) rfl]
  rfl

variable (x) in
open Classical in
/-- **The thin representation from `x`.** -/
def thinRep : Rep k (pieceQuiver S) where
  obj _ := ModuleCat.of k k
  map e := ModuleCat.ofHom (if gval x ((pieceQuiver S).src e) ≫ e.2.2.1 ≠ 0 then LinearMap.id
    else 0)

omit [Fintype P] [DecidableEq P] in
lemma exists_path_of_gval {y : (pieceQuiver S).V} (h : gval x y ≠ 0) : ∃ l, PathFrom x l y := by
  by_contra hno
  unfold gval at h
  rw [dif_neg hno] at h
  exact h rfl

omit [Fintype P] [DecidableEq P] in
lemma compD_single (e : (pieceQuiver S).A) :
    compD S [e] ((pieceQuiver S).src e) ((pieceQuiver S).tgt e) ⟨rfl, rfl⟩ = e.2.2.1 := by
  change eqToHom rfl ≫ e.2.2.1 ≫ eqToHom rfl = e.2.2.1
  simp

open Classical in
lemma thinRep_map (e : (pieceQuiver S).A) (w : k) :
    ((thinRep (k := k) x).map e).hom w =
      if gval x ((pieceQuiver S).src e) ≫ e.2.2.1 ≠ 0 then w else 0 := by
  by_cases h : gval x ((pieceQuiver S).src e) ≫ e.2.2.1 = 0 <;> simp [thinRep, h] <;> rfl

open Classical in
/-- **The path operators of the thin representation.** -/
lemma pathTot_thin (hpar : ParEq S) : ∀ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V)
    (h : PathFrom i le j), le ≠ [] → ∀ v : (thinRep (k := k) x).Tot,
      (thinRep (k := k) x).pathTot le v =
        Pi.single j (if gval x i ≫ compD S le i j h ≠ 0 then v i else 0)
  | [], _, _, _, hne, _ => absurd rfl hne
  | [e], i, j, h, _, v => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    change (pieceQuiver S).tgt e = j at h2
    subst h1 h2
    change (thinRep (k := k) x).arrOp e v = _
    rw [Rep.arrOp_apply]
    congr 1
    have : compD S [e] e.1 ((pieceQuiver S).tgt e) ⟨rfl, rfl⟩ = e.2.2.1 := compD_single e
    simp only [this]
    exact thinRep_map (k := k) e (v e.1)
  | e :: f :: le, i, j, h, _, v => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    subst h1
    have hcomp : compD S (e :: f :: le) e.1 j ⟨rfl, h2⟩ =
        e.2.2.1 ≫ compD S (f :: le) ((pieceQuiver S).tgt e) j h2 := by
      change eqToHom rfl ≫ e.2.2.1 ≫ _ = _
      rw [eqToHom_refl, Category.id_comp]
      rfl
    change (thinRep (k := k) x).pathTot (f :: le) ((thinRep (k := k) x).arrOp e v) = _
    rw [pathTot_thin hpar (f :: le) _ j h2 (List.cons_ne_nil _ _), Rep.arrOp_apply,
      Pi.single_eq_same]
    erw [thinRep_map (k := k) e (v e.1)]
    simp only [hcomp]
    congr 1
    have hassoc : (gval x e.1 ≫ e.2.2.1) ≫ compD S (f :: le) ((pieceQuiver S).tgt e) j h2 =
        gval x e.1 ≫ e.2.2.1 ≫ compD S (f :: le) ((pieceQuiver S).tgt e) j h2 :=
      Category.assoc _ _ _
    by_cases he : gval x e.1 ≫ e.2.2.1 = 0
    · have h0 : gval x e.1 ≫ e.2.2.1 ≫ compD S (f :: le) ((pieceQuiver S).tgt e) j h2 = 0 := by
        rw [← hassoc, he]
        exact Limits.zero_comp
      have he' : gval x ((pieceQuiver S).src e) ≫ e.2.2.1 = 0 := he
      have h0' : ¬(gval x e.1 ≫ e.2.2.1 ≫ compD S (f :: le) ((pieceQuiver S).tgt e) j h2 ≠ 0) :=
        not_not.2 h0
      have he'' : ¬(gval x ((pieceQuiver S).src e) ≫ e.2.2.1 ≠ 0) := not_not.2 he'
      erw [if_neg h0', if_neg he'']
      exact ite_self _
    · obtain ⟨l0, hl0⟩ := exists_path_of_gval (x := x) (y := e.1) (fun h0 ↦ he (by
        rw [h0, Limits.zero_comp]))
      have hg : gval x ((pieceQuiver S).tgt e) = gval x e.1 ≫ e.2.2.1 := by
        rw [gval_eq hpar (pathFrom_append l0 [e] hl0 ⟨rfl, rfl⟩), compD_append l0 [e] hl0
          ⟨rfl, rfl⟩, gval_eq hpar hl0]
        erw [compD_single]
        rfl
      have he' : gval x ((pieceQuiver S).src e) ≫ e.2.2.1 ≠ 0 := he
      rw [hg]
      erw [hassoc, if_pos he']

/-- **The thin representation respects the cover.** -/
theorem respectsCover_thinRep (hpar : ParEq S) : RespectsCover (thinRep (k := k) x) := by
  refine ⟨fun le i j h h0 ↦ ?_, fun le le' i j h h' he ↦ ?_⟩
  · rcases le with _ | ⟨e, le⟩
    · exact absurd h0 (compD_nil_ne_zero i j h)
    · refine LinearMap.ext fun v ↦ ?_
      rw [pathTot_thin hpar _ i j h (List.cons_ne_nil _ _)]
      have : ¬(gval x i ≫ compD S (e :: le) i j h ≠ 0) := by
        rw [not_not, h0]; exact Limits.comp_zero
      erw [if_neg this, Pi.single_zero]
      rfl
  · rcases le with _ | ⟨e, le⟩ <;> rcases le' with _ | ⟨e', le'⟩
    · rfl
    · exfalso
      change i = j at h
      subst h
      apply not_isIso_compD _ i i h' (List.cons_ne_nil _ _)
      rw [← he]
      change IsIso (eqToHom _)
      infer_instance
    · exfalso
      change i = j at h'
      subst h'
      apply not_isIso_compD _ i i h (List.cons_ne_nil _ _)
      rw [he]
      change IsIso (eqToHom _)
      infer_instance
    · refine LinearMap.ext fun v ↦ ?_
      rw [pathTot_thin hpar _ i j h (List.cons_ne_nil _ _),
        pathTot_thin hpar _ i j h' (List.cons_ne_nil _ _), he]

/-- **Paths with nonzero composite have nonzero words in the piece algebra.** -/
theorem pmk_word_ne_zero (hpar : ParEq S) {l : List (pieceQuiver S).A} {y : (pieceQuiver S).V}
    (hl : l ≠ []) (h : PathFrom x l y) (h0 : compD S l x y h ≠ 0) :
    pmk (k := k) (word k (pieceQuiver S) l) ≠ 0 := by
  intro hz
  have h1 := congrArg (pieceAct (thinRep (k := k) x) (respectsCover_thinRep hpar)) hz
  rw [map_zero, pieceAct_mk, Rep.pdAct_id_word] at h1
  have h2 := LinearMap.congr_fun h1 (Pi.single x (1 : k))
  rw [pathTot_thin hpar l x y h hl, LinearMap.zero_apply] at h2
  have h3 : gval x x ≫ compD S l x y h ≠ 0 := by
    rw [gval_self hpar, Category.id_comp]; exact h0
  erw [if_pos h3] at h2
  have h4 := congrFun h2 y
  simp only [Pi.zero_apply] at h4
  erw [Pi.single_eq_same, Pi.single_eq_same] at h4
  exact one_ne_zero (show (1 : k) = 0 from h4)

end LargeIndecomposable.RayCat
