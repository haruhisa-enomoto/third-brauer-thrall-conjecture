module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineBuild
public import LargeIndecomposable.BongartzTheorem.LongLines.ModuleLine
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.CriticalArrows
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceCritical

/-!
# Module lines from thin modules

Let `g 0, …, g n` be points of a piece joined by arrows only between consecutive points, and
`Y` a module over the piece algebra, one-dimensional at the `g i` and zero elsewhere, on which
each arrow `g i — g (i + 1)` acts. Then composites along the sequence act injectively on the
spaces of `Y` (`actInj_of_path`), paths of the cover through the points have nonzero value
(`nz_line'`; this is `nz_line` without asking the piece to be a forest), and the points with the
representation of `Y` form a module line (`mline_of_seq`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module Classical

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)} {k : Type u} [Field k] (hpar : ParEq S)
  (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)

section Seq

variable {Y : AR.FDMod k (PieceAlg k S)} {n : ℕ} {g : ℕ → (pieceQuiver S).V}
  (hinj : ∀ i j, i ≤ n → j ≤ n → g i = g j → i = j)
  (hz1 : ∀ i ≤ n, AR.dimZ (pieceDirData (k := k) hacyc) Y (g i) = 1)
  (hstep : ∀ i < n, ∃ (w : PieceAlg k S) (y : Y),
    ((pieceDirData (k := k) hacyc).Arr (g i) (g (i + 1)) ∧
      (pev (g (i + 1)) * w * pev (g i)) • y ≠ 0) ∨
    ((pieceDirData (k := k) hacyc).Arr (g (i + 1)) (g i) ∧ (pev (g i) * w * pev (g (i + 1))) • y ≠ 0))
  (hcons : ∀ a b, a ≤ n → b ≤ n → (pieceDirData (k := k) hacyc).Arr (g a) (g b) →
    b = a + 1 ∨ a = b + 1)
  (hz0 : ∀ x, (∀ m ≤ n, g m ≠ x) → ∀ y : Y, pev (k := k) x • y = 0)

include hpar hz1 hstep hcons in
lemma actInj_arr {m b : ℕ} (hm : m ≤ n) (hb : b ≤ n)
    (harr : (pieceDirData (k := k) hacyc).Arr (g m) (g b)) : ActInj k Y (g m) (g b) := by
  rcases hcons m b hm hb harr with rfl | rfl
  · exact (actInj_step hacyc hz1 hstep hpar (m := m) (by omega)).1 harr
  · exact (actInj_step hacyc hz1 hstep hpar (m := b) (by omega)).2 harr

include hpar hacyc in
lemma actInj_comp {x y z : (pieceQuiver S).V} (h1 : PR x y) (h2 : PR y z)
    (hxy : ActInj k Y x y) (hyz : ActInj k Y y z) : ActInj k Y x z := by
  intro u hu hu0
  have h3 := hxy u hu hu0
  have h4 : pev (k := k) y • cv k x y • u = cv k x y • u := by
    have hc4 : pev (k := k) y * cv k x y = cv k x y :=
      (AR.DirData.cn_corner (D := pieceDirData (k := k) hacyc) y x (pbvec x y)).1
    rw [← mul_smul, hc4]
  have h5 := hyz _ h4 h3
  rwa [← mul_smul, cv_mul hpar h1 h2] at h5

include hpar hz1 hstep hcons in
/-- **Composites along the sequence act injectively.** -/
theorem actInj_path : ∀ (l : List (pieceQuiver S).A) (i j : (pieceQuiver S).V), PathFrom i l j →
    (∀ e ∈ l, (∃ a ≤ n, pt S (g a) = ((pieceQuiver S).src e).1) ∧
      ∃ b ≤ n, pt S (g b) = ((pieceQuiver S).tgt e).1) → ActInj k Y i j
  | [], i, j, h, _ => by
    have h' : i = j := h
    subst h'
    intro u hu hu0
    rw [cv_self hpar, hu]
    exact hu0
  | e :: l, i, j, ⟨hs, hl⟩, hin => by
    obtain ⟨⟨a, ha, hga⟩, ⟨b, hb, hgb⟩⟩ := hin e List.mem_cons_self
    have hga' : g a = i := Subtype.ext (hga.trans (congrArg Subtype.val hs))
    have hgb' : g b = (pieceQuiver S).tgt e := Subtype.ext hgb
    have harr : (pieceDirData (k := k) hacyc).Arr (g a) (g b) := by
      rw [hga', hgb', ← hs]
      exact parr_arrow hpar e
    have h1 : ActInj k Y i ((pieceQuiver S).tgt e) := by
      rw [← hga', ← hgb']
      exact actInj_arr hpar hacyc hz1 hstep hcons ha hb harr
    have h2 := actInj_path l _ j hl fun e' he' ↦ hin e' (List.mem_cons_of_mem _ he')
    exact actInj_comp hpar hacyc ⟨[e], hs, rfl⟩ ⟨l, hl⟩ h1 h2

include hpar hz1 hstep hcons in
/-- **Paths on the sequence have nonzero value.** -/
lemma nz_line' {X Z : RayVert (Cover x₀)} (p : Quiver.Path X Z)
    (hp : PathIn {c | ∃ a ≤ n, pt S (g a) = c} p) : pathVal p ≠ 0 := by
  let D := pieceDirData (k := k) hacyc
  let Pts : Set (Cover x₀) := {c | ∃ a ≤ n, pt S (g a) = c}
  obtain ⟨a, ha, hXa⟩ := pathIn_start p hp
  subst hXa
  have key : ∀ {c : RayVert (Cover x₀)} (q : Quiver.Path (RayVert.mk (pt S (g a))) c),
      PathIn Pts q → ∃ m, m ≤ n ∧ PR (g a) (g m) ∧ pt S (g m) = c ∧
        HEq (gval (g a) (g m)) (pathVal q) ∧ ActInj k Y (g a) (g m) := by
    intro c q
    induction q with
    | nil =>
      intro _
      refine ⟨a, ha, PR.refl _, rfl, heq_of_eq (gval_self hpar), fun u hu hu0 ↦ ?_⟩
      rw [cv_self hpar, hu]
      exact hu0
    | @cons d c q e ih =>
      rintro ⟨h1, b, hb, hc⟩
      obtain ⟨m, hm, hpr, hd, heq, hA⟩ := ih h1
      subst hd
      subst hc
      let α : (pieceQuiver S).A := ⟨g m, g b, e.1, e.2⟩
      have harr : D.Arr (g m) (g b) := parr_arrow hpar α
      have hprm : PR (g m) (g b) := ⟨[α], rfl, rfl⟩
      have hA' : ActInj k Y (g m) (g b) := actInj_arr hpar hacyc hz1 hstep hcons hm hb harr
      refine ⟨b, hb, hpr.trans hprm, rfl, heq_of_eq ?_, actInj_comp hpar hacyc hpr hprm hA hA'⟩
      have h2 : gval (g m) (g b) = e.1 :=
        (gval_eq hpar (l := [α]) ⟨rfl, rfl⟩).trans (compD_single α)
      rw [← gval_mul hpar hpr hprm, h2, eq_of_heq heq]
      rfl
  obtain ⟨m, hm, -, hz, heq, hA⟩ := key p hp
  subst hz
  intro h0
  have hg : gval (g a) (g m) = 0 := (eq_of_heq heq).trans h0
  obtain ⟨y, hy⟩ := AR.DirData.exists_smul_ne_of_dimZ (D := D) (c := g a) (by
    rw [hz1 a ha]; norm_num)
  have hev : pev (k := k) (g a) • (pev (k := k) (g a) • y) = pev (k := k) (g a) • y := by
    rw [← mul_smul, show pev (k := k) (g a) * pev (g a) = pev (g a) from
      (pieceDirData (k := k) hacyc).e_mul_e _]
  apply hA _ hev hy
  unfold cv
  rw [bvec_eq_zero hpar hg, mul_zero, zero_mul, zero_smul]

include hpar hinj hz1 hz0 hstep hcons in
/-- **A thin module on a sequence with arrows only between consecutive points gives a module
line.** -/
theorem mline_of_seq : ∃ L : MLine x₀ S k, L.n = n := by
  let D := pieceDirData (k := k) hacyc
  have hu : ∀ i, i ≤ n → ∃ u : Y, pev (k := k) (g i) • u = u ∧ u ≠ 0 := fun i hi ↦ by
    obtain ⟨y, hy⟩ := AR.DirData.exists_smul_ne_of_dimZ (D := D) (c := g i) (by
      rw [hz1 i hi]; norm_num)
    refine ⟨pev (k := k) (g i) • y, ?_, hy⟩
    rw [← mul_smul, show pev (k := k) (g i) * pev (g i) = pev (g i) from D.e_mul_e _]
  refine ⟨{ n := n
            pt := fun i ↦ pt S (g i)
            fwd := fun i ↦ decide (D.Arr (g i) (g (i + 1)))
            inj := fun a b ha hb h ↦ hinj a b ha hb (Subtype.ext h)
            arrF := fun i _ hf ↦ arr_irr hacyc (of_decide_eq_true hf)
            arrB := fun i hi hf ↦ ?_
            uniqF := fun i _ f f' hf hf' ↦ irr_unique hpar f f' hf hf'
            uniqB := fun i _ f f' hf hf' ↦ irr_unique hpar f f' hf hf'
            only := fun a b ha hb f hf ↦ ?_
            nz := fun p hp ↦ nz_line' hpar hacyc hz1 hstep hcons p hp
            sub := fun a _ ↦ (g a).2
            X := repOf Y
            resp := respectsCover_repOf Y
            onlyNZ := fun e he ↦ ?_
            pathNZ := fun le i j hle hin ↦ ?_ }, rfl⟩
  · have hn : ¬D.Arr (g i) (g (i + 1)) := of_decide_eq_false hf
    obtain ⟨w, y, h | h⟩ := hstep i hi
    · exact absurd h.1 hn
    · exact arr_irr hacyc h.1
  · let α : (pieceQuiver S).A := ⟨g a, g b, f, hf⟩
    have harr : D.Arr (g a) (g b) := parr_arrow hpar α
    rcases hcons a b ha hb harr with rfl | rfl
    · exact Or.inl ⟨rfl, decide_eq_true harr⟩
    · exact Or.inr ⟨rfl, decide_eq_false fun h' ↦ AR.DirData.not_arr_cycle harr h'⟩
  · by_contra hno
    apply he
    refine LinearMap.ext fun z ↦ (totEquiv Y).injective ?_
    change totToMod Y ((repOf Y).arrOp e z) = totToMod Y 0
    rw [totToMod_arrOp, map_zero]
    rcases not_and_or.1 hno with h | h
    · have h0 : ∀ m ≤ n, g m ≠ (pieceQuiver S).src e := fun m hm hg ↦
        h ⟨m, hm, congrArg Subtype.val hg⟩
      rw [show ea (k := k) e = ea e * pev ((pieceQuiver S).src e) by rw [ea_mul_ev, if_pos rfl],
        mul_smul, hz0 _ h0, smul_zero]
    · have h0 : ∀ m ≤ n, g m ≠ (pieceQuiver S).tgt e := fun m hm hg ↦
        h ⟨m, hm, congrArg Subtype.val hg⟩
      rw [← ev_tgt_mul_ea, mul_smul, hz0 _ h0]
  · rcases le with _ | ⟨e, l⟩
    · obtain ⟨u, -, hu0⟩ := hu 0 (Nat.zero_le _)
      intro h0
      have h1 : (repOf Y).pathTot [] (modToTot Y u) = 0 := by rw [h0]; rfl
      apply hu0
      have h2 := congrArg (totToMod Y) h1
      change totToMod Y (modToTot Y u) = totToMod Y 0 at h2
      rwa [totToMod_modToTot, map_zero] at h2
    · obtain ⟨⟨a, ha, hga⟩, -⟩ := hin e List.mem_cons_self
      have hga' : g a = i := Subtype.ext (hga.trans (congrArg Subtype.val hle.1))
      obtain ⟨u, hu1, hu0⟩ := hu a ha
      rw [hga'] at hu1
      have hcv := actInj_path hpar hacyc hz1 hstep hcons (e :: l) i j hle hin u hu1 hu0
      rw [cv_eq_of_path hpar hle (List.cons_ne_nil _ _)] at hcv
      intro h0
      apply hcv
      have h3 := totToMod_pathTot Y (e :: l) (modToTot Y u)
      rw [h0, LinearMap.zero_apply, map_zero, totToMod_modToTot] at h3
      exact h3.symm

end Seq

section Critical

variable [IsAlgClosed k] (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
  (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
  (hlsc : CoverLocalSC x₀) (hrep : ¬PieceRepFin k S)
  (hmin : ∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < S.card →
    PieceRepFin k C')
include hS hne hacycCov hint hlsc hrep hmin

omit hpar hacyc in
/-- **A critical piece carries point–brick data on a set `T'` of points, and if `T'` has at least
`30` points, a module line with `|T'| - 3` arrows.** -/
theorem pointBrickAt_critical_line :
    ∃ (T' : Set (pieceQuiver S).V) (x : (pieceQuiver S).V) (Vr : Rep k (pieceQuiver S)),
      PointBrickAt (k := k) x Vr ∧ x ∈ T' ∧ (∀ i, Nontrivial (Vr.obj i) → i ∈ T') ∧
      (T'.ncard ≤ 29 ∨ ∃ L : MLine x₀ S k, T'.ncard ≤ L.n + 3) := by
  classical
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := S) hacycCov
  let D := pieceDirData (k := k) hacyc
  obtain ⟨T', hin, hline⟩ := AR.DirData.exists_pointBrick_line (D := D) (fun _ ↦ Set.mem_univ _)
      (fun x y ↦ cartan_piece_le_one hacyc hpar x y)
      (goodProj_piece hS hne hacycCov hint hlsc hrep hmin)
      (unb_piece hS hne hacycCov hint hlsc hrep hmin)
      (fun a b h ↦ by
        have h' := h
        obtain ⟨α, rfl, rfl, -⟩ := h
        exact ⟨fun v h1 h2 ↦ mid_eq_of_arrow hpar hacyc α v h1 h2, D.arrNe _ _ h',
          cartan_piece_le_one hacyc hpar _ _⟩)
  obtain ⟨x, Vr, hP, hx, hsupp⟩ := pointBrickAt_of_in hacyc hin
  refine ⟨T', x, Vr, hP, hx, hsupp, ?_⟩
  by_cases h30 : T'.ncard ≤ 29
  · exact Or.inl h30
  right
  obtain h | ⟨P, V, -, hinj, hArr, hnoArr, -, hoff, hdim, hact⟩ := hline
  · exact absurd h h30
  obtain ⟨L, hL⟩ := mline_of_seq hpar hacyc (Y := V) (n := T'.ncard - 3) (g := P)
    (fun i j hi hj h ↦ hinj i j (by omega) (by omega) h)
    (fun i hi ↦ by
      have := hdim i (by omega)
      change ((finrank k (AR.eSub V (D.e (P i))) : ℕ) : ℤ) = 1
      exact_mod_cast this)
    (fun i hi ↦ by
      obtain ⟨c, v, h | h⟩ := hact i (by omega)
      · refine ⟨c, v, Or.inl ⟨?_, h⟩⟩
        rcases hArr i (by omega) with h' | h'
        · exact h'
        · have hc : D.e (P (i + 1)) * c * D.e (P i) ≠ 0 := fun h0 ↦ h (by rw [h0, zero_smul])
          exact (D.acyc _ _ (Relation.TransGen.single h') (D.hom _ _ c hc)).elim
      · refine ⟨c, v, Or.inr ⟨?_, h⟩⟩
        rcases hArr i (by omega) with h' | h'
        · have hc : D.e (P i) * c * D.e (P (i + 1)) ≠ 0 := fun h0 ↦ h (by rw [h0, zero_smul])
          exact (D.acyc _ _ (Relation.TransGen.single h') (D.hom _ _ c hc)).elim
        · exact h')
    (fun a b ha hb h ↦ by
      by_contra hno
      push Not at hno
      rcases Nat.lt_trichotomy a b with hab | rfl | hab
      · exact (hnoArr a b (by omega) (by omega)).1 h
      · exact D.ne_of_arr h rfl
      · exact (hnoArr b a (by omega) (by omega)).2 h)
    (fun y hy v ↦ hoff y (fun i hi ↦ hy i (by omega)) v)
  refine ⟨L, ?_⟩
  rw [hL]
  rw [Nat.sub_add_cancel (by omega)]
  exact le_rfl

end Critical

end LargeIndecomposable.RayCat
