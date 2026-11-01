module

public import LargeIndecomposable.BongartzTheorem.LongLines.ForestPiece
public import LargeIndecomposable.BongartzTheorem.LongLines.CoverLine

/-!
# Long lines from large indecomposables

Without contours, a large indecomposable over a convex piece lives on a convex subtree
(`exists_sincere_piece`), and a long path of this tree contains a line of the cover
(`exists_cline`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module Classical Statement

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)} {k : Type u} [Field k] (hpar : ParEq S)
  (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)

include hpar in
/-- Paths of the cover between points of a convex piece are paths of the piece. -/
lemma rtg_of_reach (hS : Convex (S : Set (Cover x₀))) {a c : Cover x₀} (ha : a ∈ S) (hc : c ∈ S)
    (h : Reach a c) :
    Relation.ReflTransGen (pieceDirData (k := k) hacyc).Arr (⟨a, ha⟩ : (pieceQuiver S).V) ⟨c, hc⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @step a b c f hf rest ih =>
    have hb : b ∈ S := hS a b c ha hc (Reach.step f hf (Reach.refl _)) rest
    exact Relation.ReflTransGen.head
      (parr_arrow hpar (⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨f, hf⟩⟩ : (pieceQuiver S).A)) (ih hb hc)

include hpar in
/-- Degrees of pieces are bounded. -/
lemma card_adj_piece (a : (pieceDirData (k := k) hacyc).ι) :
    (Finset.univ.filter ((pieceDirData (k := k) hacyc).gr.Adj a)).card ≤ 2 * morCard P := by
  let D := pieceDirData (k := k) hacyc
  let F₁ : Finset D.ι := Finset.univ.filter fun b ↦ gval (S := S) a b ≠ 0
  let F₂ : Finset D.ι := Finset.univ.filter fun b ↦ gval (S := S) b a ≠ 0
  have hgv : ∀ {x y : D.ι}, D.Arr x y → gval (S := S) x y ≠ 0 := fun {x y} h ↦ by
    obtain ⟨z, hz⟩ := D.arrNe _ _ h
    exact (of_cn_ne_zero hpar hacyc (AR.DirData.cn_corner (D := D) y x z) hz).2
  have hsubF : Finset.univ.filter (D.gr.Adj a) ⊆ F₁ ∪ F₂ := by
    intro b hb
    obtain ⟨-, h | h⟩ := AR.DirData.gr_adj.1 (Finset.mem_filter.1 hb).2
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgv h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgv h⟩)
  have h1 : F₁.card ≤ morCard P := card_out_le F₁ id Function.injective_id.injOn a fun b hb ↦
    (Finset.mem_filter.1 hb).2
  have h2 : F₂.card ≤ morCard P := card_in_le F₂ id Function.injective_id.injOn a fun b hb ↦
    (Finset.mem_filter.1 hb).2
  have h3 := (Finset.card_le_card hsubF).trans (Finset.card_union_le F₁ F₂)
  exact h3.trans (by omega)

include hpar in
/-- **The support of an indecomposable, without contours.** -/
theorem exists_sincere_piece (hnc : NoContour P) (hS : Convex (S : Set (Cover x₀)))
    (hlsc : CoverLocalSC x₀) (hacycCov : CoverAcyclic x₀)
    (N : AR.FDMod k (PieceAlg k S)) (hN : AR.IndNT N) :
    ∃ (S' : Finset (Cover x₀)) (N' : AR.FDMod k (PieceAlg k S')),
      Convex (S' : Set (Cover x₀)) ∧ S'.Nonempty ∧ AR.IndNT N' ∧
      (∀ i : (pieceQuiver S').V, ∃ y : N', pev (k := k) i • y ≠ 0) ∧
      Nat.card ((pieceDirData (k := k) hacyc).Supp N) ≤ S'.card := by
  let D := pieceDirData (k := k) hacyc
  let T' : Set (pieceQuiver S).V := D.Supp N
  have hac := gr_isAcyclic (k := k) hacyc hnc hS hlsc
  have hcv : D.IsConvexSet T' := AR.DirData.isConvexSet_supp hac hN.1
  have hsubS := ptsOf_subset T'
  have hconv : Convex ((ptsOf T' : Finset (Cover x₀)) : Set (Cover x₀)) := by
    intro a b c ha hc h1 h2
    have haS : a ∈ S := hsubS ha
    have hcS : c ∈ S := hsubS hc
    have hbS : b ∈ S := hS a b c haS hcS h1 h2
    have hma := (mem_ptsOf (⟨a, haS⟩ : (pieceQuiver S).V)).1 ha
    have hmc := (mem_ptsOf (⟨c, hcS⟩ : (pieceQuiver S).V)).1 hc
    exact (mem_ptsOf (⟨b, hbS⟩ : (pieceQuiver S).V)).2 (hcv _ _ _ hma hmc
      (rtg_of_reach hpar hacyc hS haS hbS h1) (rtg_of_reach hpar hacyc hS hbS hcS h2))
  let X := repOf N
  have hX : RespectsCover X := respectsCover_repOf N
  have hzero : ∀ s, s ∉ T' → ∀ m : X.obj s, m = 0 := fun s hs m ↦ by
    by_contra hm
    apply hs
    refine ⟨val N m, ?_⟩
    change pev (k := k) s • val N m ≠ 0
    rw [ev_smul_val]
    exact fun h ↦ hm (val_injective N h)
  have hsupp : SuppIn (ptsOf T') X := fun s hs ↦
    ⟨fun a b ↦ by
      have hsR : s ∉ T' := fun h ↦ hs ((mem_ptsOf s).2 h)
      rw [hzero s hsR a, hzero s hsR b]⟩
  have hfin : ∀ i, FiniteDimensional k ((resP hsubS X).obj i) := fun i ↦ inferInstance
  have hYc := respectsCover_resP hsubS X hX
  have hYi := isIndec_resP hsubS hsupp (isIndec_repOf N hN)
  refine ⟨ptsOf T', toFDMod (resP hsubS X) hYc, hconv, ?_, indNT_toFDMod hYc hYi, fun i ↦ ?_, ?_⟩
  · obtain ⟨⟨s, hs⟩, -⟩ := hYi
    exact ⟨_, (show ptsOf T' from s).2⟩
  · have hmem : (incH hsubS).vert i ∈ T' := (mem_ptsOf _).1 (show ptsOf T' from i).2
    obtain ⟨m, hm⟩ := hmem
    let v : (resP hsubS X).obj i := (⟨pev (k := k) ((incH hsubS).vert i) • m, m, rfl⟩ :
      LinearMap.range (actK N (pev (k := k) ((incH hsubS).vert i))))
    have hv : v ≠ 0 := fun h ↦ hm (congrArg Subtype.val h)
    refine ⟨show PieceMod (resP hsubS X) hYc from Pi.single i v, fun h0 ↦ hv ?_⟩
    have h1 : pieceAct (resP hsubS X) hYc (RingQuot.mkAlgHom k _ (vertex k (pieceQuiver _) i))
        (Pi.single i v) i = v := by
      rw [pieceAct_mk, Rep.pdAct_vertex, Rep.pdVert_apply]
      exact (if_pos rfl).trans (Pi.single_eq_same _ _)
    rw [← h1]
    have h2 := congrFun h0 i
    exact h2
  · have hinj : Function.Injective (fun t : T' ↦
        (⟨t.1.1, (mem_ptsOf t.1).2 t.2⟩ : (ptsOf T' : Finset (Cover x₀)))) := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : (ptsOf T' : Finset (Cover x₀)) ↦ z.1) h
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := (ptsOf T' : Finset (Cover x₀))), Fintype.card_coe] at this

omit [Fintype P] [DecidableEq P] in
lemma pathIn_end {H : Set (Cover x₀)} {x : RayVert (Cover x₀)} : ∀ {y : RayVert (Cover x₀)}
    (p : Quiver.Path x y), PathIn H p → y.out ∈ H
  | _, .nil, h => h
  | _, .cons _ _, h => h.2

omit [Fintype P] [DecidableEq P] in
lemma pathIn_start {H : Set (Cover x₀)} {x : RayVert (Cover x₀)} : ∀ {y : RayVert (Cover x₀)}
    (p : Quiver.Path x y), PathIn H p → x.out ∈ H
  | _, .nil, h => h
  | _, .cons p _, h => pathIn_start p h.1

section Line

lemma arr_irr {x y : (pieceQuiver S).V} (h : (pieceDirData (k := k) hacyc).Arr x y) :
    ∃ f : pt S x ⟶ pt S y, IsIrreducible f := by
  obtain ⟨α, rfl, rfl, -⟩ := h
  exact ⟨α.2.2.1, α.2.2.2⟩

include hpar in
lemma irr_unique {x y : (pieceQuiver S).V} (f g : pt S x ⟶ pt S y) (hf : IsIrreducible f)
    (hg : IsIrreducible g) : f = g := by
  have h1 : gval x y = f :=
    (gval_eq hpar (l := [⟨x, y, f, hf⟩]) ⟨rfl, rfl⟩).trans (compD_single ⟨x, y, f, hf⟩)
  have h2 : gval x y = g :=
    (gval_eq hpar (l := [⟨x, y, g, hg⟩]) ⟨rfl, rfl⟩).trans (compD_single ⟨x, y, g, hg⟩)
  exact h1.symm.trans h2

end Line

section Build

variable [IsAlgClosed k] (hS : Convex (S : Set (Cover x₀)))
  (hac : (pieceDirData (k := k) hacyc).gr.IsAcyclic)
  (hC : ∀ x y, AR.cartan (pieceDirData (k := k) hacyc) y x ≤ 1)
  {Y : AR.FDMod k (PieceAlg k S)} (hY : AR.IsIndecMod (PieceAlg k S) Y) {n : ℕ}
  {g : ℕ → (pieceQuiver S).V} (hinj : ∀ i j, i ≤ n → j ≤ n → g i = g j → i = j)
  (hz1 : ∀ i ≤ n, AR.dimZ (pieceDirData (k := k) hacyc) Y (g i) = 1)
  (hz0 : ∀ c, (∀ i ≤ n, g i ≠ c) → AR.dimZ (pieceDirData (k := k) hacyc) Y c = 0)
  (hstep : ∀ i < n, ∃ (w : PieceAlg k S) (y : Y), ((pieceDirData (k := k) hacyc).Arr (g i) (g (i + 1)) ∧
      (pev (g (i + 1)) * w * pev (g i)) • y ≠ 0) ∨
    ((pieceDirData (k := k) hacyc).Arr (g (i + 1)) (g i) ∧ (pev (g i) * w * pev (g (i + 1))) • y ≠ 0))

include hstep in
omit [IsAlgClosed k] in
lemma seq_adj {i : ℕ} (hi : i < n) : (pieceDirData (k := k) hacyc).gr.Adj (g i) (g (i + 1)) := by
  obtain ⟨w, y, h | h⟩ := hstep i hi
  · exact AR.DirData.gr_adj_of_arr h.1
  · exact (AR.DirData.gr_adj_of_arr h.1).symm

include hstep hac hinj in
omit [IsAlgClosed k] in
/-- An arrow between points of the line joins consecutive points. -/
lemma seq_consecutive {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hab : a < b)
    (h : (pieceDirData (k := k) hacyc).gr.Adj (g a) (g b)) : b = a + 1 := by
  let h₂ : ℕ → (pieceDirData (k := k) hacyc).ι := fun j ↦ if j = 0 then g a else g b
  have hh0 : h₂ 0 = g a := if_pos rfl
  have hh1 : h₂ 1 = g b := if_neg (by norm_num)
  have hne : g a ≠ g b := fun h' ↦ by
    have := hinj a b ha hb h'
    omega
  have := AR.DirData.seq_unique hac (fun j ↦ g (a + j)) h₂ (r := b - a) (r' := 1)
    (by
      have e1 : a + (b - a) = b := by omega
      change g (a + (b - a)) = h₂ 1
      rw [e1, hh1])
    (by
      change g (a + 0) = h₂ 0
      rw [hh0]
      rfl)
    (fun j hj ↦ seq_adj hacyc hstep (i := a + j) (by omega))
    (fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      change (pieceDirData (k := k) hacyc).gr.Adj (h₂ 0) (h₂ 1)
      rw [hh0, hh1]
      exact h)
    (fun i j hi hj hij ↦ by
      have := hinj (a + i) (a + j) (by omega) (by omega) hij
      omega)
    (fun i j hi hj hij ↦ by
      have hi' : i = 0 ∨ i = 1 := by omega
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
      · rfl
      · rw [hh0, hh1] at hij
        exact absurd hij hne
      · rw [hh0, hh1] at hij
        exact absurd hij.symm hne
      · rfl)
  omega

variable (k) in
/-- `cv x y` acts injectively on the part of `Y` at `x`. -/
def ActInj (Y : AR.FDMod k (PieceAlg k S)) (x y : (pieceQuiver S).V) : Prop :=
  ∀ u : Y, pev (k := k) x • u = u → u ≠ 0 → cv k x y • u ≠ 0

include hz1 in
omit [IsAlgClosed k] in
lemma thin_line {i : ℕ} (hi : i ≤ n) (u v : Y) (hu : pev (k := k) (g i) • u = u)
    (hv : pev (k := k) (g i) • v = v) (h0 : v ≠ 0) : ∃ c : k, c • v = u := by
  let D := pieceDirData (k := k) hacyc
  have h1 : Module.finrank k (AR.eSub Y (D.e (g i))) = 1 := by
    have := hz1 i hi
    change ((Module.finrank k (AR.eSub Y (D.e (g i))) : ℕ) : ℤ) = 1 at this
    exact_mod_cast this
  have hv' : (⟨v, hv⟩ : AR.eSub Y (D.e (g i))) ≠ 0 := fun h ↦ h0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv').1 h1 ⟨u, hu⟩
  exact ⟨c, congrArg Subtype.val hc⟩

include hz1 in
omit [IsAlgClosed k] in
lemma actInj_of_corner (hpar' : ParEq S) {i : ℕ} (hi : i ≤ n) {y : (pieceQuiver S).V}
    {w : PieceAlg k S} {u₀ : Y} (h : (pev y * w * pev (g i)) • u₀ ≠ 0) : ActInj k Y (g i) y := by
  intro u hu hu0
  obtain ⟨c, hc⟩ := corner_smul_cv hpar' (g i) y w hacyc
  rw [hc, smul_assoc] at h
  have hcv : cv k (g i) y * pev (g i) = cv k (g i) y :=
    (AR.DirData.cn_corner (D := pieceDirData (k := k) hacyc) y (g i) _).2
  have h1 : cv k (g i) y • u₀ = cv k (g i) y • (pev (k := k) (g i) • u₀) := by
    rw [← mul_smul, hcv]
  have hv0 : pev (k := k) (g i) • u₀ ≠ 0 := fun h0 ↦ h (by rw [h1, h0, smul_zero, smul_zero])
  have hev : pev (k := k) (g i) • (pev (k := k) (g i) • u₀) = pev (k := k) (g i) • u₀ := by
    rw [← mul_smul, show pev (k := k) (g i) * pev (g i) = pev (g i) from
      (pieceDirData (k := k) hacyc).e_mul_e _]
  obtain ⟨c', hc'⟩ := thin_line hacyc hz1 hi _ _ hev hu hu0
  intro h0
  apply h
  rw [h1, ← hc', smul_comm (cv k (g i) y) c', h0, smul_zero, smul_zero]

include hz1 hstep in
omit [IsAlgClosed k] in
lemma actInj_step (hpar' : ParEq S) {m : ℕ} (hm : m < n) :
    ((pieceDirData (k := k) hacyc).Arr (g m) (g (m + 1)) → ActInj k Y (g m) (g (m + 1))) ∧
      ((pieceDirData (k := k) hacyc).Arr (g (m + 1)) (g m) → ActInj k Y (g (m + 1)) (g m)) := by
  obtain ⟨w, y, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hstep m hm
  · refine ⟨fun _ ↦ actInj_of_corner hacyc hz1 hpar' hm.le h2, fun h3 ↦ ?_⟩
    exact (AR.DirData.not_arr_cycle h1 h3).elim
  · refine ⟨fun h3 ↦ (AR.DirData.not_arr_cycle h1 h3).elim, fun _ ↦ ?_⟩
    exact actInj_of_corner hacyc hz1 hpar' (i := m + 1) (by omega) h2

include hpar hz1 hstep hac hinj in
omit [IsAlgClosed k] in
/-- **Paths on the line have nonzero value.** -/
lemma nz_line {X Z : RayVert (Cover x₀)} (p : Quiver.Path X Z)
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
      have hadj : D.gr.Adj (g m) (g b) := AR.DirData.gr_adj_of_arr harr
      have hmb : m ≠ b := fun h ↦ hadj.ne (by rw [h])
      have hprm : PR (g m) (g b) := ⟨[α], rfl, rfl⟩
      have hA' : ActInj k Y (g m) (g b) := by
        rcases Nat.lt_or_gt_of_ne hmb with h | h
        · obtain rfl := seq_consecutive hacyc hac hinj hstep hm hb h hadj
          exact (actInj_step hacyc hz1 hstep hpar (by omega)).1 harr
        · obtain rfl := seq_consecutive hacyc hac hinj hstep hb hm h hadj.symm
          exact (actInj_step hacyc hz1 hstep hpar (by omega)).2 harr
      refine ⟨b, hb, hpr.trans hprm, rfl, heq_of_eq ?_, fun u hu hu0 ↦ ?_⟩
      · have h2 : gval (g m) (g b) = e.1 :=
          (gval_eq hpar (l := [α]) ⟨rfl, rfl⟩).trans (compD_single α)
        rw [← gval_mul hpar hpr hprm, h2, eq_of_heq heq]
        rfl
      · have h3 := hA u hu hu0
        have h4 : pev (k := k) (g m) • cv k (g a) (g m) • u = cv k (g a) (g m) • u := by
          have hc4 : pev (k := k) (g m) * cv k (g a) (g m) = cv k (g a) (g m) :=
            (AR.DirData.cn_corner (D := D) (g m) (g a) (pbvec (g a) (g m))).1
          rw [← mul_smul, hc4]
        have h5 := hA' _ h4 h3
        rwa [← mul_smul, cv_mul hpar hpr hprm] at h5
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

include hpar hY hz1 hz0 hstep hac hinj hS in
omit [IsAlgClosed k] in
/-- **A clean sequence gives a line of the cover.** -/
theorem cline_of_seq : ∃ L : CLine x₀, L.n = n := by
  let D := pieceDirData (k := k) hacyc
  have hcv : D.IsConvexSet (D.Supp Y) := AR.DirData.isConvexSet_supp hac hY
  refine ⟨{ n := n
            pt := fun i ↦ pt S (g i)
            fwd := fun i ↦ decide (D.Arr (g i) (g (i + 1)))
            inj := fun a b ha hb h ↦ hinj a b ha hb (Subtype.ext h)
            arrF := fun i _ hf ↦ arr_irr hacyc (of_decide_eq_true hf)
            arrB := fun i hi hf ↦ ?_
            uniqF := fun i _ f f' hf hf' ↦ irr_unique hpar f f' hf hf'
            uniqB := fun i _ f f' hf hf' ↦ irr_unique hpar f f' hf hf'
            only := fun a b ha hb f hf ↦ ?_
            convex := ?_
            nz := fun p hp ↦ nz_line hpar hacyc hac hinj hz1 hstep p hp }, rfl⟩
  · have hn : ¬D.Arr (g i) (g (i + 1)) := of_decide_eq_false hf
    obtain ⟨w, y, h | h⟩ := hstep i hi
    · exact absurd h.1 hn
    · exact arr_irr hacyc h.1
  · let α : (pieceQuiver S).A := ⟨g a, g b, f, hf⟩
    have harr : D.Arr (g a) (g b) := parr_arrow hpar α
    have hadj : D.gr.Adj (g a) (g b) := AR.DirData.gr_adj_of_arr harr
    have hab : a ≠ b := fun h ↦ hadj.ne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · obtain rfl := seq_consecutive hacyc hac hinj hstep ha hb h hadj
      exact Or.inl ⟨rfl, decide_eq_true harr⟩
    · obtain rfl := seq_consecutive hacyc hac hinj hstep hb ha h hadj.symm
      exact Or.inr ⟨rfl, decide_eq_false fun h' ↦ AR.DirData.not_arr_cycle harr h'⟩
  · rintro _ b _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩ h1 h2
    have hbS : b ∈ S := hS _ b _ (g i).2 (g j).2 h1 h2
    have hSi : g i ∈ D.Supp Y := AR.DirData.exists_smul_ne_of_dimZ (D := D) (by
      rw [hz1 i hi]; norm_num)
    have hSj : g j ∈ D.Supp Y := AR.DirData.exists_smul_ne_of_dimZ (D := D) (by
      rw [hz1 j hj]; norm_num)
    have hb' : (⟨b, hbS⟩ : (pieceQuiver S).V) ∈ D.Supp Y :=
      hcv _ _ _ hSi hSj (rtg_of_reach hpar hacyc hS (g i).2 hbS h1)
        (rtg_of_reach hpar hacyc hS hbS (g j).2 h2)
    obtain ⟨y, hy⟩ := hb'
    by_contra hno
    have hall : ∀ m ≤ n, g m ≠ (⟨b, hbS⟩ : (pieceQuiver S).V) := fun m hm h ↦
      hno ⟨m, hm, congrArg Subtype.val h⟩
    exact AR.DirData.dimZ_ne_zero hy (hz0 _ hall)

end Build

end LargeIndecomposable.RayCat
