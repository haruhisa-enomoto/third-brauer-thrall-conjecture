module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceRun

/-!
# Exclusion of contours

A large indecomposable over a connected representation-finite convex piece of the cover cannot
exist if the ray category has a branching morphism (`false_of_branch`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module Classical Statement Graded

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)} {k : Type u} [Field k]

section Lift

variable (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y) (htf : TorsionFree (Pi1 x₀)) (hpar : ParEq S)
  (hS : Convex (S : Set (Cover x₀)))

include ℓ htf hpar hS in
/-- **A large module sees a lift of a branching morphism.** -/
theorem exists_lift_mod {x y : P} {w : x ⟶ y} (hbr : IsBranch w) {K : ℕ}
    (hK : ∀ Z : AR.FDMod k (Linearization P k), AR.IsIndecMod (Linearization P k) Z → Nontrivial Z →
      (∀ m : Z, morElt k w • m = 0) → finrank k Z ≤ K)
    (N : AR.FDMod k (PieceAlg k S)) (hN : AR.IndNT N) (hlt : K < finrank k N) :
    ∃ i j : (pieceQuiver S).V, (⟨(pt S i).y, (pt S j).y, Cover.val (gval i j)⟩ : Σ a b : P, a ⟶ b) =
      ⟨x, y, w⟩ ∧ PR i j ∧ ∃ n : N, cv k i j • n ≠ 0 := by
  obtain ⟨hw0, ⟨c, -, ⟨l, hp, he⟩, -, -⟩, -⟩ := hbr
  subst he
  let X := repOf N
  have hX : RespectsCover X := respectsCover_repOf N
  haveI : ∀ i, FiniteDimensional k (X.obj i) := fun i ↦ inferInstance
  have hind := isIndec_repOf N hN
  have hZi : AR.IsIndecMod (Linearization P k) (pdMod hS X hX) :=
    isIndecMod_pdMod ℓ hS hX htf hind
  have hfr : finrank k (pdMod hS X hX) = finrank k N := (totEquiv N).finrank_eq
  have hnt : Nontrivial (pdMod hS X hX) := by
    haveI := hN.2
    exact (totEquiv N).toEquiv.nontrivial
  have hex : ∃ m : pdMod hS X hX, morElt k (pathMor (c :: l) x y hp) • m ≠ 0 := by
    by_contra h
    push Not at h
    have := hK _ hZi hnt h
    omega
  obtain ⟨m, hm1⟩ : ∃ m : X.Tot, linAct hS hX (morElt k (pathMor (c :: l) x y hp)) m ≠ 0 := hex
  rw [morElt_of_ne k _ hw0, ← linPres_word k c l x y hp hw0, linAct_linPres, Rep.pdAct_word_eq_sum,
    LinearMap.sum_apply] at hm1
  obtain ⟨le, hle, hm2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm1
  have hmap := (Rep.mem_lab _ _ _).1 hle
  have hne : le ≠ [] := by
    rintro rfl
    simp at hmap
  have hc : ∃ i j, PathFrom i le j := by
    by_contra h
    push Not at h
    rw [Rep.pathTot_eq_zero X le h hne] at hm2
    exact hm2 rfl
  obtain ⟨i, j, hij⟩ := hc
  have hm3 := pathFrom_map (pieceProj S) le i j hij
  rw [hmap] at hm3
  obtain rfl : x = (pieceProj S).vert i :=
    pathFrom_src_unique _ _ _ _ _ (List.cons_ne_nil _ _) hp hm3
  obtain rfl : y = (pieceProj S).vert j := pathFrom_tgt_unique _ _ _ _ hp hm3
  have hvv : Cover.val (gval i j) = pathMor (c :: l) _ _ hp := by
    rw [gval_eq hpar hij]
    exact (val_compD S le i j hij).trans (pathMor_congr hmap _ hp)
  refine ⟨i, j, ?_, ⟨le, hij⟩, ?_⟩
  · exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq hvv)))
  · refine ⟨repOfEquivA N (show PieceMod X hX from m), fun h0 ↦ hm2 ?_⟩
    rw [cv_eq_of_path hpar hij hne, ← map_smul] at h0
    have h1 := (repOfEquivA N).map_eq_zero_iff.1 h0
    have h2 : pmk (k := k) (word k (pieceQuiver S) le) • (show PieceMod X hX from m) =
        (show X.Tot →ₗ[k] X.Tot from pieceAct X hX (pmk (word k (pieceQuiver S) le))) m := rfl
    rw [h2, pieceAct_mk, Rep.pdAct_id_word] at h1
    exact h1

end Lift

section Count

variable (hpar : ParEq S)
  (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)
  {T' : Set (pieceQuiver S).V} (hsub : T' ⊆ (pieceDirData (k := k) hacyc).T)
include hpar

/-- Adjacent points of a quotient have a nonzero composite. -/
lemma gval_of_arr {a b : (pieceQuiver S).V}
    (h : ∃ z, (pieceDirData (k := k) hacyc).qmap T' (pev b) * z *
      (pieceDirData (k := k) hacyc).qmap T' (pev a) ≠ 0) : gval a b ≠ 0 := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z₀, rfl⟩ := (pieceDirData (k := k) hacyc).qmap_surjective T' z
  have h0 : pev b * z₀ * pev a ≠ 0 := fun h' ↦ hz (by
    rw [← map_mul, ← map_mul, h', map_zero])
  exact (of_cn_ne_zero hpar hacyc (AR.DirData.cn_corner (D := pieceDirData (k := k) hacyc) b a z₀)
    h0).2

/-- **The degree of the underlying graph of a quotient.** -/
lemma card_adj_quot (a : ((pieceDirData (k := k) hacyc).quotAny hsub).ι) :
    (Finset.univ.filter (((pieceDirData (k := k) hacyc).quotAny hsub).gr.Adj a)).card ≤
      2 * morCard P := by
  let D := (pieceDirData (k := k) hacyc).quotAny hsub
  let v : D.ι → (pieceQuiver S).V := fun b ↦ (show T' from b).1
  have hv : Function.Injective v := Subtype.val_injective
  let F₁ : Finset D.ι := Finset.univ.filter fun b ↦ gval (v a) (v b) ≠ 0
  let F₂ : Finset D.ι := Finset.univ.filter fun b ↦ gval (v b) (v a) ≠ 0
  have hsubF : Finset.univ.filter (D.gr.Adj a) ⊆ F₁ ∪ F₂ := by
    intro b hb
    obtain ⟨-, h | h⟩ := AR.DirData.gr_adj.1 (Finset.mem_filter.1 hb).2
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        gval_of_arr hpar hacyc (T' := T') h.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        gval_of_arr hpar hacyc (T' := T') h.2⟩)
  have h1 : F₁.card ≤ morCard P := card_out_le F₁ v hv.injOn (v a) fun b hb ↦
    (Finset.mem_filter.1 hb).2
  have h2 : F₂.card ≤ morCard P := card_in_le F₂ v hv.injOn (v a) fun b hb ↦
    (Finset.mem_filter.1 hb).2
  have h3 := (Finset.card_le_card hsubF).trans (Finset.card_union_le F₁ F₂)
  exact h3.trans (by omega)

/-- Morphisms out of a point are bounded. -/
lemma card_cn_quot (a : ((pieceDirData (k := k) hacyc).quotAny hsub).ι) :
    (Finset.univ.filter fun c : ((pieceDirData (k := k) hacyc).quotAny hsub).ι ↦
      ∃ z, (pieceDirData (k := k) hacyc).Cn (show T' from c).1 (show T' from a).1 z ∧ z ≠ 0).card ≤
      morCard P := by
  let D := (pieceDirData (k := k) hacyc).quotAny hsub
  let v : D.ι → (pieceQuiver S).V := fun b ↦ (show T' from b).1
  have hv : Function.Injective v := Subtype.val_injective
  refine card_out_le _ v hv.injOn (v a) fun b hb ↦ ?_
  obtain ⟨z, hz, h0⟩ := (Finset.mem_filter.1 hb).2
  exact (of_cn_ne_zero hpar hacyc hz h0).2

end Count

section Main

variable [IsAlgClosed k] (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y) (htf : TorsionFree (Pi1 x₀))
  (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
  (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
  (hlsc : CoverLocalSC x₀)
  (hconnS : ∀ T : Set (pieceQuiver S).V, T.Nonempty →
    (∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ T ↔ (pieceQuiver S).tgt α ∈ T) →
      T = Set.univ)
  (hrep : PieceRepFin k S)
include ℓ htf hS hne hacycCov hint hlsc hconnS hrep

/-- **A branching morphism bounds indecomposables.** -/
theorem false_of_branch {x y : P} {w : x ⟶ y} (hbr : IsBranch w) {K M : ℕ}
    (hK : ∀ Z : AR.FDMod k (Linearization P k), AR.IsIndecMod (Linearization P k) Z → Nontrivial Z →
      (∀ m : Z, morElt k w • m = 0) → finrank k Z ≤ K)
    (hM : ∀ (x y : P) (l : List (quiver P).A) (h : PathFrom (D := quiver P) x l y),
      pathMor l x y h ≠ 0 → l.length < M)
    (N : AR.FDMod k (PieceAlg k S)) (hN : AR.IndNT N) (hlt : K < finrank k N)
    (hlarge : morCard P * (2 * morCard P + 1) ^ (2 * M + (K + 1) + 1) <
      Nat.card ((pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).Supp N)) : False := by
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := S) hacycCov
  let D₀ := pieceDirData (k := k) hacyc
  obtain ⟨hsub, U, hU, hfr, hs⟩ := AR.DirData.sincere_descend (A := PieceAlg k S) D₀ N hN
  have hDir := fun Y hY ↦ directing_quot hS hne hacycCov hint hlsc hconnS hrep (D₀.Supp N) Y hY
  refine AR.DirData.false_of_large_quot (D₀ := D₀) (hsub := hsub)
    (fun x y ↦ cartan_piece_le_one hacyc hpar x y) hDir (hDir U hU) hs
    (runB_piece hpar hacyc hM) (fun a ↦ card_adj_quot hpar hacyc hsub a) (by rw [hfr]; exact hlt)
    (fun a ↦ card_cn_quot hpar hacyc hsub a) (fun i j ↦ cv k i j)
    (fun i j ↦ IsBranch (Cover.val (gval i j)) ∧ PR i j)
    (fun i j ↦ AR.DirData.cn_corner (D := D₀) j i _) ?_ ?_ ?_
  · intro N' hN' hlt'
    obtain ⟨i, j, hsig, hp, n, hn⟩ := exists_lift_mod ℓ htf hpar hS hbr hK N' hN' hlt'
    refine ⟨i, j, ⟨?_, hp⟩, n, hn⟩
    exact (congrArg (fun q : Σ a b : P, a ⟶ b ↦ IsBranch q.2.2) hsig).mpr hbr
  · intro Y i j hc hact
    obtain ⟨κ, i1, i2, B, -, -⟩ := exists_branchQ hpar hS hacyc hc.1 hc.2 hact
    exact ⟨κ, i1, i2, ⟨B⟩⟩
  · rw [← Nat.card_eq_fintype_card]
    exact hlarge

end Main

section Strip

variable (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)
include hacyc

/-- Two different paths with the same ends diverge at a point. -/
lemma exists_div : ∀ (le le' : List (pieceQuiver S).A) (i j : (pieceQuiver S).V), PathFrom i le j →
    PathFrom i le' j → le ≠ le' → ∃ (p : List (pieceQuiver S).A) (i' : (pieceQuiver S).V)
      (e e' : (pieceQuiver S).A), PathFrom i p i' ∧ (pieceQuiver S).src e = i' ∧
      (pieceQuiver S).src e' = i' ∧ PR ((pieceQuiver S).tgt e) j ∧
      PR ((pieceQuiver S).tgt e') j ∧ e ≠ e'
  | [], le', i, j, h, h', hne => by
    change i = j at h
    subst h
    exact absurd h' (hacyc i le' (fun h0 ↦ hne h0.symm))
  | e :: r, [], i, j, h, h', hne => by
    change i = j at h'
    subst h'
    exact absurd h (hacyc i _ (List.cons_ne_nil _ _))
  | e :: r, e' :: r', i, j, h, h', hne => by
    by_cases hee : e = e'
    · subst hee
      obtain ⟨p, i', f, f', h1, h2, h3, h4, h5, h6⟩ := exists_div r r' _ j h.2 h'.2
        (fun h0 ↦ hne (by rw [h0]))
      exact ⟨e :: p, i', f, f', ⟨h.1, h1⟩, h2, h3, h4, h5, h6⟩
    · exact ⟨[], i, e, e', rfl, h.1, h'.1, ⟨r, h.2⟩, ⟨r', h'.2⟩, hee⟩

end Strip

/-- **A contour gives a morphism with two first arrows.** -/
theorem exists_twoFst_of_not_noContour (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y)
    (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
    (hlsc : CoverLocalSC x₀)
    (hhull : ∀ T : Finset (Cover x₀), ∃ C : Finset (Cover x₀), T ⊆ C ∧ Convex (C : Set (Cover x₀)))
    (hnc : ¬NoContour P) : ∃ (x y : P) (w : x ⟶ y), w ≠ 0 ∧ TwoFst w := by
  unfold NoContour at hnc
  push Not at hnc
  obtain ⟨l, l', x, y, h, h', he, hν, hll⟩ := hnc
  have hν' : pathMor l' x y h' ≠ 0 := he ▸ hν
  let a : Cover x₀ := ⟨x, ℓ x⟩
  let b : Cover x₀ := ⟨y, a.u ≫ cls (pathMor l x y h) hν⟩
  obtain ⟨C, hTC, hC⟩ := hhull {a, b}
  have ha : a ∈ C := hTC (by simp)
  have hb : b ∈ C := hTC (by simp)
  have hpar : ParEq C := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := C) hacycCov
  let i : (pieceQuiver C).V := ⟨a, ha⟩
  obtain ⟨le, j, hm, hp, hpt⟩ := exists_lift_piece hC l i y h hν hb
  have hb' : (⟨y, (pt C i).u ≫ cls (pathMor l' x y h') hν'⟩ : Cover x₀) ∈ C := by
    have e1 : (⟨y, (pt C i).u ≫ cls (pathMor l' x y h') hν'⟩ : Cover x₀) = b := by
      change (⟨y, a.u ≫ cls (pathMor l' x y h') hν'⟩ : Cover x₀) = ⟨y, a.u ≫ cls (pathMor l x y h) hν⟩
      rw [cls_congr he.symm hν' hν]
    rw [e1]
    exact hb
  obtain ⟨le', j', hm', hp', hpt'⟩ := exists_lift_piece hC l' i y h' hν' hb'
  have hjj : j' = j := by
    apply Subtype.ext
    refine hpt'.trans (Eq.trans ?_ hpt.symm)
    change (⟨y, a.u ≫ cls (pathMor l' x y h') hν'⟩ : Cover x₀) = ⟨y, a.u ≫ cls (pathMor l x y h) hν⟩
    rw [cls_congr he.symm hν' hν]
  subst hjj
  have hne : le ≠ le' := by
    rintro rfl
    exact hll (hm.symm.trans hm')
  obtain ⟨p, i', e, e', hp1, h1, h2, h3, h4, hee⟩ := exists_div hacyc le le' i j' hp hp' hne
  have hg : gval i j' ≠ 0 := by
    have key : ∀ (y' : P), (pt C j').y = y' → ∀ h'' : PathFrom (D := quiver P) x l y',
        pathMor l x y' h'' ≠ 0 → gval i j' ≠ 0 := by
      intro y' hy' h'' h0 g0
      subst hy'
      apply h0
      have h5 := val_compD C le i j' hp
      rw [← gval_eq hpar hp, g0, Cover.val_zero] at h5
      exact (pathMor_congr hm _ h'').symm.trans h5.symm
    exact key y (congrArg Cover.y hpt) h hν
  have hPR : PR i' j' := PR.trans ⟨[e], h1, rfl⟩ h3
  have hg' : gval i' j' ≠ 0 := by
    intro h0
    apply hg
    rw [← gval_mul hpar ⟨p, hp1⟩ hPR, h0, comp_zero]
  refine ⟨_, _, Cover.val (gval i' j'), fun h0 ↦ hg' ((val_eq_zero_iff _).1 h0), _, _,
    fst_of_arrow hpar h1 h3, fst_of_arrow hpar h2 h4, fun h0 ↦ hee ?_⟩
  exact locInj_arrow hpar hC (h1.trans h2.symm) h0

section NoContour

variable [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]

/-- **Large indecomposables exclude contours.** -/
theorem noContour_of_large (hB : IsMinimalRepInfinite B) (e : Linearization P k ≃ₐ[k] B)
    (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y) (htf : TorsionFree (Pi1 x₀))
    (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
    (hlsc : CoverLocalSC x₀)
    (hhull : ∀ T : Finset (Cover x₀), ∃ C : Finset (Cover x₀), T ⊆ C ∧ Convex (C : Set (Cover x₀)))
    (hlarge : ∀ n : ℕ, ∃ (S : Finset (Cover x₀)) (_ : Convex (S : Set (Cover x₀))) (_ : S.Nonempty)
      (_ : ∀ T : Set (pieceQuiver S).V, T.Nonempty →
        (∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ T ↔ (pieceQuiver S).tgt α ∈ T) →
          T = Set.univ) (_ : PieceRepFin k S) (N : AR.FDMod k (PieceAlg k S)), AR.IndNT N ∧
      n < Nat.card ((pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).Supp N)) :
    NoContour P := by
  by_contra hnc
  obtain ⟨x, y, w, hbr⟩ := exists_isBranch
    (exists_twoFst_of_not_noContour ℓ hacycCov hint hlsc hhull hnc)
  have hb : morElt k w ≠ 0 := by
    have := (linBasisR k P).ne_zero (⟨x, y, w, hbr.1⟩ : NZ P)
    rwa [linBasisR_apply] at this
  obtain ⟨K, hK⟩ := exists_bound_of_killed e hB hb
  obtain ⟨M, hM⟩ := exists_length_bound (P := P)
  let n : ℕ := K + morCard P * (2 * morCard P + 1) ^ (2 * M + (K + 1) + 1)
  obtain ⟨S, hS, hne, hconn, hrep, N, hN, hc⟩ := hlarge n
  have hle : Nat.card ((pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).Supp N) ≤
      finrank k N := by
    have h1 := AR.DirData.card_supp_le_finrank (D := pieceDirData (k := k)
      (piece_acyclic (S := S) hacycCov)) N
    refine le_trans (le_of_eq ?_) h1
    have hF : ((Finset.univ.filter fun c ↦ ∃ y : N,
        (pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).e c • y ≠ 0 :
          Finset (pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).ι) :
          Set (pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).ι) =
        (pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).Supp N := by
      ext c
      simp [AR.DirData.Supp]
    rw [Nat.card_coe_set_eq, ← hF, Set.ncard_coe_finset]
  exact false_of_branch ℓ htf hS hne hacycCov hint hlsc hconn hrep hbr hK hM N hN (by omega)
    (by omega)

end NoContour

end LargeIndecomposable.RayCat
