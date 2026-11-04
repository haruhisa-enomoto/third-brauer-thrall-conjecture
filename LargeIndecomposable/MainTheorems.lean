module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineBuild
public import LargeIndecomposable.BongartzTheorem.LongLines.LinesToBands
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PointBrickData
public import LargeIndecomposable.BongartzTheorem.Reduction.Count

/-!
# Long lines

In a minimal representation-infinite distributive algebra with representation-finite cover pieces
and unbounded graded indecomposables, the universal cover has lines of every length
(`linesOfEveryLength`). This removes the last input of Theorem A.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module Classical Statement Graded

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)} {k : Type u} [Field k]

/-- **A long line in a sincere piece.** -/
theorem exists_cline [IsAlgClosed k] (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
    (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
    (hlsc : CoverLocalSC x₀) (hnc : NoContour P) (hrep : PieceRepFin k S)
    (N : AR.FDMod k (PieceAlg k S)) (hN : AR.IndNT N)
    (hsinc : ∀ i : (pieceQuiver S).V, ∃ y : N, pev (k := k) i • y ≠ 0) {M : ℕ}
    (hM : ∀ (x y : P) (l : List (quiver P).A) (h : PathFrom (D := quiver P) x l y),
      pathMor l x y h ≠ 0 → l.length < M) {m : ℕ}
    (hlarge : (2 * morCard P + 1) ^ (2 * m + 2 * M + 1) < S.card) :
    ∃ L : CLine x₀, m ≤ L.n := by
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := S) hacycCov
  let D := pieceDirData (k := k) hacyc
  have hconnS : ∀ T : Set (pieceQuiver S).V, T.Nonempty →
      (∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ T ↔ (pieceQuiver S).tgt α ∈ T) →
        T = Set.univ := by
    rintro T ⟨t, ht⟩ hcl
    by_contra hT
    obtain ⟨u, hu⟩ : ∃ u, u ∉ T := by
      by_contra h
      push Not at h
      exact hT (Set.eq_univ_of_forall h)
    obtain ⟨yt, hyt⟩ := hsinc t
    obtain ⟨yu, hyu⟩ := hsinc u
    obtain ⟨a, b, ha, hb, w, y, h | h⟩ := AR.DirData.exists_cross (D := D) hN.1 T ht hyt hu hyu
    · obtain ⟨α, rfl, rfl, -⟩ := h.1
      exact hb ((hcl α).1 ha)
    · obtain ⟨α, rfl, rfl, -⟩ := h.1
      exact hb ((hcl α).2 ha)
  obtain ⟨𝒞, h𝒞, hall⟩ := exists_all_preproj (k := k) hS hne hacycCov hint hlsc hconnS hrep
  have hDir : ∀ Y : AR.FDMod k (PieceAlg k S), AR.IndNT Y → AR.Directing Y := fun Y hY ↦
    h𝒞.directing (hall Y hY)
  have hT : ∀ x, x ∈ D.T := fun _ ↦ Set.mem_univ _
  have hC : ∀ x y, AR.cartan D y x ≤ 1 := fun x y ↦ cartan_piece_le_one hacyc hpar x y
  have hac := gr_isAcyclic (k := k) hacyc hnc hS hlsc
  have hR := runB_piece (k := k) hpar hacyc hM
  have hcard : Fintype.card D.ι = S.card := Fintype.card_coe S
  obtain ⟨f, hadj, hinj⟩ := AR.DirData.exists_long_path (D := D)
    (AR.DirData.reachable_of_sincere hN.1 hsinc) (card_adj_piece hpar hacyc)
    (2 * m + 2 * M + 1) (by rw [hcard]; exact hlarge)
  obtain ⟨Y, n, g, hY, hmn, hginj, hz1, hz0, hstep⟩ := AR.DirData.exists_line_of_path hT hC hDir
    (hDir N hN) hsinc hac hR (ℓ := m) le_rfl hadj hinj
  obtain ⟨L, hL⟩ := cline_of_seq hpar hacyc hS hac hY.1 hginj hz1 hz0 hstep
  exact ⟨L, by omega⟩

/-- The support of the module of a representation. -/
lemma mem_supp_toFDMod (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] →
    ¬PathFrom i l i) (X : Rep k (pieceQuiver S)) (hX : RespectsCover X)
    [∀ i, FiniteDimensional k (X.obj i)] {i : (pieceQuiver S).V} (hi : Nontrivial (X.obj i)) :
    i ∈ (pieceDirData (k := k) hacyc).Supp (toFDMod X hX) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : X.obj i)
  refine ⟨show PieceMod X hX from Pi.single i v, fun h0 ↦ hv ?_⟩
  have h1 : pieceAct X hX (RingQuot.mkAlgHom k _ (vertex k (pieceQuiver _) i))
      (Pi.single i v) i = v := by
    rw [pieceAct_mk, Rep.pdAct_vertex, Rep.pdVert_apply]
    exact (if_pos rfl).trans (Pi.single_eq_same _ _)
  rw [← h1]
  exact congrFun h0 i

/-- **An indecomposable lives on a connected convex piece.** -/
theorem exists_connected_piece (hpar : ParEq S)
    (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)
    (hS : Convex (S : Set (Cover x₀))) (X : Rep k (pieceQuiver S)) (hind : X.IsIndec) :
    ∃ S₀ : Finset (Cover x₀), ∃ (hsub : S₀ ⊆ S), Convex (S₀ : Set (Cover x₀)) ∧ S₀.Nonempty ∧
      (∀ T : Set (pieceQuiver S₀).V, T.Nonempty →
        (∀ α : (pieceQuiver S₀).A, (pieceQuiver S₀).src α ∈ T ↔ (pieceQuiver S₀).tgt α ∈ T) →
          T = Set.univ) ∧ SuppIn S₀ X := by
  let D := pieceDirData (k := k) hacyc
  obtain ⟨⟨a, ha⟩, -⟩ := id hind
  let R : Set (pieceQuiver S).V := {c | D.gr.Reachable a c}
  have hcl : ∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ R ↔ (pieceQuiver S).tgt α ∈ R := by
    intro α
    have hadj : D.gr.Adj ((pieceQuiver S).src α) ((pieceQuiver S).tgt α) :=
      AR.DirData.gr_adj_of_arr (parr_arrow hpar α)
    exact ⟨fun h ↦ SimpleGraph.Reachable.trans h hadj.reachable,
      fun h ↦ SimpleGraph.Reachable.trans h hadj.symm.reachable⟩
  have haR : a ∈ R := SimpleGraph.Reachable.refl a
  have hsupp : SuppIn (ptsOf R) X := by
    rcases suppIn_or_suppIn hind R hcl with h | h
    · exact h
    · have h1 := h a (by
        intro h2
        exact (mem_ptsOf a).1 h2 haR)
      exact absurd h1 (not_subsingleton_iff_nontrivial.2 ha)
  have hsubS := ptsOf_subset R
  refine ⟨ptsOf R, hsubS, convex_ptsOf hS R hcl, ⟨_, (mem_ptsOf a).2 haR⟩, ?_, hsupp⟩
  rintro T ⟨t, ht⟩ hclT
  let inc := incH hsubS
  have hincR : ∀ i : (pieceQuiver (ptsOf R)).V, inc.vert i ∈ R := fun i ↦
    (mem_ptsOf (inc.vert i)).1 (show ptsOf R from i).2
  let Z : Set (pieceQuiver S).V := {z | ∃ i ∈ T, inc.vert i = z}
  have hZ : ∀ z ∈ Z, ∀ w, D.gr.Adj z w → w ∈ Z := by
    rintro z ⟨i, hi, rfl⟩ w hadj
    have hwR : w ∈ R := SimpleGraph.Reachable.trans (hincR i) hadj.reachable
    let j : (pieceQuiver (ptsOf R)).V := ⟨(show S from w).1, (mem_ptsOf w).2 hwR⟩
    refine ⟨j, ?_, rfl⟩
    rcases (AR.DirData.gr_adj.1 hadj).2 with h | h
    · obtain ⟨α, h1, h2, -⟩ := h
      subst h2
      obtain ⟨u, v, f⟩ := α
      change u = inc.vert i at h1
      subst h1
      exact (hclT ⟨i, j, f⟩).1 hi
    · obtain ⟨α, h1, h2, -⟩ := h
      subst h1
      obtain ⟨u, v, f⟩ := α
      change v = inc.vert i at h2
      subst h2
      exact (hclT ⟨j, i, f⟩).2 hi
  refine Set.eq_univ_of_forall fun i ↦ ?_
  have hr : D.gr.Reachable (inc.vert t) (inc.vert i) :=
    SimpleGraph.Reachable.trans (hincR t).symm (hincR i)
  obtain ⟨i', hi', he⟩ := AR.DirData.mem_of_reachable hZ ⟨t, ht, rfl⟩ hr
  have : i' = i := Subtype.ext (congrArg (fun z : (pieceQuiver S).V ↦ (show S from z).1) he)
  exact this ▸ hi'

end LargeIndecomposable.RayCat

namespace LargeIndecomposable

open CategoryTheory Limits RayCat Cover RayQuiver Covering FinQuiver Module Statement Graded

universe u

/-- **Long lines exist.** -/
theorem linesOfEveryLength : LinesOfEveryLength.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf hpiece ℓ hsupp m
  have hIF := intervalFiniteCover k B ι S hB hd e x₀ htf
  have hacycCov := coverIsAcyclic k B ι S hB hd x₀
  have hlsc := coverLocallySimplyConnected k B ι S hB hd x₀
  have hint := intervalFinite_of_hull hIF
  have htf' : TorsionFree (Pi1 x₀) := fun x n hn h ↦ by
    by_contra hx
    exact htf x hx n hn h
  have hlarge : ∀ n : ℕ, ∃ (C : Finset (Cover x₀)) (_ : Cover.Convex (C : Set (Cover x₀)))
      (_ : C.Nonempty)
      (_ : ∀ T : Set (pieceQuiver C).V, T.Nonempty →
        (∀ α : (pieceQuiver C).A, (pieceQuiver C).src α ∈ T ↔ (pieceQuiver C).tgt α ∈ T) →
          T = Set.univ) (_ : PieceRepFin k C) (N : AR.FDMod k (PieceAlg k C)), AR.IndNT N ∧
      n < Nat.card ((pieceDirData (k := k) (piece_acyclic (S := C) hacycCov)).Supp N) := by
    intro n
    classical
    obtain ⟨M, γ, hγ, hMnt, hcard⟩ := hsupp n
    set T := suppF k ℓ γ
    obtain ⟨C, hTC, hC⟩ := hIF T
    have hsub : ∀ b, W ℓ k γ b ≠ ⊥ → b ∈ C := fun b hb ↦
      hTC (Finset.mem_filter.2 ⟨mem_suppSet_of_W hb, hb⟩)
    haveI hfd : ∀ i, FiniteDimensional k ((grRep ℓ k γ C).obj i) := fun i ↦
      inferInstanceAs (FiniteDimensional k (W ℓ k γ _))
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨a, haT⟩ := hTne
    have ha : W ℓ k γ a ≠ ⊥ := (Finset.mem_filter.1 haT).2
    have hind : (grRep ℓ k γ C).IsIndec := by
      refine ⟨⟨⟨a, hsub a ha⟩, ?_⟩, fun φ hφ ↦ grRep_idem k hsub hγ φ hφ⟩
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
      exact ⟨⟨⟨w, hw⟩, 0, fun h ↦ hw0 (congrArg Subtype.val h)⟩⟩
    have hle : T.card ≤ (Finset.univ.filter fun i : (pieceQuiver C).V ↦
        Nontrivial ((grRep ℓ k γ C).obj i)).card := by
      rw [← Finset.card_map (⟨fun i ↦ (show C from i).1, fun i j h ↦ Subtype.ext h⟩ :
        (pieceQuiver C).V ↪ Cover x₀)]
      refine Finset.card_le_card fun b hb ↦ ?_
      have hbW : W ℓ k γ b ≠ ⊥ := (Finset.mem_filter.1 hb).2
      rw [Finset.mem_map]
      refine ⟨⟨b, hsub b hbW⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      change Nontrivial (W ℓ k γ b)
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbW
      exact ⟨⟨⟨w, hw⟩, 0, fun h ↦ hw0 (congrArg Subtype.val h)⟩⟩
    have hparC : ParEq C := parEq_of_cover hacycCov hint hlsc
    have hacycC := piece_acyclic (S := C) hacycCov
    obtain ⟨S₀, hs₀, hconv, hne, hconn, hsp⟩ :=
      exists_connected_piece (k := k) hparC hacycC hC (grRep ℓ k γ C) hind
    have hX : RespectsCover (grRep ℓ k γ C) := respectsCover_grRep
    have hYc := respectsCover_resP hs₀ (grRep ℓ k γ C) hX
    have hYi := isIndec_resP hs₀ hsp hind
    have hacyc₀ := piece_acyclic (S := S₀) hacycCov
    refine ⟨S₀, hconv, hne, hconn, hpiece S₀ hconv, toFDMod _ hYc, indNT_toFDMod hYc hYi, ?_⟩
    rw [Nat.card_coe_set_eq]
    let inc := incH hs₀
    have himg : ((Finset.univ.filter fun i : (pieceQuiver C).V ↦
        Nontrivial ((grRep ℓ k γ C).obj i) : Finset _) : Set (pieceQuiver C).V) ⊆
        inc.vert '' (pieceDirData (k := k) hacyc₀).Supp (toFDMod _ hYc) := by
      intro i hi
      have hnt : Nontrivial ((grRep ℓ k γ C).obj i) := (Finset.mem_filter.1 hi).2
      have hmem : (show C from i).1 ∈ S₀ := by
        by_contra h
        exact not_subsingleton_iff_nontrivial.2 hnt (hsp i h)
      let j : (pieceQuiver S₀).V := ⟨(show C from i).1, hmem⟩
      exact ⟨j, mem_supp_toFDMod hacyc₀ _ hYc (i := j) hnt, rfl⟩
    have h1 := Set.ncard_le_ncard himg (Set.toFinite _)
    have h2 := Set.ncard_image_le (f := inc.vert)
      (s := (pieceDirData (k := k) hacyc₀).Supp (toFDMod _ hYc)) (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h1
    exact lt_of_lt_of_le hcard (hle.trans (h1.trans h2))
  have hnc := noContour_of_large hB e ℓ htf' hacycCov hint hlsc hIF hlarge
  obtain ⟨M, hM⟩ := exists_length_bound (P := RaySmall.{0} S.toIdempotents.RayCategory)
  obtain ⟨C, hC, -, -, -, N, hN, hc⟩ :=
    hlarge ((2 * morCard (RaySmall.{0} S.toIdempotents.RayCategory) + 1) ^ (2 * m + 2 * M + 1))
  have hpar : ParEq C := parEq_of_cover hacycCov hint hlsc
  obtain ⟨S', N', hS', hne', hN', hs', hle⟩ := exists_sincere_piece hpar
    (piece_acyclic (S := C) hacycCov) hnc hC hlsc hacycCov N hN
  exact exists_cline hS' hne' hacycCov hint hlsc hnc (hpiece S' hS') N' hN' hs' hM (by omega)

/-- **Theorem A.** -/
theorem theoremA : TheoremA.{u} :=
  theoremA_of_bongartz (bongartzDistributive_of_coverDichotomy (coverDichotomy_of
    (RayCat.criticalPieceCarriesPair_of_pointBrickData RayCat.pointBrickData)
    (repFinitePiecesGiveBand_of (intervalFiniteCover_of_stage simplyConnectedStageStep) (repFinitePiecesGiveBandCore_of_longLine linesOfEveryLength))))

/-- **Corollary 1.1**, dimension part. -/
theorem corollaryDimension : CorollaryDimension.{u} :=
  corollaryDimension_of_bongartz' (bongartzDistributive_of_coverDichotomy (coverDichotomy_of
    (RayCat.criticalPieceCarriesPair_of_pointBrickData RayCat.pointBrickData)
    (repFinitePiecesGiveBand_of (intervalFiniteCover_of_stage simplyConnectedStageStep) (repFinitePiecesGiveBandCore_of_longLine linesOfEveryLength))))

/-- **Corollary 5.6**, without the number of modules and the explicit bound. -/
theorem corollaryRadical : CorollaryRadical.{u} :=
  corollaryRadical_of_bongartz' (bongartzDistributive_of_coverDichotomy (coverDichotomy_of
    (RayCat.criticalPieceCarriesPair_of_pointBrickData RayCat.pointBrickData)
    (repFinitePiecesGiveBand_of (intervalFiniteCover_of_stage simplyConnectedStageStep) (repFinitePiecesGiveBandCore_of_longLine linesOfEveryLength))))

/-- **Corollary 5.6**, without the explicit bound: `2^κ` pairwise non-isomorphic
indecomposable modules in every infinite dimension `κ`. -/
theorem corollaryCount : CorollaryCount.{u} :=
  corollaryCount_of (distributiveEmbeddingData_of_bongartz (bongartzDistributive_of_coverDichotomy
    (coverDichotomy_of (RayCat.criticalPieceCarriesPair_of_pointBrickData RayCat.pointBrickData)
      (repFinitePiecesGiveBand_of (intervalFiniteCover_of_stage simplyConnectedStageStep)
        (repFinitePiecesGiveBandCore_of_longLine linesOfEveryLength)))))

end LargeIndecomposable
