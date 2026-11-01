module

public import LargeIndecomposable.Coverings.Pieces.PieceModRep
public import LargeIndecomposable.Coverings.Pieces.PieceSepCover
public import LargeIndecomposable.DirectedAlgebras.Preprojective.PreprojDir
public import LargeIndecomposable.BongartzTheorem.Reduction.DichotomySteps

/-!
# Representation-finite pieces are representation-directed

For a module `M` over the piece algebra, the total space of `repOf M` is `M`, and the push-down
action of a path-algebra element on it is the action of its class (`totToMod_pdAct`). So an
endomorphism of `repOf M` gives one of `M` (`endOfRep`), and an indecomposable `M` gives an
indecomposable representation (`isIndec_repOf`). With representation-finiteness this bounds the
length of indecomposables, and with a preprojective component every indecomposable module over
a connected representation-finite convex piece is directing (`directing_piece`).
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

variable (M : AR.FDMod k (PieceAlg k S))

lemma totToMod_idm (v : (pieceQuiver S).V) (x : (repOf M).Tot) :
    totToMod M ((repOf M).idm v x) = pev (k := k) v • totToMod M x := by
  change ∑ i : (pieceQuiver S).V, val M ((repOf M).idm v x i) =
    pev (k := k) v • ∑ j : (pieceQuiver S).V, val M (x j)
  rw [Finset.smul_sum, Finset.sum_eq_single v, Finset.sum_eq_single v]
  · rw [Rep.idm_apply, Pi.single_eq_same, ev_smul_val]
  · intro j _ hj
    rw [← ev_smul_val M (x j), ← mul_smul, ev_mul_ev, if_neg (Ne.symm hj), zero_smul]
  · simp
  · intro j _ hj
    rw [Rep.idm_apply, Pi.single_eq_of_ne hj, val_zero]
  · simp

/-- **The push-down action on the total space is the action on `M`.** -/
lemma totToMod_pdAct (z : (pieceQuiver S).PathAlgebra k) (x : (repOf M).Tot) :
    totToMod M ((repOf M).pdAct (FinQuiver.Hom.id _) z x) =
      (RingQuot.mkAlgHom k (fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0)
        z) • totToMod M x := by
  have hz : z ∈ vwSpan k (Q := pieceQuiver S) := by rw [vwSpan_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · rw [Rep.pdAct_vertex, Rep.pdVert_id, totToMod_idm]
    · rw [Rep.pdAct_id_word, totToMod_pathTot]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, LinearMap.add_apply, map_add, ha, hb, add_smul]
  | smul c a _ ha =>
    rw [map_smul, map_smul, LinearMap.smul_apply, map_smul, ha, smul_assoc]

/-- The endomorphism of `M` given by an endomorphism of `repOf M`. -/
def endOfRep (φ : repOf M ⟶ repOf M) : M →ₗ[PieceAlg k S] M where
  toFun m := totToMod M (φ.tot (modToTot M m))
  map_add' m m' := by simp only [map_add]
  map_smul' a m := by
    obtain ⟨z, rfl⟩ := RingQuot.mkAlgHom_surjective k _ a
    have h1 : modToTot M ((RingQuot.mkAlgHom k
        (fun a b : (pieceQuiver S).PathAlgebra k ↦ a ∈ relGens k S ∧ b = 0) z) • m) =
        (repOf M).pdAct (FinQuiver.Hom.id _) z (modToTot M m) := by
      apply (totEquiv M).injective
      change totToMod M (modToTot M _) = totToMod M _
      rw [totToMod_modToTot, totToMod_pdAct, totToMod_modToTot]
    have h2 := Rep.commute_pdAct (FinQuiver.Hom.id _) (repOf M) φ.tot
      (Rep.Hom.isPdHom_tot _ φ).1 (Rep.Hom.isPdHom_tot _ φ).2 z
    rw [RingHom.id_apply, h1]
    change totToMod M ((φ.tot ∘ₗ (repOf M).pdAct (FinQuiver.Hom.id _) z) (modToTot M m)) = _
    rw [h2, LinearMap.comp_apply, totToMod_pdAct]

lemma tot_eq_endOfRep (φ : repOf M ⟶ repOf M) (x : (repOf M).Tot) :
    φ.tot x = modToTot M (endOfRep M φ (totToMod M x)) := by
  change φ.tot x = modToTot M (totToMod M (φ.tot (modToTot M (totToMod M x))))
  rw [modToTot_totToMod, modToTot_totToMod]

/-- **Indecomposable modules give indecomposable representations.** -/
theorem isIndec_repOf (hM : AR.IndNT M) : (repOf M).IsIndec := by
  refine ⟨?_, fun e he ↦ ?_⟩
  · haveI := hM.2
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    obtain ⟨i, hi⟩ : ∃ i, pev (k := k) i • m ≠ 0 := by
      by_contra h
      push_neg at h
      apply hm
      rw [← one_smul (PieceAlg k S) m, ← sum_ev, Finset.sum_smul]
      exact Finset.sum_eq_zero fun i _ ↦ h i
    exact ⟨i, ⟨⟨⟨pev (k := k) i • m, m, rfl⟩, 0, fun h ↦ hi (congrArg Subtype.val h)⟩⟩⟩
  · have hgg : ∀ m, endOfRep M e (endOfRep M e m) = endOfRep M e m := by
      intro m
      change totToMod M (e.tot (modToTot M (totToMod M (e.tot (modToTot M m))))) =
        totToMod M (e.tot (modToTot M m))
      have hee : ∀ y, e.tot (e.tot y) = e.tot y := fun y ↦ by
        rw [← LinearMap.comp_apply, ← Rep.Hom.tot_comp, he]
      rw [modToTot_totToMod, hee]
    have hidem : IsIdempotentElem (endOfRep M e) := LinearMap.ext hgg
    rcases hM.1 _ _ (LinearMap.IsIdempotentElem.isCompl hidem) with h | h
    · left
      intro i
      have hg0 : endOfRep M e = 0 := LinearMap.range_eq_bot.1 h
      ext v
      have := congrFun (tot_eq_endOfRep M e (Pi.single i v)) i
      rw [hg0, LinearMap.zero_apply, map_zero, Rep.Hom.tot_apply, Pi.single_eq_same] at this
      exact this
    · right
      have hinj : Function.Injective (endOfRep M e) := LinearMap.ker_eq_bot.1 h
      have hg1 : ∀ m, endOfRep M e m = m := fun m ↦ hinj (hgg m)
      ext i v
      have := congrFun (tot_eq_endOfRep M e (Pi.single i v)) i
      rw [hg1, modToTot_totToMod, Rep.Hom.tot_apply, Pi.single_eq_same] at this
      exact this

instance finiteDimensional_repOf (i : (pieceQuiver S).V) :
    FiniteDimensional k ((repOf M).obj i) :=
  inferInstanceAs (FiniteDimensional k (LinearMap.range (actK M (pev (k := k) i))))

omit M in
/-- Isomorphic representations have isomorphic total spaces. -/
def totEquivOfIso {X Y : Rep k (pieceQuiver S)} (φ : X ≅ Y) : X.Tot ≃ₗ[k] Y.Tot :=
  LinearEquiv.ofLinear φ.hom.tot φ.inv.tot
    (by rw [← Rep.Hom.tot_comp, φ.inv_hom_id, Rep.Hom.tot_id])
    (by rw [← Rep.Hom.tot_comp, φ.hom_inv_id, Rep.Hom.tot_id])

omit M in
/-- **Representation-finite pieces have bounded representation length.** -/
theorem finrank_le_of_pieceRepFin (hrep : PieceRepFin k S) :
    ∃ b, ∀ N : AR.FDMod k (PieceAlg k S), AR.IndNT N → Module.finrank k N ≤ b := by
  obtain ⟨n, Y, hY⟩ := hrep
  refine ⟨Finset.univ.sup fun j ↦ Module.finrank k (Y j).Tot, fun N hN ↦ ?_⟩
  obtain ⟨j, ⟨φ⟩⟩ := hY (repOf N) (fun i ↦ inferInstance) (respectsCover_repOf N)
    (isIndec_repOf N hN)
  rw [← (totEquiv N).finrank_eq, (totEquivOfIso φ).finrank_eq]
  exact Finset.le_sup (f := fun j ↦ Module.finrank k (Y j).Tot) (Finset.mem_univ j)

omit M in
/-- **Representation-finite connected convex pieces are representation-directed.** -/
theorem directing_piece (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
    (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
    (hlsc : CoverLocalSC x₀) (hrep : PieceRepFin k S)
    (hconnS : ∀ T : Set (pieceQuiver S).V, T.Nonempty →
      (∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ T ↔ (pieceQuiver S).tgt α ∈ T) →
        T = Set.univ)
    (N : AR.FDMod k (PieceAlg k S)) (hN : AR.IndNT N) : AR.Directing N := by
  obtain ⟨𝒞, h𝒞⟩ := piece_preprojComp (k := k) hS hne hacycCov hint hlsc
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := S) hacycCov
  let D := pieceDirData (k := k) hacyc
  refine AR.directing_of_preproj D.e D.idem D.sum (fun x ↦ D.projIndNT x (Set.mem_univ x))
    (fun T hT hcl ↦ hconnS T hT fun α ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩)
    (finrank_le_of_pieceRepFin hrep) h𝒞 N hN
  · exact hcl _ _ h (Or.inr (D.arrNe _ _ (parr_arrow hpar α)))
  · exact hcl _ _ h (Or.inl (D.arrNe _ _ (parr_arrow hpar α)))

end LargeIndecomposable.RayCat
