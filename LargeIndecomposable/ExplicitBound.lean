module

public import LargeIndecomposable.MainTheorems
public import LargeIndecomposable.BongartzTheorem.LongLines.WindowPair
public import LargeIndecomposable.BongartzTheorem.LongLines.LineBandRel
public import LargeIndecomposable.BongartzTheorem.Reduction.BoundedReduction
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.CriticalPieceLine

/-!
# The explicit bound `n ≤ max(30, 4 dim A)` (Corollary 1.1)

Let `B` be the minimal representation-infinite quotient of the basic corner of `A`, and
`d = dim B ≤ dim A`. The nilpotence bound of the embedding data is

* `dim` of a quotient of `B` in the nondistributive case (`SplitBasicData.exists_embeddingData_le`);
* the number of points of the band cycle in the walk case: a window of `3d` arrows of a line
  of the cover contains a good pair (`WLine.exists_goodPair_window`), and the band of a good
  pair needs no condition on contours (`exists_lineBandRel`), so the cycle has fewer than
  `3d` points;
* the number of points of a critical piece `C` in the covering case.

In the covering case, the Kronecker pair of a critical piece lives on the minimal set `T'` of
points whose quotient has unbounded indecomposables, so `n ≤ |T'|`. If `|T'| ≥ 30`, the Euler form
of that quotient is critical of type `D̃` and its long induced path gives a module line with
`|T'| - 3` arrows (`pointBrickAt_critical_line`). If that line has `3d` arrows we use its band
instead; otherwise `|T'| + 1 ≤ 3d + 3 ≤ max(30, 4d)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat RayCat.Cover RayQuiver Covering LargeIndecomposable.Graded

universe u

section Dimension

variable {P : Type} [Category.{0} P] [Limits.HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- The dimension of `B ≅ k(P)` is the number of nonzero morphisms of `P`. -/
lemma finrank_eq_card_nz (e : Linearization P k ≃ₐ[k] B) :
    Module.finrank k B = Nat.card {μ : Σ x y : P, (x ⟶ y) // μ.2.2 ≠ 0} := by
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_eq_nat_card_basis (linBasis (P := P) k)]
  exact Nat.card_congr
    { toFun := fun μ ↦ ⟨⟨μ.1, μ.2.1, μ.2.2.1⟩, μ.2.2.2⟩
      invFun := fun μ ↦ ⟨μ.1.1, μ.1.2.1, μ.1.2.2, μ.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- A window of `3 dim B` arrows gives a band with fewer than `3 dim B` points. -/
lemma exists_band_of_line {x₀ : P} (L : CLine x₀) (e : Linearization P k ≃ₐ[k] B)
    (hL : 3 * Module.finrank k B ≤ L.n) :
    ∃ M : Walk.MonomialBand k B, M.n + 2 + 1 ≤ 3 * Module.finrank k B := by
  have : ∀ x y : P, Finite (x ⟶ y) := IsRayCategory.finite_hom
  rw [finrank_eq_card_nz e] at hL ⊢
  obtain ⟨t, t', hg, ht'⟩ := L.exists_goodPair_window hL le_rfl
  obtain ⟨M, hM⟩ := exists_lineBandRel L.toWLine hg (fun hu ↦ CLine.rigid hu) e
  exact ⟨M, by omega⟩

/-- A module line with `3 dim B` arrows in a convex set gives a band with fewer than `3 dim B`
points. -/
lemma exists_band_of_mline {x₀ : P} {S : Finset (Cover x₀)} (hS : Convex (S : Set (Cover x₀)))
    (L : MLine x₀ S k) (e : Linearization P k ≃ₐ[k] B)
    (hL : 3 * Module.finrank k B ≤ L.n) :
    ∃ M : Walk.MonomialBand k B, M.n + 2 + 1 ≤ 3 * Module.finrank k B := by
  have : ∀ x y : P, Finite (x ⟶ y) := IsRayCategory.finite_hom
  rw [finrank_eq_card_nz e] at hL ⊢
  obtain ⟨t, t', hg, ht'⟩ := L.toWLine.exists_goodPair_window hL le_rfl
  obtain ⟨M, hM⟩ := exists_lineBandRel L.toWLine hg (fun hu ↦ L.rigid hS hu) e
  exact ⟨M, by omega⟩

end Dimension

/-- The walk construction has nilpotence bound the number of points of the cycle. -/
lemma Walk.MonomialBand.embeddingData_n {k : Type u} [Field k] {B : Type u} [Ring B]
    [Algebra k B] (M : Walk.MonomialBand k B) : M.toWalkData.embeddingData.n = M.n + 2 := by
  change Fintype.card (Option (Fin (M.n + 1))) = M.n + 2
  simp

/-- The covering construction of a pair on a piece has nilpotence bound at most the number of
points of the piece. -/
lemma pairCoveringData'_n {P : Type} [Category.{0} P] [Limits.HasZeroMorphisms P]
    [IsRayCategory P] [Fintype P] [DecidableEq P] {x₀ : P} {k : Type u} [Field k] {A : Type u}
    [Ring A] [Algebra k A] (e : Linearization P k ≃ₐ[k] A)
    (htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    (S : Finset (Cover x₀)) (hS : Convex (S : Set (Cover x₀)))
    (K : KroneckerPair k (pieceQuiver S))
    (h₁ : RespectsCover (K.functor.obj (Kron.Sminus k)))
    (h₂ : RespectsCover (K.functor.obj (P1K k))) :
    (pairCoveringData' e htf S hS K h₁ h₂).toCoveringData.embeddingData.n ≤ S.card := by
  classical
  change Fintype.card (FinQuiver.fullSub (pieceQuiver S) K.supp).V ≤ S.card
  refine (Fintype.card_subtype_le _).trans ?_
  change Fintype.card (S : Type) ≤ S.card
  simp

/-- The covering construction of a pair has nilpotence bound at most the size of the support
of the pair. -/
lemma pairCoveringData'_n_supp {P : Type} [Category.{0} P] [Limits.HasZeroMorphisms P]
    [IsRayCategory P] [Fintype P] [DecidableEq P] {x₀ : P} {k : Type u} [Field k] {A : Type u}
    [Ring A] [Algebra k A] (e : Linearization P k ≃ₐ[k] A)
    (htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    (S : Finset (Cover x₀)) (hS : Convex (S : Set (Cover x₀)))
    (K : KroneckerPair k (pieceQuiver S))
    (h₁ : RespectsCover (K.functor.obj (Kron.Sminus k)))
    (h₂ : RespectsCover (K.functor.obj (P1K k))) :
    (pairCoveringData' e htf S hS K h₁ h₂).toCoveringData.embeddingData.n ≤ K.supp.card := by
  classical
  change Fintype.card (FinQuiver.fullSub (pieceQuiver S) K.supp).V ≤ K.supp.card
  change Fintype.card {i // i ∈ K.supp} ≤ K.supp.card
  rw [Fintype.card_coe]

/-- **The distributive case with the explicit bound.** -/
theorem exists_embeddingData_distributive_bounded
    (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
    (hB : IsMinimalRepInfinite B) (hd : IsDistribIdeals B) :
    ∃ E : EmbeddingData k B, E.n + 1 ≤ max 30 (4 * Module.finrank k B) := by
  classical
  have hι := S.nonempty_of_minimal hB
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  obtain ⟨e⟩ := algebraIsLinearization_of_mulBasis twistedMulBasisExists
      (crownSecondCohomologyVanishes_of (crownLongSecondCohomologyVanishes_of
        (bongartzProposition2_of twistedMulBasisExists
          (longMorphismNotInContour_of_mulBasis twistedMulBasisExists)))) k B ι S hB hd
  let x₀ : RaySmall.{0} S.toIdempotents.RayCategory :=
    ⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩
  have hfree : ∀ X : FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory),
      IsFreeGroup (End X) := by
    by_cases hCB : ChainBounded S.toIdempotents.RayCategory
    · exact S.small_isFreeGroup_end hd hB hCB
    · exact crownCase_of (crownLongCase_of (bongartzProposition2_of twistedMulBasisExists
        (longMorphismNotInContour_of_mulBasis twistedMulBasisExists))) k B ι S hB hd hCB
  have htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1 := fun g hg n hn ↦
    aut_pow_ne_one_of_isFreeGroup_end _ (hfree _) g hg n hn
  -- the walk case from a long line
  have hband : ∀ L : CLine x₀, 3 * Module.finrank k B ≤ L.n →
      ∃ E : EmbeddingData k B, E.n + 1 ≤ max 30 (4 * Module.finrank k B) := by
    intro L hL
    obtain ⟨M, hM⟩ := exists_band_of_line L e hL
    refine ⟨M.toWalkData.embeddingData, ?_⟩
    rw [Walk.MonomialBand.embeddingData_n]
    omega
  by_cases h : ∃ n, ∃ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) ∧ ¬PieceRepFin k C ∧
      C.card = n
  · obtain ⟨C, hC1, hC2, hC3⟩ := Nat.find_spec h
    have hmin : ∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < C.card →
        PieceRepFin k C' := fun C' hC' hlt ↦ by
      by_contra hC''
      exact Nat.find_min h (hC3 ▸ hlt) ⟨C', hC', hC'', rfl⟩
    obtain ⟨T', x, Vr, hP, hx, hsupp, hcase⟩ := pointBrickAt_critical_line hC1
      (nonempty_of_not_repFin hC2) (coverIsAcyclic k B ι S hB hd x₀)
      (intervalFinite_of_hull (intervalFiniteCover k B ι S hB hd e x₀ htf))
      (coverLocallySimplyConnected k B ι S hB hd x₀) hC2 hmin
    obtain ⟨K, h₁, h₂, hK⟩ := pair_of_pointBrickAt hP
    have hKT : K.supp.card ≤ T'.ncard := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard (fun i hi ↦ ?_) (Set.toFinite T')
      rcases hK i hi with h | h
      · rw [h]; exact hx
      · exact hsupp i h
    have hpair : ∃ E : EmbeddingData k B, E.n ≤ T'.ncard :=
      ⟨_, (pairCoveringData'_n_supp e htf C hC1 K h₁ h₂).trans hKT⟩
    rcases hcase with hsmall | ⟨L, hL⟩
    · obtain ⟨E, hE⟩ := hpair
      exact ⟨E, by omega⟩
    · by_cases hLn : 3 * Module.finrank k B ≤ L.n
      · obtain ⟨M, hM⟩ := exists_band_of_mline hC1 L e hLn
        refine ⟨M.toWalkData.embeddingData, ?_⟩
        rw [Walk.MonomialBand.embeddingData_n]
        omega
      · obtain ⟨E, hE⟩ := hpair
        exact ⟨E, by omega⟩
  · push Not at h
    have hpiece : ∀ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) → PieceRepFin k C :=
      fun C hC ↦ by
        by_contra h'
        exact h _ C hC h' rfl
    have : Nonempty (RaySmall.{0} S.toIdempotents.RayCategory) := ⟨x₀⟩
    have hcon : IsConnected (FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory)) :=
      isConnected_fund_of_nzConnected fun x y ↦ RaySmall.nzConnected
        (S.nzConnected hd (fun e he hc ↦ hB.central_idempotent e he hc) x.as y.as)
    have hℓ : ∀ y, Nonempty (vtx x₀ ⟶ vtx y) := fun y ↦
      nonempty_hom_of_preconnected_groupoid _ _
    let ℓ : ∀ y, vtx x₀ ⟶ vtx y := fun y ↦ (hℓ y).some
    have htf' : TorsionFree (Pi1 x₀) := fun g n hn hg ↦ by
      by_contra h1; exact htf g h1 n hn hg
    have hsupp : ∀ n : ℕ, ∃ (M : AR.FDMod k (Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k))
        (μ : GrMod (rayGrAlg ℓ k) M), IsGrIndec μ ∧ Nontrivial M ∧ n < (suppF k ℓ μ).card := by
      intro n
      by_contra hno
      push Not at hno
      obtain ⟨r, Y, hY⟩ := repFin_of_bounded_support (ℓ := ℓ) htf'
        (intervalFiniteCover k B ι S hB hd e x₀ htf) hpiece n fun M μ hμ hM ↦ hno M μ hμ hM
      exact hB.1 (isRepresentationFinite_of_ringEquiv e.toRingEquiv
        (AR.isRepresentationFinite_of_fdList Y hY))
    obtain ⟨L, hL⟩ := linesOfEveryLength k B ι S hB hd e x₀ htf hpiece ℓ hsupp
      (3 * Module.finrank k B)
    exact hband L hL

/-- **Corollary 1.1 (= Corollary 5.6) with the explicit bound** `n ≤ max(30, 4 dim A)`. -/
theorem corollaryCountBounded : CorollaryCountBounded.{u} := by
  intro k _ _ A _ _ _ hA
  obtain ⟨E, hE⟩ := exists_embeddingData_bounded_of
    (fun k _ _ B _ _ _ ι _ S hB hd ↦ by
      classical
      exact exists_embeddingData_distributive_bounded k B ι S hB hd) (k := k) A hA
  refine ⟨E.n + 1, Nat.succ_le_succ (Nat.zero_le _), hE, fun κ hκ ↦ ⟨?_, fun hk ι M _ _ _ _ hni hdim ↦
    card_le_two_pow_of_pairwise_not_iso κ hκ hk M hni hdim⟩⟩
  obtain ⟨ι, T, hT, hinf, hι, hdim, hni⟩ := E.exists_noniso_family κ hκ
  exact ⟨ι, fun i ↦ FT E (hT i) (hinf i), fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ ModuleCat.moduleOfAlgebraModule _, fun _ ↦ ModuleCat.isScalarTower_of_algebra_moduleCat _,
    hι, hni, fun i ↦ ⟨(rank_FT E (hT i) (hinf i)).trans (hdim i),
      isIndecomposable_brick E (hT i) (hinf i), endLocalBounded_FT E (hT i) (hinf i)⟩⟩

end LargeIndecomposable
