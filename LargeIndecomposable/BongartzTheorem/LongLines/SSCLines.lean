module

public import LargeIndecomposable.BongartzTheorem.LongLines.LinesToBands

/-!
# Long lines from the large-line theorem for ssc algebras

`SSCNode` is Bongartz's large-line theorem for simply connected sincere representation-finite
algebras (BO13b, Theorem `ssc`), applied to the support of an indecomposable representation of a
convex piece of the universal cover (the support of a directing module is convex, BO13b §1): an
indecomposable whose support has at least `1000` points lives on a line with at least a sixth of
that many points. Graded indecomposables with unbounded supports give such representations on
convex hulls (`grRep`), so `SSCNode` gives `LongLineNode` (`longLineNode_of_ssc`).

`SSCNode` is not proved in this library. The final proof does not use it:
`LongLineNode` is proved directly in `MainTheorems.lean`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat RayCat.Cover RayQuiver Covering LargeIndecomposable.Graded
  Classical

universe u

/-- **The large-line theorem for ssc algebras** (BO13b, Theorem `ssc`), on convex pieces. -/
def SSCNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      ∀ (_ : Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k ≃ₐ[k] B)
        (x₀ : RaySmall.{0} S.toIdempotents.RayCategory),
        (∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
        (∀ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) → PieceRepFin k C) →
        ∀ (C : Finset (Cover x₀)), Convex (C : Set (Cover x₀)) →
        ∀ (X : Rep k (pieceQuiver C)), (∀ i, FiniteDimensional k (X.obj i)) → RespectsCover X →
          X.IsIndec →
          1000 ≤ (Finset.univ.filter fun i : (pieceQuiver C).V ↦ Nontrivial (X.obj i)).card →
          ∃ L : CLine x₀, (∀ a ≤ L.n, L.pt a ∈ C) ∧
            (Finset.univ.filter fun i : (pieceQuiver C).V ↦ Nontrivial (X.obj i)).card ≤
              6 * (L.n + 1)

/-- **Long lines from the ssc theorem.** -/
theorem longLineNode_of_ssc (hS : SSCNode.{u}) : LongLineNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf hpiece ℓ hsupp m
  have hIF := hullNode k B ι S hB hd e x₀ htf
  obtain ⟨M, γ, hγ, hMnt, hcard⟩ := hsupp (6 * m + 1000)
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
  -- the support of the representation contains `T`
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
  obtain ⟨L, -, hL⟩ := hS k B ι S hB hd e x₀ htf hpiece C hC (grRep ℓ k γ C) hfd
    respectsCover_grRep hind (by omega)
  exact ⟨L, by omega⟩

/-- **Theorem A** from the critical node and the ssc theorem. -/
theorem theoremA_of_critical_ssc (hC : CriticalNode.{u}) (hS : SSCNode.{u}) : TheoremA.{u} :=
  theoremA_of_critical_longLine hC (longLineNode_of_ssc hS)

/-- **Corollary 1.1** from the critical node and the ssc theorem. -/
theorem corollaryDimension_of_critical_ssc (hC : CriticalNode.{u}) (hS : SSCNode.{u}) :
    CorollaryDimension.{u} :=
  corollaryDimension_of_critical_longLine hC (longLineNode_of_ssc hS)

/-- **The radical corollary** from the critical node and the ssc theorem. -/
theorem corollaryRadical_of_critical_ssc (hC : CriticalNode.{u}) (hS : SSCNode.{u}) :
    CorollaryRadical.{u} :=
  corollaryRadical_of_critical_longLine hC (longLineNode_of_ssc hS)

end LargeIndecomposable
