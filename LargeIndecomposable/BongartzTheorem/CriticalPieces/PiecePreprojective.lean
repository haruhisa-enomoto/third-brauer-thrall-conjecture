module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.CoverLocalSCResidue
public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullStage
public import LargeIndecomposable.Coverings.Pieces.PieceSepCover

/-!
# Pieces have preprojective components in the node setting

For a minimal representation-infinite distributive algebra with torsion-free fundamental group,
every nonempty convex finite piece of the universal cover has a preprojective component
(`piece_preprojCompNode`). This combines acyclicity (`coverAcyclicNode`), interval-finiteness
(`hullNode`) and local simple connectivity (`coverLocalSCNode`) of the cover with
`piece_preprojComp`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat RayCat.Cover RayQuiver Covering LargeIndecomposable.Graded

universe u

/-- **Pieces have preprojective components in the node setting.** -/
theorem piece_preprojCompNode (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B]
    [Algebra k B] [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : SplitBasicData k B ι) (hB : IsMinimalRepInfinite B) (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    letI := S.isRayCategory hd
    letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
    letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
    ∀ (_ : Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k ≃ₐ[k] B)
      (x₀ : RaySmall.{0} S.toIdempotents.RayCategory),
      (∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
      ∀ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) → C.Nonempty →
        ∃ 𝒞 : AR.FDMod k (PieceAlg k C) → Prop, AR.PreprojComp 𝒞 := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro hlin x₀ htf C hC hne
  exact piece_preprojComp hC hne (coverAcyclicNode k B ι S hB hd x₀)
    (intervalFinite_of_hull (hullNode k B ι S hB hd hlin x₀ htf))
    (coverLocalSCNode k B ι S hB hd x₀)

end LargeIndecomposable
