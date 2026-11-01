module

public import LargeIndecomposable.BongartzTheorem.Reduction.DichotomySteps
public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerGlue

/-!
# `CriticalNode` from a pair with two extensions

`CriticalPairNode` asks, for a critical convex piece, only for a Kronecker pair on a convex piece
whose two extension modules `E(z₁)`, `E(z₂)` satisfy the relations of the cover. By
`respectsCover_generic` the generic objects then satisfy them too, which is `CriticalNode`
(`criticalNode_of_pair`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Statement Cover RayQuiver Covering

universe u

/-- Critical pieces give Kronecker pairs with two extensions respecting the cover. -/
def CriticalPairNode : Prop :=
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
        ∀ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) → ¬PieceRepFin k C →
          (∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < C.card →
            PieceRepFin k C') →
          ∃ (Sp : Finset (Cover x₀)) (_ : Convex (Sp : Set (Cover x₀)))
            (K : KroneckerPair k (pieceQuiver Sp)),
            (∀ i, Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i)) ∧
              RespectsCover (K.extRep K.z₁) ∧ RespectsCover (K.extRep K.z₂)

/-- **`CriticalNode` from `CriticalPairNode`.** -/
theorem criticalNode_of_pair (h : CriticalPairNode.{u}) : CriticalNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf C hC hrep hmin
  obtain ⟨Sp, hSp, K, hsinc, h₁, h₂⟩ := h k B ι S hB hd e x₀ htf C hC hrep hmin
  exact ⟨Sp, hSp, K, hsinc, respectsCover_generic K h₁ h₂⟩

end LargeIndecomposable.RayCat
