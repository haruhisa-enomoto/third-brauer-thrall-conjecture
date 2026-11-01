module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceTits

/-!
# Tits forms of representation-finite pieces

For a connected representation-finite convex piece, every indecomposable module is directing
(`directing_piece`), hence rigid. So the Tits form of any family of relations generating those of
the cover is weakly positive (`one_le_titsF_of_repFin`), and its positive vectors of value at
most one are dimension vectors of bricks respecting the cover (`exists_brick_of_repFin`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

section

variable (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
    (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
    (hlsc : CoverLocalSC x₀) (hrep : PieceRepFin k S)
    (hconnS : ∀ T : Set (pieceQuiver S).V, T.Nonempty →
      (∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ T ↔ (pieceQuiver S).tgt α ∈ T) →
        T = Set.univ)
    (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
include hS hne hacycCov hint hlsc hrep hconnS hF hgen

lemma rigid_of_repFin : ∀ M : AR.FDMod k (PieceAlg k S), AR.IsIndecMod (PieceAlg k S) M →
    Nontrivial M → AR.ExtVanish M M := fun M hM hnt ↦
  (directing_piece hS hne hacycCov hint hlsc hrep hconnS M ⟨hM, hnt⟩).extVanish

/-- **The Tits form of a connected representation-finite piece is weakly positive.** -/
theorem one_le_titsF_of_repFin (x : (pieceQuiver S).V → ℕ) (hx : x ≠ 0) :
    1 ≤ titsF F (fun i ↦ (x i : ℤ)) :=
  one_le_titsF F hF hgen (rigid_of_repFin hS hne hacycCov hint hlsc hrep hconnS F hF hgen) x hx

/-- **Roots of the Tits form of a connected representation-finite piece are bricks.** -/
theorem exists_brick_of_repFin (x : (pieceQuiver S).V → ℕ) (hx : x ≠ 0)
    (hq : titsF F (fun i ↦ (x i : ℤ)) ≤ 1) :
    ∃ (X : Rep k (pieceQuiver S)) (_ : RespectsCover X) (_ : ∀ i, FiniteDimensional k (X.obj i)),
      (∀ i, finrank k (X.obj i) = x i) ∧
        ∀ f : X ⟶ X, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id :=
  exists_brick_of_titsF F hF hgen (rigid_of_repFin hS hne hacycCov hint hlsc hrep hconnS F hF hgen)
    x hx hq

end

end LargeIndecomposable.RayCat
