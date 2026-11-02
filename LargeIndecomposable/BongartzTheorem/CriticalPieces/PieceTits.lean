module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceRigid
public import LargeIndecomposable.DirectedAlgebras.Directing.DimVector
public import LargeIndecomposable.Coverings.Pieces.PieceRepDir

/-!
# The Tits form of a representation-directed piece is weakly positive

Let `F` be a family of relations generating those of a piece `S`, with Tits form
`q_F(x) = Σᵢ xᵢ² - Σ_α x_{s α} x_{t α} + Σ_r x_{s r} x_{t r}`. If every nonzero indecomposable
module over the piece algebra is rigid (for instance directing), then every dimension vector
`x` has a representation `X` respecting the cover with no cocycles beyond coboundaries
(`exists_rigid_rep`; a module of minimal endomorphism dimension, ASS IX.3.3). Counting cocycles
gives `dim End X ≤ q_F(x)` (`finrank_end_le_titsF`). So `q_F` is weakly positive
(`one_le_titsF`), and a positive vector with `q_F(x) ≤ 1` is the dimension vector of a brick
(`exists_brick_of_titsF`).
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

/-! ### Paths of a piece with their lengths -/

/-! ### Representations with zero maps -/

variable (k S) in
/-- The representation with spaces `k^{x i}` and zero maps. -/
def zeroRep (x : (pieceQuiver S).V → ℕ) : Rep k (pieceQuiver S) where
  obj i := ModuleCat.of k (Fin (x i) → k)
  map _ := 0

/-! ### Dimension vectors -/

lemma pieceAct_pev (X : Rep k (pieceQuiver S)) (hX : RespectsCover X) (v : (pieceQuiver S).V) :
    pieceAct X hX (pev v) = X.idm v := by
  rw [pieceAct_mk]
  exact Ext.act_vertex X v

/-- **A module is the module of its representation.** -/
def repOfEquivA (M : AR.FDMod k (PieceAlg k S)) :
    PieceMod (repOf M) (respectsCover_repOf M) ≃ₗ[PieceAlg k S] M where
  toFun := totToMod M
  map_add' := map_add (totToMod M)
  map_smul' a x := by
    obtain ⟨z, rfl⟩ := RingQuot.mkAlgHom_surjective k _ a
    change totToMod M (pieceAct (repOf M) _ (RingQuot.mkAlgHom k _ z) x) = _
    rw [pieceAct_mk]
    exact totToMod_pdAct M z x
  invFun := modToTot M
  left_inv := modToTot_totToMod M
  right_inv := totToMod_modToTot M

/-! ### Rigid representations -/

/-! ### The Tits form -/

end LargeIndecomposable.RayCat
