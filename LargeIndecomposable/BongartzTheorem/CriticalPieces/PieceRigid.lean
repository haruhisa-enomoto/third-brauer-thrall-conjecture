module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.SinkCount
public import LargeIndecomposable.DirectedAlgebras.Directing.RigidMin

/-!
# Rigid modules over a piece have no cocycles beyond coboundaries

For representations `X`, `Y` of a piece respecting the cover and a family `F` of relations
generating those of the cover, a cocycle `z` of `F` gives an extension `E(z)` respecting the cover
(`respectsCover_extR`). If every extension of the module of `X` by that of `Y` splits, a section
is a morphism of representations, so `z` is a coboundary (`cocycles_le_range_cob`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver

universe u

lemma _root_.LargeIndecomposable.FinQuiver.Hom.id_locallyInjective (Q : FinQuiver) :
    (FinQuiver.Hom.id Q).LocallyInjective :=
  ⟨fun _ _ _ h ↦ h, fun _ _ _ h ↦ h⟩

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

lemma pieceAct_comm {X Y : Rep k (pieceQuiver S)} {hX : RespectsCover X} {hY : RespectsCover Y}
    (s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY) (a : PieceAlg k S) (x : X.Tot) :
    s (pieceAct X hX a x) = pieceAct Y hY a (s x) :=
  s.map_smul a x

/-- **A module map between representations respecting the cover is a morphism.** -/
def homOfLin {X Y : Rep k (pieceQuiver S)} {hX : RespectsCover X} {hY : RespectsCover Y}
    (s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY) : X ⟶ Y :=
  Rep.diagHom (FinQuiver.Hom.id_locallyInjective _)
    (show X.Tot →ₗ[k] Y.Tot from s.restrictScalars k) <| by
    refine (Rep.isPdHom_iff _ _).1 ⟨fun q ↦ LinearMap.ext fun x ↦ ?_, fun c ↦
      LinearMap.ext fun x ↦ ?_⟩
    · have h := pieceAct_comm s (RingQuot.mkAlgHom k _ (FinQuiver.vertex k _ q)) x
      rw [pieceAct_mk, pieceAct_mk, Rep.pdAct_vertex, Rep.pdAct_vertex] at h
      exact h
    · have h := pieceAct_comm s (RingQuot.mkAlgHom k _ (FinQuiver.arrow k _ c)) x
      rw [pieceAct_mk, pieceAct_mk, Rep.pdAct_arrow, Rep.pdAct_arrow] at h
      exact h

lemma homOfLin_app {X Y : Rep k (pieceQuiver S)} {hX : RespectsCover X} {hY : RespectsCover Y}
    (s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY) (i : (pieceQuiver S).V) (x : X.obj i) :
    ((homOfLin s).app i).hom x = (show Y.Tot from s (show X.Tot from Pi.single i x)) i := rfl

end LargeIndecomposable.RayCat
