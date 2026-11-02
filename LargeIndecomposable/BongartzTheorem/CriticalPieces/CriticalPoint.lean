module

public import LargeIndecomposable.BongartzTheorem.Reduction.CoverDichotomy
public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerGlue
public import LargeIndecomposable.Coverings.Pieces.PointPair

/-!
# `CriticalPairExists` from a point and a brick

`PointBrickData` asks, for a critical convex piece, for the data of Bongartz's Lemma 4 (BO23): a
convex piece `Sp`, a point `x`, a brick `V` on `Sp` vanishing exactly at `x` and respecting the
cover, and two independent extension tuples between `S(x)` and `V` (in either direction) whose
extension blocks agree along related paths. By `respectsCover_extRep`, `respectsCover_pointRep` and
`sincere_of_point` this gives `CriticalPairExists` (`criticalPairExists_of_point`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Statement Cover RayQuiver Covering

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- The extension blocks of `z` agree along related paths and vanish along zero paths. -/
def CrossOK (K : KroneckerPair k (pieceQuiver S))
    (z : ∀ α : (pieceQuiver S).A, K.P.obj ((pieceQuiver S).src α) →ₗ[k]
      K.Q₀.obj ((pieceQuiver S).tgt α)) : Prop :=
  (∀ le i j (h : FinQuiver.PathFrom i le j), compD S le i j h = 0 → K.cross z le = 0) ∧
    ∀ le le' i j (h : FinQuiver.PathFrom i le j) (h' : FinQuiver.PathFrom i le' j),
      compD S le i j h = compD S le' i j h' → K.cross z le = K.cross z le'

end LargeIndecomposable.RayCat
