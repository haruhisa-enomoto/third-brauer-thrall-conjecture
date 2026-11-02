module

public import LargeIndecomposable.BongartzTheorem.Reduction.DichotomySteps
public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerGlue
public import LargeIndecomposable.Coverings.Pieces.PointPair

/-!
# `CriticalPairNode` from a point and a brick

`PointBrickNode` asks, for a critical convex piece, for the data of Bongartz's Lemma 4 (BO23): a
convex piece `Sp`, a point `x`, a brick `V` on `Sp` vanishing exactly at `x` and respecting the
cover, and two independent extension tuples between `S(x)` and `V` (in either direction) whose
extension blocks agree along related paths. By `respectsCover_extRep`, `respectsCover_pointRep` and
`sincere_of_point` this gives `CriticalPairNode` (`criticalPairNode_of_point`).
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

/-- The data of Bongartz's Lemma 4 on a piece. -/
def PointBrick (Sp : Finset (Cover x₀)) : Prop :=
  ∃ (x : (pieceQuiver Sp).V) (V : Rep k (pieceQuiver Sp)) (finV : ∀ i, FiniteDimensional k (V.obj i))
    (hVx : Subsingleton (V.obj x))
    (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i)), (∀ i, i ≠ x → Nontrivial (V.obj i)) ∧ RespectsCover V ∧
    ((∃ (z₁ z₂ : ∀ α : (pieceQuiver Sp).A, (Rep.pointRep (k := k) x).obj ((pieceQuiver Sp).src α)
        →ₗ[k] V.obj ((pieceQuiver Sp).tgt α))
        (indep : ∀ c₁ c₂ : k, (∀ α, c₁ • z₁ α + c₂ • z₂ α = 0) → c₁ = 0 ∧ c₂ = 0),
        CrossOK (pairAtSource x V finV hVx brickV hV z₁ z₂ indep) z₁ ∧
          CrossOK (pairAtSource x V finV hVx brickV hV z₁ z₂ indep) z₂) ∨
      ∃ (z₁ z₂ : ∀ α : (pieceQuiver Sp).A, V.obj ((pieceQuiver Sp).src α) →ₗ[k]
          (Rep.pointRep (k := k) x).obj ((pieceQuiver Sp).tgt α))
        (indep : ∀ c₁ c₂ : k, (∀ α, c₁ • z₁ α + c₂ • z₂ α = 0) → c₁ = 0 ∧ c₂ = 0),
        CrossOK (pairAtSink x V finV hVx brickV hV z₁ z₂ indep) z₁ ∧
          CrossOK (pairAtSink x V finV hVx brickV hV z₁ z₂ indep) z₂)

/-- **A point and a brick give a Kronecker pair with extensions respecting the cover.** -/
theorem pair_of_pointBrick {Sp : Finset (Cover x₀)} (h : PointBrick (k := k) Sp) :
    ∃ K : KroneckerPair k (pieceQuiver Sp),
      (∀ i, Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i)) ∧
        RespectsCover (K.extRep K.z₁) ∧ RespectsCover (K.extRep K.z₂) := by
  obtain ⟨x, V, finV, hVx, brickV, hV, hsinc, hVc, hz⟩ := h
  rcases hz with ⟨z₁, z₂, indep, h₁, h₂⟩ | ⟨z₁, z₂, indep, h₁, h₂⟩
  · refine ⟨pairAtSource x V finV hVx brickV hV z₁ z₂ indep, sincere_of_point x V hsinc,
      respectsCover_extRep _ _ hVc (respectsCover_pointRep x) h₁.1 h₁.2,
      respectsCover_extRep _ _ hVc (respectsCover_pointRep x) h₂.1 h₂.2⟩
  · refine ⟨pairAtSink x V finV hVx brickV hV z₁ z₂ indep, fun i ↦ (sincere_of_point x V hsinc i).symm,
      respectsCover_extRep _ _ (respectsCover_pointRep x) hVc h₁.1 h₁.2,
      respectsCover_extRep _ _ (respectsCover_pointRep x) hVc h₂.1 h₂.2⟩

/-- Critical pieces carry the data of Bongartz's Lemma 4. -/
def PointBrickNode : Prop :=
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
          ∃ (Sp : Finset (Cover x₀)) (_ : Convex (Sp : Set (Cover x₀))), PointBrick (k := k) Sp

end LargeIndecomposable.RayCat
