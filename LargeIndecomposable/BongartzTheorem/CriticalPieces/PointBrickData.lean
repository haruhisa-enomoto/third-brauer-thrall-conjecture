module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PairWithoutSupport
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.SinkCount
/-!
# Point–brick data without sincerity

`PointBrick'` is `PointBrick` without the condition that `V` is nonzero at every vertex other
than `x`. It still gives a Kronecker pair whose extensions respect the cover
(`pair_of_pointBrick'`), hence the support-free critical step (`criticalPieceCarriesPair_of_pointBrickData`). Two
independent cocycles give `PointBrick'` (`pointBrick'_of_cocycles`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Statement Cover RayQuiver Covering FinQuiver

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

/-- The data of Bongartz's Lemma 4 on a piece, without sincerity. -/
def PointBrick' (Sp : Finset (Cover x₀)) : Prop :=
  ∃ (x : (pieceQuiver Sp).V) (V : Rep k (pieceQuiver Sp)) (finV : ∀ i, FiniteDimensional k (V.obj i))
    (hVx : Subsingleton (V.obj x))
    (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i)), RespectsCover V ∧
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
theorem pair_of_pointBrick' {Sp : Finset (Cover x₀)} (h : PointBrick' (k := k) Sp) :
    ∃ K : KroneckerPair k (pieceQuiver Sp),
      RespectsCover (K.functor.obj (SminusK k)) ∧ RespectsCover (K.functor.obj (P1K k)) := by
  obtain ⟨x, V, finV, hVx, brickV, hV, hVc, hz⟩ := h
  rcases hz with ⟨z₁, z₂, indep, h₁, h₂⟩ | ⟨z₁, z₂, indep, h₁, h₂⟩
  · exact ⟨_, respectsCover_generic _
      (respectsCover_extRep _ _ hVc (respectsCover_pointRep x) h₁.1 h₁.2)
      (respectsCover_extRep _ _ hVc (respectsCover_pointRep x) h₂.1 h₂.2)⟩
  · exact ⟨_, respectsCover_generic _
      (respectsCover_extRep _ _ (respectsCover_pointRep x) hVc h₁.1 h₁.2)
      (respectsCover_extRep _ _ (respectsCover_pointRep x) hVc h₂.1 h₂.2)⟩

/-- Critical pieces carry the data of Bongartz's Lemma 4, without sincerity. -/
def PointBrickData : Prop :=
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
          ∃ (Sp : Finset (Cover x₀)) (_ : Convex (Sp : Set (Cover x₀))), PointBrick' (k := k) Sp

/-- **The support-free critical step from point–brick data.** -/
theorem criticalPieceCarriesPair_of_pointBrickData (h : PointBrickData.{u}) : CriticalPieceCarriesPair.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf C hC hrep hmin
  obtain ⟨Sp, hSp, hpb⟩ := h k B ι S hB hd e x₀ htf C hC hrep hmin
  obtain ⟨K, hK⟩ := pair_of_pointBrick' hpb
  exact ⟨Sp, hSp, K, hK⟩

end LargeIndecomposable.RayCat
