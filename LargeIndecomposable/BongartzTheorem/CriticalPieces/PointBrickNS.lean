module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.NonSincere
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.SinkCount
/-!
# Point–brick data without sincerity

`PointBrick'` is `PointBrick` without the condition that `V` is nonzero at every vertex other
than `x`. It still gives a Kronecker pair whose extensions respect the cover
(`pair_of_pointBrick'`), hence the support-free critical node (`criticalNode'_of_point'`). Two
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
def PointBrickNode' : Prop :=
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

/-- **The support-free critical node from point–brick data.** -/
theorem criticalNode'_of_point' (h : PointBrickNode'.{u}) : CriticalNode'.{u} := by
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

/-- **Point–brick data from two independent cocycles, without sincerity.** -/
theorem pointBrick'_of_cocycles {S : Finset (Cover x₀)} (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    (x : (pieceQuiver S).V) (V : Rep k (pieceQuiver S)) (finV : ∀ i, FiniteDimensional k (V.obj i))
    (hVx : Subsingleton (V.obj x))
    (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i)) (hVc : RespectsCover V)
    (h2 : 2 ≤ Module.finrank k (Ext.cocycles F (X := V) (Y := Rep.pointRep (k := k) x))) :
    PointBrick' (k := k) S := by
  haveI := finV
  haveI : ∀ i, FiniteDimensional k ((Rep.pointRep (k := k) x).obj i) := fun i ↦
    inferInstanceAs (FiniteDimensional k (Fin _ → k))
  obtain ⟨w₁, w₂, hw⟩ := exists_pair h2
  have hind : ∀ c₁ c₂ : k, (∀ α, c₁ • (w₁ : Ext.Data V (Rep.pointRep (k := k) x)) α +
      c₂ • (w₂ : Ext.Data V (Rep.pointRep (k := k) x)) α = 0) → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ hc
    apply hw
    apply Subtype.ext
    funext α
    simpa using hc α
  have hK : ∀ w : Ext.cocycles F (X := V) (Y := Rep.pointRep (k := k) x),
      CrossOK (pairAtSink x V finV hVx brickV hV (w₁ : Ext.Data V (Rep.pointRep (k := k) x))
        (w₂ : Ext.Data V (Rep.pointRep (k := k) x)) hind)
        (w : Ext.Data V (Rep.pointRep (k := k) x)) := fun w ↦
    crossOK_of_cocycle _ hVc (respectsCover_pointRep x) F hF hgen _ w.2
  exact ⟨x, V, finV, hVx, brickV, hV, hVc,
    Or.inr ⟨(w₁ : Ext.Data V (Rep.pointRep (k := k) x)),
      (w₂ : Ext.Data V (Rep.pointRep (k := k) x)), hind, hK w₁, hK w₂⟩⟩

/-- **Point–brick data at a source from two independent cocycles.** -/
theorem pointBrick'_of_cocycles_source {S : Finset (Cover x₀)} (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    (x : (pieceQuiver S).V) (V : Rep k (pieceQuiver S)) (finV : ∀ i, FiniteDimensional k (V.obj i))
    (hVx : Subsingleton (V.obj x))
    (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i)) (hVc : RespectsCover V)
    (h2 : 2 ≤ Module.finrank k (Ext.cocycles F (X := Rep.pointRep (k := k) x) (Y := V))) :
    PointBrick' (k := k) S := by
  haveI := finV
  haveI : ∀ i, FiniteDimensional k ((Rep.pointRep (k := k) x).obj i) := fun i ↦
    inferInstanceAs (FiniteDimensional k (Fin _ → k))
  obtain ⟨w₁, w₂, hw⟩ := exists_pair h2
  have hind : ∀ c₁ c₂ : k, (∀ α, c₁ • (w₁ : Ext.Data (Rep.pointRep (k := k) x) V) α +
      c₂ • (w₂ : Ext.Data (Rep.pointRep (k := k) x) V) α = 0) → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ hc
    apply hw
    apply Subtype.ext
    funext α
    simpa using hc α
  have hK : ∀ w : Ext.cocycles F (X := Rep.pointRep (k := k) x) (Y := V),
      CrossOK (pairAtSource x V finV hVx brickV hV
        (w₁ : Ext.Data (Rep.pointRep (k := k) x) V) (w₂ : Ext.Data (Rep.pointRep (k := k) x) V) hind)
        (w : Ext.Data (Rep.pointRep (k := k) x) V) := fun w ↦
    crossOK_of_cocycle _ (respectsCover_pointRep x) hVc F hF hgen _ w.2
  exact ⟨x, V, finV, hVx, brickV, hV, hVc,
    Or.inl ⟨(w₁ : Ext.Data (Rep.pointRep (k := k) x) V),
      (w₂ : Ext.Data (Rep.pointRep (k := k) x) V), hind, hK w₁, hK w₂⟩⟩

end LargeIndecomposable.RayCat

namespace LargeIndecomposable

open Statement

universe u

end LargeIndecomposable
