module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PairWithoutSupport
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.SinkCount
/-!
# Point–brick data without sincerity

`PointBrick'` is `PointBrick` without the condition that `V` is nonzero at every vertex other
than `x`; its body at a fixed point and brick is `PointBrickAt`. It still gives a Kronecker pair
whose extensions respect the cover, supported on the point and the support of the brick
(`pair_of_pointBrickAt`, `pair_of_pointBrick'`), hence the support-free critical step
(`criticalPieceCarriesPair_of_pointBrickData`).
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

/-- The data of Bongartz's Lemma 4 on a piece at a point `x` and a brick `V`. -/
abbrev PointBrickAt {Sp : Finset (Cover x₀)} (x : (pieceQuiver Sp).V) (V : Rep k (pieceQuiver Sp)) :
    Prop :=
  ∃ (finV : ∀ i, FiniteDimensional k (V.obj i))
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

/-- The data of Bongartz's Lemma 4 on a piece, without sincerity. -/
def PointBrick' (Sp : Finset (Cover x₀)) : Prop :=
  ∃ (x : (pieceQuiver Sp).V) (V : Rep k (pieceQuiver Sp)), PointBrickAt (k := k) x V

/-- **A point and a brick give a Kronecker pair with extensions respecting the cover**,
supported on the point and the support of the brick. -/
theorem pair_of_pointBrickAt {Sp : Finset (Cover x₀)} {x : (pieceQuiver Sp).V}
    {V : Rep k (pieceQuiver Sp)} (h : PointBrickAt (k := k) x V) :
    ∃ K : KroneckerPair k (pieceQuiver Sp),
      RespectsCover (K.functor.obj (Kron.Sminus k)) ∧ RespectsCover (K.functor.obj (P1K k)) ∧
        ∀ i ∈ K.supp, i = x ∨ Nontrivial (V.obj i) := by
  obtain ⟨finV, hVx, brickV, hV, hVc, hz⟩ := h
  have hpt : ∀ i, Nontrivial ((Rep.pointRep (k := k) x).obj i) → i = x := fun i hi ↦ by
    by_contra hne
    exact not_nontrivial_iff_subsingleton.2 (Rep.subsingleton_pointRep (k := k) hne) hi
  rcases hz with ⟨z₁, z₂, indep, h₁, h₂⟩ | ⟨z₁, z₂, indep, h₁, h₂⟩
  · obtain ⟨g₁, g₂⟩ := respectsCover_generic _
      (respectsCover_extRep _ _ hVc (respectsCover_pointRep x) h₁.1 h₁.2)
      (respectsCover_extRep _ _ hVc (respectsCover_pointRep x) h₂.1 h₂.2)
    refine ⟨_, g₁, g₂, fun i hi ↦ ?_⟩
    rcases (KroneckerPair.mem_supp _).1 hi with h | h
    · exact Or.inl (hpt i h)
    · exact Or.inr h
  · obtain ⟨g₁, g₂⟩ := respectsCover_generic _
      (respectsCover_extRep _ _ (respectsCover_pointRep x) hVc h₁.1 h₁.2)
      (respectsCover_extRep _ _ (respectsCover_pointRep x) hVc h₂.1 h₂.2)
    refine ⟨_, g₁, g₂, fun i hi ↦ ?_⟩
    rcases (KroneckerPair.mem_supp _).1 hi with h | h
    · exact Or.inr h
    · exact Or.inl (hpt i h)

/-- **A point and a brick give a Kronecker pair with extensions respecting the cover.** -/
theorem pair_of_pointBrick' {Sp : Finset (Cover x₀)} (h : PointBrick' (k := k) Sp) :
    ∃ K : KroneckerPair k (pieceQuiver Sp),
      RespectsCover (K.functor.obj (Kron.Sminus k)) ∧ RespectsCover (K.functor.obj (P1K k)) := by
  obtain ⟨x, V, h⟩ := h
  obtain ⟨K, h₁, h₂, -⟩ := pair_of_pointBrickAt h
  exact ⟨K, h₁, h₂⟩

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
