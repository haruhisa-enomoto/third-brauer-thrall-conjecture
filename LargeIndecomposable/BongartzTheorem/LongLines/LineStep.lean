module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.GabrielPieces

/-!
# The line step from interval-finiteness and the core step

`RepFinitePiecesGiveBand` (all finite convex pieces representation-finite ⇒ monomial band) follows from

* `IntervalFiniteCover`: every finite set of objects of the universal cover lies in a finite convex
  piece (interval-finiteness), and
* `RepFinitePiecesGiveBandCore`: if all finite convex pieces are representation-finite and graded-indecomposable
  `k(P)`-modules have supports of unbounded size, there is a monomial band.

The link is Gabriel's covering theorem (`repFin_of_bounded_support`): bounded supports would
make `k(P) ≅ B` representation-finite.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat RayCat.Cover RayQuiver Covering LargeIndecomposable.Graded

universe u

/-- Interval-finiteness of the universal cover. -/
def IntervalFiniteCover : Prop :=
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
        (∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) → HullFinite x₀

/-- The core of the line step: unbounded graded supports over representation-finite pieces give a
monomial band. -/
def RepFinitePiecesGiveBandCore : Prop :=
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
        (∀ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) → PieceRepFin k C) →
        ∀ ℓ : ∀ y, vtx x₀ ⟶ vtx y,
          (∀ n : ℕ, ∃ (M : AR.FDMod k (Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k))
            (μ : GrMod (rayGrAlg ℓ k) M), IsGrIndec μ ∧ Nontrivial M ∧ n < (suppF k ℓ μ).card) →
          Nonempty (Walk.MonomialBand k B)

/-- **`RepFinitePiecesGiveBand` from interval-finiteness and the core step.** -/
theorem repFinitePiecesGiveBand_of (hH : IntervalFiniteCover.{u}) (hD : RepFinitePiecesGiveBandCore.{u}) : RepFinitePiecesGiveBand.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf hpiece
  -- lifts of the objects to the fundamental groupoid
  have hι := S.nonempty_of_minimal hB
  have : Nonempty (RaySmall.{0} S.toIdempotents.RayCategory) :=
    ⟨⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩⟩
  have hcon : IsConnected (FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory)) :=
    isConnected_fund_of_nzConnected fun x y ↦ RaySmall.nzConnected
      (S.nzConnected hd (fun e he hc ↦ hB.central_idempotent e he hc) x.as y.as)
  have hℓ : ∀ y, Nonempty (vtx x₀ ⟶ vtx y) := fun y ↦
    nonempty_hom_of_preconnected_groupoid _ _
  let ℓ : ∀ y, vtx x₀ ⟶ vtx y := fun y ↦ (hℓ y).some
  have htf' : TorsionFree (Pi1 x₀) := fun g n hn hg ↦ by
    by_contra h1; exact htf g h1 n hn hg
  refine hD k B ι S hB hd e x₀ htf hpiece ℓ fun n ↦ ?_
  by_contra hno
  push Not at hno
  obtain ⟨r, Y, hY⟩ := repFin_of_bounded_support (ℓ := ℓ) htf' (hH k B ι S hB hd e x₀ htf)
    hpiece n fun M μ hμ hM ↦ hno M μ hμ hM
  exact hB.1 (isRepresentationFinite_of_ringEquiv e.toRingEquiv
    (AR.isRepresentationFinite_of_fdList Y hY))

end LargeIndecomposable
