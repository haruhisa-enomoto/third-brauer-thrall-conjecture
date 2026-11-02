module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineContour
public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullStage

/-!
# The line step from long lines

`LinesOfEveryLength` is the large-line input of the representation-finite case (BO23, proof of
Theorem 7, lines 876–882; BO13b, Theorem `ssc`): when every finite convex piece of the universal
cover is representation-finite and graded indecomposables have unbounded supports, the cover
contains lines of every length. The line lemma (BO13b, Lemma 7.2) then gives the line step: lines of
every length exclude contours (`noContour_of_lines`), so `k(P)` is a zero-relation algebra, and a
minimal good pair of sinks of a long line gives a monomial band (`nonempty_monomialBand`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat RayCat.Cover RayQuiver Covering LargeIndecomposable.Graded

universe u

/-- **The large-line input**: lines of every length in the universal cover. -/
def LinesOfEveryLength : Prop :=
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
          ∀ m : ℕ, ∃ L : CLine x₀, m ≤ L.n

/-- **The line step from long lines** (BO13b, Lemma 7.2; BO23, proof of Theorem 7). -/
theorem repFinitePiecesGiveBandCore_of_longLine (hL : LinesOfEveryLength.{u}) : RepFinitePiecesGiveBandCore.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf hpiece ℓ hsupp
  have hlines := hL k B ι S hB hd e x₀ htf hpiece ℓ hsupp
  have hnc := noContour_of_lines hB e htf hlines
  haveI : ∀ x y : RaySmall.{0} S.toIdempotents.RayCategory, Finite (x ⟶ y) := IsRayCategory.finite_hom
  obtain ⟨L, hLn⟩ := hlines ((2 * Fintype.card (RaySmall.{0} S.toIdempotents.RayCategory) + 1) *
    (2 * CLine.bound (RaySmall.{0} S.toIdempotents.RayCategory)))
  exact nonempty_monomialBand L hLn hnc e

end LargeIndecomposable
