module

public import LargeIndecomposable.BongartzTheorem.Reduction.Steps

/-!
# The dichotomy node, split

`DichotomyNode` follows from two nodes (`dichotomyNode_of`):

* `CriticalNode`: a finite convex piece of the universal cover that is
  representation-infinite, with every convex piece of fewer points
  representation-finite (a *critical* piece), carries a Kronecker pair;
* `LineNode`: if every finite convex piece is representation-finite,
  the algebra has a monomial band.

Representation-finiteness of a piece `S` (`PieceRepFin`) is stated for
representations of its quiver that satisfy the relations of the cover.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat RayCat.Cover RayQuiver Covering

universe u

/-- A representation is indecomposable: nonzero, and every idempotent endomorphism
is zero or the identity. -/
def Rep.IsIndec {k : Type u} [Field k] {D : FinQuiver} (X : Rep k D) : Prop :=
  (∃ i, Nontrivial (X.obj i)) ∧
    ∀ e : X ⟶ X, e ≫ e = e → (∀ i, e.app i = 0) ∨ e = 𝟙 X

section Piece

variable {P : Type} [Category.{0} P] [Limits.HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

variable (k : Type u) [Field k] in
/-- A finite piece of the cover is representation-finite: finitely many isomorphism
classes of finite-dimensional indecomposable representations satisfying the
relations of the cover. -/
def PieceRepFin (S : Finset (Cover x₀)) : Prop :=
  ∃ (n : ℕ) (Y : Fin n → Rep k (pieceQuiver S)),
    ∀ X : Rep k (pieceQuiver S), (∀ i, FiniteDimensional k (X.obj i)) →
      RespectsCover X → X.IsIndec → ∃ j, Nonempty (X ≅ Y j)

end Piece

/-- a critical piece carries a Kronecker pair. -/
def CriticalNode : Prop :=
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
          ∃ (Sp : Finset (Cover x₀)) (_ : Convex (Sp : Set (Cover x₀)))
            (K : KroneckerPair k (pieceQuiver Sp)),
            (∀ i, Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i)) ∧
              RespectsCover (K.functor.obj (SminusK k)) ∧ RespectsCover (K.functor.obj (P1K k))

/-- If every finite convex piece is representation-finite, there is a
monomial band. -/
def LineNode : Prop :=
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
          Nonempty (Walk.MonomialBand k B)

/-- **The dichotomy** from the critical and line nodes. -/
theorem dichotomyNode_of (hC : CriticalNode.{u}) (hL : LineNode.{u}) : DichotomyNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro e x₀ htf
  classical
  by_cases h : ∃ n, ∃ C : Finset (Cover x₀), Convex (C : Set (Cover x₀)) ∧ ¬PieceRepFin k C ∧
      C.card = n
  · left
    obtain ⟨C, hC1, hC2, hC3⟩ := Nat.find_spec h
    refine hC k B ι S hB hd e x₀ htf C hC1 hC2 fun C' hC' hlt ↦ ?_
    by_contra hC''
    exact Nat.find_min h (hC3 ▸ hlt) ⟨C', hC', hC'', rfl⟩
  · right
    push Not at h
    exact hL k B ι S hB hd e x₀ htf fun C hC ↦ by
      by_contra h'
      exact h _ C hC h' rfl

end LargeIndecomposable
