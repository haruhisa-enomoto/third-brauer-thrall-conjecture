module

public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaRightLadderPropagation
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaSpecialMorphism
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaKrullSchmidtNormalForm
public import LargeIndecomposable.Foundations.CategoryTheory.SplitMorphismComplement
public import LargeIndecomposable.AuslanderReiten.TauCategories.FiniteTauCategory
set_option backward.isDefEq.respectTransparency.types false

/-!
# Infinite special right ladders

This file iterates the split-complement successor construction from Iyama,
*Tau-categories I*, Section 3.2. Starting from an arbitrary special arrow,
it produces the full dependent family of normalized special arrows and chosen
right-mesh ladder rungs. The zero-padded summand of the initial normalization
is retained explicitly for the radical-power argument in Lemma 6.4.1(1)(i).

The construction is entirely categorical: it uses no presentation or
classification of a concrete algebra or its modules.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LargeIndecomposable.Iyama.RightLadder

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- One normalized special split factor through a chosen right mesh.  The
object `U` remembers the zero-padded source summand of the arrow which was
normalized to obtain this state. -/
structure SpecialSplitState (T : FiniteRightTauCategoryData C Ind) (Y : C) where
  Z : C
  U : C
  j : Z ⟶ (T.rightMesh Y).X₂
  [j_split : IsSplitMono j]
  special : IsSpecial T.radical
    (j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom)

instance {T : FiniteRightTauCategoryData C Ind} {Y : C}
    (s : SpecialSplitState T Y) : IsSplitMono s.j :=
  s.j_split

namespace SpecialSplitState

variable {T : FiniteRightTauCategoryData C Ind} {Y : C}

/-- The essential special arrow represented by a normalized state. -/
def b (s : SpecialSplitState T Y) : s.Z ⟶ Y :=
  s.j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom

theorem b_special (s : SpecialSplitState T Y) :
    IsSpecial T.radical s.b :=
  s.special

/-- The raw successor obtained from the complement of the split mesh
factor. -/
def rawSuccessor (s : SpecialSplitState T Y) :
    (T.rightMesh Y).X₁ ⟶ (splitMonoComplement s.j).complement :=
  (T.rightMesh Y).f ≫ (splitMonoComplement s.j).projection

end SpecialSplitState

/-- A special arrow together with one chosen split-factor normalization. -/
structure SpecialNormalization
    (T : FiniteRightTauCategoryData C Ind) {X Y : C} (a : X ⟶ Y) where
  state : SpecialSplitState T Y
  arrowIso : Nonempty
    (Arrow.mk a ≅
      Arrow.mk
        (biprod.desc state.b (0 : state.U ⟶ Y)))

/-- Pack a dependent state together with its current right endpoint. -/
abbrev PackedSpecialSplitState (T : FiniteRightTauCategoryData C Ind) :=
  Σ Y : C, SpecialSplitState T Y

/-- An infinite special right ladder beginning at an arbitrary arrow.

`U 0` is the zero-padded branch in the normalization of the initial arrow;
the rung at `n` uses `U (n+1)`, exactly as in Iyama's displayed ladder. -/
structure InfiniteSpecialRightLadder
    (T : FiniteRightTauCategoryData C Ind)
    {X Y₀ : C} (a₀ : X ⟶ Y₀) where
  Y : ℕ → C
  Z : ℕ → C
  U : ℕ → C
  b : ∀ n, Z n ⟶ Y n
  b_special : ∀ n, IsSpecial T.radical (b n)
  initialIso : Nonempty
    (Arrow.mk a₀ ≅
      Arrow.mk (biprod.desc (b 0) (0 : U 0 ⟶ Y 0)))
  f : ∀ n, Y (Nat.succ n) ⟶ Y n
  g : ∀ n, Z (Nat.succ n) ⟶ Z n
  h : ∀ n, U (Nat.succ n) ⟶ Z n
  comm : ∀ n, b (Nat.succ n) ≫ f n = g n ≫ b n
  hzero : ∀ n, h n ≫ b n = 0
  meshIso : ∀ n, Nonempty
    (T.rightMesh (Y n) ≅
      stepComplex (b n) (b (Nat.succ n))
        (f n) (g n) (h n) (comm n) (hzero n))

end LargeIndecomposable.Iyama.RightLadder
