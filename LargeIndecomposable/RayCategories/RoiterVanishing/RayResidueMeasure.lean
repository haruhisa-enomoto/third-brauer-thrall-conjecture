module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueTackle
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# A finite induction measure for ray residue categories

In the finite-object setting, the total number of nonzero morphisms gives a
simpler well-founded measure than the local tackle/morphism-pair count used by
BGRS for categories which may have infinitely many objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A nonzero morphism with both endpoints allowed to vary. -/
@[ext]
structure NonzeroCategoryMorphism (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] where
  source : C
  target : C
  hom : source ⟶ target
  ne_zero : hom ≠ 0

/-- The type of all nonzero morphisms is finite in a finite ray category with
finitely many objects. -/
instance [Finite C] [IsFiniteRayCategory C] :
    Finite (NonzeroCategoryMorphism C) := by
  letI (X Y : C) : Finite (X ⟶ Y) :=
    IsFiniteRayCategory.hom_finite X Y
  letI : Fintype C := Fintype.ofFinite C
  letI (X Y : C) : Fintype (X ⟶ Y) := Fintype.ofFinite (X ⟶ Y)
  let encode : NonzeroCategoryMorphism C → Σ X : C, Σ Y : C, X ⟶ Y :=
    fun f ↦ ⟨f.source, f.target, f.hom⟩
  apply Finite.of_injective encode
  intro f g h
  rcases f with ⟨fs, ft, f, hf⟩
  rcases g with ⟨gs, gt, g, hg⟩
  dsimp [encode] at h
  cases h
  rfl

namespace NonzeroCategoryMorphism

/-- Lift a nonzero quotient morphism to its chosen original representative. -/
def quotOut (I : ZeroHomIdeal C) :
    NonzeroCategoryMorphism (CategoryTheory.Quotient I.rel) →
      NonzeroCategoryMorphism C
  | ⟨X, Y, f, hf⟩ =>
      ⟨X.as, Y.as, Quot.out f,
        (I.quotOutNonzeroHom ⟨f, hf⟩).2⟩

/-- Choosing representatives is injective on nonzero quotient morphisms. -/
theorem quotOut_injective (I : ZeroHomIdeal C) :
    Function.Injective (quotOut I) := by
  intro f g h
  rcases f with ⟨⟨fs⟩, ⟨ft⟩, f, hf⟩
  rcases g with ⟨⟨gs⟩, ⟨gt⟩, g, hg⟩
  have hout := (NonzeroCategoryMorphism.ext_iff).1 h
  dsimp [quotOut] at hout
  have hs : fs = gs := hout.1
  subst gs
  have ht : ft = gt := hout.2.1
  subst gt
  have hrep : Quot.out f = Quot.out g := eq_of_heq hout.2.2
  have hfout :
      Quot.mk (@HomRel.CompClosure C _ I.rel fs ft) (Quot.out f) = f := by
    simp
  have hgout :
      Quot.mk (@HomRel.CompClosure C _ I.rel fs ft) (Quot.out g) = g := by
    simp
  have hfg : f = g := hfout.symm.trans <|
    (congrArg
      (fun q ↦ Quot.mk (@HomRel.CompClosure C _ I.rel fs ft) q) hrep).trans
        hgout
  subst g
  rfl

/-- The chosen original representative of a nonzero quotient morphism lies
outside the collapsed ideal. -/
theorem quotOut_not_mem (I : ZeroHomIdeal C)
    (f : NonzeroCategoryMorphism (CategoryTheory.Quotient I.rel)) :
    ¬I.mem (quotOut I f).hom := by
  rcases f with ⟨X, Y, f, hf⟩
  exact I.quotOutNonzeroHom_not_mem ⟨f, hf⟩

end NonzeroCategoryMorphism

namespace NonzeroHom

/-- Package a fixed-endpoint nonzero morphism as a nonzero category morphism
with varying endpoints. -/
def toNonzeroCategoryMorphism {X Y : C} (f : NonzeroHom X Y) :
    NonzeroCategoryMorphism C :=
  ⟨X, Y, f.1, f.2⟩

@[simp]
theorem toNonzeroCategoryMorphism_hom {X Y : C} (f : NonzeroHom X Y) :
    f.toNonzeroCategoryMorphism.hom = f.1 :=
  rfl

end NonzeroHom

/-- The fixed-source lower-interval rank of a nonzero ray morphism is bounded
by the total number of nonzero morphisms in the category. -/
theorem rayMorphismLowerCard_le_nonzeroCategoryMorphism_card
    [Finite C] [IsFiniteRayCategory C]
    {X : C} (f : NonzeroMorphismFrom X) :
    rayMorphismLowerCard f ≤ Nat.card (NonzeroCategoryMorphism C) := by
  let embed : NonzeroMorphismFrom X → NonzeroCategoryMorphism C :=
    fun g ↦ ⟨X, g.target, g.hom, g.ne_zero⟩
  have hinjective : Function.Injective embed := by
    intro g h hgh
    cases g with
    | mk gtarget ghom gzero =>
        cases h with
        | mk htarget hhom hzero =>
            have hdata := (NonzeroCategoryMorphism.ext_iff).1 hgh
            dsimp [embed] at hdata
            cases hdata.2.1
            cases eq_of_heq hdata.2.2
            rfl
  exact (Set.Iic f).ncard_le_card.trans
    (Nat.card_le_card_of_injective embed hinjective)

/-- Every nonzero irreducible ray path has length strictly below the total
number of nonzero category morphisms. -/
theorem rayPath_length_lt_nonzeroCategoryMorphism_card
    [Finite C] [IsFiniteRayCategory C]
    {i j : RayVertex C} (p : Quiver.Path i j) (hp : rayPathMap p ≠ 0) :
    p.length < Nat.card (NonzeroCategoryMorphism C) := by
  have hlength := rayPath_length_add_one_le_lowerCard p hp
  have hcard := rayMorphismLowerCard_le_nonzeroCategoryMorphism_card
    (rayPathMorphism p hp)
  omega

/-- Annihilating a nonzero noninvertible morphism strictly decreases the
total number of nonzero morphisms. -/
theorem rayResidueCategory_nonzeroMorphism_card_lt
    [Finite C] [IsFiniteRayCategory C]
    {A B : C} (mu : A ⟶ B) (hmu : mu ≠ 0) (hmuIso : ¬IsIso mu) :
    letI : IsFiniteRayCategory (RayResidueCategory mu) :=
      rayResidueCategory_isFiniteRayCategory mu hmuIso
    Nat.card (NonzeroCategoryMorphism (RayResidueCategory mu)) <
      Nat.card (NonzeroCategoryMorphism C) := by
  let I := principalZeroHomIdeal mu
  letI : IsFiniteRayCategory (RayResidueCategory mu) :=
    rayResidueCategory_isFiniteRayCategory mu hmuIso
  let distinguished : NonzeroCategoryMorphism C := ⟨A, B, mu, hmu⟩
  let lift := NonzeroCategoryMorphism.quotOut I
  have hinj : Function.Injective lift :=
    NonzeroCategoryMorphism.quotOut_injective I
  have hnotSurj : ¬Function.Surjective lift := by
    intro hsurj
    obtain ⟨f, hf⟩ := hsurj distinguished
    have hnot := NonzeroCategoryMorphism.quotOut_not_mem I f
    apply hnot
    change NonzeroCategoryMorphism.quotOut I f = distinguished at hf
    rw [hf]
    change FactorsThroughMorphism mu mu
    exact ⟨𝟙 A, 𝟙 B, by simp⟩
  have hle := Nat.card_le_card_of_injective lift hinj
  apply lt_of_le_of_ne hle
  intro hcard
  have hbij : Function.Bijective lift :=
    (Nat.bijective_iff_injective_and_card lift).2 ⟨hinj, hcard⟩
  exact hnotSurj hbij.2

end LargeIndecomposable
