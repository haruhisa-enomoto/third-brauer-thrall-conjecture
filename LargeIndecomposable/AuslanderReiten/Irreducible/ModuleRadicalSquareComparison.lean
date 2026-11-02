module

public import LargeIndecomposable.AuslanderReiten.Irreducible.CategoricalIrreducibleSpace
public import LargeIndecomposable.AuslanderReiten.Irreducible.IrreducibleRadicalQuotient

set_option backward.isDefEq.respectTransparency.types false

/-! # Intrinsic and module-skeleton radical-square definitions agree -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory

open LargeIndecomposable.CategoricalRadical
namespace LargeIndecomposable.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {ι : Type v} (S : IndecomposableSkeleton.{u,v,w} R ι)

/-- The intrinsic product ideal has the same Hom subgroup as the existing
arbitrary-middle radical-square factorization predicate. -/
theorem intrinsic_radicalSquare_eq (x y : ι) :
    ((homIdeal : MorphismIdeal (FGModuleCat.{w} R)) ⋆ᵢ homIdeal).hom (S.obj x) (S.obj y) =
      S.radicalSquareHomAddSubgroup x y := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).2
    rintro f ⟨M, a, b, ha, hb, rfl⟩
    exact (S.hasRadicalSquareFactorization_iff_categoricalRadical (a ≫ b)).mpr
      ⟨M, a, b, ha, hb, rfl⟩
  · intro f hf
    obtain ⟨M, a, b, ha, hb, rfl⟩ :=
      (S.hasRadicalSquareFactorization_iff_categoricalRadical f).mp hf
    exact MorphismIdeal.comp_mem_mul ha hb

end LargeIndecomposable.IndecomposableSkeleton
