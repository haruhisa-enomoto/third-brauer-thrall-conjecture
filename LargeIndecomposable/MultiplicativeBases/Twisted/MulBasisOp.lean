module

public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasis
public import LargeIndecomposable.RayCategories.Opposite.Op
public import LargeIndecomposable.Modules.Duality.OppositeDuality

/-!
# The dual multiplicative basis

A twisted multiplicative basis of `A` over `P` gives one of `Aᵐᵒᵖ` over `Pᵒᵖ`
(`RayQuiver.MulBasis.op`). With `hmin_op`, every statement proved for `P`
from a multiplicative basis and minimality holds for `Pᵒᵖ` as well: this is
the "duality" of BO13a §2.2.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits MulOpposite Opposite

universe u

namespace RayQuiver

namespace MulBasis

variable {k : Type u} [Field k] {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)
  [IsRayCategory Pᵒᵖ] [Fintype Pᵒᵖ] [DecidableEq Pᵒᵖ]

/-- The index equivalence of the bases. -/
def nzOp : NZ Pᵒᵖ ≃ NZ P where
  toFun μ := ⟨μ.2.1.unop, μ.1.unop, ⟨μ.2.2.1.unop, fun h ↦ μ.2.2.2 (by rw [← Quiver.Hom.op_unop μ.2.2.1, h]; rfl)⟩⟩
  invFun μ := ⟨op μ.2.1, op μ.1, ⟨μ.2.2.1.op, fun h ↦ μ.2.2.2 (by rw [← Quiver.Hom.unop_op μ.2.2.1, h]; rfl)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The dual multiplicative basis.** -/
def op : MulBasis k Pᵒᵖ Aᵐᵒᵖ where
  elt f := MulOpposite.op (B.elt f.unop)
  tw f g := B.tw g.unop f.unop
  elt_zero := by
    intro x y
    rw [show (0 : x ⟶ y).unop = 0 from rfl, B.elt_zero, MulOpposite.op_zero]
  elt_mul f g := by
    rw [← op_mul, B.elt_mul g.unop f.unop, op_smul]
    rfl
  elt_mul_ne f g h := by
    rw [← op_mul, B.elt_mul_ne g.unop f.unop (fun e ↦ h (congrArg Opposite.op e).symm), MulOpposite.op_zero]
  sum_id := by
    rw [← MulOpposite.op_one, ← B.sum_id]
    have := map_sum (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ) (fun x : P ↦ B.elt (𝟙 x)) Finset.univ
    rw [show MulOpposite.op (∑ x : P, B.elt (𝟙 x)) =
      (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ) (∑ x : P, B.elt (𝟙 x)) from rfl, this]
    exact Fintype.sum_equiv (Opposite.equivToOpposite.symm) _ _ (fun _ ↦ rfl)
  tw_id_left f := B.tw_id_right f.unop
  tw_id_right f := B.tw_id_left f.unop
  linearIndependent := by
    have h := (B.linearIndependent.comp _ (nzOp (P := P)).injective).map'
      (MulOpposite.opLinearEquiv k).toLinearMap (by simp)
    exact h
  span := by
    have hr : Set.range (fun μ : NZ Pᵒᵖ ↦ MulOpposite.op (B.elt μ.2.2.1.unop)) =
        (MulOpposite.opLinearEquiv k).toLinearMap '' Set.range (fun μ : NZ P ↦ B.elt μ.2.2.1) := by
      ext a
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨μ, rfl⟩; exact ⟨_, ⟨nzOp μ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨μ, rfl⟩, rfl⟩; exact ⟨(nzOp (P := P)).symm μ, rfl⟩
    change Submodule.span k (Set.range (fun μ : NZ Pᵒᵖ ↦ MulOpposite.op (B.elt μ.2.2.1.unop))) = ⊤
    rw [hr, Submodule.span_image, B.span, Submodule.map_top, LinearMap.range_eq_top]
    exact (MulOpposite.opLinearEquiv k).surjective

end MulBasis

end RayQuiver

end LargeIndecomposable
