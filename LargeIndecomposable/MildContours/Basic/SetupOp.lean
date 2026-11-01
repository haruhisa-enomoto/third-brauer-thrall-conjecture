module

public import LargeIndecomposable.MildContours.Basic.Setup
public import LargeIndecomposable.RayCategories.Linearization.LinOp
public import LargeIndecomposable.RayCategories.Basic.Op

/-!
# `MildHyp` passes to the opposite category

The residue `Pᵒᵖ/τ` is anti-isomorphic to `P/τᵘⁿᵒᵖ` (`resAntiPair`), so their
linearizations are anti-isomorphic and representation-finiteness transfers
(`MildHyp.op`). Cancellation swaps sides.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat RayQuiver LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- The residue of `Pᵒᵖ` by `τ` is anti-isomorphic to the residue of `P` by
`τ.unop`. -/
def resAntiPair {a b : Pᵒᵖ} (τ : a ⟶ b) : AntiPair (Res τ) (Res τ.unop) where
  obj X := ⟨X.as.unop⟩
  obj' x := ⟨op x.as⟩
  hom {X Y} f := Quot.map (fun g : X.as ⟶ Y.as ↦ g.unop) (by
    intro g g' h
    cases h with
    | intro a' b' f m₁ m₂ g'' hm =>
      simp only [unop_comp, Category.assoc]
      refine HomRel.CompClosure.intro _ _ g''.unop m₁.unop m₂.unop f.unop ?_
      rcases hm with hm | ⟨hg, hg'⟩
      · exact Or.inl (by rw [hm])
      · obtain ⟨u, v, hu⟩ := hg
        obtain ⟨u', v', hu'⟩ := hg'
        exact Or.inr ⟨⟨v.unop, u.unop, by rw [hu]; simp [Category.assoc]⟩, ⟨v'.unop, u'.unop, by rw [hu']; simp [Category.assoc]⟩⟩) f
  hom' {x y} f := Quot.map (fun g : x.as ⟶ y.as ↦ g.op) (by
    intro g g' h
    cases h with
    | intro a' b' f m₁ m₂ g'' hm =>
      simp only [op_comp, Category.assoc]
      refine HomRel.CompClosure.intro _ _ g''.op m₁.op m₂.op f.op ?_
      rcases hm with hm | ⟨hg, hg'⟩
      · exact Or.inl (by rw [hm])
      · obtain ⟨u, v, hu⟩ := hg
        obtain ⟨u', v', hu'⟩ := hg'
        exact Or.inr ⟨⟨v.op, u.op, by rw [hu]; simp [Category.assoc]⟩, ⟨v'.op, u'.op, by rw [hu']; simp [Category.assoc]⟩⟩) f
  obj'_obj X := rfl
  obj_obj' x := rfl
  hom'_hom {X Y} f := by
    induction f using Quot.inductionOn with
    | _ g =>
      rw [eqToHom_refl, eqToHom_refl, Category.id_comp]
      erw [Category.comp_id]; rfl
  hom_hom' {x y} f := by
    induction f using Quot.inductionOn with
    | _ g =>
      rw [eqToHom_refl, eqToHom_refl, Category.id_comp]
      erw [Category.comp_id]; rfl
  map_comp {X Y Z} f g := by
    induction f using Quot.inductionOn with
    | _ f =>
      induction g using Quot.inductionOn with
      | _ g => rfl
  map_comp' {x y z} f g := by
    induction f using Quot.inductionOn with
    | _ f =>
      induction g using Quot.inductionOn with
      | _ g => rfl
  map_id X := rfl
  map_id' x := rfl
  map_zero := rfl
  map_zero' := rfl

variable [LargeIndecomposable.IsFiniteRayCategory P] [Finite P] {k : Type*} [Field k]

/-- **`MildHyp` passes to the opposite category.** -/
theorem MildHyp.op (hM : MildHyp k P) : MildHyp k Pᵒᵖ where
  left := leftCancel_op hM.right
  right := rightCancel_op hM.left
  res := by
    intro a b τ hτ hτ0
    have hτ' : ¬IsIso τ.unop := fun h ↦ hτ ((isIso_unop_iff τ).1 h)
    have hτ0' : τ.unop ≠ 0 := fun h ↦ hτ0 (Quiver.Hom.unop_inj (by rw [h, unop_zero]))
    have h := hM.res τ.unop hτ' hτ0'
    letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ.unop hτ'
    letI : IsRayCategory (RayCat.Res τ.unop) := isRayCategory_of_finiteRayCategory
    letI : Fintype (RayCat.Res τ.unop) := Fintype.ofFinite _
    letI : DecidableEq (RayCat.Res τ.unop) := Classical.decEq _
    letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
    letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
    letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
    letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
    exact (resAntiPair τ).isRepresentationFinite k h

end RayCat

end LargeIndecomposable
