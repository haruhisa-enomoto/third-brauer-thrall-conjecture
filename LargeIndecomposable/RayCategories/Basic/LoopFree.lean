module

public import LargeIndecomposable.FundamentalGroups.Basic.OpFund
public import LargeIndecomposable.FundamentalGroups.Basic.CocycleExtendMax

/-!
# Loop-free ray categories

A ray category is *loop-free* when every nonzero endomorphism has trivial homotopy class. This
passes to the reduction `P/⟨αᵢ⟩` of Lemma 2.2 (`loopFree_quot`, via `Φ ⋙ Ψ = 𝟭`) and to the
opposite category (`loopFree_op`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Opposite

/-- Every nonzero endomorphism has trivial homotopy class. -/
def LoopFree (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q] : Prop :=
  ∀ (a : Q) (e : a ⟶ a) (he : e ≠ 0), cls e he = 𝟙 _

lemma eq_id_of_conj {C : Type*} [Category C] {X Y : C} (f : X ⟶ X) (h : Y = X) (h' : X = Y)
    (H : 𝟙 Y = eqToHom h ≫ f ≫ eqToHom h') : f = 𝟙 X := by
  subst h
  simpa using H.symm

section Quot

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [LargeIndecomposable.IsFiniteRayCategory0 P]
  [Finite P] {ι : Type} {b : P} {d : ι → P} {α : ∀ i, b ⟶ d i} {hα : ∀ i, ¬IsIso (α i)}

attribute [local instance] isRayCategory_of_finiteRayCategory

/-- **Loop-freeness passes to the reduction.** -/
theorem loopFree_quot (D : RedData α) (hE : D.EssHyp (hα := hα)) (h : LoopFree P) :
    letI := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
    LoopFree (ArrowQuot α) := by
  letI := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
  intro a e he
  obtain ⟨p, hp⟩ := exists_path e he
  have hv := pathVal_inclQuiver α hα p
  have hne : pathVal ((inclQuiver α hα).mapPath p) ≠ 0 := fun h0 ↦ he (by
    rw [← hp, ← hv, h0]
    exact Functor.map_zero _ _ _)
  have h1 : (phiBar α hα).map (cls e he) = 𝟙 _ := by
    rw [cls_eq e he p hp]
    change (CategoryTheory.Quotient.lift homotopy (inclFG α hα ⋙
      CategoryTheory.Quotient.functor homotopy) _).map
        ((CategoryTheory.Quotient.functor homotopy).map _) = _
    rw [CategoryTheory.Quotient.lift_map_functor_map]
    change (CategoryTheory.Quotient.functor homotopy).map ((inclFG α hα).map (pathFG p)) = _
    rw [freeGroupoidFunctor_pathFG]
    exact (cls_eq _ hne _ rfl).symm.trans (h _ _ hne)
  have h2 := Functor.congr_hom (D.phiBar_psiBar hE) (cls e he)
  rw [Functor.comp_map, h1, CategoryTheory.Functor.map_id, Functor.id_map] at h2
  exact eq_id_of_conj _ _ _ h2

end Quot

section Op

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q]

/-- **Loop-freeness passes to the opposite category.** -/
theorem loopFree_op (h : LoopFree Q) : LoopFree Qᵒᵖ := by
  intro a e he
  obtain ⟨p, hp⟩ := exists_path e he
  have hne : pathVal (unrevPath p) ≠ 0 := by
    rw [pathVal_unrevPath, hp]
    exact fun h0 ↦ he (Quiver.Hom.unop_inj (by rw [h0]; rfl))
  have h1 : unopBar.map (cls e he) = 𝟙 _ := by
    rw [cls_eq e he p hp]
    change (CategoryTheory.Quotient.lift homotopy unopFG _).map
      ((CategoryTheory.Quotient.functor homotopy).map _) = _
    rw [CategoryTheory.Quotient.lift_map_functor_map, unopFG_map_pathFG]
    have h3 : pcls (unrevPath p) = 𝟙 _ := (cls_eq _ hne _ rfl).symm.trans (h _ _ hne)
    exact IsIso.inv_eq_of_hom_inv_id (by rw [h3]; exact Category.comp_id _)
  have h2 := Functor.congr_hom unopBar_opBar (cls e he)
  rw [Functor.comp_map, h1, CategoryTheory.Functor.map_id, Functor.id_map] at h2
  exact eq_id_of_conj _ _ _ h2

end Op

end LargeIndecomposable.RayCat
