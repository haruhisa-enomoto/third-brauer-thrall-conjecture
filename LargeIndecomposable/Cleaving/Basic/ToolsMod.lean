module

public import LargeIndecomposable.Cleaving.Basic.Tools

/-!
# Thin diagrams with relations modulo `τ`

`MildHyp.not_thin_diagram'`: the version of `MildHyp.not_thin_diagram` where the
zero relations of the diagram only hold in `P/τ` (the composite factors through
`τ`), as in [mild] figure 3.3, where `ω' ≫ η` is only known to be zero in `P/τ`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable RayQuiver

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]

lemma ftm_comp_left {a b x y z : P} {μ : a ⟶ b} {g : y ⟶ z} (h : FactorsThroughMorphism μ g)
    (f : x ⟶ y) : FactorsThroughMorphism μ (f ≫ g) := by
  obtain ⟨c, d, rfl⟩ := h
  exact ⟨f ≫ c, d, by simp⟩

lemma ftm_comp_right {a b x y z : P} {μ : a ⟶ b} {f : x ⟶ y} (h : FactorsThroughMorphism μ f)
    (g : y ⟶ z) : FactorsThroughMorphism μ (f ≫ g) := by
  obtain ⟨c, d, rfl⟩ := h
  exact ⟨c, d ≫ g, by simp⟩

open Classical in
theorem MildHyp.not_thin_diagram' (hM : MildHyp k P)
    {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] {T : ThinData V}
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat T) k)) (Ar : ThinArrows T)
    (obj : V → P) (mor : ∀ x y, T.le x y → (obj x ⟶ obj y))
    (mor_id : ∀ x, mor x x (T.refl x) = 𝟙 _)
    (mor_comp : ∀ x y z (h : T.le x y) (h' : T.le y z),
      if hn : T.nz x y z then mor x y h ≫ mor y z h' = mor x z (T.nz_le x y z h h' hn)
      else FactorsThroughMorphism τ (mor x y h ≫ mor y z h'))
    (h0 : ∀ x y h, ¬FactorsThroughMorphism τ (mor x y h))
    (hleft : ∀ x z y (ha : Ar.ar x z) (hy : T.le x y),
      (∃ g, mor x z (Ar.ar_le x z ha) ≫ g = mor x y hy) → T.le z y ∧ T.nz x z y)
    (hright : ∀ x z y (ha : Ar.ar z y) (hx : T.le x y),
      (∃ g, g ≫ mor z y (Ar.ar_le z y ha) = mor x y hx) → T.le x z ∧ T.nz x z y) : False := by
  letI := rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  let D : ThinFunctorData T (RayCat.Res τ) :=
    { obj := fun x ↦ (resF τ).obj (obj x)
      mor := fun x y h ↦ (resF τ).map (mor x y h)
      mor_id := fun x ↦ by rw [mor_id]; exact (resF τ).map_id _
      mor_comp := fun x y z h h' ↦ by
        rw [← Functor.map_comp]
        have := mor_comp x y z h h'
        split_ifs with hn
        · rw [dif_pos hn] at this; rw [this]
        · rw [dif_neg hn] at this; exact (rayResidueFunctor_map_eq_zero_iff τ _).2 this }
  refine hM.not_thin_cleaving τ hτ hτ0 hD D Ar ⟨?_, ?_, ?_⟩
  · intro x y h hz
    exact h0 x y h ((rayResidueFunctor_map_eq_zero_iff τ _).1 hz)
  · rintro x z y ha hy ⟨g, hg⟩
    refine hleft x z y ha hy ⟨lift τ g, (resF_map_injective τ (h0 _ _ _) ?_).symm⟩
    rw [Functor.map_comp, resF_lift]
    exact hg.symm
  · rintro x z y ha hx ⟨g, hg⟩
    refine hright x z y ha hx ⟨lift τ g, (resF_map_injective τ (h0 _ _ _) ?_).symm⟩
    rw [Functor.map_comp, resF_lift]
    exact hg.symm

end RayCat

end LargeIndecomposable
