module

public import LargeIndecomposable.RayCategories.Basic.MinimalQuotLin
public import LargeIndecomposable.Cleaving.Basic.BipDiagram

/-!
# Thin cleaving diagrams with conditions in `P`

`MulBasis.not_thin_diagram`: a thin diagram (a finite poset with zero
relations) given by objects and morphisms of `P`, whose morphisms are not
divisible by `τ` and which satisfies the arrow conditions of the local
cleaving criterion in `P`, cannot exist when its thin category is
representation-infinite.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

lemma not_split_mono {x y : P} {f : x ⟶ y} (hf : ¬IsIso f) : ¬∃ g, f ≫ g = 𝟙 x := by
  rintro ⟨g, hg⟩
  have hf0 : f ≠ 0 := fun h ↦ IsRayCategory.id_ne_zero x (by rw [← hg, h, zero_comp])
  exact hf (isIso_of_isIso_comp f g hf0 (by rw [hg]; infer_instance))

lemma not_split_epi {x y : P} {f : x ⟶ y} (hf : ¬IsIso f) : ¬∃ g, g ≫ f = 𝟙 y := by
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := fun h ↦ IsRayCategory.id_ne_zero y (by rw [← hg, h, zero_comp])
  have := isIso_of_isIso_comp g f hg0 (by rw [hg]; infer_instance)
  have e : f = inv g := by rw [← IsIso.inv_hom_id_assoc g f, hg, Category.comp_id]
  exact hf (by rw [e]; infer_instance)

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

open Classical in
include B in
/-- **No representation-infinite thin cleaving diagram in `P/τ`**, conditions in
`P`. -/
theorem not_thin_diagram
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] {T : ThinData V}
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat T) k)) (Ar : ThinArrows T)
    (obj : V → P) (mor : ∀ x y, T.le x y → (obj x ⟶ obj y))
    (mor_id : ∀ x, mor x x (T.refl x) = 𝟙 _)
    (mor_comp : ∀ x y z (h : T.le x y) (h' : T.le y z),
      mor x y h ≫ mor y z h' = if hn : T.nz x y z then mor x z (T.nz_le x y z h h' hn) else 0)
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
        rw [← Functor.map_comp, mor_comp]
        split_ifs <;> simp }
  refine B.not_thin_cleaving_res hmin hL hR τ hτ hτ0 hD D Ar ⟨?_, ?_, ?_⟩
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

end MulBasis

end RayQuiver

end LargeIndecomposable
