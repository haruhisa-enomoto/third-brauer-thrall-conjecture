module

public import LargeIndecomposable.Cleaving.Functors.BipCleaving
public import LargeIndecomposable.RayCategories.Quotients.MinimalQuotLin
public import LargeIndecomposable.Cleaving.PathCategories.ReorientedQuiver

/-!
# Bipartite cleaving diagrams in `P/τ`

A diagram of morphisms of `P` indexed by a bipartite quiver `Q` whose path
category is representation-infinite, avoiding `τ` and satisfying the zigzag
conditions, contradicts minimality (`RayQuiver.MulBasis.not_bip_diagram`).
This is the form in which BO13a uses most `D̃ₘ` diagrams.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- A non-invertible `τ` does not divide an identity. -/
lemma not_factorsThrough_id {a b : P} {τ : a ⟶ b} (hτ : ¬IsIso τ) (x : P) :
    ¬FactorsThroughMorphism τ (𝟙 x) := by
  rintro ⟨f, g, h⟩
  have h1 : IsIso ((f ≫ τ) ≫ g) := by rw [Category.assoc, ← h]; infer_instance
  have hfτ : f ≫ τ ≠ 0 := fun h0 ↦ IsRayCategory.id_ne_zero x (by rw [h, ← Category.assoc, h0, zero_comp])
  have h2 := isIso_of_isIso_comp _ g hfτ h1
  have hf : f ≠ 0 := fun h0 ↦ hfτ (by rw [h0, zero_comp])
  have h3 := isIso_of_isIso_comp f τ hf h2
  exact hτ (IsIso.of_isIso_comp_left f τ)

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **No bipartite cleaving diagram in `P/τ`.** -/
theorem not_bip_diagram
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {Q : Type} [Quiver.{0} Q] [Fintype Q] [DecidableEq Q]
    [∀ a b : Q, Subsingleton (a ⟶ b)] [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic Q)]
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat Q) k))
    (hb : PathCat.NoTwoPaths Q) (φ : Q ⥤q P)
    (h0 : ∀ {x y : Q} (e : x ⟶ y), ¬FactorsThroughMorphism τ (φ.map e))
    (hiso : ∀ {x y : Q} (e : x ⟶ y), ¬IsIso (φ.map e))
    (hl : ∀ {x y y' : Q} (e : x ⟶ y) (e' : x ⟶ y'), y ≠ y' → ¬∃ g, φ.map e ≫ g = φ.map e')
    (hr : ∀ {x x' y : Q} (e : x ⟶ y) (e' : x' ⟶ y), x ≠ x' → ¬∃ g, g ≫ φ.map e = φ.map e') :
    False := by
  let _ := rayResidueCategory_isFiniteRayCategory τ hτ
  let _ : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  have : ∀ a b : Q, Finite (a ⟶ b) := fun _ _ ↦ Finite.of_subsingleton
  let F := PathCat.lift (φ ⋙q (resF τ).toPrefunctor)
  have hFe : ∀ {x y : Q} (e : x ⟶ y), F.map (PathCat.ofPath e.toPath) = (resF τ).map (φ.map e) :=
    fun e ↦ by
      rw [PathCat.lift_map_ofPath]
      exact Category.id_comp _
  refine B.not_pathCat_cleaving_res hmin hL hR τ hτ hτ0 hD F
    (PathCat.arrowCleaving_of_bip hb Fact.out (fun e ↦ ?_) (fun e ↦ ?_) (fun e e' h ↦ ?_)
      (fun e e' h ↦ ?_))
  · rw [hFe]
    exact fun h ↦ h0 e ((rayResidueFunctor_map_eq_zero_iff τ _).1 h)
  · rw [hFe]
    intro hi
    obtain ⟨c, hc1, -⟩ := hi.out
    let c' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := c
    have h1 : 𝟙 _ = φ.map e ≫ lift τ c' := by
      refine resF_map_injective τ (not_factorsThrough_id hτ _) ?_
      rw [Functor.map_comp, resF_lift, CategoryTheory.Functor.map_id]
      exact hc1.symm
    have hne : φ.map e ≠ 0 := fun h ↦ h0 e ⟨0, 0, by rw [h]; simp⟩
    exact hiso e (RayCat.isIso_of_isIso_comp _ _ hne (by rw [← h1]; infer_instance))
  · rw [hFe, hFe]
    rintro ⟨g, hg⟩
    let g' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := g
    have hg' : (resF τ).map (φ.map e) ≫ (resF τ).map (lift τ g') =
        (resF τ).map (φ.map e') := by rw [resF_lift]; exact hg
    refine hl e e' h ⟨lift τ g', (resF_map_injective τ (h0 e') ?_).symm⟩
    rw [Functor.map_comp, hg']
  · rw [hFe, hFe]
    rintro ⟨g, hg⟩
    let g' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := g
    have hg' : (resF τ).map (lift τ g') ≫ (resF τ).map (φ.map e) =
        (resF τ).map (φ.map e') := by rw [resF_lift]; exact hg
    refine hr e e' h ⟨lift τ g', (resF_map_injective τ (h0 e') ?_).symm⟩
    rw [Functor.map_comp, hg']

end MulBasis

end RayQuiver

end LargeIndecomposable
