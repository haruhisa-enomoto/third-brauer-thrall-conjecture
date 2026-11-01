module

public import LargeIndecomposable.Crowns.Lemma6.Setup
public import LargeIndecomposable.Cleaving.Shapes.ShapeD6

/-!
# BO13a Lemma 6, case I: helpers and figure 6.1

* `RayCat.not_ftm_long_dom/cod`: a long morphism divides a nonzero morphism
  with the same domain (codomain) only if it is a multiple of it.
* `RayQuiver.MulBasis.not_factors_both_last`: dual of Lemma 4 b) (last
  arrows), via `Pᵒᵖ`.
* `RayQuiver.MulBasis.l6_fig61`: figure 6.1 from the data of figure 6.0 and
  two morphisms `t₀ → y₀`, `t₁ → y₁`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable Opposite

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma not_ftm_long_dom {x y y' : P} {σ : x ⟶ y} (hσ : IsLong σ) {f : x ⟶ y'} (hf : f ≠ 0)
    (hv : ¬∃ c, σ ≫ c = f) : ¬FactorsThroughMorphism σ f := by
  intro h
  obtain ⟨hx, hy, he⟩ := hσ.2.2.2 f hf h
  exact hv ⟨eqToHom hy.symm, by rw [he]; simp⟩

lemma not_ftm_long_cod {x x' y : P} {σ : x ⟶ y} (hσ : IsLong σ) {f : x' ⟶ y} (hf : f ≠ 0)
    (hv : ¬∃ c, c ≫ σ = f) : ¬FactorsThroughMorphism σ f := by
  intro h
  obtain ⟨hx, hy, he⟩ := hσ.2.2.2 f hf h
  exact hv ⟨eqToHom hx, by rw [he]; simp⟩

variable [IsRayCategory P]

lemma pos_length_of_not_isIso {x y : RayVert P} (t : Quiver.Path x y)
    (ht : ¬IsIso (pathVal t : x.out ⟶ y.out)) : 0 < t.length := by
  cases t with
  | nil => exact absurd (IsIso.id _) ht
  | cons _ _ => simp

namespace L6Data

variable {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (D : L6Data σ ρ)

/-- `ψ`. -/
abbrev ψ : x ⟶ D.m.out := pathVal (D.α.toPath.comp D.χ)
/-- `u₂`. -/
abbrev U : D.m.out ⟶ y₀ := pathVal D.u₂
/-- `u₂'`. -/
abbrev U' : D.m.out ⟶ y₁ := pathVal D.u₂'
/-- `w₂`. -/
abbrev W : D.b.out ⟶ y₀ := pathVal D.w
/-- `w₂'`. -/
abbrev W' : D.b'.out ⟶ y₁ := pathVal D.w'

lemma ψU : D.ψ ≫ D.U = σ := by
  have := D.hσu; rw [pathVal_comp] at this; exact this
lemma ψU' : D.ψ ≫ D.U' = ρ := by
  have := D.hρu; rw [pathVal_comp] at this; exact this
lemma βW : D.β.1 ≫ D.W = σ := by
  have := D.hσw; rw [pathVal_comp, pathVal_toPath] at this; exact this
lemma βW' : D.β'.1 ≫ D.W' = ρ := by
  have := D.hρw; rw [pathVal_comp, pathVal_toPath] at this; exact this

lemma ψ_not_isIso : ¬IsIso D.ψ :=
  not_isIso_pathVal (D.α.toPath.comp D.χ) (by rw [Quiver.Path.length_comp]; simp)
lemma U_not_isIso : ¬IsIso D.U := not_isIso_pathVal _ D.hu₂
lemma U'_not_isIso : ¬IsIso D.U' := not_isIso_pathVal _ D.hu₂'

lemma W_not_isIso (hσ : ¬IsIrreducible σ) : ¬IsIso D.W := fun h ↦
  hσ (by rw [← D.βW]; exact IsIrreducible.comp_isIso D.β.2 D.W)

lemma W'_not_isIso (hρ : ¬IsIrreducible ρ) : ¬IsIso D.W' := fun h ↦
  hρ (by rw [← D.βW']; exact IsIrreducible.comp_isIso D.β'.2 D.W')

lemma U_U' (hv1 : ¬∃ c, σ ≫ c = ρ) : ¬∃ g, D.U ≫ g = D.U' := fun ⟨g, hg⟩ ↦
  hv1 ⟨g, by rw [← D.ψU, Category.assoc, hg, D.ψU']⟩

lemma U'_U (hv2 : ¬∃ c, ρ ≫ c = σ) : ¬∃ g, D.U' ≫ g = D.U := fun ⟨g, hg⟩ ↦
  hv2 ⟨g, by rw [← D.ψU', Category.assoc, hg, D.ψU]⟩

/-- `w₂` and `u₂` are incomparable from the left. -/
lemma W_U (hL : LeftCancel P) (hR : RightCancel P) (hσ0 : σ ≠ 0) (hσ : ¬IsIrreducible σ) :
    (¬∃ g, g ≫ D.W = D.U) ∧ (¬∃ g, g ≫ D.U = D.W) := by
  have hw := pos_length_of_not_isIso D.w (D.W_not_isIso hσ)
  have hval : pathVal ((D.α.toPath.comp D.χ).comp D.u₂) = pathVal (D.β.toPath.comp D.w) := by
    rw [D.hσu, D.hσw]
  have hσ0' : pathVal ((D.α.toPath.comp D.χ).comp D.u₂) ≠ 0 := by rw [D.hσu]; exact hσ0
  exact ⟨(contour_cross hL hR _ _ _ _ hval hσ0' D.hniσ (by simp) hw).1,
    (contour_cross hL hR _ _ _ _ hval.symm (by rw [← hval]; exact hσ0')
      (fun h ↦ D.hniσ h.symm) (by simp) D.hu₂).1⟩

/-- `w₂'` and `u₂'` are incomparable from the left. -/
lemma W'_U' (hL : LeftCancel P) (hR : RightCancel P) (hρ0 : ρ ≠ 0) (hρ : ¬IsIrreducible ρ) :
    (¬∃ g, g ≫ D.W' = D.U') ∧ (¬∃ g, g ≫ D.U' = D.W') := by
  have hw := pos_length_of_not_isIso D.w' (D.W'_not_isIso hρ)
  have hval : pathVal ((D.α.toPath.comp D.χ).comp D.u₂') = pathVal (D.β'.toPath.comp D.w') := by
    rw [D.hρu, D.hρw]
  have hρ0' : pathVal ((D.α.toPath.comp D.χ).comp D.u₂') ≠ 0 := by rw [D.hρu]; exact hρ0
  exact ⟨(contour_cross hL hR _ _ _ _ hval hρ0' D.hniρ (by simp) hw).1,
    (contour_cross hL hR _ _ _ _ hval.symm (by rw [← hval]; exact hρ0')
      (fun h ↦ D.hniρ h.symm) (by simp) D.hu₂').1⟩

end L6Data

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 4 b), dual form**: a morphism `ρ` incomparable from the left
with `σ = val v = val w` does not factor through the last arrows of both
paths of the contour `(v, w)`. -/
theorem not_factors_both_last
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x a b y : RayVert P} (α : a ⟶ y) (β : b ⟶ y)
    (v' : Quiver.Path x a) (w' : Quiver.Path x b)
    (hval : pathVal (v'.cons α) = pathVal (w'.cons β)) (h0 : pathVal (v'.cons α) ≠ 0)
    (hni : ¬Interlaced (v'.cons α) (w'.cons β)) {z : P} (ρ : z ⟶ y.out) (hρ : ρ ≠ 0)
    (hσρ : ¬∃ c, c ≫ pathVal (v'.cons α) = ρ) (hρσ : ¬∃ c, c ≫ ρ = pathVal (v'.cons α))
    (hα : ∃ c, c ≫ α.1 = ρ) (hβ : ∃ c, c ≫ β.1 = ρ) : False := by
  let _ : IsRayCategory Pᵒᵖ := isRayCategory_of_finiteRayCategory
  let _ : Fintype Pᵒᵖ := Fintype.ofFinite _
  let _ : DecidableEq Pᵒᵖ := Classical.decEq _
  have _ : FiniteDimensional k A := B.finiteDimensional
  have e1 : pathVal ((revArr α).toPath.comp (revPath v')) = (pathVal (v'.cons α)).op :=
    pathVal_revPath (v'.cons α)
  have e2 : pathVal ((revArr β).toPath.comp (revPath w')) = (pathVal (w'.cons β)).op :=
    pathVal_revPath (w'.cons β)
  refine (B.op).not_factors_both (hmin_op (k := k) hmin) (leftCancel_op hR) (rightCancel_op hL)
    (revArr α) (revArr β) (revPath v') (revPath w') (by rw [e1, e2, hval]) ?_ ?_ ⟨Opposite.op z, ρ.op⟩
    (fun h ↦ hρ (Quiver.Hom.op_inj h)) ?_ ?_ ?_ ?_
  · rw [e1]
    exact fun h ↦ h0 (Quiver.Hom.op_inj h)
  · intro h
    apply hni
    have := interlaced_unrevPath (P := P) h
    change Interlaced (unrevPath (revPath (v'.cons α))) (unrevPath (revPath (w'.cons β))) at this
    rwa [unrevPath_revPath, unrevPath_revPath] at this
  · rintro ⟨c, hc⟩
    change pathVal ((revArr α).toPath.comp (revPath v')) ≫ c = ρ.op at hc
    rw [e1] at hc
    exact hσρ ⟨c.unop, Quiver.Hom.op_inj (by rw [op_comp]; exact hc)⟩
  · rintro ⟨c, hc⟩
    change ρ.op ≫ c = pathVal ((revArr α).toPath.comp (revPath v')) at hc
    rw [e1] at hc
    exact hρσ ⟨c.unop, Quiver.Hom.op_inj (by rw [op_comp]; exact hc)⟩
  · obtain ⟨c, hc⟩ := hα
    exact ⟨c.op, by change α.1.op ≫ c.op = ρ.op; rw [← op_comp, hc]⟩
  · obtain ⟨c, hc⟩ := hβ
    exact ⟨c.op, by change β.1.op ≫ c.op = ρ.op; rw [← op_comp, hc]⟩

include B in
/-- **BO13a figure 6.1.** The data of figure 6.0 for long neighbours `σ, ρ`,
with morphisms `t₀ → y₀` and `t₁ → y₁` not dividing `σ`, `ρ` from the left and
not factoring through `w₂, u₂` resp. `w₂', u₂'`, give a cleaving `D̃₆` in
`P/σ`. -/
theorem l6_fig61
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) {T₀ T₁ : P} (t₀ : T₀ ⟶ y₀) (t₁ : T₁ ⟶ y₁)
    (h0t₀ : ¬FactorsThroughMorphism σ t₀) (h0t₁ : ¬FactorsThroughMorphism σ t₁)
    (hit₀ : ¬IsIso t₀) (hit₁ : ¬IsIso t₁)
    (hpk₀ : ¬∃ g, g ≫ t₀ = σ) (hpk₁ : ¬∃ g, g ≫ t₁ = ρ)
    (hW₀ : ¬∃ g, g ≫ D.W = t₀) (hU₀ : ¬∃ g, g ≫ D.U = t₀)
    (hW₁ : ¬∃ g, g ≫ D.W' = t₁) (hU₁ : ¬∃ g, g ≫ D.U' = t₁) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  refine B.not_d6s hmin hL hR σ hσ.2.1 hσ0 t₀ D.W D.U D.U' D.W' t₁ h0t₀
    (not_ftm_suffix hσ0 D.β.2.2.1 D.βW) (not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU)
    (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
      rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
    (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
      rw [← D.βW']; exact FactorsThroughMorphism.comp_left h _)) h0t₁
    hit₀ (D.W_not_isIso hσ.2.2.1) D.U_not_isIso D.U'_not_isIso (D.W'_not_isIso hρ.2.2.1) hit₁
    (D.U_U' hv1) (D.U'_U hv2) ?_ ?_ hW₀ (D.W_U hL hR hσ0 hσ.2.2.1).1 hU₀
    (D.W_U hL hR hσ0 hσ.2.2.1).2 ?_ ?_ hW₁ (D.W'_U' hL hR hρ0 hρ.2.2.1).1 hU₁
    (D.W'_U' hL hR hρ0 hρ.2.2.1).2
  · rintro ⟨g, hg⟩
    exact hpk₀ ⟨D.β.1 ≫ g, by rw [Category.assoc, hg, D.βW]⟩
  · rintro ⟨g, hg⟩
    exact hpk₀ ⟨D.ψ ≫ g, by rw [Category.assoc, hg, D.ψU]⟩
  · rintro ⟨g, hg⟩
    exact hpk₁ ⟨D.β'.1 ≫ g, by rw [Category.assoc, hg, D.βW']⟩
  · rintro ⟨g, hg⟩
    exact hpk₁ ⟨D.ψ ≫ g, by rw [Category.assoc, hg, D.ψU']⟩

end MulBasis

end RayQuiver

end LargeIndecomposable
