module

public import LargeIndecomposable.MildContours.Diamonds.CaseD
public import LargeIndecomposable.MildContours.Basic.SetupOp
public import LargeIndecomposable.Crowns.Lemma5.DualNeighbour
public import LargeIndecomposable.RayCategories.Basic.RayFirstArrow

/-!
# Diamond data

`DiamondData P`: the local data of a mild contour in case (D) once `γ` and `δ` are
known to be arrows: the arrows `γ δ α β`, the morphisms `η : a ⟶ x`, `ω' : y ⟶ a`,
the relations `γα = δβ`, `αω' = ηγ`, `τ = γαω'α ≠ 0`, and the non-factorizations used
by the cleaving diagrams. The list is closed under duality (`DiamondData.op`:
`x ↔ y`, `γ ↔ αᵒᵖ`, `δ ↔ βᵒᵖ`, `η ↔ ω'ᵒᵖ`), so each closure fact for `P_x` gives the
dual one for `I_y`. `MildContour.diamondData` builds it in case (D).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

/-- The local data of a diamond (case (D) of a mild contour). -/
structure DiamondData (P : Type) [Category.{0} P] [HasZeroMorphisms P] where
  x : P
  a : P
  b : P
  y : P
  γ : x ⟶ a
  δ : x ⟶ b
  α : a ⟶ y
  β : b ⟶ y
  η : a ⟶ x
  ω' : y ⟶ a
  hγ : IsIrreducible γ
  hδ : IsIrreducible δ
  hα : IsIrreducible α
  hβ : IsIrreducible β
  hη : ¬IsIso η
  hω' : ¬IsIso ω'
  hval : γ ≫ α = δ ≫ β
  hD : α ≫ ω' = η ≫ γ
  hτ0 : γ ≫ α ≫ ω' ≫ α ≠ 0
  apγδ : ¬∃ g, γ ≫ g = δ
  apδγ : ¬∃ g, δ ≫ g = γ
  apαβ : ¬∃ g, g ≫ α = β
  apβα : ¬∃ g, g ≫ β = α
  nA : ¬∃ g, g ≫ ω' = γ
  nA' : ¬∃ g, η ≫ g = α
  nB : ¬∃ g, g ≫ γ = ω'
  nB' : ¬∃ g, α ≫ g = η
  nL : ¬∃ g, g ≫ β = ω' ≫ α
  nL' : ¬∃ g, δ ≫ g = γ ≫ η
  nC : ¬∃ g, g ≫ γ = β ≫ ω'
  nC' : ¬∃ g, α ≫ g = η ≫ δ
  uniq : ∀ {c : P} (e : x ⟶ c) (g : c ⟶ y), IsIrreducible e → e ≫ g = γ ≫ α →
    (∃ h, γ ≫ h = e) ∨ (∃ h, δ ≫ h = e)
  uniq' : ∀ {c : P} (e : c ⟶ y) (g : x ⟶ c), IsIrreducible e → g ≫ e = γ ≫ α →
    (∃ h, h ≫ α = e) ∨ (∃ h, h ≫ β = e)
  zero : FactorsThroughMorphism (γ ≫ α ≫ ω' ≫ α) (ω' ≫ η)

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma neg_op_left {a b c : P} {f : a ⟶ b} {h : c ⟶ b} (H : ¬∃ g, g ≫ f = h) :
    ¬∃ g : op a ⟶ op c, f.op ≫ g = h.op := fun ⟨g, hg⟩ ↦
  H ⟨g.unop, Quiver.Hom.op_inj (by simpa using hg)⟩

lemma neg_op_right {a b c : P} {f : a ⟶ b} {h : a ⟶ c} (H : ¬∃ g, f ≫ g = h) :
    ¬∃ g : op c ⟶ op b, g ≫ f.op = h.op := fun ⟨g, hg⟩ ↦
  H ⟨g.unop, Quiver.Hom.op_inj (by simpa using hg)⟩

namespace DiamondData

variable (D : DiamondData P)

/-- `τ = γ α ω' α = γ η γ α`. -/
lemma τ_eq : D.γ ≫ D.α ≫ D.ω' ≫ D.α = D.γ ≫ D.η ≫ D.γ ≫ D.α := by
  rw [← Category.assoc D.α, D.hD]; simp

/-- **The dual diamond** in `Pᵒᵖ`. -/
def op : DiamondData Pᵒᵖ where
  x := Opposite.op D.y
  a := Opposite.op D.a
  b := Opposite.op D.b
  y := Opposite.op D.x
  γ := D.α.op
  δ := D.β.op
  α := D.γ.op
  β := D.δ.op
  η := D.ω'.op
  ω' := D.η.op
  hγ := (isIrreducible_op _).2 D.hα
  hδ := (isIrreducible_op _).2 D.hβ
  hα := (isIrreducible_op _).2 D.hγ
  hβ := (isIrreducible_op _).2 D.hδ
  hη := fun h ↦ D.hω' ((isIso_op_iff D.ω').1 h)
  hω' := fun h ↦ D.hη ((isIso_op_iff D.η).1 h)
  hval := by rw [← op_comp, ← op_comp, D.hval]
  hD := by rw [← op_comp, ← op_comp, D.hD]
  hτ0 := by
    intro h
    apply D.hτ0
    rw [D.τ_eq]
    apply Quiver.Hom.op_inj
    simpa using h
  apγδ := neg_op_left D.apαβ
  apδγ := neg_op_left D.apβα
  apαβ := neg_op_right D.apγδ
  apβα := neg_op_right D.apδγ
  nA := neg_op_right D.nA'
  nA' := neg_op_left D.nA
  nB := neg_op_right D.nB'
  nB' := neg_op_left D.nB
  nL := by have := neg_op_right D.nL'; rwa [op_comp] at this
  nL' := by have := neg_op_left D.nL; rwa [op_comp] at this
  nC := by have := neg_op_right D.nC'; rwa [op_comp] at this
  nC' := by have := neg_op_left D.nC; rwa [op_comp] at this
  uniq := by
    intro c e g he hg
    rcases D.uniq' e.unop g.unop ((isIrreducible_unop e).2 he)
      (Quiver.Hom.op_inj (by simpa using hg)) with ⟨h, hh⟩ | ⟨h, hh⟩
    · exact Or.inl ⟨h.op, by rw [← op_comp, hh]; rfl⟩
    · exact Or.inr ⟨h.op, by rw [← op_comp, hh]; rfl⟩
  uniq' := by
    intro c e g he hg
    rcases D.uniq e.unop g.unop ((isIrreducible_unop e).2 he)
      (Quiver.Hom.op_inj (by simpa using hg)) with ⟨h, hh⟩ | ⟨h, hh⟩
    · exact Or.inl ⟨h.op, by rw [← op_comp, hh]; rfl⟩
    · exact Or.inr ⟨h.op, by rw [← op_comp, hh]; rfl⟩
  zero := by
    have := (ftm_op_iff _ _).2 D.zero
    rw [D.τ_eq] at this
    simpa using this

end DiamondData


variable [IsRayCategory P] [Fintype P] [DecidableEq P] [IsFiniteRayCategory P]
  {k : Type*} [Field k] [Infinite k]

namespace MildContour

variable {x y : P} (C : MildContour x y)

/-- With `γ` an arrow, `v' = γ` as a path. -/
lemma v'_eq_of_irr (hγ : IsIrreducible C.γ) :
    ∃ e : (RayVert.mk x : RayVert P) ⟶ RayVert.mk C.sv, e.1 = C.γ ∧ C.v' = e.toPath := by
  have hl : C.v'.length ≠ 0 := fun h0 ↦ hγ.2.1 (isIso_pathVal_of_length_zero _ h0)
  obtain ⟨c', p', e', hv'⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons C.v').1 hl
  cases p' with
  | nil =>
      refine ⟨e', ?_, hv'⟩
      rw [show C.γ = pathVal C.v' from rfl, hv']; exact (Category.id_comp _).symm
  | cons q f =>
      exfalso
      rcases hγ.2.2 _ (pathVal (q.cons f)) e'.1 (by rw [show C.γ = pathVal C.v' from rfl, hv']; rfl)
        with h | h
      · exact not_isIso_pathVal (q.cons f) (by rw [Quiver.Path.length_cons]; omega) h
      · exact e'.2.2.1 h

/-- The first arrow of a path with value `ω` is `γ` or `δ` (path uniqueness). -/
lemma first_arrow (hM : MildHyp k P) (hγ : IsIrreducible C.γ) (hδ : IsIrreducible C.δ) {c : P}
    (e : x ⟶ c) (g : c ⟶ y) (he : IsIrreducible e) (hg : e ≫ g = C.γ ≫ C.α.1) :
    (∃ h, C.γ ≫ h = e) ∨ (∃ h, C.δ ≫ h = e) := by
  have hg0 : g ≠ 0 := fun h0 ↦ C.h0 (by change C.γ ≫ C.α.1 = 0; rw [← hg, h0, comp_zero])
  let ea : (RayVert.mk x : RayVert P) ⟶ RayVert.mk c := ⟨e, he⟩
  let u := ea.toPath.comp (pathOf g hg0)
  have hu : pathVal u = pathVal (C.v'.cons C.α) := by
    change pathVal (ea.toPath.comp (pathOf g hg0)) = C.γ ≫ C.α.1
    rw [pathVal_comp, pathVal_toPath, pathVal_pathOf]; exact hg
  obtain ⟨ev, hev, hv'⟩ := C.v'_eq_of_irr hγ
  obtain ⟨ew, hew, hw'⟩ := MildContour.v'_eq_of_irr C.swap (by exact hδ)
  have hfu : firstE u = some ⟨_, ea⟩ := firstE_toPath_comp _ _
  rcases hM.path_unique C.hval C.h0 C.hni C.ρ_not_isIso C.hωρ u hu with h | h
  · rw [h, hv', show ev.toPath.cons C.α = ev.toPath.comp (Quiver.Path.nil.cons C.α) from rfl,
      firstE_toPath_comp] at hfu
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 (Option.some.inj hfu)
    have hc : c = C.sv := congrArg RayVert.out h1.symm
    subst hc
    have : ea = ev := (eq_of_heq h2).symm
    exact Or.inl ⟨𝟙 _, by rw [Category.comp_id, ← hev, ← this]⟩
  · let ew' : (RayVert.mk x : RayVert P) ⟶ RayVert.mk C.sw := ew
    have hew' : ew'.1 = C.δ := hew
    have hw2 : C.w' = ew'.toPath := hw'
    rw [h, hw2, show ew'.toPath.cons C.β = ew'.toPath.comp (Quiver.Path.nil.cons C.β) from rfl,
      firstE_toPath_comp] at hfu
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 (Option.some.inj hfu)
    have hc : c = C.sw := congrArg RayVert.out h1.symm
    subst hc
    have : ea = ew' := (eq_of_heq h2).symm
    exact Or.inr ⟨𝟙 _, by rw [Category.comp_id, ← hew', ← this]⟩

/-- The last arrow of a path with value `ω` is `α` or `β`. -/
lemma last_arrow (hM : MildHyp k P) {c : P} (e : c ⟶ y) (g : x ⟶ c) (he : IsIrreducible e)
    (hg : g ≫ e = C.γ ≫ C.α.1) : (∃ h, h ≫ C.α.1 = e) ∨ (∃ h, h ≫ C.β.1 = e) := by
  have hg0 : g ≠ 0 := fun h0 ↦ C.h0 (by change C.γ ≫ C.α.1 = 0; rw [← hg, h0, zero_comp])
  let ea : (RayVert.mk c : RayVert P) ⟶ RayVert.mk y := ⟨e, he⟩
  let u := (pathOf g hg0).cons ea
  have hu : pathVal u = pathVal (C.v'.cons C.α) := by
    change pathVal (pathOf g hg0) ≫ e = C.γ ≫ C.α.1
    rw [pathVal_pathOf]; exact hg
  rcases hM.path_unique C.hval C.h0 C.hni C.ρ_not_isIso C.hωρ u hu with h | h
  · have h1 := Quiver.Path.obj_eq_of_cons_eq_cons h
    have h2 := Quiver.Path.hom_heq_of_cons_eq_cons h
    have hc : c = C.sv := congrArg RayVert.out h1
    subst hc
    exact Or.inl ⟨𝟙 _, by rw [Category.id_comp]; exact congrArg Subtype.val (eq_of_heq h2).symm⟩
  · have h1 := Quiver.Path.obj_eq_of_cons_eq_cons h
    have h2 := Quiver.Path.hom_heq_of_cons_eq_cons h
    have hc : c = C.sw := congrArg RayVert.out h1
    subst hc
    exact Or.inr ⟨𝟙 _, by rw [Category.id_comp]; exact congrArg Subtype.val (eq_of_heq h2).symm⟩

/-- **The diamond data of a mild contour in case (D).** -/
def diamondData (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    {η : C.sv ⟶ x} (hη : C.α.1 ≫ ω' = η ≫ C.γ) : DiamondData P where
  x := x
  a := C.sv
  b := C.sw
  y := y
  γ := C.γ
  δ := C.δ
  α := C.α.1
  β := C.β.1
  η := η
  ω' := ω'
  hγ := C.D_γirr hM hω' hρ hη
  hδ := C.D_δirr hM hω' hρ hη
  hα := C.α.2
  hβ := C.β.2
  hη := C.D_η hM hω' hρ hη
  hω' := hω'
  hval := C.hval
  hD := hη
  hτ0 := by have := C.τ_ne_zero; rwa [C.τ_eq_v, hρ] at this
  apγδ := (C.γ_δ_apart hM.right hM.left).2
  apδγ := (C.γ_δ_apart hM.right hM.left).1
  apαβ := (C.apart hM.right).2
  apβα := (C.apart hM.right).1
  nA := fun ⟨g, hg⟩ ↦ C.caseA hM hω' hρ hg
  nA' := fun ⟨g, hg⟩ ↦ by
    have hαω : C.α.1 ≫ ω' ≠ 0 := fun h0 ↦ C.τ_ne_zero (by
      rw [C.τ_eq_v, hρ, ← Category.assoc C.α.1, h0]; simp)
    exact C.caseA hM hω' hρ (ξ := g) (hM.left _ _ _ (show η ≫ (g ≫ ω') = η ≫ C.γ by
      rw [← Category.assoc, hg, hη]) (by rw [← Category.assoc, hg, hη, ← hη]; exact hαω))
  nB := fun ⟨g, hg⟩ ↦ C.caseB hM hρ g hg
  nB' := fun ⟨g, hg⟩ ↦ by
    have hαω : C.α.1 ≫ ω' ≠ 0 := fun h0 ↦ C.τ_ne_zero (by
      rw [C.τ_eq_v, hρ, ← Category.assoc C.α.1, h0]; simp)
    exact C.caseB hM hρ g (hM.left _ _ _ (show C.α.1 ≫ (g ≫ C.γ) = C.α.1 ≫ ω' by
      rw [← Category.assoc, hg, hη]) (by rw [← Category.assoc, hg, ← hη]; exact hαω))
  nL := fun ⟨g, hg⟩ ↦ C.not_ρ_factor_both hM hρ (ω'' := g) (by rw [hρ, hg])
  nL' := fun ⟨g, hg⟩ ↦ by
    have hvw : C.γ ≫ C.α.1 = C.δ ≫ C.β.1 := C.hval
    have hωω : C.γ ≫ C.α.1 ≫ ω' ≠ 0 := fun h0 ↦ C.τ_ne_zero (by
      rw [C.τ_eq_v, hρ, show C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 = (C.γ ≫ C.α.1 ≫ ω') ≫ C.α.1 by simp,
        h0, zero_comp])
    have e : C.δ ≫ (g ≫ C.γ) = C.δ ≫ (C.β.1 ≫ ω') := by
      rw [← Category.assoc, hg, Category.assoc, ← hη, ← Category.assoc, hvw, Category.assoc]
    have e2 := hM.left _ _ _ e (by rw [e, ← Category.assoc, ← hvw, Category.assoc]; exact hωω)
    exact C.crownD hM hω' hρ hη C.β.1 g C.δ C.ω_eq_w.symm e2.symm (C.apart hM.right).1
      (C.apart hM.right).2 (C.ftm_β hM.right)
  nC := fun ⟨g, hg⟩ ↦ C.crownD hM hω' hρ hη C.β.1 g C.δ C.ω_eq_w.symm hg.symm
      (C.apart hM.right).1 (C.apart hM.right).2 (C.ftm_β hM.right)
  nC' := fun ⟨g, hg⟩ ↦ by
    have hvw : C.γ ≫ C.α.1 = C.δ ≫ C.β.1 := C.hval
    have hηω : η ≫ C.δ ≫ C.β.1 = C.α.1 ≫ ω' ≫ C.α.1 := by
      rw [← hvw, ← Category.assoc, ← hη]; simp
    have e : C.α.1 ≫ (g ≫ C.β.1) = C.α.1 ≫ (ω' ≫ C.α.1) := by
      rw [← Category.assoc, hg, Category.assoc, hηω]
    exact C.not_ρ_factor_both hM hρ (ω'' := g)
      (by rw [hρ]; exact (hM.left _ _ _ e (by rw [e, ← hρ]; exact C.αρ_ne_zero)).symm)
  uniq := fun e g he hg ↦ C.first_arrow hM (C.D_γirr hM hω' hρ hη) (C.D_δirr hM hω' hρ hη) e g he hg
  uniq' := fun e g he hg ↦ C.last_arrow hM e g he hg
  zero := by have := C.D_zero hM hω' hρ hη; rwa [C.τ_eq_v, hρ] at this

end MildContour

end RayCat

end LargeIndecomposable
