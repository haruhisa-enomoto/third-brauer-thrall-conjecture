module

public import LargeIndecomposable.MildContours.Basic.Lemma22
public import LargeIndecomposable.RayCategories.Basic.Op

/-!
# Mild contours: reduction to the case `ρ = ω' ≫ α`

[mild] Lemma 2.1 and duality reduce "no non-deep contour" to the core case
where `ρ = π(y)` factors through the last arrow `α` of `v`
(`CoreHyp`). If Lemma 2.1 gives the alternative (2) instead, the contour is
also non-deep at `x`, and its reversal in `Pᵒᵖ` is a mild contour; Lemma 2.1
for the reversal gives (1) for it, or the alternative (2') which, combined with
(2), forces `σ = π(x)` to factor through the first arrow of `v` or `w`, which
is (1) for the reversal again (`MildContour.no_mildContour`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

/-- The core statement: no mild contour has `ρ` factoring through `α`. -/
def CoreHyp (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q] : Prop :=
  ∀ {x y : Q} (C : MildContour x y) (ω' : y ⟶ C.sv), C.ρ = ω' ≫ C.α.1 → False

lemma op_rpow {C : Type*} [Category C] {x : C} (e : x ⟶ x) : ∀ n, (rpow e n).op = rpow e.op n
  | 0 => rfl
  | n + 1 => by rw [rpow_succ, op_comp, op_rpow e n, ← rpow_succ']

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

lemma revPath_cons_first {x c y : RayVert P} (a : x ⟶ c) (v₁ : Quiver.Path c y) :
    revPath ((Quiver.Path.nil.cons a).comp v₁) = (revPath v₁).cons (revArr a) := by
  rw [revPath_comp]; rfl

variable [Fintype P] [DecidableEq P] [IsFiniteRayCategory P]

/-- **The reversed contour.** For paths `v = a₁ v₁`, `w = b₁ w₁` from `x` to
`y` with the same nonzero value, not interlaced, and `σ = π(x)` with
`σ ≫ v̄ ≠ 0`, the reversals form a mild contour of `Pᵒᵖ`. -/
def revContour {x y c d : RayVert P} (a : x ⟶ c)
    (v₁ : Quiver.Path c y) (b : x ⟶ d)
    (w₁ : Quiver.Path d y)
    (hval : pathVal ((Quiver.Path.nil.cons a).comp v₁) = pathVal ((Quiver.Path.nil.cons b).comp w₁))
    (h0 : pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
    (hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁))
    (σ : x.out ⟶ x.out) (hσ : ∀ e : x.out ⟶ x.out, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow σ n)
    (hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0) :
    letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
    MildContour (op y.out) (op x.out) :=
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  { sv := op c.out
    sw := op d.out
    v' := revPath v₁
    α := revArr a
    w' := revPath w₁
    β := revArr b
    hval := by
      rw [← revPath_cons_first a v₁, ← revPath_cons_first b w₁, pathVal_revPath, pathVal_revPath,
        hval]
    h0 := by
      rw [← revPath_cons_first a v₁, pathVal_revPath]
      exact fun h ↦ h0 (Quiver.Hom.op_inj (by rw [h, op_zero]))
    hni := fun h ↦ hni (by
      rw [← revPath_cons_first a v₁, ← revPath_cons_first b w₁] at h
      have := interlaced_unrevPath h
      rwa [unrevPath_revPath, unrevPath_revPath] at this)
    ρ := σ.op
    hρ := fun f hf ↦ by
      obtain ⟨n, hn, he⟩ := hσ f.unop (fun h ↦ hf (by
        have : IsIso f.unop.op := inferInstance
        exact this))
      exact ⟨n, hn, by rw [← op_rpow, ← he]; rfl⟩
    hωρ := by
      rw [← revPath_cons_first a v₁, pathVal_revPath]
      intro h
      apply hσω
      apply Quiver.Hom.op_inj
      rw [op_comp, h, op_zero] }

section Dual

variable {x y c d : RayVert P} (a : x ⟶ c) (v₁ : Quiver.Path c y) (b : x ⟶ d)
  (w₁ : Quiver.Path d y)
  (hval : pathVal ((Quiver.Path.nil.cons a).comp v₁) = pathVal ((Quiver.Path.nil.cons b).comp w₁))
  (h0 : pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)
  (hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp v₁) ((Quiver.Path.nil.cons b).comp w₁))
  (σ : x.out ⟶ x.out) (hσ : ∀ e : x.out ⟶ x.out, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow σ n)
  (hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) ≠ 0)

lemma revContour_ω :
    letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
    (revContour a v₁ b w₁ hval h0 hni σ hσ hσω).ω =
      (pathVal ((Quiver.Path.nil.cons a).comp v₁)).op := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  change pathVal ((revPath v₁).cons (revArr a)) = _
  rw [← revPath_cons_first a v₁, pathVal_revPath]

variable {k : Type*} [Field k] [Infinite k]

include b w₁ hval h0 hni hσ hσω in
/-- **Lemma 2.1 on the reversal**: unless the core case applies in `Pᵒᵖ`, the
contour is non-deep at `y` with `σ ≫ v̄ = v̄ ≫ R`. -/
theorem dual_step (hMo : MildHyp k Pᵒᵖ) (hcoreo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); CoreHyp Pᵒᵖ) :
    ∃ R : y.out ⟶ y.out, ¬IsIso R ∧
      σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) =
        pathVal ((Quiver.Path.nil.cons a).comp v₁) ≫ R := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  set C' := revContour a v₁ b w₁ hval h0 hni σ hσ hσω with hC'
  have hRo : RightCancel Pᵒᵖ := hMo.right
  have hω := revContour_ω a v₁ b w₁ hval h0 hni σ hσ hσω
  rw [← hC'] at hω
  have key : ∀ (g : (op y.out : Pᵒᵖ) ⟶ op y.out), ¬IsIso g → C'.τ = g ≫ C'.ω → ∃ R : y.out ⟶ y.out, ¬IsIso R ∧
      σ ≫ pathVal ((Quiver.Path.nil.cons a).comp v₁) =
        pathVal ((Quiver.Path.nil.cons a).comp v₁) ≫ R := by
    intro g hg he
    refine ⟨g.unop, fun h ↦ hg (by have : IsIso g.unop.op := inferInstance; exact this), ?_⟩
    have := congrArg Quiver.Hom.unop he
    change (C'.ω ≫ σ.op).unop = (g ≫ C'.ω).unop at this
    rw [unop_comp, unop_comp, hω] at this
    exact this
  rcases C'.lemma21 hMo with ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩
  · exact (hcoreo C' ξ hξ.symm).elim
  · exact (hcoreo C'.swap ξ hξ.symm).elim
  · exact key _ (not_isIso_comp_of_left _ _ (C'.γ_not_isIso hRo)) hξ
  · exact key _ (not_isIso_comp_of_left _ _ (C'.δ_not_isIso hRo)) hξ

end Dual

namespace MildContour

variable {k : Type*} [Field k] [Infinite k]

/-- The alternative (2) of Lemma 2.1 through `γ` leads to the core case for the
reversed contour. -/
theorem gamma_case (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hcoreo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); CoreHyp Pᵒᵖ) {x y : P}
    (C : MildContour x y) {ξ : C.sv ⟶ x} (hξ : C.τ = (C.γ ≫ ξ) ≫ C.ω) : False := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  obtain ⟨σ, hσ⟩ := hE x
  obtain ⟨n, hn, hn'⟩ := hσ _ (not_isIso_comp_of_left _ _ (C.γ_not_isIso hR))
  obtain ⟨c, a, v₁', hv'⟩ := path_first_arrow C.v' (by have := C.v'_pos hR; omega)
  obtain ⟨d, b, w₁', hw'⟩ := path_first_arrow C.w' (by have := C.w'_pos hR; omega)
  have hvfull : C.v'.cons C.α = (Quiver.Path.nil.cons a).comp (v₁'.cons C.α) := by rw [hv']; rfl
  have hwfull : C.w'.cons C.β = (Quiver.Path.nil.cons b).comp (w₁'.cons C.β) := by rw [hw']; rfl
  have hval : pathVal ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α)) =
      pathVal ((Quiver.Path.nil.cons b).comp (w₁'.cons C.β)) := by
    rw [← hvfull, ← hwfull]; exact C.hval
  have h0 : pathVal ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α)) ≠ 0 := by
    rw [← hvfull]; exact C.h0
  have hni : ¬Interlaced ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α))
      ((Quiver.Path.nil.cons b).comp (w₁'.cons C.β)) := by
    rw [← hvfull, ← hwfull]; exact C.hni
  have hωv : pathVal ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α)) = C.ω := by rw [← hvfull]
  have hτ : C.τ = rpow σ n ≫ C.ω := by rw [hξ, hn']
  have hσω : σ ≫ pathVal ((Quiver.Path.nil.cons a).comp (v₁'.cons C.α)) ≠ 0 := by
    rw [hωv]; intro h
    apply C.τ_ne_zero
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hτ, rpow_succ, Category.assoc, h, comp_zero]
  obtain ⟨R, hRi, hRe⟩ := dual_step (k := k) a (v₁'.cons C.α) b (w₁'.cons C.β) hval h0 hni σ hσ hσω
    hMo hcoreo
  rw [hωv] at hRe
  obtain ⟨i, hi, hRi'⟩ := C.hρ R hRi
  have hiter : ∀ m, rpow σ m ≫ C.ω = C.ω ≫ rpow C.ρ (m * i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [rpow_succ, Category.assoc, hRe, ← Category.assoc, ih, Category.assoc, hRi',
          ← rpow_add, Nat.succ_mul]
  have h1 : C.ω ≫ C.ρ = C.ω ≫ rpow C.ρ (n * i) := by
    change C.τ = _; rw [hτ, hiter]
  have h2 : rpow C.ρ 1 = rpow C.ρ (n * i) := by
    rw [show rpow C.ρ 1 = C.ρ by simp [rpow_succ]]
    exact hL _ _ _ h1 C.τ_ne_zero
  have hρ1 : rpow C.ρ 1 ≠ 0 := by
    rw [show rpow C.ρ 1 = C.ρ by simp [rpow_succ]]
    intro h
    apply C.τ_ne_zero
    change C.ω ≫ C.ρ = 0
    rw [h, comp_zero]
  have h3 := rpow_le_of_eq C.ρ C.ρ_not_isIso hρ1 h2
  have hn1 : n = 1 := by
    have : n * i ≤ 1 := h3
    rcases Nat.lt_or_ge 1 n with h | h
    · have : 2 ≤ n * i := le_trans (by omega) (Nat.mul_le_mul_right i h)
      omega
    · omega
  subst hn1
  have hσa : σ = a.1 ≫ (pathVal v₁' ≫ ξ) := by
    have hγ : C.γ = a.1 ≫ pathVal v₁' := by
      change pathVal C.v' = _; rw [hv', pathVal_comp]; change (𝟙 _ ≫ a.1) ≫ _ = _
      rw [Category.id_comp]
    rw [← Category.assoc, ← hγ, hn']; simp [rpow_succ]
  refine hcoreo (revContour a (v₁'.cons C.α) b (w₁'.cons C.β) hval h0 hni σ hσ hσω)
    (pathVal v₁' ≫ ξ).op ?_
  change σ.op = (pathVal v₁' ≫ ξ).op ≫ a.1.op
  rw [← op_comp, ← hσa]

/-- **No mild contour** in `P`, given the core case for `P` and `Pᵒᵖ`. -/
theorem no_mildContour (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hcore : CoreHyp P) (hcoreo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); CoreHyp Pᵒᵖ)
    {x y : P} (C : MildContour x y) : False := by
  rcases C.lemma21 hM with ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩
  · exact hcore C ξ hξ.symm
  · exact hcore C.swap ξ hξ.symm
  · exact C.gamma_case hM hMo hE hcoreo hξ
  · refine C.swap.gamma_case hM hMo hE hcoreo (ξ := ξ) ?_
    rw [swap_τ, swap_ω]; exact hξ

/-- Paths of a contour are nonempty. -/
lemma length_pos_of_contour {x y : RayVert P} {v w : Quiver.Path x y}
    (hval : pathVal v = pathVal w) (hni : ¬Interlaced v w) : 0 < v.length := by
  cases v with
  | nil =>
      cases w with
      | nil => exact absurd (Relation.EqvGen.refl _) hni
      | cons w' β =>
          exact absurd (by rw [← hval]; exact isIso_pathVal_nil) (not_isIso_pathVal _ (by simp))
  | cons _ _ => simp

/-- **Contours are deep** ([mild] Theorem 3 at the ray level, given the core
case for `P` and `Pᵒᵖ`): two non-interlaced paths with the same nonzero value
`ω` have `ω ≫ e = 0` and `e' ≫ ω = 0` for all non-invertible endomorphisms
`e`, `e'`. -/
theorem deep_of_contour (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hcore : CoreHyp P) (hcoreo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); CoreHyp Pᵒᵖ)
    {x y : RayVert P} (v w : Quiver.Path x y) (hval : pathVal v = pathVal w)
    (h0 : pathVal v ≠ 0) (hni : ¬Interlaced v w) :
    (∀ e : y.out ⟶ y.out, ¬IsIso e → pathVal v ≫ e = 0) ∧
      (∀ e : x.out ⟶ x.out, ¬IsIso e → e ≫ pathVal v = 0) := by
  have hy : ∀ e : y.out ⟶ y.out, ¬IsIso e → pathVal v ≫ e = 0 := by
    intro e he
    by_contra hne
    obtain ⟨ρ, hρ⟩ := hE y.out
    obtain ⟨n, hn, rfl⟩ := hρ e he
    have hωρ : pathVal v ≫ ρ ≠ 0 := by
      intro h; apply hne
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [rpow_succ', ← Category.assoc, h, zero_comp]
    cases v with
    | nil => exact absurd (length_pos_of_contour hval hni) (by simp)
    | cons v' α =>
        cases w with
        | nil => exact absurd (length_pos_of_contour hval.symm (fun h ↦ hni h.symm)) (by simp)
        | cons w' β =>
            exact MildContour.no_mildContour hM hMo hE hcore hcoreo
              (⟨_, _, v', α, w', β, hval, h0, hni, ρ, hρ, hωρ⟩ : MildContour x.out y.out)
  refine ⟨hy, fun e he ↦ ?_⟩
  by_contra hne
  obtain ⟨σ, hσ⟩ := hE x.out
  obtain ⟨n, hn, rfl⟩ := hσ e he
  have hσω : σ ≫ pathVal v ≠ 0 := by
    intro h; apply hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [rpow_succ, Category.assoc, h, comp_zero]
  obtain ⟨c, a, v₁, hv⟩ := path_first_arrow v (by have := length_pos_of_contour hval hni; omega)
  obtain ⟨d, b, w₁, hw⟩ := path_first_arrow w
    (by have := length_pos_of_contour hval.symm (fun h ↦ hni h.symm); omega)
  subst hv hw
  obtain ⟨R, hRi, hRe⟩ := dual_step (k := k) a v₁ b w₁ hval h0 hni σ hσ hσω hMo hcoreo
  exact hσω (by rw [hRe, hy R hRi])

end MildContour

end RayCat

end LargeIndecomposable
