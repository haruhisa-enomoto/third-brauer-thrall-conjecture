module

public import LargeIndecomposable.MildContours.Basic.Assembly
public import LargeIndecomposable.MildContours.Basic.Global
public import LargeIndecomposable.Cleaving.Shapes.ShapePF1
public import LargeIndecomposable.Cleaving.Shapes.ShapePF2
public import LargeIndecomposable.Cleaving.Shapes.ShapeD4B

/-!
# [mild] Proposition PPF, first part: the penny-farthing contour is `v = α²`

Case (PF) of [mild] Lemma 2.2: `α` is a loop at `y` with `ρ = α` and the arrow
of `v` before `α` is `α`. Then `x = y` and `v = α α` (`PFData.v_eq`). The
proof follows [mild]: an arrow `β` in front of `αⁱ` (`i ≥ 2`) gives the
cleaving `D̃₅` of figure 2.4 (first diagram) unless `α α = η β` or
`β α = g β`, and both relations make `v` and `w` interlaced by Lemma 1.1;
for `v = αⁱ`, `i ≥ 3`, the second `D̃₅` of figure 2.4 is cleaving.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- The path `α ⋯ α` around a loop. -/
def loopPath {y : RayVert P} (α : y ⟶ y) : ℕ → Quiver.Path y y
  | 0 => .nil
  | n + 1 => (loopPath α n).cons α

lemma pathVal_loopPath {y : RayVert P} (α : y ⟶ y) : ∀ n, pathVal (loopPath α n) = rpow α.1 n
  | 0 => rfl
  | n + 1 => by
      change pathVal (loopPath α n) ≫ α.1 = rpow α.1 n ≫ α.1
      rw [pathVal_loopPath α n]

lemma loopPath_add {y : RayVert P} (α : y ⟶ y) (m : ℕ) : ∀ n,
    loopPath α (m + n) = (loopPath α m).comp (loopPath α n)
  | 0 => rfl
  | n + 1 => by
      change ((loopPath α (m + n)).cons α) = (loopPath α m).comp ((loopPath α n).cons α)
      rw [loopPath_add α m n, Quiver.Path.comp_cons]

lemma loopPath_length {y : RayVert P} (α : y ⟶ y) : ∀ n, (loopPath α n).length = n
  | 0 => rfl
  | n + 1 => by simp [loopPath, loopPath_length α n]

/-- One interlacing step. -/
lemma interlaced_step {x a b y : RayVert P} (p : Quiver.Path x a) (v' w' : Quiver.Path a b)
    (q : Quiver.Path b y) (hval : pathVal v' = pathVal w') (h0 : pathVal v' ≠ 0)
    (hpq : 0 < p.length ∨ 0 < q.length) :
    Interlaced ((p.comp v').comp q) ((p.comp w').comp q) :=
  Relation.EqvGen.rel _ _ ⟨a, b, p, v', w', q, rfl, rfl, hval, h0, hpq⟩

/-- Paths ending with apart arrows differ. -/
lemma cons_ne_of_apart {x a b y : RayVert P} (p : Quiver.Path x a) (e : a ⟶ y)
    (p' : Quiver.Path x b) (f : b ⟶ y) (h : ArrowsApart e f) : p.cons e ≠ p'.cons f := by
  intro hpq
  have hab := Quiver.Path.obj_eq_of_cons_eq_cons hpq
  have he := Quiver.Path.hom_heq_of_cons_eq_cons hpq
  subst hab
  have := eq_of_heq he
  subst this
  exact h.1 ⟨𝟙 _, Category.id_comp _⟩

/-- Equal paths start with the same arrow. -/
lemma first_arrow_eq {x c d y : RayVert P} {e : x ⟶ c} {e' : x ⟶ d} {r : Quiver.Path c y}
    {r' : Quiver.Path d y} (h : (Quiver.Path.nil.cons e).comp r = (Quiver.Path.nil.cons e').comp r') :
    ∃ h : c = d, HEq e e' := by
  have h' := congrArg revPath h
  rw [revPath_cons_first, revPath_cons_first] at h'
  have hcd := Quiver.Path.obj_eq_of_cons_eq_cons h'
  have he := Quiver.Path.hom_heq_of_cons_eq_cons h'
  have hcd' : c = d := by
    have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) hcd
    exact this
  subst hcd'
  refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
  have := congrArg (fun f : (RayVert.mk (Opposite.op c.out) : RayVert Pᵒᵖ) ⟶
    RayVert.mk (Opposite.op x.out) ↦ f.1.unop) (eq_of_heq he)
  exact this

/-- The two paths of a contour start with different arrows. -/
lemma first_arrows_ne (hL : LeftCancel P) {x y c d : RayVert P} {e : x ⟶ c} {e' : x ⟶ d}
    {v₁ : Quiver.Path c y} {w₁ : Quiver.Path d y}
    (hval : pathVal ((Quiver.Path.nil.cons e).comp v₁) = pathVal ((Quiver.Path.nil.cons e').comp w₁))
    (h0 : pathVal ((Quiver.Path.nil.cons e).comp v₁) ≠ 0)
    (hni : ¬Interlaced ((Quiver.Path.nil.cons e).comp v₁) ((Quiver.Path.nil.cons e').comp w₁)) :
    ¬∃ h : c = d, HEq e e' := by
  rintro ⟨h, he⟩
  subst h
  have he' := eq_of_heq he
  subst he'
  rw [pathVal_comp, pathVal_comp] at hval
  rw [pathVal_comp] at h0
  have hv : pathVal v₁ = pathVal w₁ := hL _ _ _ hval h0
  apply hni
  have := interlaced_step (Quiver.Path.nil.cons e) v₁ w₁ .nil hv
    (fun h ↦ h0 (by rw [h, comp_zero])) (Or.inl (by simp))
  simpa using this

/-- Contour data in case (PF) of [mild] Lemma 2.2: `v = q α α`, `w = w' β`,
`ρ = α`. -/
structure PFData (x y : RayVert P) where
  α : y ⟶ y
  t : RayVert P
  w' : Quiver.Path x t
  β : t ⟶ y
  q : Quiver.Path x y
  hval : pathVal ((q.cons α).cons α) = pathVal (w'.cons β)
  h0 : pathVal ((q.cons α).cons α) ≠ 0
  hni : ¬Interlaced ((q.cons α).cons α) (w'.cons β)
  hρ : ∀ f : y.out ⟶ y.out, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow α.1 n
  hωρ : pathVal ((q.cons α).cons α) ≫ α.1 ≠ 0

namespace PFData

variable {x y : RayVert P} (D : PFData x y)

/-- The underlying mild contour. -/
def C : MildContour x.out y.out :=
  ⟨y, D.t, D.q.cons D.α, D.α, D.w', D.β, D.hval, D.h0, D.hni, D.α.1, D.hρ, D.hωρ⟩

/-- The path `v`. -/
abbrev v : Quiver.Path x y := (D.q.cons D.α).cons D.α

lemma C_ω : D.C.ω = pathVal D.v := rfl

lemma C_τ : D.C.τ = pathVal D.v ≫ D.α.1 := rfl

variable [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

/-- **Step A**: the arrow in front of `αⁱ` (`i ≥ 2`) is `α` or `β`. -/
theorem prev (hM : MildHyp k P) {s : RayVert P} (r' : Quiver.Path x s) (e₀ : s ⟶ y) (j : ℕ)
    (hv : D.v = (r'.cons e₀).comp (loopPath D.α (j + 2))) :
    (∃ h : s = y, HEq e₀ D.α) ∨ (∃ h : s = D.t, HEq e₀ D.β) := by
  have hR : RightCancel P := hM.right
  have hap := D.C.apart hR
  have hτ0 := D.C.τ_ne_zero
  rcases arrows_eq_or_apart e₀ D.α with h | hea
  · exact Or.inl h
  rcases arrows_eq_or_apart e₀ D.β with h | heb
  · exact Or.inr h
  exfalso
  have hτ : D.C.τ = pathVal r' ≫ e₀.1 ≫ rpow D.α.1 (j + 2) ≫ D.α.1 := by
    rw [C_τ, hv, pathVal_comp, pathVal_loopPath]
    change ((pathVal r' ≫ e₀.1) ≫ _) ≫ _ = _
    simp only [Category.assoc]
  have hα := D.α.2.2.1
  have hτe : pathVal r' ≫ e₀.1 ≫ (rpow D.α.1 (j + 2) ≫ D.α.1) = D.C.τ := hτ.symm
  have hτe' : pathVal r' ≫ (e₀.1 ≫ D.α.1) ≫ (rpow D.α.1 (j + 1) ≫ D.α.1) = D.C.τ := by
    rw [hτ, rpow_succ' D.α.1 (j + 1)]; simp only [Category.assoc]
  exact hM.not_in3 D.C.τ D.C.τ_not_isIso hτ0 D.α.1 D.β.1 e₀.1 D.C.ρ D.C.ftm_ρ (D.C.ftm_α hR)
    (D.C.ftm_αρ hR) (D.C.ftm_β hR) (D.C.ftm_βρ hR)
    (MildContour.not_ftm_mid_right hτ0 (not_isIso_comp_of_right _ _ hα) hτe)
    (MildContour.not_ftm_mid_right hτ0 (not_isIso_comp_of_right _ _ hα) hτe')
    hα D.β.2.2.1 e₀.2.2.1 D.C.ρ_not_isIso hap.2 hea.1 hap.1 heb.1 hea.2 heb.2

/-- `v` is `α α` at the end; `pathVal v ≠ 0` gives `α ≫ α ≠ 0`. -/
lemma αα_ne_zero : D.α.1 ≫ D.α.1 ≠ 0 := D.C.αρ_ne_zero

/-- **Step B**: `β` does not stand in front of `αⁱ`, `i ≥ 2`. -/
theorem not_beta (hM : MildHyp k P) (r' : Quiver.Path x D.t) (j : ℕ)
    (hv : D.v = (r'.cons D.β).comp (loopPath D.α (j + 2))) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := D.C.apart hR
  have hτ0 := D.C.τ_ne_zero
  have hα := D.α.2.2.1
  have hβ := D.β.2.2.1
  have hapβα : ArrowsApart D.β D.α := ⟨hap.2, hap.1⟩
  have hω : pathVal D.v = pathVal r' ≫ D.β.1 ≫ rpow D.α.1 (j + 2) := by
    rw [hv, pathVal_comp, pathVal_loopPath]
    change (pathVal r' ≫ D.β.1) ≫ _ = _; rw [Category.assoc]
  have hτ : D.C.τ = pathVal r' ≫ D.β.1 ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ rpow D.α.1 j := by
    rw [C_τ, hω, Category.assoc, Category.assoc, ← rpow_succ, rpow_succ', rpow_succ',
      rpow_succ']
  have hvu : ∀ u : Quiver.Path x y, Interlaced D.v u → u = D.w'.cons D.β → False := by
    intro u h hu
    exact D.hni (hu ▸ h)
  -- the exception `α α = g β`
  have E1 : ¬∃ g, g ≫ D.β.1 = D.α.1 ≫ D.α.1 := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ D.αα_ne_zero (by rw [← hg, h, zero_comp])
    let L := (r'.cons D.β).comp (loopPath D.α j)
    have hvL : D.v = L.comp (loopPath D.α 2) := by
      rw [hv, loopPath_add, Quiver.Path.comp_assoc]
    let u' := (L.comp (pathOf (P := P) g hg0)).cons D.β
    have h2 : pathVal (loopPath D.α 2) = pathVal ((pathOf (P := P) g hg0).cons D.β) := by
      rw [pathVal_loopPath]
      change rpow D.α.1 2 = pathVal (pathOf (P := P) g hg0) ≫ D.β.1
      rw [pathVal_pathOf, hg]; simp [rpow_succ]
    have hstep : Interlaced D.v u' := by
      have := interlaced_step L (loopPath D.α 2) ((pathOf (P := P) g hg0).cons D.β) .nil h2
        (by rw [pathVal_loopPath]; simpa [rpow_succ] using D.αα_ne_zero)
        (Or.inl (by simp [L]))
      simpa [hvL, u'] using this
    have hu' : pathVal u' = pathVal D.v := (interlaced_val hstep).symm
    rcases hM.path_unique D.hval D.h0 D.hni (ρ := D.α.1) hα D.hωρ u' hu' with h | h
    · exact cons_ne_of_apart _ D.β _ D.α hapβα h
    · exact hvu u' hstep h
  -- the exception `β α = g β`
  have E2 : ¬∃ g, g ≫ D.β.1 = D.β.1 ≫ D.α.1 := by
    rintro ⟨g, hg⟩
    have hβ0 : D.β.1 ≠ 0 := fun h ↦ D.C.βρ_ne_zero (by change D.β.1 ≫ D.α.1 = 0; rw [h, zero_comp])
    have hgi : ¬IsIso g := by
      intro hgi
      obtain ⟨htt, he⟩ := RayQuiver.eq_id_of_isIso g
      have hg1 : g = 𝟙 _ := by rw [he]; rfl
      rw [hg1, Category.id_comp] at hg
      have := (IsRayCategory.eq_id_of_two_sided D.β.1 hβ0 (𝟙 _) D.α.1
        (by rw [Category.id_comp]; exact hg)).2
      exact hα (by rw [this]; infer_instance)
    have hiter : ∀ n, rpow (C := P) g n ≫ D.β.1 = D.β.1 ≫ rpow D.α.1 n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [rpow_succ, Category.assoc, hg, ← Category.assoc, ih, Category.assoc,
          ← rpow_succ]
    have hβα0 : D.β.1 ≫ rpow D.α.1 (j + 1) ≠ 0 := by
      intro h
      apply D.h0
      rw [hω, rpow_succ, ← Category.assoc D.β.1, h, zero_comp, comp_zero]
    have hg0 : g ≠ 0 := fun h ↦ D.C.βρ_ne_zero (by
      change D.β.1 ≫ D.α.1 = 0; rw [← hg, h, zero_comp])
    have hgn : rpow (C := P) g (j + 1) ≠ 0 := fun h ↦ hβα0 (by rw [← hiter, h, zero_comp])
    have hlen : 0 < (pathOf (P := P) g hg0).length := by
      by_contra h0
      exact hgi (by
        have := MildContour.isIso_pathVal_of_length_zero (pathOf (P := P) g hg0) (by omega)
        rwa [pathVal_pathOf] at this)
    have e1 : loopPath D.α (j + 2) = (Quiver.Path.nil.cons D.α).comp (loopPath D.α (j + 1)) := by
      rw [show j + 2 = 1 + (j + 1) by omega, loopPath_add]; rfl
    have hv1 : D.v = (r'.comp ((Quiver.Path.nil.cons D.β).cons D.α)).comp
        (loopPath D.α (j + 1)) := by
      rw [hv, e1, ← Quiver.Path.comp_assoc]; rfl
    let u₁ := (r'.comp ((pathOf (P := P) g hg0).cons D.β)).comp (loopPath D.α (j + 1))
    have step1 : Interlaced D.v u₁ := by
      rw [hv1]
      refine interlaced_step r' _ _ _ ?_ ?_ (Or.inr (by rw [loopPath_length]; omega))
      · change (𝟙 _ ≫ D.β.1) ≫ D.α.1 = pathVal (pathOf (P := P) g hg0) ≫ D.β.1
        rw [pathVal_pathOf, hg, Category.id_comp]
      · change (𝟙 _ ≫ D.β.1) ≫ D.α.1 ≠ 0
        rw [Category.id_comp]; exact D.C.βρ_ne_zero
    let u := ((r'.comp (pathOf (P := P) g hg0)).comp (pathOf (P := P) (rpow (C := P) g (j + 1)) hgn)).cons D.β
    have step2 : Interlaced u₁ u := by
      have hu₁ : u₁ = ((r'.comp (pathOf (P := P) g hg0)).comp
          ((Quiver.Path.nil.cons D.β).comp (loopPath D.α (j + 1)))).comp .nil := by
        simp only [u₁, Quiver.Path.comp_nil, ← Quiver.Path.comp_assoc, Quiver.Path.comp_cons]
      have hu : u = ((r'.comp (pathOf (P := P) g hg0)).comp
          ((pathOf (P := P) (rpow (C := P) g (j + 1)) hgn).cons D.β)).comp .nil := by
        simp only [u, Quiver.Path.comp_nil, Quiver.Path.comp_cons]
      rw [hu₁, hu]
      refine interlaced_step _ _ _ _ ?_ ?_ (Or.inl (by simp; omega))
      · rw [pathVal_comp, pathVal_loopPath]
        change (𝟙 _ ≫ D.β.1) ≫ _ = pathVal (pathOf (P := P) (rpow (C := P) g (j + 1)) hgn) ≫ D.β.1
        rw [pathVal_pathOf, hiter, Category.id_comp]
      · rw [pathVal_comp, pathVal_loopPath]
        change (𝟙 _ ≫ D.β.1) ≫ _ ≠ 0
        rw [Category.id_comp]; exact hβα0
    have hstep : Interlaced D.v u := Relation.EqvGen.trans _ _ _ step1 step2
    have hu' : pathVal u = pathVal D.v := (interlaced_val hstep).symm
    rcases hM.path_unique D.hval D.h0 D.hni (ρ := D.α.1) hα D.hωρ u hu' with h | h
    · exact cons_ne_of_apart _ D.β _ D.α hapβα h
    · exact hvu u hstep h
  have hrα : ∀ n, ¬IsIso (D.α.1 ≫ rpow D.α.1 n) := fun n ↦ not_isIso_comp_of_left _ _ hα
  exact hM.not_mpf1 D.C.τ D.C.τ_not_isIso hτ0 D.α.1 D.α.1 D.α.1 D.β.1 D.β.1
    (D.C.ftm_α hR) (D.C.ftm_αρ hR) (D.C.ftm_α hR) (D.C.ftm_αρ hR)
    (not_ftm_mid (q := rpow D.α.1 j) hτ0 (not_isIso_comp_of_right (pathVal r') D.β.1 hβ)
      (by rw [hτ]; simp only [Category.assoc]))
    (D.C.ftm_β hR) (D.C.ftm_βρ hR)
    (MildContour.not_ftm_mid_right (p := pathVal r') hτ0 (hrα j)
      (by rw [hτ]; simp only [Category.assoc]))
    (D.C.ftm_α hR) (D.C.ftm_β hR) (D.C.ftm_βρ hR)
    hα hα hα hβ hβ hap.2 hap.1 hap.2 hap.1 E1 E2

/-- **Step C**: `v = αⁱ` with `i ≥ 3` is impossible (figure 2.4, second diagram). -/
theorem not_long (hM : MildHyp k P) {x : RayVert P} (D : PFData x x) (j : ℕ)
    (hv : D.v = loopPath D.α (j + 3)) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := D.C.apart hR
  have hτ0 := D.C.τ_ne_zero
  have hα := D.α.2.2.1
  have hβ := D.β.2.2.1
  have hω : pathVal D.v = rpow D.α.1 (j + 3) := by rw [hv, pathVal_loopPath]
  have hωδ : pathVal D.v = pathVal D.w' ≫ D.β.1 := D.hval
  have hδi : ¬IsIso (pathVal D.w') := D.C.δ_not_isIso hR
  have hftmδ : ¬FactorsThroughMorphism D.C.τ (pathVal D.w') := D.C.ftm_δ hR
  have hτ : D.C.τ = rpow D.α.1 (j + 4) := by rw [C_τ, hω]; rfl
  have hω0 : pathVal D.v ≠ 0 := D.h0
  have hvw : ∀ u : Quiver.Path x x, Interlaced D.v u → Interlaced u (D.w'.cons D.β) → False :=
    fun u h1 h2 ↦ D.hni (Relation.EqvGen.trans _ _ _ h1 h2)
  -- `α g = δ`
  have H1 : ¬∃ g, D.α.1 ≫ g = pathVal D.w' := by
    rintro ⟨g, hg⟩
    have hδ0 : pathVal D.w' ≠ 0 := fun h ↦ hω0 (by rw [hωδ, h]; exact zero_comp)
    have hg0 : g ≠ 0 := fun h ↦ hδ0 (by rw [← hg, h, comp_zero])
    let u := ((Quiver.Path.nil.cons D.α).comp (pathOf (P := P) (x := x.out) (y := D.t.out) g hg0)).cons D.β
    have h1 : Interlaced u (D.w'.cons D.β) := by
      have := interlaced_step .nil ((Quiver.Path.nil.cons D.α).comp (pathOf (P := P) (x := x.out) (y := D.t.out) g hg0)) D.w'
        (Quiver.Path.nil.cons D.β) (by
          rw [pathVal_comp, pathVal_pathOf]; change (𝟙 _ ≫ D.α.1) ≫ g = _
          rw [Category.id_comp, hg]) (by
          rw [pathVal_comp, pathVal_pathOf]; change (𝟙 _ ≫ D.α.1) ≫ g ≠ 0
          rw [Category.id_comp, hg]
          intro h; apply hω0; rw [hωδ]; change pathVal D.w' ≫ _ = 0; rw [h, zero_comp])
        (Or.inr (by simp))
      simpa [u] using this
    have hgβ : g ≫ D.β.1 = rpow D.α.1 (j + 2) := by
      refine hL D.α.1 _ _ ?_ (by rw [← Category.assoc, hg, ← hωδ]; exact hω0)
      rw [← Category.assoc, hg, ← hωδ, hω, rpow_succ']
    have h2 : Interlaced D.v u := by
      have hv' : D.v = ((Quiver.Path.nil.cons D.α).comp (loopPath D.α (j + 2))).comp .nil := by
        rw [hv, Quiver.Path.comp_nil, show j + 3 = 1 + (j + 2) by omega, loopPath_add]; rfl
      have hu' : u = ((Quiver.Path.nil.cons D.α).comp ((pathOf (P := P) (x := x.out) (y := D.t.out) g hg0).cons D.β)).comp
          .nil := by
        simp only [u, Quiver.Path.comp_nil, Quiver.Path.comp_cons]
      rw [hv', hu']
      refine interlaced_step _ _ _ _ ?_ ?_ (Or.inl (by simp))
      · rw [pathVal_loopPath]; change _ = pathVal (pathOf (P := P) (x := x.out) (y := D.t.out) g hg0) ≫ _
        rw [pathVal_pathOf, hgβ]
      · rw [pathVal_loopPath, ← hgβ]; intro h
        apply hω0; rw [hω, rpow_succ', ← hgβ, h, comp_zero]
    exact hvw u h2 h1
  -- `g β = α α`
  have H2 : ¬∃ g, g ≫ D.β.1 = D.α.1 ≫ D.α.1 := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ D.αα_ne_zero (by rw [← hg, h, zero_comp])
    have hδ : pathVal D.w' = rpow D.α.1 (j + 1) ≫ g := by
      refine hR _ _ D.β.1 ?_ (by rw [← hωδ]; exact hω0)
      rw [← hωδ, hω, Category.assoc, hg, show j + 3 = (j + 1) + 2 by omega, rpow_add]
      simp [rpow_succ]
    let u := ((loopPath D.α (j + 1)).comp (pathOf (P := P) (x := x.out) (y := D.t.out) g hg0)).cons D.β
    have h1 : Interlaced D.v u := by
      have hv' : D.v = ((loopPath D.α (j + 1)).comp (loopPath D.α 2)).comp .nil := by
        rw [hv, Quiver.Path.comp_nil, show j + 3 = (j + 1) + 2 by omega, loopPath_add]
      have hu' : u = ((loopPath D.α (j + 1)).comp ((pathOf (P := P) (x := x.out) (y := D.t.out) g hg0).cons D.β)).comp
          .nil := by
        simp only [u, Quiver.Path.comp_nil, Quiver.Path.comp_cons]
      rw [hv', hu']
      refine interlaced_step _ _ _ _ ?_ ?_ (Or.inl (by rw [loopPath_length]; omega))
      · rw [pathVal_loopPath]; change _ = pathVal (pathOf (P := P) (x := x.out) (y := D.t.out) g hg0) ≫ _
        rw [pathVal_pathOf, hg]; simp [rpow_succ]
      · rw [pathVal_loopPath]; simpa [rpow_succ] using D.αα_ne_zero
    have h2 : Interlaced u (D.w'.cons D.β) := by
      have := interlaced_step .nil ((loopPath D.α (j + 1)).comp (pathOf (P := P) (x := x.out) (y := D.t.out) g hg0)) D.w'
        (Quiver.Path.nil.cons D.β) (by
          rw [pathVal_comp, pathVal_pathOf, pathVal_loopPath, ← hδ]) (by
          rw [pathVal_comp, pathVal_pathOf, pathVal_loopPath, ← hδ]
          intro h; apply hω0; rw [hωδ, h, zero_comp])
        (Or.inr (by simp))
      simpa [u] using this
    exact hvw u h1 h2
  -- `δ g = α α`
  have H3 : ¬∃ g, pathVal D.w' ≫ g = D.α.1 ≫ D.α.1 := by
    rintro ⟨g, hg⟩
    have : pathVal D.w' ≫ (g ≫ rpow D.α.1 (j + 1)) = pathVal D.w' ≫ D.β.1 := by
      rw [← Category.assoc, hg, ← hωδ, hω, rpow_succ' _ (j + 2), rpow_succ' _ (j + 1),
        Category.assoc]
    have h2 := hL _ _ _ this (by rw [this, ← hωδ]; exact hω0)
    have h3 : (g ≫ rpow D.α.1 j) ≫ D.α.1 = D.β.1 := by rw [Category.assoc, ← rpow_succ, h2]
    exact hap.2 ⟨_, h3⟩
  have H4 : ¬∃ g, pathVal D.w' ≫ g = D.α.1 := by
    rintro ⟨g, hg⟩
    rcases D.α.2.2.2 _ (pathVal D.w') g hg.symm with h | h
    · exact hδi h
    · exact H1 ⟨inv g, by rw [← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id]⟩
  have hτ3 : 𝟙 _ ≫ ((D.α.1 ≫ D.α.1) ≫ D.α.1) ≫ rpow D.α.1 (j + 1) = D.C.τ := by
    rw [hτ, rpow_succ' _ (j + 3), rpow_succ' _ (j + 2), rpow_succ' _ (j + 1)]
    simp only [Category.id_comp, Category.assoc]
  have hτδ : (D.α.1 ≫ pathVal D.w') ≫ D.β.1 = D.C.τ := by
    rw [Category.assoc, ← hωδ, hω, hτ, ← rpow_succ']
  exact hM.not_mpf2 D.C.τ D.C.τ_not_isIso hτ0 D.α.1 D.α.1 D.α.1 (pathVal D.w') D.β.1
    (D.C.ftm_α hR) (D.C.ftm_αρ hR) hftmδ (D.C.ftm_α hR) (D.C.ftm_αρ hR)
    (MildContour.not_ftm_mid_right hτ0 (not_isIso_comp_of_right _ _ hα) hτ3)
    (MildContour.not_ftm_left hτ0 hβ hτδ)
    (D.C.ftm_α hR) (D.C.ftm_β hR) (D.C.ftm_βρ hR)
    hα hα hα (hδi) hβ H1 H4 H3 hap.2 hap.1 H2

/-- Any way of writing `v = r αⁱ` (`i ≥ 2`) has `r` empty and `i = 2`. -/
theorem split_main (hM : MildHyp k P) (n : ℕ) : ∀ {x y : RayVert P} (D : PFData x y)
    (r : Quiver.Path x y) (j : ℕ), r.length = n → D.v = r.comp (loopPath D.α (j + 2)) →
      j = 0 ∧ n = 0 := by
  induction n with
  | zero =>
      intro x y D r j hn hv
      cases r with
      | nil =>
          refine ⟨?_, rfl⟩
          rcases j with _ | j
          · rfl
          · exact (not_long hM D j (by rw [hv, Quiver.Path.nil_comp])).elim
      | cons _ _ => simp at hn
  | succ n ih =>
      intro x y D r j hn hv
      cases r with
      | nil => simp at hn
      | cons r' e₀ =>
          exfalso
          rcases D.prev hM r' e₀ j hv with ⟨h, he⟩ | ⟨h, he⟩
          · subst h
            have he' := eq_of_heq he
            subst he'
            have e : loopPath D.α (j + 1 + 2) =
                (Quiver.Path.nil.cons D.α).comp (loopPath D.α (j + 2)) := by
              rw [show j + 1 + 2 = 1 + (j + 2) by omega, loopPath_add D.α 1 (j + 2)]; rfl
            have hv' : D.v = r'.comp (loopPath D.α (j + 1 + 2)) := by
              rw [hv, e, ← Quiver.Path.comp_assoc]; rfl
            have := ih D r' (j + 1) (by simpa using hn) hv'
            omega
          · subst h
            have he' := eq_of_heq he
            subst he'
            exact D.not_beta hM r' j hv

/-- **[mild] PPF, first part**: in case (PF), `v = α α` (so `x = y`). -/
theorem q_length (hM : MildHyp k P) : D.q.length = 0 :=
  (split_main hM _ D D.q 0 rfl rfl).2

/-- **[mild] PPF, the points of `w` other than its ends differ from `x₀`**: `w`
does not return to `x₀` before its end. -/
theorem no_return (hM : MildHyp k P) {x : RayVert P} (D : PFData x x) (hq : D.q = .nil)
    (w₁ w₂ : Quiver.Path x x) (hw : D.w'.cons D.β = w₁.comp w₂) (h₁ : 0 < w₁.length)
    (h₂ : 0 < w₂.length) : False := by
  have hα := D.α.2.2.1
  have hv : D.v = (Quiver.Path.nil.cons D.α).cons D.α := by
    show (D.q.cons D.α).cons D.α = _; rw [hq]
  have hω : pathVal D.v = D.α.1 ≫ D.α.1 := by
    rw [hv]; change (𝟙 _ ≫ D.α.1) ≫ D.α.1 = _; rw [Category.id_comp]
  have hω2 : pathVal D.v = rpow D.α.1 2 := by rw [hω]; simp [rpow_succ]
  have hw12 : pathVal D.v = pathVal w₁ ≫ pathVal w₂ := by rw [D.hval, hw, pathVal_comp]
  obtain ⟨r, hr, hr'⟩ := D.hρ _ (not_isIso_pathVal _ h₁)
  obtain ⟨s, hs, hs'⟩ := D.hρ _ (not_isIso_pathVal _ h₂)
  have hrs : rpow D.α.1 2 = rpow D.α.1 (r + s) := by rw [← hω2, hw12, hr', hs', rpow_add]
  have hle := MildContour.rpow_le_of_eq D.α.1 hα (by rw [← hω2]; exact D.h0) hrs
  have hr1 : r = 1 := by omega
  have hs1 : s = 1 := by omega
  subst hr1 hs1
  have hα1 : rpow D.α.1 1 = D.α.1 := by simp [rpow_succ]
  let u := (Quiver.Path.nil.cons D.α).comp w₂
  have h1 : Interlaced D.v u := by
    have := interlaced_step (Quiver.Path.nil.cons D.α) (Quiver.Path.nil.cons D.α) w₂ .nil
      (by rw [hs', hα1]; change 𝟙 _ ≫ D.α.1 = _; rw [Category.id_comp])
      (by change 𝟙 _ ≫ D.α.1 ≠ 0; rw [Category.id_comp]; exact D.α.2.1)
      (Or.inl (by simp))
    rw [hv]; simpa [u] using this
  have h2 : Interlaced u (D.w'.cons D.β) := by
    have := interlaced_step .nil (Quiver.Path.nil.cons D.α) w₁ w₂
      (by rw [hr', hα1]; change 𝟙 _ ≫ D.α.1 = _; rw [Category.id_comp])
      (by change 𝟙 _ ≫ D.α.1 ≠ 0; rw [Category.id_comp]; exact D.α.2.1)
      (Or.inr h₂)
    rw [hw]; simpa [u] using this
  exact D.hni (Relation.EqvGen.trans _ _ _ h1 h2)

section Closed

variable {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P} (a₁ : x ⟶ c)
  (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)
include hq hw

lemma ω_pf : pathVal D.v = D.α.1 ≫ D.α.1 := by
  show pathVal ((D.q.cons D.α).cons D.α) = _
  rw [hq]; change (𝟙 _ ≫ D.α.1) ≫ D.α.1 = _; rw [Category.id_comp]

lemma ω_pf_w : pathVal D.v = a₁.1 ≫ pathVal w₁ ≫ D.β.1 := by
  rw [D.hval]; change pathVal D.w' ≫ D.β.1 = _
  rw [hw, pathVal_comp]; change ((𝟙 _ ≫ a₁.1) ≫ _) ≫ _ = _
  rw [Category.id_comp, Category.assoc]

/-- **Fig. 2.4, third diagram**: `β ≫ a₁` lies in the ideal of `τ = ρ³`. -/
theorem β_a₁ (hM : MildHyp k P) : FactorsThroughMorphism D.C.τ (D.β.1 ≫ a₁.1) := by
  by_contra h
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := D.C.apart hR
  have hτ0 := D.C.τ_ne_zero
  have hα := D.α.2.2.1
  have hω := D.ω_pf hq a₁ w₁ hw
  have hωw := D.ω_pf_w hq a₁ w₁ hw
  have hτ : D.C.τ = D.α.1 ≫ D.α.1 ≫ D.α.1 := by
    rw [C_τ, hω, Category.assoc]
  -- the out-arrows `α`, `a₁` of `x` are distinct
  have hvv : D.v = (Quiver.Path.nil.cons D.α).comp (Quiver.Path.nil.cons D.α) := by
    show (D.q.cons D.α).cons D.α = _; rw [hq]; rfl
  have hww : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (w₁.cons D.β) := by
    rw [hw]; rfl
  have hout := (arrows_eq_or_apart_out D.α a₁).resolve_left (first_arrows_ne hL
    (by rw [← hvv, ← hww]; exact D.hval) (by rw [← hvv]; exact D.h0)
    (by rw [← hvv, ← hww]; exact D.hni))
  have hτa₁ : 𝟙 _ ≫ a₁.1 ≫ (pathVal w₁ ≫ D.β.1 ≫ D.α.1) = D.C.τ := by
    rw [C_τ, hωw]; simp only [Category.id_comp, Category.assoc]
  have hταa₁ : 𝟙 _ ≫ (D.α.1 ≫ a₁.1) ≫ (pathVal w₁ ≫ D.β.1) = D.C.τ := by
    rw [hτ, ← hω, hωw]; simp only [Category.id_comp, Category.assoc]
  have hr : ¬IsIso (pathVal w₁ ≫ D.β.1 ≫ D.α.1) :=
    not_isIso_comp_of_right _ _ (not_isIso_comp_of_right _ _ hα)
  have hr' : ¬IsIso (pathVal w₁ ≫ D.β.1) := not_isIso_comp_of_right _ _ D.β.2.2.1
  exact hM.not_md4b D.C.τ D.C.τ_not_isIso hτ0 D.α.1 D.β.1 D.α.1 a₁.1
    (D.C.ftm_α hR) (MildContour.not_ftm_mid_right hτ0 hr hτa₁) (D.C.ftm_α hR) (D.C.ftm_αρ hR)
    (MildContour.not_ftm_mid_right hτ0 hr' hταa₁) (D.C.ftm_β hR) (D.C.ftm_βρ hR) h
    hα D.β.2.2.1 hα a₁.2.2.1 hout.1 hout.2 hap.2 hap.1

/-- `ρ⁴ = 0`, `ρ² ≫ a₁ = 0` and `β ≫ ρ² = 0` (from `β ≫ a₁ ∈ (ρ³)`). -/
theorem rho_four (hM : MildHyp k P) :
    rpow D.α.1 4 = 0 ∧ (D.α.1 ≫ D.α.1) ≫ a₁.1 = 0 ∧ D.β.1 ≫ D.α.1 ≫ D.α.1 = 0 := by
  have hα := D.α.2.2.1
  have hω := D.ω_pf hq a₁ w₁ hw
  have hωw := D.ω_pf_w hq a₁ w₁ hw
  obtain ⟨u, v', huv⟩ := D.β_a₁ hq a₁ w₁ hw hM
  have hτ : D.C.τ = rpow D.α.1 3 := by
    rw [C_τ, hω]; simp [rpow_succ]
  obtain ⟨p₁, hp₁, hp₁'⟩ := D.hρ (a₁.1 ≫ pathVal w₁ ≫ u)
    (not_isIso_comp_of_left _ _ a₁.2.2.1)
  obtain ⟨p₂, hp₂, hp₂'⟩ := D.hρ (v' ≫ pathVal w₁ ≫ D.β.1)
    (not_isIso_comp_of_right _ _ (not_isIso_comp_of_right _ _ D.β.2.2.1))
  have hρ2 : D.α.1 ≫ D.α.1 = a₁.1 ≫ pathVal w₁ ≫ D.β.1 := by rw [← hω, hωw]
  have h4 : rpow D.α.1 4 = rpow D.α.1 (p₁ + 3 + p₂) := by
    have : rpow D.α.1 4 = (D.α.1 ≫ D.α.1) ≫ (D.α.1 ≫ D.α.1) := by simp [rpow_succ]
    rw [this, rpow_add, rpow_add, ← hp₁', ← hp₂', ← hτ, hρ2]
    conv_lhs => rw [show a₁.1 ≫ pathVal w₁ ≫ D.β.1 = a₁.1 ≫ pathVal w₁ ≫ D.β.1 from rfl]
    simp only [Category.assoc]
    rw [← Category.assoc D.β.1 a₁.1, huv]; simp only [Category.assoc]
  have hzero : rpow D.α.1 4 = 0 := by
    by_contra hne
    have := MildContour.rpow_le_of_eq D.α.1 hα hne h4
    omega
  have hhi : ∀ n, 4 ≤ n → rpow D.α.1 n = 0 := fun n hn ↦ by
    rw [show n = 4 + (n - 4) by omega, rpow_add, hzero, zero_comp]
  refine ⟨hzero, ?_, ?_⟩
  · rw [hρ2]
    have : (a₁.1 ≫ pathVal w₁ ≫ D.β.1) ≫ a₁.1 = rpow D.α.1 (p₁ + 3) ≫ v' := by
      rw [rpow_add, ← hp₁', ← hτ]; simp only [Category.assoc]
      rw [huv]; simp only [MildContour.τ, Category.assoc]
    rw [this, hhi _ (by omega), zero_comp]
  · rw [hρ2]
    have : D.β.1 ≫ a₁.1 ≫ pathVal w₁ ≫ D.β.1 = u ≫ rpow D.α.1 (3 + p₂) := by
      rw [rpow_add, ← hp₂', ← hτ, ← Category.assoc D.β.1 a₁.1, huv]
      simp only [Category.assoc]
    rw [this, hhi _ (by omega), comp_zero]

omit hw in
/-- A proper prefix of `w` is not of the form `ρ ≫ d`. -/
theorem prefix_not_rho (hM : MildHyp k P) {q : RayVert P} (p : Quiver.Path x q)
    (s₁ : Quiver.Path q x) (hs : 0 < s₁.length) (hps : D.w'.cons D.β = p.comp s₁) :
    ¬∃ d : x.out ⟶ q.out, pathVal p = D.α.1 ≫ d := by
  rintro ⟨d, hd⟩
  have hL : LeftCancel P := hM.left
  have hvv : D.v = (Quiver.Path.nil.cons D.α).cons D.α := by
    show (D.q.cons D.α).cons D.α = _; rw [hq]
  have hω : pathVal D.v = D.α.1 ≫ D.α.1 := by
    rw [hvv]; change (𝟙 _ ≫ D.α.1) ≫ D.α.1 = _; rw [Category.id_comp]
  have hωps : pathVal D.v = pathVal p ≫ pathVal s₁ := by rw [D.hval, hps, pathVal_comp]
  have hd0 : d ≠ 0 := fun h ↦ D.h0 (by rw [hωps, hd, h, comp_zero, zero_comp])
  let u := ((Quiver.Path.nil.cons D.α).comp (pathOf (P := P) (x := x.out) (y := q.out) d hd0)).comp s₁
  have h1 : Interlaced u (D.w'.cons D.β) := by
    rw [hps]
    have := interlaced_step .nil ((Quiver.Path.nil.cons D.α).comp
      (pathOf (P := P) (x := x.out) (y := q.out) d hd0)) p s₁ (by
        rw [pathVal_comp, pathVal_pathOf, hd]; change (𝟙 _ ≫ D.α.1) ≫ d = _
        rw [Category.id_comp]) (by
        rw [pathVal_comp, pathVal_pathOf]; change (𝟙 _ ≫ D.α.1) ≫ d ≠ 0
        rw [Category.id_comp, ← hd]; intro h; apply D.h0; rw [hωps, h, zero_comp])
      (Or.inr hs)
    simpa [u] using this
  have hds : d ≫ pathVal s₁ = D.α.1 := by
    refine hL D.α.1 _ _ ?_ ?_
    · rw [← Category.assoc, ← hd, ← hωps, hω]
    · rw [← Category.assoc, ← hd, ← hωps]; exact D.h0
  have h2 : Interlaced D.v u := by
    rw [hvv]
    have := interlaced_step (Quiver.Path.nil.cons D.α) (Quiver.Path.nil.cons D.α)
      ((pathOf (P := P) (x := x.out) (y := q.out) d hd0).comp s₁) .nil (by
        rw [pathVal_comp, pathVal_pathOf, hds]; change 𝟙 _ ≫ D.α.1 = _; rw [Category.id_comp])
      (by change 𝟙 _ ≫ D.α.1 ≠ 0; rw [Category.id_comp]; exact D.α.2.1) (Or.inl (by simp))
    simpa [u, Quiver.Path.comp_assoc] using this
  exact D.hni (Relation.EqvGen.trans _ _ _ h2 h1)

/-- An endomorphism of `x₀` is the identity or a positive power of `ρ`. -/
lemma endo_cases (a : x.out ⟶ x.out) : a = 𝟙 _ ∨ ∃ n, 0 < n ∧ a = rpow D.α.1 n := by
  by_cases ha : IsIso a
  · left
    obtain ⟨hxx, he⟩ := RayQuiver.eq_id_of_isIso a
    rw [he]; rfl
  · exact Or.inr (D.hρ a ha)

/-- **Key lemma Z**: a radical endomorphism at an interior point `q` of `w` kills
the prefix of `w` ending at `q`. Otherwise `ρ ≫ λ = λ ≫ c'` for a radical
`c'`, and the crown `Ã(λ, c', μ, ρ)` cleaves into `P/ρ³`. -/
theorem Z (hM : MildHyp k P) (hE : EndCyclic P) {q : RayVert P} (p : Quiver.Path x q)
    (s₁ : Quiver.Path q x) (hp : 0 < p.length) (hs : 0 < s₁.length)
    (hps : D.w'.cons D.β = p.comp s₁) (c : q.out ⟶ q.out) (hc : ¬IsIso c) : pathVal p ≫ c = 0 := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hα := D.α.2.2.1
  have hτ0 := D.C.τ_ne_zero
  have hω := D.ω_pf hq a₁ w₁ hw
  have hωps : pathVal D.v = pathVal p ≫ pathVal s₁ := by rw [D.hval, hps, pathVal_comp]
  have hτ : D.C.τ = pathVal D.v ≫ D.α.1 := rfl
  -- `q ≠ x₀`
  have hqx : q.out ≠ x.out := by
    intro h
    have h' : q = x := h
    subst h'
    exact D.no_return hM hq p s₁ hps hp hs
  have hiso_ne : ∀ d : x.out ⟶ q.out, ¬IsIso d := by
    intro d hd
    obtain ⟨h, -⟩ := RayQuiver.eq_id_of_isIso d; exact hqx h.symm
  have hiso_ne' : ∀ d : q.out ⟶ x.out, ¬IsIso d := by
    intro d hd
    obtain ⟨h, -⟩ := RayQuiver.eq_id_of_isIso d; exact hqx h
  -- `ρ² ≫ λ = 0`
  obtain ⟨e, ee, p', hp'⟩ := path_first_arrow p (by omega)
  have h1 : D.w'.cons D.β = (Quiver.Path.nil.cons ee).comp (p'.comp s₁) := by
    rw [hps, hp', Quiver.Path.comp_assoc]
  have h2 : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (w₁.cons D.β) := by rw [hw]; rfl
  obtain ⟨hec, hee⟩ := first_arrow_eq (h1.symm.trans h2)
  subst hec
  have hee' := eq_of_heq hee
  subst hee'
  have hlam : pathVal p = ee.1 ≫ pathVal p' := by
    rw [hp', pathVal_comp]; change (𝟙 _ ≫ ee.1) ≫ _ = _; rw [Category.id_comp]
  have hρρl : (D.α.1 ≫ D.α.1) ≫ pathVal p = 0 := by
    rw [hlam, ← Category.assoc, (D.rho_four hq ee w₁ hw hM).2.1, zero_comp]
  have hρnl : ∀ n, 2 ≤ n → rpow D.α.1 n ≫ pathVal p = 0 := fun n hn ↦ by
    rw [show n = (n - 2) + 2 by omega, rpow_add]
    simp only [rpow_succ, rpow_zero, Category.id_comp, Category.assoc] at hρρl ⊢
    rw [hρρl, comp_zero]
  have hρl0 : D.α.1 ≫ pathVal p ≠ 0 := by
    intro h; apply hτ0
    rw [hτ, show pathVal D.v ≫ D.α.1 = D.α.1 ≫ pathVal D.v by rw [hω]; simp only [Category.assoc],
      hωps, ← Category.assoc, h, zero_comp]
  -- reduce to the generator `π` of the radical at `q`
  obtain ⟨π, hπ⟩ := hE q.out
  suffices hπ0 : pathVal p ≫ π = 0 by
    obtain ⟨l, hl, rfl⟩ := hπ c hc
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [rpow_succ', ← Category.assoc, hπ0, zero_comp]
  by_contra hlπ
  have hπi : ¬IsIso π := fun h ↦ hc (by
    obtain ⟨l, hl, rfl⟩ := hπ c hc
    exact absurd h (fun h' ↦ hc (by
      obtain ⟨hqq, he⟩ := RayQuiver.eq_id_of_isIso π
      have : π = 𝟙 _ := by rw [he]; rfl
      rw [this, MildContour.rpow_id]; infer_instance)))
  -- `ρ ≫ λ = λ ≫ c'` with `c'` radical
  obtain ⟨c', hc', hrel⟩ : ∃ c' : q.out ⟶ q.out, ¬IsIso c' ∧
      D.α.1 ≫ pathVal p = pathVal p ≫ c' := by
    rcases IsFiniteRayCategory.factorization_comparable (D.α.1 ≫ pathVal p) (pathVal p ≫ π) with
      ⟨a, b, hab⟩ | ⟨a, b, hab⟩
    · rcases D.endo_cases hq ee w₁ hw a with rfl | ⟨n, hn, rfl⟩
      · rcases (show b = 𝟙 _ ∨ ¬IsIso b by
            by_cases hb : IsIso b
            · left; obtain ⟨hqq, he⟩ := RayQuiver.eq_id_of_isIso b; rw [he]; rfl
            · exact Or.inr hb) with rfl | hb
        · exact ⟨π, hπi, by rw [hab]; simp⟩
        · exfalso
          obtain ⟨l, hl, rfl⟩ := hπ b hb
          obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
          have h1 : pathVal p ≫ π = D.α.1 ≫ (pathVal p ≫ π) ≫ rpow π l' := by
            conv_lhs => rw [hab, rpow_succ']
            simp only [Category.id_comp, Category.assoc]
          exact hα (by rw [(IsRayCategory.eq_id_of_two_sided _ hlπ _ _ h1).1]; infer_instance)
      · exfalso
        apply hlπ
        have key : rpow D.α.1 n ≫ D.α.1 ≫ pathVal p = 0 := by
          rw [← Category.assoc, ← rpow_succ, hρnl _ (by omega)]
        rw [hab, key, zero_comp]
    · rcases D.endo_cases hq ee w₁ hw a with rfl | ⟨n, hn, rfl⟩
      · exact ⟨π ≫ b, not_isIso_comp_of_left _ _ hπi, by rw [hab]; simp only [Category.id_comp,
          Category.assoc]⟩
      · exfalso
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rcases Nat.eq_zero_or_pos n' with rfl | hn'
        · have e : D.α.1 ≫ pathVal p = 𝟙 _ ≫ (D.α.1 ≫ pathVal p) ≫ (π ≫ b) := by
            conv_lhs => rw [hab]
            simp [rpow_succ, Category.assoc]
          have := (IsRayCategory.eq_id_of_two_sided _ hρl0 _ _ e).2
          exact not_isIso_comp_of_left _ _ hπi (by rw [this]; infer_instance)
        · apply hρl0
          have key : rpow D.α.1 (n' + 1) ≫ (pathVal p ≫ π) = 0 := by
            rw [← Category.assoc, hρnl _ (by omega), zero_comp]
          rw [hab, key, zero_comp]
  -- the crown `Ã(λ, c', μ, ρ)`
  set ρ := D.α.1 with hρdef
  set lam := pathVal p with hlamdef
  set μ := pathVal s₁ with hμdef
  have hlami : ¬IsIso lam := not_isIso_pathVal _ hp
  have hμi : ¬IsIso μ := not_isIso_pathVal _ hs
  have hρρ : pathVal D.v = ρ ≫ ρ := hω
  have hτ3 : D.C.τ = ρ ≫ lam ≫ μ := by
    rw [hτ, show pathVal D.v ≫ ρ = ρ ≫ pathVal D.v by rw [hρρ]; simp only [Category.assoc], hωps]
  have hτ3' : D.C.τ = lam ≫ μ ≫ ρ := by rw [hτ, hωps, Category.assoc]
  have hirr : ∀ {z : P} (f : x.out ⟶ z) (g : z ⟶ x.out), f ≫ g = ρ → IsIso f ∨ IsIso g :=
    fun f g h ↦ D.α.2.2.2 _ f g h.symm
  have hμ : c' ≫ μ = μ ≫ ρ := by
    apply hL lam
    · rw [← Category.assoc, ← hrel, Category.assoc, ← hτ3, hτ3']
    · rw [← Category.assoc, ← hrel, Category.assoc, ← hτ3]; exact hτ0
  have hωne : ρ ≫ ρ ≠ 0 := by rw [← hρρ]; exact D.h0
  -- `ρ = λ ≫ d` is impossible
  have nld : ∀ d : q.out ⟶ x.out, lam ≫ d ≠ ρ := fun d h ↦ by
    rcases hirr lam d h with h' | h'
    · exact hlami h'
    · exact hiso_ne' d h'
  have ndm : ∀ d : x.out ⟶ q.out, d ≫ μ ≠ ρ := fun d h ↦ by
    rcases hirr d μ h with h' | h'
    · exact hiso_ne d h'
    · exact hμi h'
  have npr := D.prefix_not_rho hq hM p s₁ hs hps
  have e₂ : lam ≫ c' ≫ μ = D.C.τ := by
    rw [← Category.assoc, ← hrel, Category.assoc]; exact hτ3.symm
  have e₃ : (ρ ≫ lam) ≫ μ ≫ 𝟙 _ = D.C.τ := by
    rw [Category.comp_id, Category.assoc]; exact hτ3.symm
  refine hM.not_crown2 D.C.τ D.C.τ_not_isIso hτ0 lam c' μ ρ
    (not_ftm_mid hτ0 hα hτ3.symm) (not_ftm_mid hτ0 hlami e₂)
    (not_ftm_mid hτ0 (not_isIso_comp_of_left _ _ hα) e₃) D.C.ftm_ρ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, hd⟩
    have e : (d ≫ μ) ≫ ρ = ρ ≫ ρ := by
      rw [Category.assoc, ← hμ, ← Category.assoc, hd, ← hωps, hρρ]
    exact ndm d (hR _ _ ρ e (by rw [e]; exact hωne))
  · rintro ⟨d, hd⟩
    have hμρ0 : μ ≫ ρ ≠ 0 := fun h ↦ hτ0 (by rw [hτ3', h, comp_zero])
    have e : μ ≫ ρ = (d ≫ ρ) ≫ ρ := by
      rw [← hμ, ← hd, Category.assoc, ← hωps, hρρ, ← Category.assoc]
    have hμd : μ = d ≫ ρ := hR _ _ ρ e hμρ0
    have e' : (lam ≫ d) ≫ ρ = ρ ≫ ρ := by rw [Category.assoc, ← hμd, ← hωps, hρρ]
    exact nld d (hR _ _ ρ e' (by rw [e']; exact hωne))
  · rintro ⟨d, hd⟩
    have e' : (lam ≫ d) ≫ ρ = ρ ≫ ρ := by rw [Category.assoc, hd, ← hωps, hρρ]
    exact nld d (hR _ _ ρ e' (by rw [e']; exact hωne))
  · rintro ⟨d, hd⟩; exact ndm d hd
  · rintro ⟨d, hd⟩
    have e : ρ ≫ (lam ≫ d) = ρ ≫ ρ := by
      rw [← Category.assoc, hrel, Category.assoc, hd, ← hωps, hρρ]
    exact nld d (hL ρ _ _ e (by rw [e]; exact hωne))
  · rintro ⟨d, hd⟩
    have e : ρ ≫ lam = ρ ≫ (ρ ≫ d) := by
      rw [hrel, ← hd, ← Category.assoc, ← hωps, hρρ, Category.assoc]
    exact npr ⟨d, hL ρ _ _ e hρl0⟩
  · rintro ⟨d, hd⟩; exact npr ⟨d, hd.symm⟩
  · rintro ⟨d, hd⟩; exact nld d hd

/-- **Right-deep rays out of `x₀` ending on `w`**: such a ray is `ρ³`. -/
theorem rightDeep_unique_at (hM : MildHyp k P) (hE : EndCyclic P) {z : RayVert P}
    (p : Quiver.Path x z) (s₁ : Quiver.Path z x) (hps : D.w'.cons D.β = p.comp s₁)
    (μ : x.out ⟶ z.out) (hμ0 : μ ≠ 0) (hμ : RightDeep μ) :
    ∃ h : z.out = x.out, μ ≫ eqToHom h = rpow D.α.1 3 := by
  have hα := D.α.2.2.1
  have h4 := (D.rho_four hq a₁ w₁ hw hM).1
  have hω := D.ω_pf hq a₁ w₁ hw
  have h3 : rpow D.α.1 3 ≠ 0 := by
    intro h; apply D.C.τ_ne_zero
    rw [C_τ, hω]; simpa [rpow_succ] using h
  have hωps : pathVal D.v = pathVal p ≫ pathVal s₁ := by rw [D.hval, hps, pathVal_comp]
  -- endpoints of `w`: `z = x₀`
  have endpoint : z.out = x.out → ∃ h : z.out = x.out, μ ≫ eqToHom h = rpow D.α.1 3 := by
    intro h
    have h' : z = x := h
    subst h'
    refine ⟨rfl, ?_⟩
    rw [eqToHom_refl, Category.comp_id]
    have hμi : ¬IsIso μ := fun hi ↦ by
      have := hμ D.α.1 hα
      obtain ⟨hzz, he⟩ := RayQuiver.eq_id_of_isIso μ
      rw [show μ = 𝟙 _ by rw [he]; rfl, Category.id_comp] at this
      exact D.α.2.1 this
    obtain ⟨n, hn, rfl⟩ := D.hρ μ hμi
    have hn3 : 3 ≤ n := by
      by_contra hlt
      have := hμ (rpow D.α.1 (3 - n)) (MildContour.rpow_not_isIso _ hα _ (by omega))
      rw [← rpow_add, show n + (3 - n) = 3 by omega] at this
      exact h3 this
    have hn3' : n ≤ 3 := by
      by_contra hlt
      apply hμ0
      rw [show n = 4 + (n - 4) by omega, rpow_add, h4, zero_comp]
    rw [show n = 3 by omega]
  by_cases hp0 : p.length = 0
  · cases p with
    | nil => exact endpoint rfl
    | cons _ _ => simp at hp0
  by_cases hs0 : s₁.length = 0
  · cases s₁ with
    | nil => exact endpoint rfl
    | cons _ _ => simp at hs0
  exfalso
  have hp : 0 < p.length := by omega
  have hs : 0 < s₁.length := by omega
  have hlami : ¬IsIso (pathVal p) := not_isIso_pathVal _ hp
  have hsi : ¬IsIso (pathVal s₁) := not_isIso_pathVal _ hs
  have hlam_ndeep : ¬RightDeep (pathVal p) := fun h ↦ D.h0 (by rw [hωps, h _ hsi])
  have npr := D.prefix_not_rho hq hM p s₁ hs hps
  have hZ := D.Z hq a₁ w₁ hw hM hE p s₁ hp hs hps
  have hρρl : ∀ n, 2 ≤ n → rpow D.α.1 n ≫ pathVal p = 0 := by
    intro n hn
    obtain ⟨e, ee, p', hp'⟩ := path_first_arrow p (by omega)
    have h1 : D.w'.cons D.β = (Quiver.Path.nil.cons ee).comp (p'.comp s₁) := by
      rw [hps, hp', Quiver.Path.comp_assoc]
    have h2 : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (w₁.cons D.β) := by rw [hw]; rfl
    obtain ⟨hec, hee⟩ := first_arrow_eq (h1.symm.trans h2)
    subst hec
    have hee' := eq_of_heq hee
    subst hee'
    have hlam : pathVal p = ee.1 ≫ pathVal p' := by
      rw [hp', pathVal_comp]; change (𝟙 _ ≫ ee.1) ≫ _ = _; rw [Category.id_comp]
    rw [show n = (n - 2) + 2 by omega, rpow_add, Category.assoc, hlam, ← Category.assoc
      (rpow D.α.1 2), show rpow D.α.1 2 = D.α.1 ≫ D.α.1 by simp [rpow_succ],
      (D.rho_four hq ee w₁ hw hM).2.1]
    simp
  rcases IsFiniteRayCategory.factorization_comparable μ (pathVal p) with ⟨a, b, hab⟩ | ⟨a, b, hab⟩
  · -- `λ = a μ b`
    by_cases hb : IsIso b
    · obtain ⟨hzz, he⟩ := RayQuiver.eq_id_of_isIso b
      have hb1 : b = 𝟙 _ := by rw [he]; rfl
      rw [hb1, Category.comp_id] at hab
      rcases D.endo_cases hq a₁ w₁ hw a with rfl | ⟨n, hn, rfl⟩
      · rw [Category.id_comp] at hab; exact hlam_ndeep (hab ▸ hμ)
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact npr ⟨rpow D.α.1 n' ≫ μ, by rw [hab, rpow_succ', Category.assoc]⟩
    · exact D.h0 (by rw [hωps, hab, Category.assoc, Category.assoc,
        hμ _ (not_isIso_comp_of_left _ _ hb), comp_zero])
  · -- `μ = a λ b`
    by_cases hb : IsIso b
    · obtain ⟨hzz, he⟩ := RayQuiver.eq_id_of_isIso b
      have hb1 : b = 𝟙 _ := by rw [he]; rfl
      rw [hb1, Category.comp_id] at hab
      rcases D.endo_cases hq a₁ w₁ hw a with rfl | ⟨n, hn, rfl⟩
      · rw [Category.id_comp] at hab; exact hlam_ndeep (hab ▸ hμ)
      · rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · have hn1 : n = 1 := by omega
          subst hn1
          have := hμ (pathVal s₁) hsi
          rw [hab] at this
          have key : (rpow D.α.1 1 ≫ pathVal p) ≫ pathVal s₁ = (D.α.1 ≫ D.α.1) ≫ D.α.1 := by
            rw [Category.assoc, ← hωps, hω]; simp [rpow_succ, Category.assoc]
          apply D.C.τ_ne_zero
          rw [C_τ, hω, ← key, this]
        · exact hμ0 (by rw [hab, hρρl n hn2])
    · exact hμ0 (by rw [hab, Category.assoc, hZ b hb, comp_zero])


/-- **Closed case, right-deep rays out of `x₀`**: if every nonzero morphism out of
`x₀` ends at a point of `w`, the only nonzero right-deep morphism out of `x₀` is
`ρ³`. -/
theorem rightDeep_unique (hM : MildHyp k P) (hE : EndCyclic P)
    (hcl : ∀ {z : RayVert P} (μ : x.out ⟶ z.out), μ ≠ 0 →
      ∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁)
    {z : RayVert P} (μ : x.out ⟶ z.out) (hμ0 : μ ≠ 0) (hμ : RightDeep μ) :
    ∃ h : z.out = x.out, μ ≫ eqToHom h = rpow D.α.1 3 := by
  obtain ⟨p, s₁, hps⟩ := hcl μ hμ0
  exact D.rightDeep_unique_at hq a₁ w₁ hw hM hE p s₁ hps μ hμ0 hμ

end Closed

section Op

variable {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P} (a₁ : x ⟶ c)
  (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)

include hw in
lemma revPath_w : revPath (D.w'.cons D.β) =
    ((Quiver.Path.nil.cons (revArr D.β)).comp (revPath w₁)).cons (revArr a₁) := by
  have : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (w₁.cons D.β) := by rw [hw]; rfl
  rw [this, revPath_cons_first]
  rfl

include hq hw in
/-- **The reversed penny-farthing** in `Pᵒᵖ`. -/
def op : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); PFData (RayVert.mk (Opposite.op x.out) : RayVert Pᵒᵖ)
    (RayVert.mk (Opposite.op x.out)) :=
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  { α := revArr D.α
    t := RayVert.mk (Opposite.op c.out)
    w' := (Quiver.Path.nil.cons (revArr D.β)).comp (revPath w₁)
    β := revArr a₁
    q := .nil
    hval := by
      rw [← D.revPath_w a₁ w₁ hw, pathVal_revPath, ← D.hval]
      show (𝟙 _ ≫ D.α.1.op) ≫ D.α.1.op = (pathVal ((D.q.cons D.α).cons D.α)).op
      rw [hq]; change _ = ((𝟙 _ ≫ D.α.1) ≫ D.α.1).op
      simp
    h0 := by
      change (𝟙 _ ≫ D.α.1.op) ≫ D.α.1.op ≠ 0
      intro h; apply D.h0
      show pathVal ((D.q.cons D.α).cons D.α) = 0
      rw [hq]; change (𝟙 _ ≫ D.α.1) ≫ D.α.1 = 0
      apply Quiver.Hom.op_inj; simpa using h
    hni := by
      intro h
      apply D.hni
      rw [← D.revPath_w a₁ w₁ hw] at h
      have h' := interlaced_unrevPath h
      rw [unrevPath_revPath] at h'
      have : unrevPath ((Quiver.Path.nil.cons (revArr D.α)).cons (revArr D.α) :
          Quiver.Path (RayVert.mk (Opposite.op x.out) : RayVert Pᵒᵖ) _) = D.v := by
        show _ = (D.q.cons D.α).cons D.α
        rw [hq]; rfl
      rwa [this] at h'
    hρ := fun f hf ↦ by
      obtain ⟨n, hn, he⟩ := D.hρ f.unop (fun h ↦ hf ((isIso_unop_iff f).1 h))
      exact ⟨n, hn, by change f = rpow D.α.1.op n; rw [← op_rpow, ← he]; rfl⟩
    hωρ := by
      change ((𝟙 _ ≫ D.α.1.op) ≫ D.α.1.op) ≫ D.α.1.op ≠ 0
      intro h; apply D.hωρ
      show pathVal ((D.q.cons D.α).cons D.α) ≫ _ = 0
      rw [hq]; change ((𝟙 _ ≫ D.α.1) ≫ D.α.1) ≫ D.α.1 = 0
      apply Quiver.Hom.op_inj; simpa using h }

end Op

section ClosedFinal

variable {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P} (a₁ : x ⟶ c)
  (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)
include hq hw

/-- In the closed case, `ρ³` is right-deep. -/
theorem rightDeep_rho3 (hM : MildHyp k P) (hE : EndCyclic P)
    (hcl : ∀ {z : RayVert P} (μ : x.out ⟶ z.out), μ ≠ 0 →
      ∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁) :
    RightDeep (rpow D.α.1 3) := by
  intro w ζ hζ
  by_contra h
  obtain ⟨z, ν, hν, hd⟩ := exists_rightDeep_ext (rpow D.α.1 3 ≫ ζ) h
  obtain ⟨hz, he⟩ := D.rightDeep_unique hq a₁ w₁ hw hM hE hcl (z := z)
    ((rpow D.α.1 3 ≫ ζ) ≫ ν) hν hd
  have hz' : z = x.out := hz
  subst hz'
  rw [eqToHom_refl, Category.comp_id, Category.assoc] at he
  have h3 : rpow D.α.1 3 ≠ 0 := fun h0 ↦ hν (by rw [h0, zero_comp, zero_comp])
  have := (IsRayCategory.eq_id_of_two_sided (rpow D.α.1 3) h3 (𝟙 _) (ζ ≫ ν)
    (by rw [Category.id_comp, he])).2
  haveI : IsIso (ζ ≫ ν) := by rw [this]; infer_instance
  exact hζ (ray_isIso_factors ζ ν).1

/-- **[mild] Theorem 3, closed penny-farthing**: if every nonzero morphism out of
or into `x₀` ends or starts at a point of `w`, then `ρ³` is projective-injective
at `x₀`, which `NoProjInj` excludes. -/
theorem closed_false (hM : MildHyp k P) (hE : EndCyclic P) (hNPI : NoProjInj P)
    (hclR : ∀ {z : RayVert P} (μ : x.out ⟶ z.out), μ ≠ 0 →
      ∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁)
    (hclL : ∀ {z : RayVert P} (μ : z.out ⟶ x.out), μ ≠ 0 →
      ∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁) : False := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have hω := D.ω_pf hq a₁ w₁ hw
  have h3 : rpow D.α.1 3 ≠ 0 := by
    intro h; apply D.C.τ_ne_zero
    rw [C_τ, hω]; simpa [rpow_succ] using h
  -- the reversed penny-farthing
  set Do := D.op hq a₁ w₁ hw with hDo
  have hqo : Do.q = .nil := rfl
  have hwo : Do.w' = (Quiver.Path.nil.cons (revArr D.β)).comp (revPath w₁) := rfl
  have hclo : ∀ {Z : RayVert Pᵒᵖ} (μ : (Opposite.op x.out : Pᵒᵖ) ⟶ Z.out), μ ≠ 0 →
      ∃ (p : Quiver.Path (RayVert.mk (Opposite.op x.out)) Z)
        (s₁ : Quiver.Path Z (RayVert.mk (Opposite.op x.out))), Do.w'.cons Do.β = p.comp s₁ := by
    intro Z μ hμ
    obtain ⟨p₀, s₀, hps⟩ := hclL (z := RayVert.mk Z.out.unop) μ.unop
      (fun h ↦ hμ (Quiver.Hom.unop_inj (by rw [h, unop_zero])))
    refine ⟨revPath s₀, revPath p₀, ?_⟩
    change ((Quiver.Path.nil.cons (revArr D.β)).comp (revPath w₁)).cons (revArr a₁) = _
    rw [← D.revPath_w a₁ w₁ hw, hps, revPath_comp]
    rfl
  have hEo := hE.op
  have hMo := hM.op
  have hρo : rpow Do.α.1 3 = (rpow D.α.1 3).op := (op_rpow _ 3).symm
  refine hNPI (rpow D.α.1 3) ⟨h3, D.rightDeep_rho3 hq a₁ w₁ hw hM hE hclR, ?_,
    fun {y} μ hμ0 hμ ↦ D.rightDeep_unique hq a₁ w₁ hw hM hE hclR (z := y) μ hμ0 hμ, ?_⟩
  · have hR3 : RightDeep (rpow Do.α.1 3) :=
      Do.rightDeep_rho3 hqo (revArr D.β) (revPath w₁) hwo hMo hEo hclo
    rw [hρo] at hR3
    apply (rightDeep_op (μ := rpow D.α.1 3)).mp
    exact @hR3
  · intro w ν hν0 hν
    obtain ⟨h, he⟩ := Do.rightDeep_unique hqo (revArr D.β) (revPath w₁) hwo hMo hEo hclo
      (z := RayVert.mk (Opposite.op w)) ν.op
      (fun h ↦ hν0 (Quiver.Hom.op_inj (by rw [h, op_zero])))
      ((rightDeep_op (μ := ν)).mpr @hν)
    have hw' : w = x.out := congrArg Opposite.unop h
    subst hw'
    refine ⟨rfl, ?_⟩
    rw [hρo, eqToHom_refl, Category.comp_id] at he
    rw [eqToHom_refl, Category.id_comp]
    exact Quiver.Hom.op_inj he

end ClosedFinal

end PFData

end RayCat

end LargeIndecomposable
