module

public import LargeIndecomposable.MildContours.PennyFarthings.Contour
public import LargeIndecomposable.MildContours.Basic.Separated
public import LargeIndecomposable.Cleaving.Shapes.ShapeOut3

/-!
# The open penny-farthing ([mild] LPF, MIPF)

Penny-farthing data `D : PFData x₀ x₀` with `v = ρ ρ`, `w = a₁ w₁ β`. Here we
study arrows leaving the penny-farthing.

* `rho_eps`: an arrow `ε` out of `x₀` other than `ρ`, `a₁` has `ρ ≫ ε = 0`
  (the `D̃₄` star `ρ | ρ, a₁, ε` would cleave into `P/ρ³`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

namespace PFData

section Open

variable {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P} (a₁ : x ⟶ c)
  (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)
include hq hw

lemma τ_eq : D.C.τ = D.α.1 ≫ D.α.1 ≫ D.α.1 := by
  rw [C_τ, D.ω_pf hq a₁ w₁ hw, Category.assoc]

lemma τ_not_irreducible : ¬IsIrreducible D.C.τ := fun h ↦
  (h.2.2 _ D.α.1 (D.α.1 ≫ D.α.1) (D.τ_eq hq a₁ w₁ hw)).elim D.α.2.2.1
    (not_isIso_comp_of_left _ _ D.α.2.2.1)

/-- The two first arrows `ρ`, `a₁` out of `x₀` are distinct. -/
lemma rho_a₁_apart (hM : MildHyp k P) : ¬∃ h : x = c, HEq D.α a₁ := by
  have hL : LeftCancel P := hM.left
  have hvv : D.v = (Quiver.Path.nil.cons D.α).comp (Quiver.Path.nil.cons D.α) := by
    show (D.q.cons D.α).cons D.α = _; rw [hq]; rfl
  have hww : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (w₁.cons D.β) := by
    rw [hw]; rfl
  exact first_arrows_ne hL (by rw [← hvv, ← hww]; exact D.hval) (by rw [← hvv]; exact D.h0)
    (by rw [← hvv, ← hww]; exact D.hni)

/-- A loop at `x₀` is `ρ`. -/
lemma loop_eq_rho (e : x ⟶ x) : e = D.α := by
  obtain ⟨n, hn, hen⟩ := D.hρ e.1 e.2.2.1
  have hn1 : n = 1 := by
    by_contra h1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [rpow_succ] at hen
    rcases e.2.2.2 _ _ _ hen with h | h
    · exact MildContour.rpow_not_isIso _ D.α.2.2.1 _ (by omega) h
    · exact D.α.2.2.1 h
  subst hn1
  exact Subtype.ext (by rw [hen]; simp [rpow_succ])

/-- **[mild] LPF, first step**: an arrow `ε` out of `x₀` other than `ρ`, `a₁` has
`ρ ≫ ε = 0`. -/
theorem rho_eps (hM : MildHyp k P) {y : RayVert P} (ε : x ⟶ y)
    (h₁ : ¬∃ h : y = x, HEq ε D.α) (h₂ : ¬∃ h : y = c, HEq ε a₁) : D.α.1 ≫ ε.1 = 0 := by
  by_contra hne
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hτ0 := D.C.τ_ne_zero
  have hα := D.α.2.2.1
  have hτ := D.τ_eq hq a₁ w₁ hw
  have hτi := D.τ_not_irreducible hq a₁ w₁ hw
  have hωw := D.ω_pf_w hq a₁ w₁ hw
  have hω := D.ω_pf hq a₁ w₁ hw
  have hyx : y ≠ x := fun h ↦ h₁ ⟨h, by subst h; exact heq_of_eq (D.loop_eq_rho hq a₁ w₁ hw ε)⟩
  have hρa := D.rho_a₁_apart hq a₁ w₁ hw hM
  have o12 := arrows_out_apart D.α a₁ hρa
  have o13 := arrows_out_apart D.α ε (fun ⟨h, he⟩ ↦ h₁ ⟨h.symm, he.symm⟩)
  have o23 := arrows_out_apart a₁ ε (fun ⟨h, he⟩ ↦ h₂ ⟨h.symm, he.symm⟩)
  have hταa₁ : 𝟙 _ ≫ (D.α.1 ≫ a₁.1) ≫ (pathVal w₁ ≫ D.β.1) = D.C.τ := by
    rw [hτ, ← hω, hωw]
    simp only [Category.id_comp, Category.assoc]
  have hr' : ¬IsIso (pathVal w₁ ≫ D.β.1) := not_isIso_comp_of_right _ _ D.β.2.2.1
  -- `ρ ≫ ε` does not factor through `τ = ρ³`
  have hρε : ¬FactorsThroughMorphism D.C.τ (D.α.1 ≫ ε.1) := by
    rintro ⟨u, v, huv⟩
    have hcomm : u ≫ D.C.τ = D.α.1 ≫ (u ≫ D.α.1 ≫ D.α.1) := by
      rcases D.endo_cases hq a₁ w₁ hw u with rfl | ⟨n, -, rfl⟩
      · rw [hτ]; simp
      · rw [hτ, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc]
        congr 2
        rw [show rpow D.α.1 n ≫ D.α.1 = rpow D.α.1 (n + 1) from (rpow_succ _ _).symm,
          rpow_succ']
    change D.α.1 ≫ ε.1 = u ≫ D.C.τ ≫ v at huv
    rw [← Category.assoc, hcomm, Category.assoc] at huv
    have hε := hL _ _ _ huv hne
    rcases ε.2.2.2 _ _ _ hε with h | h
    · exact not_isIso_comp_of_right _ _ (not_isIso_comp_of_right _ _ hα) h
    · obtain ⟨hxy, -⟩ := RayQuiver.eq_id_of_isIso v
      exact hyx (congrArg RayVert.mk hxy).symm
  exact hM.not_out3 D.C.τ D.C.τ_not_isIso hτ0 D.α.1 D.α.1 a₁.1 ε.1
    (D.C.ftm_α hR) (not_ftm_of_irreducible D.C.τ_not_isIso hτi a₁.2)
    (not_ftm_of_irreducible D.C.τ_not_isIso hτi ε.2) (D.C.ftm_α hR) (D.C.ftm_αρ hR)
    (MildContour.not_ftm_mid_right hτ0 hr' hταa₁) hρε hα hα a₁.2.2.1 ε.2.2.1
    o12.1 o13.1 o12.2 o23.1 o13.2 o23.2

/-- A prefix of `w` whose value is an arrow `ε` out of `x₀` is `a₁`, and `ε = a₁`. -/
lemma prefix_eq_arrow {q : RayVert P} (p : Quiver.Path x q) (s₁ : Quiver.Path q x)
    (hp : 0 < p.length) (hps : D.w'.cons D.β = p.comp s₁) (ε : x ⟶ q) (he : pathVal p = ε.1) :
    ∃ h : q = c, HEq ε a₁ := by
  cases p with
  | nil => simp at hp
  | cons p' e =>
    have hirr : IsIrreducible (pathVal p' ≫ e.1) := by
      change IsIrreducible (pathVal (p'.cons e)); rw [he]; exact ε.2
    have hl := length_eq_zero_of_irreducible_cons p' e hirr
    cases p' with
    | cons _ _ => simp at hl
    | nil =>
      have h1 : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (w₁.cons D.β) := by rw [hw]; rfl
      have h2 : D.w'.cons D.β = (Quiver.Path.nil.cons e).comp s₁ := by rw [hps]
      obtain ⟨hcq, hea⟩ := first_arrow_eq (h1.symm.trans h2)
      subst hcq
      have hee : e = ε := Subtype.ext (by
        change 𝟙 _ ≫ e.1 = ε.1 at he; rwa [Category.id_comp] at he)
      subst hee
      exact ⟨rfl, hea.symm⟩

/-- **[mild] PPF**: the only arrow from `x₀` to a point of `w` other than `x₀` is
`a₁`. -/
theorem arrow_into_w (hM : MildHyp k P) {q : RayVert P} (p : Quiver.Path x q)
    (s₁ : Quiver.Path q x) (hp : 0 < p.length) (hs : 0 < s₁.length)
    (hps : D.w'.cons D.β = p.comp s₁) (ε : x ⟶ q) : ∃ h : q = c, HEq ε a₁ := by
  have hα := D.α.2.2.1
  have npr := D.prefix_not_rho hq hM p s₁ hs hps
  have hqx : q ≠ x := by
    rintro rfl
    exact PFData.no_return hM D hq p s₁ hps hp hs
  have hωps : pathVal D.v = pathVal p ≫ pathVal s₁ := by rw [D.hval, hps, pathVal_comp]
  have hpi : ¬IsIso (pathVal p) := not_isIso_pathVal _ hp
  have fin : pathVal p = ε.1 → ∃ h : q = c, HEq ε a₁ := D.prefix_eq_arrow hq a₁ w₁ hw p s₁ hp hps ε
  have h1 : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (w₁.cons D.β) := by rw [hw]; rfl
  have hvv : D.v = (Quiver.Path.nil.cons D.α).comp (Quiver.Path.nil.cons D.α) := by
    show (D.q.cons D.α).cons D.α = _; rw [hq]; rfl
  rcases IsFiniteRayCategory.factorization_comparable ε.1 (pathVal p) with ⟨a, b, hab⟩ | ⟨a, b, hab⟩
  · rcases D.endo_cases hq a₁ w₁ hw a with rfl | ⟨n, hn, rfl⟩
    · rw [Category.id_comp] at hab
      by_cases hb : IsIso b
      · obtain ⟨hqq, hb'⟩ := RayQuiver.eq_id_of_isIso b
        exact fin (by rw [hab, hb']; simp)
      · have hb0 : b ≠ 0 := fun h0 ↦ D.h0 (by rw [hωps, hab, h0, comp_zero, zero_comp])
        let u : Quiver.Path x x := (Quiver.Path.nil.cons ε).comp
          ((pathOf (P := P) (x := q.out) (y := q.out) b hb0).comp s₁)
        have hu : pathVal u = pathVal D.v := by
          rw [hωps, hab, pathVal_comp, pathVal_comp, pathVal_pathOf]
          change (𝟙 _ ≫ ε.1) ≫ _ = _; rw [Category.id_comp, Category.assoc]
        rcases hM.path_unique D.hval D.h0 D.hni hα D.hωρ u hu with h | h
        · exfalso
          have h' : u = (Quiver.Path.nil.cons D.α).comp (Quiver.Path.nil.cons D.α) := by
            rw [h, hq]; rfl
          obtain ⟨hqx', -⟩ := first_arrow_eq h'
          exact hqx hqx'
        · rw [h1] at h
          obtain ⟨hqc, hea⟩ := first_arrow_eq h
          exact ⟨hqc, hea⟩
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact npr ⟨rpow D.α.1 m ≫ ε.1 ≫ b, by rw [hab, rpow_succ']; simp only [Category.assoc]⟩
  · rcases ε.2.2.2 _ _ _ hab with h | h
    · exact absurd (ray_isIso_factors a (pathVal p)).2 hpi
    · obtain ⟨hqq, hb'⟩ := RayQuiver.eq_id_of_isIso b
      have hab' : ε.1 = a ≫ pathVal p := by rw [hab, hb']; simp
      rcases ε.2.2.2 _ _ _ hab' with h' | h'
      · obtain ⟨hxx, ha'⟩ := RayQuiver.eq_id_of_isIso a
        exact fin (by rw [hab', ha']; simp)
      · exact absurd h' hpi

/-- **`w` is a simple cycle**: it does not pass twice through a point. -/
theorem no_revisit (hM : MildHyp k P) (hE : EndCyclic P) {q : RayVert P} (p₁ : Quiver.Path x q)
    (cyc : Quiver.Path q q) (s : Quiver.Path q x) (hc : 0 < cyc.length)
    (hps : 0 < p₁.length + s.length) (hws : D.w'.cons D.β = (p₁.comp cyc).comp s) : False := by
  rcases Nat.eq_zero_or_pos p₁.length with h1 | h1
  · cases p₁ with
    | cons _ _ => simp at h1
    | nil =>
        rw [Quiver.Path.nil_comp] at hws
        rcases Nat.eq_zero_or_pos s.length with h2 | h2
        · cases s with
          | cons _ _ => simp at h2
          | nil => simp at hps
        · exact PFData.no_return hM D hq cyc s hws hc h2
  · rcases Nat.eq_zero_or_pos s.length with h2 | h2
    · cases s with
      | cons _ _ => simp at h2
      | nil =>
          rw [Quiver.Path.comp_nil] at hws
          exact PFData.no_return hM D hq p₁ cyc hws h1 hc
    · have hs : 0 < (cyc.comp s).length := by rw [Quiver.Path.length_comp]; omega
      have hz := D.Z hq a₁ w₁ hw hM hE p₁ (cyc.comp s) h1 hs (by rw [hws, Quiver.Path.comp_assoc])
        (pathVal cyc) (not_isIso_pathVal _ hc)
      apply D.h0
      rw [D.hval, hws, pathVal_comp, pathVal_comp, hz, zero_comp]

/-- **Morphisms from `x₀` to an interior point `q` of `w`** are `ρᵐ ≫ λ`, `λ` the
prefix of `w` ending at `q`. -/
theorem mor_to_interior (hM : MildHyp k P) (hE : EndCyclic P) {q : RayVert P}
    (p : Quiver.Path x q) (s₁ : Quiver.Path q x) (hp : 0 < p.length) (hs : 0 < s₁.length)
    (hps : D.w'.cons D.β = p.comp s₁) (f : x.out ⟶ q.out) (hf : f ≠ 0) :
    ∃ m, f = rpow D.α.1 m ≫ pathVal p := by
  have hα := D.α.2.2.1
  have npr := D.prefix_not_rho hq hM p s₁ hs hps
  have hωps : pathVal D.v = pathVal p ≫ pathVal s₁ := by rw [D.hval, hps, pathVal_comp]
  have hp0 : pathVal p ≠ 0 := fun h ↦ D.h0 (by rw [hωps, h, zero_comp])
  have hlen : ∀ {a b : P} (g : a ⟶ b) (hg : g ≠ 0), ¬IsIso g →
      0 < (pathOf (P := P) g hg).length := by
    intro a b g hg hgi
    rcases Nat.eq_zero_or_pos (pathOf (P := P) g hg).length with h | h
    · exfalso; apply hgi
      have := pathVal_pathOf g hg
      revert this
      generalize pathOf (P := P) g hg = r at h
      cases r with
      | cons _ _ => simp at h
      | nil => intro h'; rw [← h']; exact isIso_pathVal_nil
    · exact h
  rcases IsFiniteRayCategory.factorization_comparable f (pathVal p) with ⟨u, v, h⟩ | ⟨u, v, h⟩
  · rcases D.endo_cases hq a₁ w₁ hw u with rfl | ⟨n, hn, rfl⟩
    · rw [Category.id_comp] at h
      by_cases hv : IsIso v
      · obtain ⟨hqq, hv'⟩ := RayQuiver.eq_id_of_isIso v
        exact ⟨0, by rw [h, hv']; simp⟩
      · exfalso
        have hv0 : v ≠ 0 := fun h0 ↦ hp0 (by rw [h, h0, comp_zero])
        have hqx : q ≠ x := by
          rintro rfl
          exact PFData.no_return hM D hq p s₁ hps hp hs
        have hfi : ¬IsIso f := fun hi ↦ by
          obtain ⟨hxq, -⟩ := RayQuiver.eq_id_of_isIso f
          exact hqx (congrArg RayVert.mk hxq).symm
        let u' : Quiver.Path x x := (pathOf (P := P) (x := x.out) (y := q.out) f hf).comp
          ((pathOf (P := P) (x := q.out) (y := q.out) v hv0).comp s₁)
        have hu : pathVal u' = pathVal D.v := by
          rw [hωps, h, pathVal_comp, pathVal_comp, pathVal_pathOf, pathVal_pathOf,
            Category.assoc]
        rcases hM.path_unique D.hval D.h0 D.hni hα D.hωρ u' hu with h' | h'
        · have hvl : D.v.length = 2 := by
            show ((D.q.cons D.α).cons D.α).length = 2; rw [hq]; rfl
          have hl : u'.length = 2 := by rw [h']; exact hvl
          have h1 := hlen f hf hfi
          have h2 := hlen v hv0 hv
          simp only [u', Quiver.Path.length_comp] at hl
          omega
        · exact D.no_revisit hq a₁ w₁ hw hM hE (pathOf (P := P) (x := x.out) (y := q.out) f hf)
            (pathOf (P := P) (x := q.out) (y := q.out) v hv0) s₁ (hlen v hv0 hv)
            (by have := hlen f hf hfi; omega)
            (by rw [← h']; simp only [u', Quiver.Path.comp_assoc])
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact npr ⟨rpow D.α.1 m ≫ f ≫ v, by rw [h, rpow_succ']; simp only [Category.assoc]⟩
  · by_cases hv : IsIso v
    · obtain ⟨hqq, hv'⟩ := RayQuiver.eq_id_of_isIso v
      rcases D.endo_cases hq a₁ w₁ hw u with rfl | ⟨n, hn, rfl⟩
      · exact ⟨0, by rw [h, hv']; simp⟩
      · exact ⟨n, by rw [h, hv']; simp⟩
    · exfalso
      apply hf
      rw [h, Category.assoc, D.Z hq a₁ w₁ hw hM hE p s₁ hp hs hps v hv, comp_zero]

end Open

section Dual

variable {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P} (a₁ : x ⟶ c)
  (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)
include hq hw

/-- A split of `w` gives a split of the reversed `w` in `Pᵒᵖ`. -/
lemma op_split {q : RayVert P} (p : Quiver.Path x q) (s₁ : Quiver.Path q x)
    (hps : D.w'.cons D.β = p.comp s₁) :
    letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
    (D.op hq a₁ w₁ hw).w'.cons (D.op hq a₁ w₁ hw).β = (revPath s₁).comp (revPath p) := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  change ((Quiver.Path.nil.cons (revArr D.β)).comp (revPath w₁)).cons (revArr a₁) = _
  rw [← D.revPath_w a₁ w₁ hw, hps, revPath_comp]

/-- **Dual of `Z`**: a radical endomorphism at an interior point `q` of `w`
followed by the suffix of `w` from `q` vanishes. -/
theorem Z_dual (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) {q : RayVert P} (p : Quiver.Path x q)
    (s₁ : Quiver.Path q x) (hp : 0 < p.length) (hs : 0 < s₁.length)
    (hps : D.w'.cons D.β = p.comp s₁) (e : q.out ⟶ q.out) (he : ¬IsIso e) :
    e ≫ pathVal s₁ = 0 := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have h := (D.op hq a₁ w₁ hw).Z rfl (revArr D.β) (revPath w₁) rfl hMo hE.op (revPath s₁)
    (revPath p) (by rw [length_revPath]; exact hs) (by rw [length_revPath]; exact hp)
    (D.op_split hq a₁ w₁ hw p s₁ hps) e.op (fun hi ↦ he ((isIso_op_iff e).1 hi))
  rw [pathVal_revPath] at h
  apply Quiver.Hom.op_inj
  rw [op_comp, h, op_zero]

/-- **Dual of `prefix_not_rho`**: a proper suffix of `w` does not factor as `d ≫ ρ`. -/
theorem suffix_not_rho (hMo : MildHyp k Pᵒᵖ) {q : RayVert P} (p : Quiver.Path x q)
    (s₁ : Quiver.Path q x) (hp : 0 < p.length) (hps : D.w'.cons D.β = p.comp s₁) :
    ¬∃ d, pathVal s₁ = d ≫ D.α.1 := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have h := (D.op hq a₁ w₁ hw).prefix_not_rho rfl hMo (revPath s₁) (revPath p)
    (by rw [length_revPath]; exact hp) (D.op_split hq a₁ w₁ hw p s₁ hps)
  rintro ⟨d, hd⟩
  exact h ⟨d.op, by rw [pathVal_revPath, hd, op_comp]; rfl⟩

/-- **Dual of `mor_to_interior`**: morphisms from an interior point `q` of `w` to
`x₀` are `μ ≫ ρᵐ`, `μ` the suffix of `w` from `q`. -/
theorem mor_from_interior (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) {q : RayVert P}
    (p : Quiver.Path x q) (s₁ : Quiver.Path q x) (hp : 0 < p.length) (hs : 0 < s₁.length)
    (hps : D.w'.cons D.β = p.comp s₁) (f : q.out ⟶ x.out) (hf : f ≠ 0) :
    ∃ m, f = pathVal s₁ ≫ rpow D.α.1 m := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  obtain ⟨m, hm⟩ := (D.op hq a₁ w₁ hw).mor_to_interior rfl (revArr D.β) (revPath w₁) rfl hMo hE.op
    (revPath s₁) (revPath p) (by rw [length_revPath]; exact hs)
    (by rw [length_revPath]; exact hp) (D.op_split hq a₁ w₁ hw p s₁ hps)
    (show (RayVert.mk (Opposite.op x.out) : RayVert Pᵒᵖ).out ⟶
      (RayVert.mk (Opposite.op q.out) : RayVert Pᵒᵖ).out from f.op)
    (fun h ↦ hf (Quiver.Hom.op_inj (h.trans (op_zero _ _).symm)))
  refine ⟨m, Quiver.Hom.op_inj ?_⟩
  rw [op_comp]
  refine hm.trans ?_
  rw [pathVal_revPath]
  change rpow D.α.1.op m ≫ _ = _
  rw [← op_rpow]

/-- **Dual of `arrow_into_w`**: the only arrow from a point of `w` other than `x₀`
into `x₀` is `β`. -/
theorem arrow_from_w (hMo : MildHyp k Pᵒᵖ) {q : RayVert P} (p : Quiver.Path x q)
    (s₁ : Quiver.Path q x) (hp : 0 < p.length) (hs : 0 < s₁.length)
    (hps : D.w'.cons D.β = p.comp s₁) (e : q ⟶ x) : ∃ h : q = D.t, HEq e D.β := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  obtain ⟨h, he⟩ := (D.op hq a₁ w₁ hw).arrow_into_w rfl (revArr D.β) (revPath w₁) rfl hMo
    (revPath s₁) (revPath p) (by rw [length_revPath]; exact hs)
    (by rw [length_revPath]; exact hp) (D.op_split hq a₁ w₁ hw p s₁ hps) (revArr e)
  have hqt : q.out = D.t.out := Opposite.op_injective (congrArg RayVert.out h)
  have hqt' : q = D.t := congrArg RayVert.mk hqt
  subst hqt'
  refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
  have := congrArg (fun r ↦ r.1) (eq_of_heq he)
  exact Quiver.Hom.op_inj this

end Dual

end PFData

end RayCat

end LargeIndecomposable
