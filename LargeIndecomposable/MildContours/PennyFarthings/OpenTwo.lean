module

public import LargeIndecomposable.MildContours.PennyFarthings.Open
public import LargeIndecomposable.MildContours.Setup.SepD5
public import LargeIndecomposable.Cleaving.Families.FamM43A
public import LargeIndecomposable.Cleaving.Families.FamM43B
public import LargeIndecomposable.Cleaving.Families.FamM44A
public import LargeIndecomposable.Cleaving.Families.FamM44B
public import LargeIndecomposable.Cleaving.Families.FamM44C
public import LargeIndecomposable.Cleaving.Families.FamM45B

/-!
# The open penny-farthing with `n = 2` ([mild] MIPF)

Penny-farthing data with `v = ρ ρ`, `w = a₁ β` (points `x₀`, `x₁ = t`). An
*exit* is an arrow from `x₀` or `x₁` to a point off the penny-farthing, an
*entry* an arrow from such a point into `x₀` or `x₁`.

* `not_exit_entry_a`: an exit `ε` at `x₀` and an entry `δ` at `x₁` with
  `δ ≫ β ≠ 0` do not coexist ([mild] figure 4.3, first diagram).
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

/-- A morphism between distinct points is not invertible. -/
lemma not_isIso_of_ne {a b : RayVert P} (h : a ≠ b) (f : a.out ⟶ b.out) : ¬IsIso f :=
  fun _ ↦ by
    obtain ⟨hab, -⟩ := RayQuiver.eq_id_of_isIso f
    exact h (congrArg RayVert.mk hab)

/-- An arrow does not factor through two non-invertible morphisms. -/
lemma arrow_ne_comp {a b : RayVert P} (e : a ⟶ b) {m : P} (g : a.out ⟶ m) (h : m ⟶ b.out)
    (hg : ¬IsIso g) (hh : ¬IsIso h) : g ≫ h ≠ e.1 := fun he ↦
  (e.2.2.2 _ g h he.symm).elim hg hh

/-- Iterating `f = u ≫ f ≫ r`. -/
lemma eq_rpow_sandwich {a b : P} {f : a ⟶ b} {u : a ⟶ a} {r : b ⟶ b} (h : f = u ≫ f ≫ r) :
    ∀ n, f = rpow u n ≫ f ≫ rpow r n
  | 0 => by simp
  | n + 1 => by
    conv_lhs => rw [eq_rpow_sandwich h n]
    conv_lhs => rw [h]
    rw [rpow_succ u n, rpow_succ' r n]
    simp only [Category.assoc]

namespace PFData

section Two

variable {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) (a₁ : x ⟶ D.t)
  (hw : D.w' = Quiver.Path.nil.cons a₁)
include hq hw

lemma hw2 : D.w' = (Quiver.Path.nil.cons a₁).comp (.nil : Quiver.Path D.t D.t) := by
  rw [hw]; rfl

lemma split2 : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (Quiver.Path.nil.cons D.β) := by
  rw [hw]; rfl

lemma ab_eq : a₁.1 ≫ D.β.1 = D.α.1 ≫ D.α.1 := by
  have h1 := D.ω_pf hq a₁ .nil (D.hw2 hq a₁ hw)
  have h2 := D.ω_pf_w hq a₁ .nil (D.hw2 hq a₁ hw)
  rw [← h1, h2]
  change a₁.1 ≫ D.β.1 = a₁.1 ≫ 𝟙 _ ≫ D.β.1
  rw [Category.id_comp]

lemma t_ne_x (hM : MildHyp k P) : D.t ≠ x := by
  intro h
  have key : ∀ {t : RayVert P} (a : x ⟶ t), t = x → HEq D.α a := by
    intro t a ht
    subst ht
    exact heq_of_eq (D.loop_eq_rho hq a₁ .nil (D.hw2 hq a₁ hw) a).symm
  exact D.rho_a₁_apart hq a₁ .nil (D.hw2 hq a₁ hw) hM ⟨h.symm, key a₁ h⟩

/-- **[mild] MIPF, figure 4.3 (first diagram)**: an exit `ε` at `x₀` and an entry
`δ` at `x₁` with `δ ≫ β ≠ 0` do not coexist. -/
theorem not_exit_entry_a (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    {b z : RayVert P} (ε : x ⟶ b) (hbx : b ≠ x) (hbt : b ≠ D.t) (δ : z ⟶ D.t) (hzx : z ≠ x)
    (hzt : z ≠ D.t) (hδβ : δ.1 ≫ D.β.1 ≠ 0) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hw' := D.hw2 hq a₁ hw
  have hτ0 := D.C.τ_ne_zero
  have hτ := D.τ_eq hq a₁ .nil hw'
  have hτi := D.τ_not_irreducible hq a₁ .nil hw'
  have hα := D.α.2.2.1
  have hβ := D.β.2.2.1
  have ha := a₁.2.2.1
  have hab := D.ab_eq hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  have hsp := D.split2 hq a₁ hw
  have hρε := D.rho_eps hq a₁ .nil hw' hM ε (fun ⟨h, _⟩ ↦ hbx h) (fun ⟨h, _⟩ ↦ hbt h)
  have hρa := D.rho_a₁_apart hq a₁ .nil hw' hM
  have o12 := arrows_out_apart D.α a₁ hρa
  have o13 := arrows_out_apart D.α ε (fun ⟨h, _⟩ ↦ hbx h.symm)
  have o23 := arrows_out_apart a₁ ε (fun ⟨h, _⟩ ↦ hbt h.symm)
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism D.C.τ e.1 :=
    fun e ↦ not_ftm_of_irreducible D.C.τ_not_isIso hτi e.2
  have hτab : a₁.1 ≫ (D.β.1 ≫ D.α.1) ≫ 𝟙 _ = D.C.τ := by
    rw [hτ, Category.comp_id, ← Category.assoc, hab, Category.assoc]
  have hρ3 : D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 := by rw [← hτ]; exact hτ0
  -- the dual `Z` at `x₁`
  have hZd := D.Z_dual hq a₁ .nil hw' hMo hE (Quiver.Path.nil.cons a₁)
    (Quiver.Path.nil.cons D.β) (by simp) (by simp) hsp
  have hβv : pathVal (Quiver.Path.nil.cons D.β) = D.β.1 := by
    change 𝟙 _ ≫ D.β.1 = _; rw [Category.id_comp]
  -- `δ ≫ β` does not factor through `τ`
  have h0δβ : ¬FactorsThroughMorphism D.C.τ (δ.1 ≫ D.β.1) := by
    rintro ⟨u, v, huv⟩
    rcases D.endo_cases hq a₁ .nil hw' v with rfl | ⟨n, hn, rfl⟩
    · rw [Category.comp_id, hτ] at huv
      have e1 : δ.1 ≫ D.β.1 = (u ≫ D.α.1 ≫ a₁.1) ≫ D.β.1 := by
        rw [huv, Category.assoc, Category.assoc, hab]
      have e2 := hR _ _ _ e1 hδβ
      exact arrow_ne_comp δ u (D.α.1 ≫ a₁.1) (not_isIso_of_ne hzx u)
        (not_isIso_comp_of_left _ _ hα) e2.symm
    · apply hδβ
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h4 := (D.rho_four hq a₁ .nil hw' hM).1
      rw [huv, hτ, rpow_succ']
      simp only [← Category.assoc]
      rw [show ((((u ≫ D.α.1) ≫ D.α.1) ≫ D.α.1) ≫ D.α.1) = u ≫ rpow D.α.1 4 by
        simp [rpow_succ, Category.assoc], h4]
      simp
  -- `δ ≫ β = g ≫ ρ` is impossible
  have hZBW : ¬∃ g, g ≫ D.α.1 = δ.1 ≫ D.β.1 := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h0 ↦ hδβ (by rw [← hg, h0, zero_comp])
    have h4 := (D.rho_four hq a₁ .nil hw' hM).1
    have kill : ∀ u : z.out ⟶ z.out, δ.1 ≫ D.β.1 = u ≫ (δ.1 ≫ D.β.1) ≫ D.α.1 → False := by
      intro u hu
      apply hδβ
      rw [eq_rpow_sandwich hu 4, h4, comp_zero, comp_zero]
    obtain ⟨s, e, r'', hr⟩ : ∃ (s : RayVert P) (e : s ⟶ x) (r'' : Quiver.Path z s),
        pathOf (P := P) (x := z.out) (y := x.out) g hg0 = r''.cons e := by
      generalize hr : pathOf (P := P) (x := z.out) (y := x.out) g hg0 = r
      cases r with
      | nil => exact absurd rfl hzx
      | cons r'' e => exact ⟨_, e, r'', rfl⟩
    have hge : g = pathVal r'' ≫ e.1 := by
      rw [← pathVal_pathOf (P := P) (x := z.out) (y := x.out) g hg0, hr]; rfl
    by_cases hsx : s = x
    · subst hsx
      have he := D.loop_eq_rho hq a₁ .nil hw' e
      subst he
      have e1 : δ.1 ≫ D.β.1 = (pathVal r'' ≫ a₁.1) ≫ D.β.1 := by
        rw [← hg, hge]; simp only [Category.assoc]; rw [hab]
      exact arrow_ne_comp δ (pathVal r'') a₁.1 (not_isIso_of_ne hzx _) ha
        (hR _ _ _ e1 hδβ).symm
    by_cases hst : s = D.t
    · subst hst
      obtain ⟨-, he⟩ := D.arrow_from_w hq a₁ .nil hw' hMo (Quiver.Path.nil.cons a₁)
        (Quiver.Path.nil.cons D.β) (by simp) (by simp) hsp e
      have he' := eq_of_heq he
      subst he'
      set g' := pathVal r''
      have hgb : δ.1 ≫ D.β.1 = (g' ≫ D.β.1) ≫ D.α.1 := by rw [← hg, hge]
      rcases IsFiniteRayCategory.factorization_comparable g' δ.1 with ⟨u, v, huv⟩ | ⟨u, v, huv⟩
      · -- `δ = (u ≫ g') ≫ v`
        rcases δ.2.2.2 _ _ _ huv with h | h
        · exact not_isIso_of_ne hzt _ ((ray_isIso_factors u g').2)
        · obtain ⟨hzz, hv⟩ := RayQuiver.eq_id_of_isIso v
          rw [hv, eqToHom_refl, Category.comp_id] at huv
          rcases δ.2.2.2 _ _ _ huv with h' | h'
          · obtain ⟨hzz', hu⟩ := RayQuiver.eq_id_of_isIso u
            rw [hu, eqToHom_refl, Category.id_comp] at huv
            exact kill (𝟙 _) (by rw [Category.id_comp]; rw [huv] at hgb ⊢; exact hgb)
          · exact not_isIso_of_ne hzt _ h'
      · -- `g' = (u ≫ δ) ≫ v`
        by_cases hv : IsIso v
        · obtain ⟨htt, hv'⟩ := RayQuiver.eq_id_of_isIso v
          rw [hv', eqToHom_refl, Category.comp_id] at huv
          exact kill u (by conv_lhs => rw [hgb, huv]
                           simp only [Category.assoc])
        · have := hZd v hv
          rw [hβv] at this
          have this' : v ≫ D.β.1 ≫ D.α.1 = 0 := by rw [← Category.assoc, this, zero_comp]
          apply hδβ
          rw [hgb, huv]
          simp only [Category.assoc, this', comp_zero]
    · exact hM.not_loop_d5 D.C.τ D.C.τ_not_isIso hτ0 hτi D.α a₁ ε D.β e hρa
        (fun ⟨h, _⟩ ↦ hbx h.symm) (fun ⟨h, _⟩ ↦ hbt h.symm) (fun ⟨h, _⟩ ↦ htx h.symm)
        (fun ⟨h, _⟩ ↦ hsx h.symm) (fun ⟨h, _⟩ ↦ hst h.symm)
  exact hM.not_m43a D.C.τ D.C.τ_not_isIso hτ0 δ.1 D.β.1 D.α.1 a₁.1 ε.1 D.α.1 D.β.1
    M43A.not_isRepresentationFinite hab (hf D.α) (hf ε) (D.C.ftm_αρ hR) (hf a₁) (hf D.α)
    (hf D.β) (not_ftm_mid hτ0 ha hτab) (hf D.β) h0δβ (hf δ)
    δ.2.2.1 hβ hα ha ε.2.2.1 hα hβ o12.1 o13.1 o23.2
    (by
      rintro ⟨g, hg⟩
      apply hρ3
      rw [← hg, ← Category.assoc, hρε, zero_comp])
    o13.2 o12.2 o23.1
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp δ g a₁.1 (not_isIso_of_ne hzx g) ha hg)
    hZBW
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
    (by
      rintro ⟨g, hg⟩
      by_cases hgi : IsIso g
      · obtain ⟨htt, hg'⟩ := RayQuiver.eq_id_of_isIso g
        rw [hg', eqToHom_refl, Category.id_comp] at hg
        have e : a₁.1 ≫ D.β.1 = (a₁.1 ≫ D.β.1) ≫ D.α.1 := by
          rw [Category.assoc, ← hg]
        rw [hab] at e
        have := MildContour.rpow_le_of_eq D.α.1 hα (m := 2) (n := 3)
          (by simpa [rpow_succ] using D.αα_ne_zero) (by simpa [rpow_succ, Category.assoc] using e)
        omega
      · have := hZd g hgi
        rw [hβv] at this
        apply hρ3
        rw [← Category.assoc, ← hab, Category.assoc, ← hg, this, comp_zero])
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp a₁ g δ.1 (not_isIso_of_ne hzx.symm g) δ.2.2.1 hg)

/-- `β ≫ a₁ = 0` (it lies in the ideal of `ρ³`, and `ρ³` kills every morphism
`x₀ → x₁`). -/
lemma ba_zero (hM : MildHyp k P) (hE : EndCyclic P) : D.β.1 ≫ a₁.1 = 0 := by
  have hw' := D.hw2 hq a₁ hw
  obtain ⟨u, v, huv⟩ := D.β_a₁ hq a₁ .nil hw' hM
  by_cases hv : v = 0
  · rw [huv, hv, comp_zero, comp_zero]
  obtain ⟨m, rfl⟩ := D.mor_to_interior hq a₁ .nil hw' hM hE (Quiver.Path.nil.cons a₁)
    (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) v hv
  have h2 := (D.rho_four hq a₁ .nil hw' hM).2.1
  have ha : pathVal (Quiver.Path.nil.cons a₁) = a₁.1 := by
    change 𝟙 _ ≫ a₁.1 = _; rw [Category.id_comp]
  rw [huv, ha, D.τ_eq hq a₁ .nil hw']
  have : (D.α.1 ≫ D.α.1 ≫ D.α.1) ≫ rpow D.α.1 m ≫ a₁.1 =
      rpow D.α.1 (m + 1) ≫ (D.α.1 ≫ D.α.1) ≫ a₁.1 := by
    have e1 : D.α.1 ≫ D.α.1 ≫ D.α.1 = rpow D.α.1 3 := by simp [rpow_succ]
    have e2 : D.α.1 ≫ D.α.1 = rpow D.α.1 2 := by simp [rpow_succ]
    rw [e1, e2, ← Category.assoc, ← Category.assoc, ← rpow_add, ← rpow_add,
      show 3 + m = m + 1 + 2 by omega]
  rw [this, h2, comp_zero, comp_zero]

/-- There is no loop at `x₁` (it would close a crown `ρ, a₁, ℓ, β` in the separated
quiver). -/
lemma no_loop_x1 (hM : MildHyp k P) (ℓ : D.t ⟶ D.t) : False := by
  have hw' := D.hw2 hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  exact hM.not_arrow_crown2 D.C.τ D.C.τ_not_isIso D.C.τ_ne_zero
    (D.τ_not_irreducible hq a₁ .nil hw') D.α D.β ℓ a₁ (fun ⟨h, _⟩ ↦ htx h.symm)
    (fun ⟨h, _⟩ ↦ htx h) (fun ⟨h, _⟩ ↦ htx h.symm) (fun ⟨h, _⟩ ↦ htx h.symm)

/-- The arrows into `x₁`, given an exit `ε` at `x₀` and an entry `δ` at `x₁`, are
`a₁` and `δ`. -/
lemma in_x1 (hM : MildHyp k P) {b z : RayVert P} (ε : x ⟶ b) (hbx : b ≠ x) (hbt : b ≠ D.t)
    (δ : z ⟶ D.t) (hzx : z ≠ x) {s : RayVert P} (e : s ⟶ D.t) :
    (∃ h : s = x, HEq e a₁) ∨ (∃ h : s = z, HEq e δ) := by
  have hw' := D.hw2 hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  by_cases hsx : s = x
  · subst hsx
    obtain ⟨-, he⟩ := D.arrow_into_w hq a₁ .nil hw' hM (Quiver.Path.nil.cons a₁)
      (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) e
    exact Or.inl ⟨rfl, he⟩
  by_cases hst : s = D.t
  · subst hst
    exact (D.no_loop_x1 hq a₁ hw hM e).elim
  by_cases hsz : ∃ h : s = z, HEq e δ
  · exact Or.inr hsz
  exfalso
  exact hM.not_arrow_d5 D.C.τ D.C.τ_not_isIso D.C.τ_ne_zero
    (D.τ_not_irreducible hq a₁ .nil hw') a₁ D.α ε δ e (fun ⟨h, _⟩ ↦ htx h)
    (fun ⟨h, _⟩ ↦ hbt h.symm) (fun ⟨h, _⟩ ↦ hbx h.symm) (fun ⟨h, _⟩ ↦ hzx h.symm)
    (fun ⟨h, _⟩ ↦ hsx h.symm) (fun ⟨h, he⟩ ↦ hsz ⟨h.symm, he.symm⟩)

/-- No endomorphism `g` of `x₁` has `g ≫ β = β ≫ ρ`. -/
lemma not_endo_beta (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (g : D.t.out ⟶ D.t.out) (hg : g ≫ D.β.1 = D.β.1 ≫ D.α.1) : False := by
  have hw' := D.hw2 hq a₁ hw
  have hα := D.α.2.2.1
  have hab := D.ab_eq hq a₁ hw
  have hρ3 : D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 := by
    rw [← D.τ_eq hq a₁ .nil hw']; exact D.C.τ_ne_zero
  by_cases hgi : IsIso g
  · obtain ⟨htt, hg'⟩ := RayQuiver.eq_id_of_isIso g
    rw [hg', eqToHom_refl, Category.id_comp] at hg
    have e : a₁.1 ≫ D.β.1 = (a₁.1 ≫ D.β.1) ≫ D.α.1 := by
      rw [Category.assoc, ← hg]
    rw [hab] at e
    have := MildContour.rpow_le_of_eq D.α.1 hα (m := 2) (n := 3)
      (by simpa [rpow_succ] using D.αα_ne_zero) (by simpa [rpow_succ, Category.assoc] using e)
    omega
  · have := D.Z_dual hq a₁ .nil hw' hMo hE (Quiver.Path.nil.cons a₁)
      (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) g hgi
    change g ≫ 𝟙 _ ≫ D.β.1 = 0 at this
    rw [Category.id_comp] at this
    apply hρ3
    rw [← Category.assoc, ← hab, Category.assoc, ← hg, this, comp_zero]

/-- **[mild] MIPF, figure 4.3 (second diagram)**: an exit `ε` at `x₀` and an entry
`δ` at `x₁` with `δ ≫ β = 0` do not coexist. -/
theorem not_exit_entry_b (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    {b z : RayVert P} (ε : x ⟶ b) (hbx : b ≠ x) (hbt : b ≠ D.t) (δ : z ⟶ D.t) (hzx : z ≠ x)
    (hzt : z ≠ D.t) (hδβ : δ.1 ≫ D.β.1 = 0) : False := by
  have hR : RightCancel P := hM.right
  have hw' := D.hw2 hq a₁ hw
  have hτ0 := D.C.τ_ne_zero
  have hτ := D.τ_eq hq a₁ .nil hw'
  have hτi := D.τ_not_irreducible hq a₁ .nil hw'
  have hα := D.α.2.2.1
  have hβ := D.β.2.2.1
  have ha := a₁.2.2.1
  have hab := D.ab_eq hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  have hsp := D.split2 hq a₁ hw
  have hρε := D.rho_eps hq a₁ .nil hw' hM ε (fun ⟨h, _⟩ ↦ hbx h) (fun ⟨h, _⟩ ↦ hbt h)
  have hρa := D.rho_a₁_apart hq a₁ .nil hw' hM
  have o12 := arrows_out_apart D.α a₁ hρa
  have o13 := arrows_out_apart D.α ε (fun ⟨h, _⟩ ↦ hbx h.symm)
  have o23 := arrows_out_apart a₁ ε (fun ⟨h, _⟩ ↦ hbt h.symm)
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism D.C.τ e.1 :=
    fun e ↦ not_ftm_of_irreducible D.C.τ_not_isIso hτi e.2
  have hτab : a₁.1 ≫ (D.β.1 ≫ D.α.1) ≫ 𝟙 _ = D.C.τ := by
    rw [hτ, Category.comp_id, ← Category.assoc, hab, Category.assoc]
  have hτρa : 𝟙 _ ≫ (D.α.1 ≫ a₁.1) ≫ D.β.1 = D.C.τ := by
    rw [hτ, Category.id_comp, Category.assoc, hab]
  have hρ3 : D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 := by rw [← hτ]; exact hτ0
  have hρaβ : (D.α.1 ≫ a₁.1) ≫ D.β.1 ≠ 0 := by rw [Category.assoc, hab]; exact hρ3
  have hρa0 : D.α.1 ≫ a₁.1 ≠ 0 := fun h ↦ hρaβ (by rw [h, zero_comp])
  -- `ε ≫ g = ρ ≫ a₁` is impossible
  have hεg : ¬∃ g, ε.1 ≫ g = D.α.1 ≫ a₁.1 := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h0 ↦ hρa0 (by rw [← hg, h0, comp_zero])
    obtain ⟨s, e, r'', hr⟩ : ∃ (s : RayVert P) (e : s ⟶ D.t) (r'' : Quiver.Path b s),
        pathOf (P := P) (x := b.out) (y := D.t.out) g hg0 = r''.cons e := by
      generalize hr : pathOf (P := P) (x := b.out) (y := D.t.out) g hg0 = r
      cases r with
      | nil => exact absurd rfl hbt
      | cons r'' e => exact ⟨_, e, r'', rfl⟩
    have hge : g = pathVal r'' ≫ e.1 := by
      rw [← pathVal_pathOf (P := P) (x := b.out) (y := D.t.out) g hg0, hr]; rfl
    rcases D.in_x1 hq a₁ hw hM ε hbx hbt δ hzx e with ⟨hs, he⟩ | ⟨hs, he⟩
    · subst hs
      have he' := eq_of_heq he
      subst he'
      have e1 : (ε.1 ≫ pathVal r'') ≫ e.1 = D.α.1 ≫ e.1 := by
        rw [Category.assoc, ← hge, hg]
      have e2 := hR _ _ _ e1 (by rw [e1]; exact hρa0)
      exact arrow_ne_comp D.α ε.1 (pathVal r'') ε.2.2.1 (not_isIso_of_ne hbx _) e2
    · subst hs
      have he' := eq_of_heq he
      subst he'
      apply hρaβ
      rw [← hg, hge]
      simp only [Category.assoc, hδβ, comp_zero]
  exact hM.not_m43b D.C.τ D.C.τ_not_isIso hτ0 δ.1 D.β.1 D.α.1 ε.1 a₁.1 D.α.1 a₁.1 D.β.1 δ.1
    M43B.not_isRepresentationFinite hab (D.ba_zero hq a₁ hw hM hE) hδβ
    (hf D.α) (hf ε) (MildContour.not_ftm_mid_right hτ0 hβ hτρa) (D.C.ftm_αρ hR) (hf a₁)
    (hf a₁) (hf D.α) (hf D.β) (not_ftm_mid hτ0 ha hτab) (hf D.β) (hf δ) (hf δ)
    δ.2.2.1 hβ hα ε.2.2.1 ha hα ha hβ δ.2.2.1
    o12.1 o13.1 o23.2
    (by
      rintro ⟨g, hg⟩
      apply hρ3
      rw [← hg, ← Category.assoc, hρε, zero_comp])
    o13.2 hεg o12.2 o23.1
    (by
      rintro ⟨g, hg⟩
      by_cases hgi : IsIso g
      · obtain ⟨htt, hg'⟩ := RayQuiver.eq_id_of_isIso g
        rw [hg', eqToHom_refl, Category.comp_id] at hg
        exact arrow_ne_comp a₁ D.α.1 a₁.1 hα ha hg.symm
      · apply hρa0
        rw [← hg]
        have hz := D.Z hq a₁ .nil hw' hM hE (Quiver.Path.nil.cons a₁) (Quiver.Path.nil.cons D.β)
          (by simp) (by simp) hsp g hgi
        change (𝟙 _ ≫ a₁.1) ≫ g = 0 at hz
        rwa [Category.id_comp] at hz)
    o12.2 o12.1
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp δ g a₁.1 (not_isIso_of_ne hzx g) ha hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp δ g a₁.1 (not_isIso_of_ne hzx g) ha hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
    (fun ⟨g, hg⟩ ↦ D.not_endo_beta hq a₁ hw hM hMo hE g hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp a₁ g δ.1 (not_isIso_of_ne hzx.symm g) δ.2.2.1 hg)
    (by
      rintro ⟨g, hg⟩
      apply hρaβ
      rw [← hg, Category.assoc, hδβ, comp_zero])
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp a₁ g δ.1 (not_isIso_of_ne hzx.symm g) δ.2.2.1 hg)

/-- A path from a point of `{x₀, x₁}` to a point off it contains an exit arrow
from `x₀` or `x₁`. -/
lemma exists_exit : ∀ (n : ℕ) {u v : RayVert P} (r : Quiver.Path u v), r.length = n →
    (u = x ∨ u = D.t) → v ≠ x → v ≠ D.t →
    ∃ (s y : RayVert P) (_ : y ≠ x) (_ : y ≠ D.t) (e : s ⟶ y), s = x ∨ s = D.t := by
  intro n
  induction n with
  | zero =>
      intro u v r hr hu hvx hvt
      cases r with
      | nil => exact (hu.elim hvx hvt).elim
      | cons _ _ => simp at hr
  | succ n ih =>
      intro u v r hr hu hvx hvt
      cases r with
      | nil => simp at hr
      | cons r' e =>
          rename_i s
          by_cases hs : s = x ∨ s = D.t
          · exact ⟨s, v, hvx, hvt, e, hs⟩
          · push Not at hs
            exact ih r' (by simpa using hr) hu hs.1 hs.2

/-- **The open case gives an exit**: a nonzero morphism from `x₀` to a point off
`{x₀, x₁}` gives an exit arrow at `x₀` or at `x₁`. -/
lemma exit_of_open {z : RayVert P} (hzx : z ≠ x) (hzt : z ≠ D.t) (μ : x.out ⟶ z.out)
    (hμ : μ ≠ 0) :
    (∃ (y : RayVert P) (_ : y ≠ x) (_ : y ≠ D.t), Nonempty (x ⟶ y)) ∨
      (∃ (y : RayVert P) (_ : y ≠ x) (_ : y ≠ D.t), Nonempty (D.t ⟶ y)) := by
  obtain ⟨s, y, hyx, hyt, e, hs⟩ := D.exists_exit hq a₁ hw _ (pathOf (P := P) (x := x.out) (y := z.out) μ hμ)
    rfl (Or.inl rfl) hzx hzt
  rcases hs with rfl | rfl
  · exact Or.inl ⟨y, hyx, hyt, ⟨e⟩⟩
  · exact Or.inr ⟨y, hyx, hyt, ⟨e⟩⟩

section Exit

variable (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) {b : RayVert P}
  (ε : x ⟶ b) (hbx : b ≠ x) (hbt : b ≠ D.t)
include hM hMo hE ε hbx hbt

/-- Given an exit `ε` at `x₀`, the only arrow into `x₁` is `a₁`. -/
lemma in_x1_only {s : RayVert P} (e : s ⟶ D.t) : ∃ h : s = x, HEq e a₁ := by
  have hw' := D.hw2 hq a₁ hw
  by_cases hsx : s = x
  · subst hsx
    obtain ⟨-, he⟩ := D.arrow_into_w hq a₁ .nil hw' hM (Quiver.Path.nil.cons a₁)
      (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) e
    exact ⟨rfl, he⟩
  by_cases hst : s = D.t
  · subst hst
    exact (D.no_loop_x1 hq a₁ hw hM e).elim
  exfalso
  by_cases h0 : e.1 ≫ D.β.1 = 0
  · exact D.not_exit_entry_b hq a₁ hw hM hMo hE ε hbx hbt e hsx hst h0
  · exact D.not_exit_entry_a hq a₁ hw hM hMo hE ε hbx hbt e hsx hst h0

/-- `ε ≫ g = ρ ≫ ρ` is impossible (`ρ ≫ ε = 0`). -/
lemma eps_not_rho_rho : ¬∃ g, ε.1 ≫ g = D.α.1 ≫ D.α.1 := by
  have hw' := D.hw2 hq a₁ hw
  have hρε := D.rho_eps hq a₁ .nil hw' hM ε (fun ⟨h, _⟩ ↦ hbx h) (fun ⟨h, _⟩ ↦ hbt h)
  rintro ⟨g, hg⟩
  apply D.C.τ_ne_zero
  rw [D.τ_eq hq a₁ .nil hw', ← hg, ← Category.assoc, hρε, zero_comp]

/-- `ε ≫ g = ρ ≫ a₁` is impossible (the only arrow into `x₁` is `a₁`). -/
lemma eps_not_rho_a : ¬∃ g, ε.1 ≫ g = D.α.1 ≫ a₁.1 := by
  have hR : RightCancel P := hM.right
  have hw' := D.hw2 hq a₁ hw
  have hab := D.ab_eq hq a₁ hw
  have hρa0 : D.α.1 ≫ a₁.1 ≠ 0 := fun h ↦ D.C.τ_ne_zero (by
    rw [D.τ_eq hq a₁ .nil hw', ← hab, ← Category.assoc, h, zero_comp])
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := fun h0 ↦ hρa0 (by rw [← hg, h0, comp_zero])
  obtain ⟨s, e, r'', hr⟩ : ∃ (s : RayVert P) (e : s ⟶ D.t) (r'' : Quiver.Path b s),
      pathOf (P := P) (x := b.out) (y := D.t.out) g hg0 = r''.cons e := by
    generalize hr : pathOf (P := P) (x := b.out) (y := D.t.out) g hg0 = r
    cases r with
    | nil => exact absurd rfl hbt
    | cons r'' e => exact ⟨_, e, r'', rfl⟩
  have hge : g = pathVal r'' ≫ e.1 := by
    rw [← pathVal_pathOf (P := P) (x := b.out) (y := D.t.out) g hg0, hr]; rfl
  obtain ⟨hs, he⟩ := D.in_x1_only hq a₁ hw hM hMo hE ε hbx hbt e
  subst hs
  have he' := eq_of_heq he
  subst he'
  have e1 : (ε.1 ≫ pathVal r'') ≫ e.1 = D.α.1 ≫ e.1 := by
    rw [Category.assoc, ← hge, hg]
  have e2 := hR _ _ _ e1 (by rw [e1]; exact hρa0)
  exact arrow_ne_comp D.α ε.1 (pathVal r'') ε.2.2.1 (not_isIso_of_ne hbx _) e2

/-- There is only one exit at `x₀`. -/
lemma exit_unique {b' : RayVert P} (ε' : x ⟶ b') (hb'x : b' ≠ x) (hb't : b' ≠ D.t) :
    ∃ h : b = b', HEq ε ε' := by
  by_contra hne
  have hw' := D.hw2 hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  exact hM.not_four_out D.C.τ D.C.τ_not_isIso D.C.τ_ne_zero
    (D.τ_not_irreducible hq a₁ .nil hw') D.α a₁ ε ε' (D.rho_a₁_apart hq a₁ .nil hw' hM)
    (fun ⟨h, _⟩ ↦ hbx h.symm) (fun ⟨h, _⟩ ↦ hb'x h.symm) (fun ⟨h, _⟩ ↦ hbt h.symm)
    (fun ⟨h, _⟩ ↦ hb't h.symm) hne

/-- **[mild] MIPF, figure 4.4 (first diagram)**: the only arrow into `b` is `ε`. -/
theorem in_b_only {z : RayVert P} (e : z ⟶ b) : ∃ h : z = x, HEq e ε := by
  have hR : RightCancel P := hM.right
  have hw' := D.hw2 hq a₁ hw
  have hτ0 := D.C.τ_ne_zero
  have hτ := D.τ_eq hq a₁ .nil hw'
  have hτi := D.τ_not_irreducible hq a₁ .nil hw'
  have hα := D.α.2.2.1
  have hβ := D.β.2.2.1
  have ha := a₁.2.2.1
  have hab := D.ab_eq hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  by_cases hzx : z = x
  · subst hzx
    obtain ⟨h, he⟩ := D.exit_unique hq a₁ hw hM hMo hE ε hbx hbt e hbx hbt
    exact ⟨rfl, he.symm⟩
  exfalso
  have hρa := D.rho_a₁_apart hq a₁ .nil hw' hM
  have o12 := arrows_out_apart D.α a₁ hρa
  have o13 := arrows_out_apart D.α ε (fun ⟨h, _⟩ ↦ hbx h.symm)
  have o23 := arrows_out_apart a₁ ε (fun ⟨h, _⟩ ↦ hbt h.symm)
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism D.C.τ e.1 :=
    fun e ↦ not_ftm_of_irreducible D.C.τ_not_isIso hτi e.2
  have hτab : a₁.1 ≫ (D.β.1 ≫ D.α.1) ≫ 𝟙 _ = D.C.τ := by
    rw [hτ, Category.comp_id, ← Category.assoc, hab, Category.assoc]
  have hτρa : 𝟙 _ ≫ (D.α.1 ≫ a₁.1) ≫ D.β.1 = D.C.τ := by
    rw [hτ, Category.id_comp, Category.assoc, hab]
  have hρa0 : D.α.1 ≫ a₁.1 ≠ 0 := fun h ↦ hτ0 (by
    rw [hτ, ← hab, ← Category.assoc, h, zero_comp])
  have hsp := D.split2 hq a₁ hw
  exact hM.not_m44a D.C.τ D.C.τ_not_isIso hτ0 e.1 ε.1 a₁.1 D.α.1 a₁.1 D.β.1 D.β.1 D.α.1
    M44A.not_isRepresentationFinite hab (D.ba_zero hq a₁ hw hM hE)
    (hf D.α) (hf ε) (D.C.ftm_αρ hR) (hf a₁) (MildContour.not_ftm_mid_right hτ0 hβ hτρa)
    (hf D.α) (hf a₁) (hf D.β) (not_ftm_mid hτ0 ha hτab) (hf D.β) (hf e)
    e.2.2.1 ε.2.2.1 ha hα ha hβ hβ hα
    o13.1 o12.1 o23.2 o13.2 (D.eps_not_rho_a hq a₁ hw hM hMo hE ε hbx hbt)
    (D.eps_not_rho_rho hq a₁ hw hM hMo hE ε hbx hbt) o23.1 o12.2
    (by
      rintro ⟨g, hg⟩
      by_cases hgi : IsIso g
      · obtain ⟨htt, hg'⟩ := RayQuiver.eq_id_of_isIso g
        rw [hg', eqToHom_refl, Category.comp_id] at hg
        exact arrow_ne_comp a₁ D.α.1 a₁.1 hα ha hg.symm
      · apply hρa0
        rw [← hg]
        have hz := D.Z hq a₁ .nil hw' hM hE (Quiver.Path.nil.cons a₁) (Quiver.Path.nil.cons D.β)
          (by simp) (by simp) hsp g hgi
        change (𝟙 _ ≫ a₁.1) ≫ g = 0 at hz
        rwa [Category.id_comp] at hz)
    o12.1 o12.2
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp e g ε.1 (not_isIso_of_ne hzx g) ε.2.2.1 hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
    (fun ⟨g, hg⟩ ↦ D.not_endo_beta hq a₁ hw hM hMo hE g hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp ε g e.1 (not_isIso_of_ne (Ne.symm hzx) g) e.2.2.1 hg)

/-- Given an exit at `x₀`, a point off the penny-farthing has no nonzero morphism
into `x₀` or `x₁` (there is no entry arrow). -/
lemma no_mor_into : ∀ (n : ℕ) {z y : RayVert P} (r : Quiver.Path z y), r.length = n →
    z ≠ x → z ≠ D.t → (y = x ∨ y = D.t) → pathVal r = 0 := by
  intro n
  induction n with
  | zero =>
      intro z y r hr hzx hzt hy
      cases r with
      | nil => exact (hy.elim hzx hzt).elim
      | cons _ _ => simp at hr
  | succ n ih =>
      intro z y r hr hzx hzt hy
      cases r with
      | nil => simp at hr
      | cons r' e =>
          rename_i s
          have hr' : r'.length = n := by simpa using hr
          by_cases hs : s = x ∨ s = D.t
          · change pathVal r' ≫ e.1 = 0
            rw [ih r' hr' hzx hzt hs, zero_comp]
          · push Not at hs
            exfalso
            rcases hy with rfl | rfl
            · -- an entry into `x₀`: separated `D̃₅`
              have hw' := D.hw2 hq a₁ hw
              have htx := D.t_ne_x hq a₁ hw hM
              exact hM.not_loop_d5 D.C.τ D.C.τ_not_isIso D.C.τ_ne_zero
                (D.τ_not_irreducible hq a₁ .nil hw') D.α a₁ ε D.β e
                (D.rho_a₁_apart hq a₁ .nil hw' hM) (fun ⟨h, _⟩ ↦ hbx h.symm)
                (fun ⟨h, _⟩ ↦ hbt h.symm) (fun ⟨h, _⟩ ↦ htx h.symm) (fun ⟨h, _⟩ ↦ hs.1 h.symm)
                (fun ⟨h, _⟩ ↦ hs.2 h.symm)
            · obtain ⟨h, -⟩ := D.in_x1_only hq a₁ hw hM hMo hE ε hbx hbt e
              exact hs.1 h

/-- The arrows out of `x₀` are `ρ`, `a₁` and the exit `ε`. -/
lemma out_x0 {y : RayVert P} (e : x ⟶ y) :
    (∃ h : y = x, HEq e D.α) ∨ (∃ h : y = D.t, HEq e a₁) ∨ (∃ h : y = b, HEq e ε) := by
  have hw' := D.hw2 hq a₁ hw
  by_cases hyx : y = x
  · subst hyx; exact Or.inl ⟨rfl, heq_of_eq (D.loop_eq_rho hq a₁ .nil hw' e)⟩
  by_cases hyt : y = D.t
  · subst hyt
    obtain ⟨-, he⟩ := D.arrow_into_w hq a₁ .nil hw' hM (Quiver.Path.nil.cons a₁)
      (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) e
    exact Or.inr (Or.inl ⟨rfl, he⟩)
  obtain ⟨h, he⟩ := D.exit_unique hq a₁ hw hM hMo hE ε hbx hbt e hyx hyt
  exact Or.inr (Or.inr ⟨h.symm, he.symm⟩)

/-- `ρ³` is right-deep. -/
lemma rho3_kill {y : P} (ξ : x.out ⟶ y) (hξ : ¬IsIso ξ) :
    D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ ξ = 0 := by
  have hw' := D.hw2 hq a₁ hw
  have h4 := (D.rho_four hq a₁ .nil hw' hM).1
  have h2a := (D.rho_four hq a₁ .nil hw' hM).2.1
  have hρε := D.rho_eps hq a₁ .nil hw' hM ε (fun ⟨h, _⟩ ↦ hbx h) (fun ⟨h, _⟩ ↦ hbt h)
  by_cases hξ0 : ξ = 0
  · rw [hξ0]; simp
  obtain ⟨s, e, r', hr⟩ : ∃ (s : RayVert P) (e : x ⟶ s) (r' : Quiver.Path s (RayVert.mk y)),
      pathOf (P := P) (x := x.out) (y := y) ξ hξ0 = (Quiver.Path.nil.cons e).comp r' :=
    path_first_arrow _ (fun h0 ↦ hξ (by
      have := pathVal_pathOf (P := P) (x := x.out) (y := y) ξ hξ0
      revert this
      generalize pathOf (P := P) (x := x.out) (y := y) ξ hξ0 = r at h0
      cases r with
      | cons _ _ => simp at h0
      | nil => intro h; rw [← h]; exact isIso_pathVal_nil))
  have hξe : ξ = e.1 ≫ pathVal r' := by
    rw [← pathVal_pathOf (P := P) (x := x.out) (y := y) ξ hξ0, hr, pathVal_comp]
    change (𝟙 _ ≫ e.1) ≫ _ = _; rw [Category.id_comp]
  rw [hξe]
  have key : D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ e.1 = 0 := by
    rcases D.out_x0 hq a₁ hw hM hMo hE ε hbx hbt e with ⟨h, he⟩ | ⟨h, he⟩ | ⟨h, he⟩
    · subst h; rw [eq_of_heq he]
      have : D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = rpow D.α.1 4 := by simp [rpow_succ]
      rw [this, h4]
    · subst h; rw [eq_of_heq he, ← Category.assoc D.α.1 D.α.1 a₁.1, h2a, comp_zero]
    · subst h; rw [eq_of_heq he, hρε, comp_zero, comp_zero]
  rw [show D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ e.1 ≫ pathVal r' =
    (D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ e.1) ≫ pathVal r' by simp only [Category.assoc], key, zero_comp]

/-- A non-invertible morphism out of `x₀` starts with `ρ`, `a₁` or `ε`. -/
lemma first_out {y : P} (g : x.out ⟶ y) (hg : g ≠ 0) (hgi : ¬IsIso g) :
    (∃ g₁ : x.out ⟶ y, g = D.α.1 ≫ g₁) ∨ (∃ g₁ : D.t.out ⟶ y, g = a₁.1 ≫ g₁) ∨
      (∃ g₁ : b.out ⟶ y, g = ε.1 ≫ g₁) := by
  obtain ⟨s, e, r', hr⟩ : ∃ (s : RayVert P) (e : x ⟶ s) (r' : Quiver.Path s (RayVert.mk y)),
      pathOf (P := P) (x := x.out) (y := y) g hg = (Quiver.Path.nil.cons e).comp r' :=
    path_first_arrow _ (fun h0 ↦ hgi (by
      have := pathVal_pathOf (P := P) (x := x.out) (y := y) g hg
      revert this
      generalize pathOf (P := P) (x := x.out) (y := y) g hg = r at h0
      cases r with
      | cons _ _ => simp at h0
      | nil => intro h; rw [← h]; exact isIso_pathVal_nil))
  have hge : g = e.1 ≫ pathVal r' := by
    rw [← pathVal_pathOf (P := P) (x := x.out) (y := y) g hg, hr, pathVal_comp]
    change (𝟙 _ ≫ e.1) ≫ _ = _; rw [Category.id_comp]
  rcases D.out_x0 hq a₁ hw hM hMo hE ε hbx hbt e with ⟨h, he⟩ | ⟨h, he⟩ | ⟨h, he⟩
  · subst h; rw [eq_of_heq he] at hge; exact Or.inl ⟨_, hge⟩
  · subst h; rw [eq_of_heq he] at hge; exact Or.inr (Or.inl ⟨_, hge⟩)
  · subst h; rw [eq_of_heq he] at hge; exact Or.inr (Or.inr ⟨_, hge⟩)

/-- `ρ² ≫ g = 0` for every `g` from `x₀` to another point. -/
lemma rho2_kill {z : RayVert P} (hzx : z ≠ x) (g : x.out ⟶ z.out) :
    D.α.1 ≫ D.α.1 ≫ g = 0 := by
  have hw' := D.hw2 hq a₁ hw
  have h2a := (D.rho_four hq a₁ .nil hw' hM).2.1
  have hρε := D.rho_eps hq a₁ .nil hw' hM ε (fun ⟨h, _⟩ ↦ hbx h) (fun ⟨h, _⟩ ↦ hbt h)
  by_cases hg : g = 0
  · rw [hg]; simp
  rcases D.first_out hq a₁ hw hM hMo hE ε hbx hbt g hg (not_isIso_of_ne hzx.symm g) with
    ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩
  · exact D.rho3_kill hq a₁ hw hM hMo hE ε hbx hbt g₁ (not_isIso_of_ne hzx.symm g₁)
  · rw [show D.α.1 ≫ D.α.1 ≫ a₁.1 ≫ g₁ = ((D.α.1 ≫ D.α.1) ≫ a₁.1) ≫ g₁ by
      simp only [Category.assoc], h2a, zero_comp]
  · rw [show D.α.1 ≫ D.α.1 ≫ ε.1 ≫ g₁ = D.α.1 ≫ (D.α.1 ≫ ε.1) ≫ g₁ by
      simp only [Category.assoc], hρε, zero_comp, comp_zero]

/-- Every non-invertible morphism into `b` factors through `ε`. -/
lemma into_b {s : RayVert P} (ν : s.out ⟶ b.out) (hν : ν ≠ 0) (hsb : s ≠ b) :
    ∃ ν' : s.out ⟶ x.out, ν = ν' ≫ ε.1 := by
  obtain ⟨r, e, r'', hr⟩ : ∃ (r : RayVert P) (e : r ⟶ b) (r'' : Quiver.Path s r),
      pathOf (P := P) (x := s.out) (y := b.out) ν hν = r''.cons e := by
    generalize hr : pathOf (P := P) (x := s.out) (y := b.out) ν hν = r
    cases r with
    | nil => exact absurd rfl hsb
    | cons r'' e => exact ⟨_, e, r'', rfl⟩
  have hνe : ν = pathVal r'' ≫ e.1 := by
    rw [← pathVal_pathOf (P := P) (x := s.out) (y := b.out) ν hν, hr]; rfl
  obtain ⟨h, he⟩ := D.in_b_only hq a₁ hw hM hMo hE ε hbx hbt e
  subst h
  exact ⟨pathVal r'', by rw [hνe, eq_of_heq he]⟩

/-- **[mild] MIPF, figure 4.4 (second and third diagrams)**: every arrow out of `b`
kills the exit `ε`. -/
theorem eps_kill {z : RayVert P} (ε₂ : b ⟶ z) : ε.1 ≫ ε₂.1 = 0 := by
  by_contra hne
  have hR : RightCancel P := hM.right
  have hw' := D.hw2 hq a₁ hw
  have hτ0 := D.C.τ_ne_zero
  have hτ := D.τ_eq hq a₁ .nil hw'
  have hτi := D.τ_not_irreducible hq a₁ .nil hw'
  have hα := D.α.2.2.1
  have hβ := D.β.2.2.1
  have ha := a₁.2.2.1
  have hab := D.ab_eq hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  have hsp := D.split2 hq a₁ hw
  have hρε := D.rho_eps hq a₁ .nil hw' hM ε (fun ⟨h, _⟩ ↦ hbx h) (fun ⟨h, _⟩ ↦ hbt h)
  have hρa := D.rho_a₁_apart hq a₁ .nil hw' hM
  have o12 := arrows_out_apart D.α a₁ hρa
  have o13 := arrows_out_apart D.α ε (fun ⟨h, _⟩ ↦ hbx h.symm)
  have o23 := arrows_out_apart a₁ ε (fun ⟨h, _⟩ ↦ hbt h.symm)
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism D.C.τ e.1 :=
    fun e ↦ not_ftm_of_irreducible D.C.τ_not_isIso hτi e.2
  have hτab : a₁.1 ≫ (D.β.1 ≫ D.α.1) ≫ 𝟙 _ = D.C.τ := by
    rw [hτ, Category.comp_id, ← Category.assoc, hab, Category.assoc]
  have hτρa : 𝟙 _ ≫ (D.α.1 ≫ a₁.1) ≫ D.β.1 = D.C.τ := by
    rw [hτ, Category.id_comp, Category.assoc, hab]
  have hρ3 : D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 := by rw [← hτ]; exact hτ0
  have hρa0 : D.α.1 ≫ a₁.1 ≠ 0 := fun h ↦ hρ3 (by
    rw [← hab, ← Category.assoc, h, zero_comp])
  have hβρ0 : D.β.1 ≫ D.α.1 ≠ 0 := fun h ↦ hρ3 (by
    rw [← Category.assoc, ← hab, Category.assoc, h, comp_zero])
  -- `z` is off the penny-farthing
  have hzC : z ≠ x ∧ z ≠ D.t := by
    have key : ∀ y, (y = x ∨ y = D.t) → ∀ e : b ⟶ y, False := by
      intro y hy e
      have := D.no_mor_into hq a₁ hw hM hMo hE ε hbx hbt 1 (Quiver.Path.nil.cons e) rfl hbx hbt hy
      change 𝟙 _ ≫ e.1 = 0 at this
      rw [Category.id_comp] at this
      exact e.2.1 this
    exact ⟨fun h ↦ key z (Or.inl h) ε₂, fun h ↦ key z (Or.inr h) ε₂⟩
  have hk3 : ∀ {y : P} (ξ : x.out ⟶ y), ¬IsIso ξ → D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ ξ = 0 :=
    fun ξ hξ ↦ D.rho3_kill hq a₁ hw hM hMo hE ε hbx hbt ξ hξ
  have hk2 : ∀ {z' : RayVert P}, z' ≠ x → ∀ g : x.out ⟶ z'.out, D.α.1 ≫ D.α.1 ≫ g = 0 :=
    fun h g ↦ D.rho2_kill hq a₁ hw hM hMo hE ε hbx hbt h g
  -- the common conditions
  have hA_X1_Y1 : ¬∃ g, a₁.1 ≫ g = D.α.1 ≫ a₁.1 := by
    rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨htt, hg'⟩ := RayQuiver.eq_id_of_isIso g
      rw [hg', eqToHom_refl, Category.comp_id] at hg
      exact arrow_ne_comp a₁ D.α.1 a₁.1 hα ha hg.symm
    · apply hρa0
      rw [← hg]
      have hz := D.Z hq a₁ .nil hw' hM hE (Quiver.Path.nil.cons a₁) (Quiver.Path.nil.cons D.β)
        (by simp) (by simp) hsp g hgi
      change (𝟙 _ ≫ a₁.1) ≫ g = 0 at hz
      rwa [Category.id_comp] at hz
  have hεna := D.eps_not_rho_a hq a₁ hw hM hMo hE ε hbx hbt
  have hεnr := D.eps_not_rho_rho hq a₁ hw hM hMo hE ε hbx hbt
  have hGAB := fun (h : ∃ g, g ≫ D.α.1 = D.β.1) ↦ (by
    obtain ⟨g, hg⟩ := h; exact arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg : False)
  have hAGB := fun (h : ∃ g, g ≫ D.β.1 = D.α.1) ↦ (by
    obtain ⟨g, hg⟩ := h
    exact arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg : False)
  have hGX1W := fun (h : ∃ g, g ≫ D.β.1 = D.β.1 ≫ D.α.1) ↦ (by
    obtain ⟨g, hg⟩ := h; exact D.not_endo_beta hq a₁ hw hM hMo hE g hg : False)
  by_cases hcase : (∃ η : D.t.out ⟶ z.out, ε.1 ≫ ε₂.1 = a₁.1 ≫ η) ∨
      (∃ η : D.t.out ⟶ z.out, ε.1 ≫ ε₂.1 = D.α.1 ≫ a₁.1 ≫ η)
  · -- the third diagram
    obtain ⟨η, hη, hηcase⟩ : ∃ η : D.t.out ⟶ z.out, (ε.1 ≫ ε₂.1 = a₁.1 ≫ η ∨
        ε.1 ≫ ε₂.1 = D.α.1 ≫ a₁.1 ≫ η) ∧ True := by
      rcases hcase with ⟨η, h⟩ | ⟨η, h⟩
      · exact ⟨η, Or.inl h, trivial⟩
      · exact ⟨η, Or.inr h, trivial⟩
    -- `a₁ ≫ η = 0` contradicts the case
    have hkill : a₁.1 ≫ η = 0 → False := fun h ↦ hne (by
      rcases hη with h' | h'
      · rw [h', h]
      · rw [h', h, comp_zero])
    have hηi : ¬IsIso η := not_isIso_of_ne hzC.2.symm η
    exact hM.not_m44c D.C.τ D.C.τ_not_isIso hτ0 ε.1 a₁.1 D.α.1 D.α.1 D.β.1 η ε₂.1 a₁.1 D.β.1
      M44C.not_isRepresentationFinite hab (D.ba_zero hq a₁ hw hM hE)
      (hf D.α) (hf ε) (D.C.ftm_αρ hR) (hf a₁) (MildContour.not_ftm_mid_right hτ0 hβ hτρa)
      (hf D.α) (hf a₁) (hf D.β)
      (by
        rintro ⟨u, v, huv⟩
        apply hkill
        rw [hτ] at huv
        simp only [Category.assoc] at huv
        rw [huv, hk3 v (not_isIso_of_ne hzC.1.symm v), comp_zero, comp_zero])
      (not_ftm_mid hτ0 ha hτab) (hf ε₂) (hf D.β)
      ε.2.2.1 ha hα hα hβ hηi ε₂.2.2.1 ha hβ
      o13.1 o12.1 o23.2 o13.2 hεnr hεna o23.1 o12.2 hA_X1_Y1 o12.1 o12.2
      (by
        rintro ⟨g, hg⟩
        apply hkill
        have hg0 : D.α.1 ≫ D.α.1 ≫ g = 0 := hk2 hzC.1 g
        rcases hη with h' | h'
        · rw [← hg, ← Category.assoc, hab, Category.assoc, hg0]
        · rw [← hg, ← Category.assoc, hab, Category.assoc, hg0])
      (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β η g hηi (not_isIso_of_ne hzC.1 g) hg)
      (by
        rintro ⟨g, hg⟩
        apply hβρ0
        rw [← hg]
        have := D.no_mor_into hq a₁ hw hM hMo hE ε hbx hbt _
          (pathOf (P := P) (x := z.out) (y := x.out) g (fun h0 ↦ hβρ0 (by rw [← hg, h0,
            comp_zero]))) rfl hzC.1 hzC.2 (Or.inl rfl)
        rw [pathVal_pathOf] at this
        rw [this, comp_zero])
      hGAB
      (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
      hAGB
      (fun ⟨g, hg⟩ ↦ arrow_ne_comp ε₂ g η (not_isIso_of_ne hbt g) hηi hg)
      (by
        rintro ⟨g, hg⟩
        apply hkill
        rw [← hg, ← Category.assoc]
        by_cases hag : a₁.1 ≫ g = 0
        · rw [hag, zero_comp]
        obtain ⟨θ, hθ⟩ := D.into_b hq a₁ hw hM hMo hE ε hbx hbt (a₁.1 ≫ g) hag hbx.symm
        exfalso
        rcases D.endo_cases hq a₁ .nil hw' θ with rfl | ⟨m, hm, rfl⟩
        · rw [Category.id_comp] at hθ
          exact arrow_ne_comp ε a₁.1 g ha (not_isIso_of_ne hbt.symm g) hθ
        · apply hag
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rw [hθ, rpow_succ, Category.assoc, hρε, comp_zero])
      (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
      hGX1W
  · -- the second diagram
    push Not at hcase
    obtain ⟨hc1, hc2⟩ := hcase
    have hAB : ¬∃ g, D.α.1 ≫ g = ε.1 ≫ ε₂.1 := by
      rintro ⟨g, hg⟩
      have hg0 : g ≠ 0 := fun h0 ↦ hne (by rw [← hg, h0, comp_zero])
      rcases D.first_out hq a₁ hw hM hMo hE ε hbx hbt g hg0 (not_isIso_of_ne hzC.1.symm g) with
        ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩
      · exact hne (by rw [← hg, hk2 hzC.1 g₁])
      · exact hc2 g₁ hg.symm
      · exact hne (by rw [← hg, ← Category.assoc, hρε, zero_comp])
    exact hM.not_m44b D.C.τ D.C.τ_not_isIso hτ0 ε₂.1 ε.1 a₁.1 D.α.1 a₁.1 D.β.1 D.β.1 D.α.1
      M44B.not_isRepresentationFinite hab (D.ba_zero hq a₁ hw hM hE)
      (hf D.α) (hf ε) (D.C.ftm_αρ hR) (hf a₁) (MildContour.not_ftm_mid_right hτ0 hβ hτρa)
      (by
        rintro ⟨u, v, huv⟩
        apply hne
        rw [hτ] at huv
        simp only [Category.assoc] at huv
        rw [huv, hk3 v (not_isIso_of_ne hzC.1.symm v), comp_zero])
      (hf D.α) (hf a₁) (hf ε₂) (hf D.β) (not_ftm_mid hτ0 ha hτab) (hf D.β)
      ε₂.2.2.1 ε.2.2.1 ha hα ha hβ hβ hα
      hAB o13.1 o12.1 o23.2 o13.2 hεna hεnr (fun ⟨g, hg⟩ ↦ hc1 g hg.symm) o23.1 o12.2
      hA_X1_Y1 o12.1 o12.2 hGAB
      (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
      hAGB
      (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
      hGX1W

/-- A non-invertible nonzero morphism out of `b` starts with an arrow. -/
lemma first_out_b {y : P} (g : b.out ⟶ y) (hg : g ≠ 0) (hgi : ¬IsIso g) :
    ∃ (s : RayVert P) (δ : b ⟶ s) (g₁ : s.out ⟶ y), g = δ.1 ≫ g₁ := by
  obtain ⟨s, e, r', hr⟩ : ∃ (s : RayVert P) (e : b ⟶ s) (r' : Quiver.Path s (RayVert.mk y)),
      pathOf (P := P) (x := b.out) (y := y) g hg = (Quiver.Path.nil.cons e).comp r' :=
    path_first_arrow _ (fun h0 ↦ hgi (by
      have := pathVal_pathOf (P := P) (x := b.out) (y := y) g hg
      revert this
      generalize pathOf (P := P) (x := b.out) (y := y) g hg = r at h0
      cases r with
      | cons _ _ => simp at h0
      | nil => intro h; rw [← h]; exact isIso_pathVal_nil))
  refine ⟨s, e, pathVal r', ?_⟩
  rw [← pathVal_pathOf (P := P) (x := b.out) (y := y) g hg, hr, pathVal_comp]
  change (𝟙 _ ≫ e.1) ≫ _ = _; rw [Category.id_comp]

/-- With an exit at `x₀`, the arrows out of `x₁` are `β` and at most one further
exit `γ` (a second one gives a separated `D̃₆`). -/
lemma out_x1 {c : RayVert P} (γ : D.t ⟶ c) (hcx : c ≠ x) (hct : c ≠ D.t) {y : RayVert P}
    (e : D.t ⟶ y) : (∃ h : y = x, HEq e D.β) ∨ (∃ h : y = c, HEq e γ) := by
  have hw' := D.hw2 hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  by_cases hyx : y = x
  · subst hyx
    obtain ⟨-, he⟩ := D.arrow_from_w hq a₁ .nil hw' hMo (Quiver.Path.nil.cons a₁)
      (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) e
    exact Or.inl ⟨rfl, he⟩
  by_cases hyt : y = D.t
  · subst hyt; exact (D.no_loop_x1 hq a₁ hw hM e).elim
  by_cases hyc : ∃ h : y = c, HEq e γ
  · exact Or.inr hyc
  exfalso
  exact hM.not_sep_d6 D.C.τ D.C.τ_not_isIso D.C.τ_ne_zero (D.τ_not_irreducible hq a₁ .nil hw')
    γ e D.β D.α a₁ ε (fun ⟨h, he⟩ ↦ hyc ⟨h.symm, he.symm⟩) (fun ⟨h, _⟩ ↦ hcx h)
    (fun ⟨h, _⟩ ↦ hyx h) (D.rho_a₁_apart hq a₁ .nil hw' hM) (fun ⟨h, _⟩ ↦ hbx h.symm)
    (fun ⟨h, _⟩ ↦ hbt h.symm) (fun ⟨h, _⟩ ↦ htx h)

/-- **[mild] MIPF, figure 4.5 (second diagram)**: with an exit `ε` at `x₀`, every exit
`γ` at `x₁` has `a₁ ≫ γ = 0`. -/
theorem a_gamma_zero {c : RayVert P} (γ : D.t ⟶ c) (hcx : c ≠ x) (hct : c ≠ D.t) :
    a₁.1 ≫ γ.1 = 0 := by
  by_contra hne
  have hR : RightCancel P := hM.right
  have hw' := D.hw2 hq a₁ hw
  have hτ0 := D.C.τ_ne_zero
  have hτ := D.τ_eq hq a₁ .nil hw'
  have hτi := D.τ_not_irreducible hq a₁ .nil hw'
  have hα := D.α.2.2.1
  have hβ := D.β.2.2.1
  have ha := a₁.2.2.1
  have hab := D.ab_eq hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  have hρε := D.rho_eps hq a₁ .nil hw' hM ε (fun ⟨h, _⟩ ↦ hbx h) (fun ⟨h, _⟩ ↦ hbt h)
  have hρa := D.rho_a₁_apart hq a₁ .nil hw' hM
  have o12 := arrows_out_apart D.α a₁ hρa
  have o13 := arrows_out_apart D.α ε (fun ⟨h, _⟩ ↦ hbx h.symm)
  have o23 := arrows_out_apart a₁ ε (fun ⟨h, _⟩ ↦ hbt h.symm)
  have hf : ∀ {p q : RayVert P} (e : p ⟶ q), ¬FactorsThroughMorphism D.C.τ e.1 :=
    fun e ↦ not_ftm_of_irreducible D.C.τ_not_isIso hτi e.2
  have hτab : a₁.1 ≫ (D.β.1 ≫ D.α.1) ≫ 𝟙 _ = D.C.τ := by
    rw [hτ, Category.comp_id, ← Category.assoc, hab, Category.assoc]
  have hcb : c ≠ b := by
    intro h; subst h
    obtain ⟨h', -⟩ := D.in_b_only hq a₁ hw hM hMo hE ε hbx hbt γ
    exact htx h'
  have hk3 : ∀ {y : P} (ξ : x.out ⟶ y), ¬IsIso ξ → D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ ξ = 0 :=
    fun ξ hξ ↦ D.rho3_kill hq a₁ hw hM hMo hE ε hbx hbt ξ hξ
  have hk2 : ∀ {z' : RayVert P}, z' ≠ x → ∀ g : x.out ⟶ z'.out, D.α.1 ≫ D.α.1 ≫ g = 0 :=
    fun h g ↦ D.rho2_kill hq a₁ hw hM hMo hE ε hbx hbt h g
  have h4 := (D.rho_four hq a₁ .nil hw' hM).1
  have hεnr := D.eps_not_rho_rho hq a₁ hw hM hMo hE ε hbx hbt
  -- `ρ ≫ g = a₁ ≫ γ` is impossible
  have hABC : ¬∃ g, D.α.1 ≫ g = a₁.1 ≫ γ.1 := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h0 ↦ hne (by rw [← hg, h0, comp_zero])
    rcases D.first_out hq a₁ hw hM hMo hE ε hbx hbt g hg0 (not_isIso_of_ne hcx.symm g) with
      ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩
    · exact hne (by rw [← hg, hk2 hcx g₁])
    · -- `g₁ : x₁ → c` starts with `β` or `γ`
      have hg₁0 : g₁ ≠ 0 := fun h0 ↦ hg0 (by rw [h0, comp_zero])
      obtain ⟨s, e, r', hr⟩ : ∃ (s : RayVert P) (e : D.t ⟶ s) (r' : Quiver.Path s c),
          pathOf (P := P) (x := D.t.out) (y := c.out) g₁ hg₁0 = (Quiver.Path.nil.cons e).comp r' :=
        path_first_arrow _ (fun h0 ↦ not_isIso_of_ne hct.symm g₁ (by
          have := pathVal_pathOf (P := P) (x := D.t.out) (y := c.out) g₁ hg₁0
          revert this
          generalize pathOf (P := P) (x := D.t.out) (y := c.out) g₁ hg₁0 = r at h0
          cases r with
          | cons _ _ => simp at h0
          | nil => intro h; rw [← h]; exact isIso_pathVal_nil))
      have hge : g₁ = e.1 ≫ pathVal r' := by
        rw [← pathVal_pathOf (P := P) (x := D.t.out) (y := c.out) g₁ hg₁0, hr, pathVal_comp]
        change (𝟙 _ ≫ e.1) ≫ _ = _; rw [Category.id_comp]
      rcases D.out_x1 hq a₁ hw hM hMo hE ε hbx hbt γ hcx hct e with ⟨h, he⟩ | ⟨h, he⟩
      · subst h; rw [eq_of_heq he] at hge
        apply hne
        rw [← hg, hge, show D.α.1 ≫ a₁.1 ≫ D.β.1 ≫ pathVal r' =
          D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ pathVal r' by
            rw [← Category.assoc a₁.1, hab]; simp only [Category.assoc]]
        exact hk3 _ (not_isIso_of_ne hcx.symm _)
      · subst h; rw [eq_of_heq he] at hge
        have hs : a₁.1 ≫ γ.1 = D.α.1 ≫ (a₁.1 ≫ γ.1) ≫ pathVal r' := by
          conv_lhs => rw [← hg, hge]
          simp only [Category.assoc]
        apply hne
        rw [eq_rpow_sandwich hs 4, h4, zero_comp]
    · exact hne (by rw [← hg, ← Category.assoc, hρε, zero_comp])
  exact hM.not_m45b D.C.τ D.C.τ_not_isIso hτ0 ε.1 D.α.1 a₁.1 γ.1 D.β.1 D.α.1 D.β.1
    M45B.not_isRepresentationFinite hab
    (hf D.α) (hf ε)
    (by
      rintro ⟨u, v, huv⟩
      apply hne
      rw [hτ] at huv
      simp only [Category.assoc] at huv
      rw [huv, hk3 v (not_isIso_of_ne hcx.symm v), comp_zero])
    (D.C.ftm_αρ hR) (hf a₁) (hf D.α) (hf D.β) (not_ftm_mid hτ0 ha hτab) (hf γ) (hf D.β)
    ε.2.2.1 hα ha γ.2.2.1 hβ hα hβ
    o13.1 o12.1 hABC o13.2 o23.2
    (by
      rintro ⟨g, hg⟩
      apply hne
      rw [← hg]
      by_cases hg0 : g = 0
      · rw [hg0, comp_zero]
      rcases D.first_out_b hq a₁ hw hM hMo hE ε hbx hbt g hg0 (not_isIso_of_ne hcb.symm g) with
        ⟨s, δ, g₁, rfl⟩
      rw [← Category.assoc, D.eps_kill hq a₁ hw hM hMo hE ε hbx hbt δ, zero_comp])
    hεnr o23.1 o12.2
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β γ.1 g γ.2.2.1 (not_isIso_of_ne hcx g) hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp γ D.β.1 g hβ (not_isIso_of_ne hcx.symm g) hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.β g D.α.1 (not_isIso_of_ne htx g) hα hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
    (fun ⟨g, hg⟩ ↦ arrow_ne_comp D.α g D.β.1 (not_isIso_of_ne htx.symm g) hβ hg)
    (fun ⟨g, hg⟩ ↦ D.not_endo_beta hq a₁ hw hM hMo hE g hg)

/-- A non-invertible nonzero morphism out of `x₁` starts with an arrow. -/
lemma first_out_t {y : P} (g : D.t.out ⟶ y) (hg : g ≠ 0) (hgi : ¬IsIso g) :
    ∃ (s : RayVert P) (e : D.t ⟶ s) (g₁ : s.out ⟶ y), g = e.1 ≫ g₁ := by
  obtain ⟨s, e, r', hr⟩ : ∃ (s : RayVert P) (e : D.t ⟶ s) (r' : Quiver.Path s (RayVert.mk y)),
      pathOf (P := P) (x := D.t.out) (y := y) g hg = (Quiver.Path.nil.cons e).comp r' :=
    path_first_arrow _ (fun h0 ↦ hgi (by
      have := pathVal_pathOf (P := P) (x := D.t.out) (y := y) g hg
      revert this
      generalize pathOf (P := P) (x := D.t.out) (y := y) g hg = r at h0
      cases r with
      | cons _ _ => simp at h0
      | nil => intro h; rw [← h]; exact isIso_pathVal_nil))
  refine ⟨s, e, pathVal r', ?_⟩
  rw [← pathVal_pathOf (P := P) (x := D.t.out) (y := y) g hg, hr, pathVal_comp]
  change (𝟙 _ ≫ e.1) ≫ _ = _; rw [Category.id_comp]

/-- `a₁ ≫ g = 0` for `g` from `x₁` to a point off the penny-farthing. -/
lemma a_kill_off {y : RayVert P} (hyx : y ≠ x) (hyt : y ≠ D.t) (g : D.t.out ⟶ y.out) :
    a₁.1 ≫ g = 0 := by
  have hab := D.ab_eq hq a₁ hw
  by_cases hg : g = 0
  · rw [hg, comp_zero]
  obtain ⟨s, e, g₁, rfl⟩ := D.first_out_t hq a₁ hw hM hMo hE ε hbx hbt g hg
    (not_isIso_of_ne hyt.symm g)
  by_cases hsx : s = x
  · subst hsx
    obtain ⟨-, he⟩ := D.arrow_from_w hq a₁ .nil (D.hw2 hq a₁ hw) hMo (Quiver.Path.nil.cons a₁)
      (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) e
    rw [eq_of_heq he, ← Category.assoc, hab, Category.assoc,
      D.rho2_kill hq a₁ hw hM hMo hE ε hbx hbt hyx g₁]
  by_cases hst : s = D.t
  · subst hst; exact (D.no_loop_x1 hq a₁ hw hM e).elim
  rw [← Category.assoc, D.a_gamma_zero hq a₁ hw hM hMo hE ε hbx hbt e hsx hst, zero_comp]

/-- `ρ ≫ g = 0` for `g` from `x₀` to a point off the penny-farthing. -/
lemma rho_kill_off {y : RayVert P} (hyx : y ≠ x) (hyt : y ≠ D.t) (g : x.out ⟶ y.out) :
    D.α.1 ≫ g = 0 := by
  have hw' := D.hw2 hq a₁ hw
  have hρε := D.rho_eps hq a₁ .nil hw' hM ε (fun ⟨h, _⟩ ↦ hbx h) (fun ⟨h, _⟩ ↦ hbt h)
  by_cases hg : g = 0
  · rw [hg, comp_zero]
  rcases D.first_out hq a₁ hw hM hMo hE ε hbx hbt g hg (not_isIso_of_ne hyx.symm g) with
    ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩
  · exact D.rho2_kill hq a₁ hw hM hMo hE ε hbx hbt hyx g₁
  · rw [D.a_kill_off hq a₁ hw hM hMo hE ε hbx hbt hyx hyt g₁, comp_zero]
  · rw [← Category.assoc, hρε, zero_comp]

/-- **The exit `ε` makes `x₀` a tiny penny-farthing point** (`s = ρ³`, `t = ε`). -/
theorem tiny_x0 : TinyAt (D.α.1 ≫ D.α.1 ≫ D.α.1) ε.1 := by
  have hw' := D.hw2 hq a₁ hw
  have hα := D.α.2.2.1
  have hab := D.ab_eq hq a₁ hw
  have htx := D.t_ne_x hq a₁ hw hM
  have h4 := (D.rho_four hq a₁ .nil hw' hM).1
  have h2a := (D.rho_four hq a₁ .nil hw' hM).2.1
  have hb2 := (D.rho_four hq a₁ .nil hw' hM).2.2
  have hρ3 : D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 := by
    rw [← D.τ_eq hq a₁ .nil hw']; exact D.C.τ_ne_zero
  have hr3 : rpow D.α.1 3 = D.α.1 ≫ D.α.1 ≫ D.α.1 := by simp [rpow_succ]
  have hr2 : ∀ n, n ≤ 2 → rpow D.α.1 n ≫ D.α.1 ≠ 0 := by
    intro n hn h0
    apply hρ3
    rw [← hr3, show 3 = n + 1 + (2 - n) by omega, rpow_add, rpow_succ, h0, zero_comp]
  have hsp := D.split2 hq a₁ hw
  have hbe : x.out ≠ b.out := fun h ↦ hbx (congrArg RayVert.mk h).symm
  refine ⟨hρ3, ε.2.1, hbe, hbe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w ζ hζ
    simp only [Category.assoc]
    exact D.rho3_kill hq a₁ hw hM hMo hE ε hbx hbt ζ hζ
  · intro u ζ hζ
    by_cases hζ0 : ζ = 0
    · rw [hζ0, zero_comp]
    obtain ⟨r, e, r'', hr⟩ : ∃ (r : RayVert P) (e : r ⟶ x) (r'' : Quiver.Path (RayVert.mk u) r),
        pathOf (P := P) (x := u) (y := x.out) ζ hζ0 = r''.cons e := by
      generalize hr : pathOf (P := P) (x := u) (y := x.out) ζ hζ0 = r
      cases r with
      | nil => exact absurd (by rw [← pathVal_pathOf ζ hζ0, hr]; exact isIso_pathVal_nil) hζ
      | cons r'' e => exact ⟨_, e, r'', rfl⟩
    have hζe : ζ = pathVal r'' ≫ e.1 := by
      rw [← pathVal_pathOf (P := P) (x := u) (y := x.out) ζ hζ0, hr]; rfl
    rw [hζe, Category.assoc]
    by_cases hrx : r = x
    · subst hrx
      rw [D.loop_eq_rho hq a₁ .nil hw' e]
      rw [show D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = rpow D.α.1 4 by simp [rpow_succ], h4, comp_zero]
    by_cases hrt : r = D.t
    · subst hrt
      obtain ⟨-, he⟩ := D.arrow_from_w hq a₁ .nil hw' hMo (Quiver.Path.nil.cons a₁)
        (Quiver.Path.nil.cons D.β) (by simp) (by simp) hsp e
      have hb3 : D.β.1 ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = 0 := by
        rw [show D.β.1 ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = (D.β.1 ≫ D.α.1 ≫ D.α.1) ≫ D.α.1 by
          simp only [Category.assoc], hb2, zero_comp]
      rw [eq_of_heq he, hb3, comp_zero]
    exfalso
    exact hM.not_loop_d5 D.C.τ D.C.τ_not_isIso D.C.τ_ne_zero
      (D.τ_not_irreducible hq a₁ .nil hw') D.α a₁ ε D.β e
      (D.rho_a₁_apart hq a₁ .nil hw' hM) (fun ⟨h, _⟩ ↦ hbx h.symm)
      (fun ⟨h, _⟩ ↦ hbt h.symm) (fun ⟨h, _⟩ ↦ htx h.symm) (fun ⟨h, _⟩ ↦ hrx h.symm)
      (fun ⟨h, _⟩ ↦ hrt h.symm)
  · intro w ζ hζ
    by_cases hζ0 : ζ = 0
    · rw [hζ0, comp_zero]
    obtain ⟨s, δ, g₁, rfl⟩ := D.first_out_b hq a₁ hw hM hMo hE ε hbx hbt ζ hζ0 hζ
    rw [← Category.assoc, D.eps_kill hq a₁ hw hM hMo hE ε hbx hbt δ, zero_comp]
  · intro y a c hac
    exact ε.2.2.2 _ a c hac.symm
  · intro y μ hμ0 hμ
    have hβ := D.β.2.2.1
    by_cases hyx : y = x.out
    · subst hyx
      left
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.comp_id]
      rcases D.endo_cases hq a₁ .nil hw' μ with rfl | ⟨n, hn, rfl⟩
      · exact absurd (by simpa using hμ D.α.1 hα) D.α.2.1
      · have hn3 : 3 ≤ n := by
          by_contra hlt
          exact hr2 n (by omega) (hμ D.α.1 hα)
        have hn3' : n ≤ 3 := by
          by_contra hlt
          apply hμ0
          rw [show n = 4 + (n - 4) by omega, rpow_add, h4, zero_comp]
        rw [show n = 3 by omega, hr3]
    by_cases hyt : y = D.t.out
    · subst hyt
      exfalso
      obtain ⟨m, hm⟩ := D.mor_to_interior hq a₁ .nil hw' hM hE (Quiver.Path.nil.cons a₁)
        (Quiver.Path.nil.cons D.β) (by simp) (by simp) hsp μ hμ0
      have ha' : pathVal (Quiver.Path.nil.cons a₁) = a₁.1 := by
        change 𝟙 _ ≫ a₁.1 = _; rw [Category.id_comp]
      rw [ha'] at hm
      have h1 := hμ D.β.1 hβ
      rw [hm, Category.assoc, hab] at h1
      by_cases hm2 : m ≤ 1
      · apply hr2 (m + 1) (by omega)
        rw [rpow_succ, Category.assoc]; exact h1
      · apply hμ0
        rw [hm, show m = (m - 2) + 1 + 1 by omega, rpow_succ, rpow_succ, Category.assoc,
          Category.assoc, ← Category.assoc D.α.1 D.α.1, h2a, comp_zero]
    have hYx : RayVert.mk y ≠ x := fun h ↦ hyx (congrArg RayVert.out h)
    have hYt : RayVert.mk y ≠ D.t := fun h ↦ hyt (congrArg RayVert.out h)
    rcases D.first_out hq a₁ hw hM hMo hE ε hbx hbt μ hμ0 (not_isIso_of_ne hYx.symm μ) with
      ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩
    · exact absurd (D.rho_kill_off hq a₁ hw hM hMo hE ε hbx hbt hYx hYt g₁) hμ0
    · exact absurd (D.a_kill_off hq a₁ hw hM hMo hE ε hbx hbt hYx hYt g₁) hμ0
    · right
      by_cases hg : IsIso g₁
      · obtain ⟨hby, hg'⟩ := RayQuiver.eq_id_of_isIso g₁
        exact ⟨hby.symm, by rw [hg']; simp⟩
      · exfalso
        apply hμ0
        have hg0 : g₁ ≠ 0 := fun h0 ↦ hμ0 (by rw [h0, comp_zero])
        obtain ⟨s', δ, g₂, rfl⟩ := D.first_out_b hq a₁ hw hM hMo hE ε hbx hbt g₁ hg0 hg
        rw [← Category.assoc, D.eps_kill hq a₁ hw hM hMo hE ε hbx hbt δ, zero_comp]
  · intro w ν hν0 hν
    have ha := a₁.2.2.1
    by_cases hwx : w = x.out
    · subst hwx
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.id_comp]
      rcases D.endo_cases hq a₁ .nil hw' ν with rfl | ⟨n, hn, rfl⟩
      · exact absurd (by simpa using hν D.α.1 hα) D.α.2.1
      · have h1 := hν D.α.1 hα
        rw [← rpow_succ', rpow_succ] at h1
        have hn3 : 3 ≤ n := by
          by_contra hlt
          exact hr2 n (by omega) h1
        have hn3' : n ≤ 3 := by
          by_contra hlt
          apply hν0
          rw [show n = 4 + (n - 4) by omega, rpow_add, h4, zero_comp]
        rw [show n = 3 by omega, hr3]
    by_cases hwt : w = D.t.out
    · subst hwt
      exfalso
      obtain ⟨m, hm⟩ := D.mor_from_interior hq a₁ .nil hw' hMo hE (Quiver.Path.nil.cons a₁)
        (Quiver.Path.nil.cons D.β) (by simp) (by simp) hsp ν hν0
      have hb' : pathVal (Quiver.Path.nil.cons D.β) = D.β.1 := by
        change 𝟙 _ ≫ D.β.1 = _; rw [Category.id_comp]
      rw [hb'] at hm
      have h1 := hν a₁.1 ha
      rw [hm, ← Category.assoc, hab] at h1
      have e2 : (D.α.1 ≫ D.α.1) ≫ rpow D.α.1 m = rpow D.α.1 (m + 1) ≫ D.α.1 := by
        rw [show D.α.1 ≫ D.α.1 = rpow D.α.1 2 by simp [rpow_succ], ← rpow_add, ← rpow_succ]
        congr 1; omega
      by_cases hm2 : m ≤ 1
      · exact hr2 (m + 1) (by omega) (by rw [← e2]; exact h1)
      · apply hν0
        rw [hm, show m = 2 + (m - 2) by omega, rpow_add,
          show rpow D.α.1 2 = D.α.1 ≫ D.α.1 by simp [rpow_succ], ← Category.assoc, hb2,
          zero_comp]
    have hWx : RayVert.mk w ≠ x := fun h ↦ hwx (congrArg RayVert.out h)
    have hWt : RayVert.mk w ≠ D.t := fun h ↦ hwt (congrArg RayVert.out h)
    exact absurd (by
      have := D.no_mor_into hq a₁ hw hM hMo hE ε hbx hbt _
        (pathOf (P := P) (x := w) (y := x.out) ν hν0) rfl hWx hWt (Or.inl rfl)
      rwa [pathVal_pathOf] at this) hν0
  · intro y ν hν
    by_cases hν0 : ν = 0
    · exact ⟨0, by rw [hν0, zero_comp]⟩
    obtain ⟨r, e, r'', hr⟩ : ∃ (r : RayVert P) (e : r ⟶ b) (r'' : Quiver.Path (RayVert.mk y) r),
        pathOf (P := P) (x := y) (y := b.out) ν hν0 = r''.cons e := by
      generalize hr : pathOf (P := P) (x := y) (y := b.out) ν hν0 = r
      cases r with
      | nil => exact absurd (by rw [← pathVal_pathOf ν hν0, hr]; exact isIso_pathVal_nil) hν
      | cons r'' e => exact ⟨_, e, r'', rfl⟩
    have hνe : ν = pathVal r'' ≫ e.1 := by
      rw [← pathVal_pathOf (P := P) (x := y) (y := b.out) ν hν0, hr]; rfl
    obtain ⟨h, he⟩ := D.in_b_only hq a₁ hw hM hMo hE ε hbx hbt e
    subst h
    exact ⟨pathVal r'', by rw [hνe, eq_of_heq he]⟩

end Exit

end Two

end PFData

end RayCat

end LargeIndecomposable
