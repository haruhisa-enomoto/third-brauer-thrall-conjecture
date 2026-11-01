module

public import LargeIndecomposable.MildContours.PennyFarthings.Open
public import LargeIndecomposable.MildContours.PennyFarthings.OpenCase2
public import LargeIndecomposable.Cleaving.Shapes.ShapeLPF3
public import LargeIndecomposable.Cleaving.Families.FamLPF2
public import LargeIndecomposable.Cleaving.Families.FamLPF1
public import LargeIndecomposable.Cleaving.Shapes.ShapeLPF0D
public import LargeIndecomposable.Cleaving.Shapes.ShapeLPF0E
public import LargeIndecomposable.Crowns.Section225.Split

/-!
# [mild] LPF: the open penny-farthing has `n = 2`

`OnW y`: `y` is a point of the cycle `w`. `first_exit`: a nonzero morphism from `x₀`
to a point off `w` is `ρᵐ ≫ λ ≫ ε ≫ g` with `λ` a prefix of `w` and `ε` an arrow
leaving `w`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

namespace PFData

section LPF

variable {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P} (a₁ : x ⟶ c)
  (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)
include hq hw

/-- `y` is a point of the cycle `w`. -/
def OnW (y : RayVert P) : Prop :=
  ∃ (p : Quiver.Path x y) (s : Quiver.Path y x), D.w'.cons D.β = p.comp s

omit hq hw in
lemma onW_x : D.OnW x := ⟨.nil, D.w'.cons D.β, (Quiver.Path.nil_comp _).symm⟩

/-- **The first exit**: a nonzero morphism from `x₀` along a path ending off `w` is
`ρᵐ ≫ λ ≫ ε ≫ g` with `λ` a prefix of `w` and `ε` an arrow from a point of `w` to a
point off `w`. -/
theorem first_exit (hM : MildHyp k P) (hE : EndCyclic P) :
    ∀ (n : ℕ) {z : RayVert P} (r : Quiver.Path x z), r.length = n → pathVal r ≠ 0 →
      ¬D.OnW z → ∃ (q : RayVert P) (p : Quiver.Path x q) (s : Quiver.Path q x)
        (_ : D.w'.cons D.β = p.comp s) (y : RayVert P) (ε : q ⟶ y) (_ : ¬D.OnW y) (m : ℕ)
        (g : y.out ⟶ z.out), pathVal r = rpow D.α.1 m ≫ pathVal p ≫ ε.1 ≫ g := by
  intro n
  induction n with
  | zero =>
    intro z r hr _ hz
    cases r with
    | nil => exact (hz (D.onW_x)).elim
    | cons _ _ => simp at hr
  | succ n ih =>
    intro z r hr h0 hz
    cases r with
    | nil => simp at hr
    | cons r' e =>
      rename_i s'
      have h0' : pathVal r' ≠ 0 := fun h ↦ h0 (by change pathVal r' ≫ e.1 = 0; rw [h, zero_comp])
      by_cases hs' : D.OnW s'
      · obtain ⟨p, s, hps⟩ := hs'
        -- the value of `r'` is `ρᵐ ≫ λ`
        have key : ∃ (q : RayVert P) (p₀ : Quiver.Path x q) (s₀ : Quiver.Path q x)
            (_ : D.w'.cons D.β = p₀.comp s₀) (_ : q = s') (m : ℕ),
            HEq (pathVal r') (rpow D.α.1 m ≫ pathVal p₀) := by
          rcases Nat.eq_zero_or_pos p.length with hp | hp
          · cases p with
            | cons _ _ => simp at hp
            | nil =>
              rcases D.endo_cases hq a₁ w₁ hw (pathVal r') with h | ⟨m, -, h⟩
              · exact ⟨x, .nil, D.w'.cons D.β, (Quiver.Path.nil_comp _).symm, rfl, 0,
                  heq_of_eq (by rw [h]; simp [pathVal])⟩
              · exact ⟨x, .nil, D.w'.cons D.β, (Quiver.Path.nil_comp _).symm, rfl, m,
                  heq_of_eq (by rw [h]; simp [pathVal])⟩
          rcases Nat.eq_zero_or_pos s.length with hs | hs
          · cases s with
            | cons _ _ => simp at hs
            | nil =>
              rcases D.endo_cases hq a₁ w₁ hw (pathVal r') with h | ⟨m, -, h⟩
              · exact ⟨x, .nil, D.w'.cons D.β, (Quiver.Path.nil_comp _).symm, rfl, 0,
                  heq_of_eq (by rw [h]; simp [pathVal])⟩
              · exact ⟨x, .nil, D.w'.cons D.β, (Quiver.Path.nil_comp _).symm, rfl, m,
                  heq_of_eq (by rw [h]; simp [pathVal])⟩
          obtain ⟨m, hm⟩ := D.mor_to_interior hq a₁ w₁ hw hM hE p s hp hs hps (pathVal r') h0'
          exact ⟨s', p, s, hps, rfl, m, heq_of_eq hm⟩
        obtain ⟨q, p₀, s₀, hps₀, rfl, m, hm⟩ := key
        exact ⟨q, p₀, s₀, hps₀, z, e, hz, m, 𝟙 _, by
          change pathVal r' ≫ e.1 = _; rw [eq_of_heq hm]; simp⟩
      · obtain ⟨q, p, s, hps, y, ε, hy, m, g, hg⟩ := ih r' (by simpa using hr) h0' hs'
        exact ⟨q, p, s, hps, y, ε, hy, m, g ≫ e.1, by
          change pathVal r' ≫ e.1 = _; rw [hg]; simp⟩

/-- The split of `w` after its first arrow. -/
lemma split1 : D.w'.cons D.β = (Quiver.Path.nil.cons a₁).comp (w₁.cons D.β) := by
  rw [hw]; rfl

/-- `ρ³ ≠ 0`. -/
lemma rho3_ne : D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 := by
  rw [← D.τ_eq hq a₁ w₁ hw]; exact D.C.τ_ne_zero

/-- `β ≫ a₁ = 0`. -/
lemma ba_zero_gen (hM : MildHyp k P) (hE : EndCyclic P) : D.β.1 ≫ a₁.1 = 0 := by
  obtain ⟨u, v, huv⟩ := D.β_a₁ hq a₁ w₁ hw hM
  by_cases hv : v = 0
  · rw [huv, hv, comp_zero, comp_zero]
  obtain ⟨m, rfl⟩ := D.mor_to_interior hq a₁ w₁ hw hM hE (Quiver.Path.nil.cons a₁)
    (w₁.cons D.β) (by simp) (by simp) (D.split1 hq a₁ w₁ hw) v hv
  have h2 := (D.rho_four hq a₁ w₁ hw hM).2.1
  have ha : pathVal (Quiver.Path.nil.cons a₁) = a₁.1 := by
    change 𝟙 _ ≫ a₁.1 = _; rw [Category.id_comp]
  rw [huv, ha, D.τ_eq hq a₁ w₁ hw]
  have : (D.α.1 ≫ D.α.1 ≫ D.α.1) ≫ rpow D.α.1 m ≫ a₁.1 =
      rpow D.α.1 (m + 1) ≫ (D.α.1 ≫ D.α.1) ≫ a₁.1 := by
    have e1 : D.α.1 ≫ D.α.1 ≫ D.α.1 = rpow D.α.1 3 := by simp [rpow_succ]
    have e2 : D.α.1 ≫ D.α.1 = rpow D.α.1 2 := by simp [rpow_succ]
    rw [e1, e2, ← Category.assoc, ← Category.assoc, ← rpow_add, ← rpow_add,
      show 3 + m = m + 1 + 2 by omega]
  rw [this, h2, comp_zero, comp_zero]

/-- **Dual of `rho_eps`**: an arrow into `x₀` other than `ρ`, `β` is killed by `ρ`. -/
theorem eps_rho (hMo : MildHyp k Pᵒᵖ) {y : RayVert P} (ζ : y ⟶ x)
    (h₁ : ¬∃ h : y = x, HEq ζ D.α) (h₂ : ¬∃ h : y = D.t, HEq ζ D.β) : ζ.1 ≫ D.α.1 = 0 := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have h := (D.op hq a₁ w₁ hw).rho_eps rfl (revArr D.β) (revPath w₁) rfl hMo (revArr ζ) ?_ ?_
  · apply Quiver.Hom.op_inj
    rw [op_comp, op_zero]
    exact h
  · rintro ⟨hh, he⟩
    apply h₁
    have hyx : y = x := by
      have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) hh
      exact this
    subst hyx
    refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
    have := congrArg (fun f : (RayVert.mk (Opposite.op y.out) : RayVert Pᵒᵖ) ⟶
      RayVert.mk (Opposite.op y.out) ↦ f.1.unop) (eq_of_heq he)
    exact this
  · rintro ⟨hh, he⟩
    apply h₂
    have hyt : y = D.t := by
      have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) hh
      exact this
    subst hyt
    refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
    have := congrArg (fun f : (RayVert.mk (Opposite.op x.out) : RayVert Pᵒᵖ) ⟶
      RayVert.mk (Opposite.op D.t.out) ↦ f.1.unop) (eq_of_heq he)
    exact this

/-- `ρ³` is killed by every non-invertible morphism after it. -/
lemma τ_right_gen (hM : MildHyp k P) {w : P} (v : x.out ⟶ w) (hv : ¬IsIso v) :
    D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ v = 0 := by
  obtain ⟨r1, r2, r3⟩ := D.rho_four hq a₁ w₁ hw hM
  by_cases hv0 : v = 0
  · rw [hv0]; simp
  obtain ⟨c', e, r, he, rfl⟩ := exists_first_arrow' v hv0 hv
  let e' : x ⟶ (RayVert.mk c') := ⟨e, he⟩
  rcases arrows_eq_or_apart_out e' D.α with ⟨h, hh⟩ | hap1
  · obtain rfl : c' = x.out := h
    have : e = D.α.1 := congrArg Subtype.val (eq_of_heq hh)
    subst this
    rw [show D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ r = rpow D.α.1 4 ≫ r by simp [rpow_succ], r1,
      zero_comp]
  by_cases h2 : ∃ h : (RayVert.mk c' : RayVert P) = c, HEq e' a₁
  · obtain ⟨h, hh⟩ := h2
    obtain rfl : c' = c.out := h
    have : e = a₁.1 := congrArg Subtype.val (eq_of_heq hh)
    subst this
    rw [show D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ a₁.1 ≫ r = D.α.1 ≫ ((D.α.1 ≫ D.α.1) ≫ a₁.1) ≫ r by simp,
      r2, zero_comp, comp_zero]
  have h1 : ¬∃ h : (RayVert.mk c' : RayVert P) = x, HEq e' D.α := by
    rintro ⟨h, hh⟩
    exact hap1.1 (by obtain rfl : c' = x.out := h; exact ⟨𝟙 _, by
      rw [show e' = D.α from eq_of_heq hh]; simp⟩)
  rw [show D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ e ≫ r = D.α.1 ≫ D.α.1 ≫ (D.α.1 ≫ e) ≫ r by simp,
    D.rho_eps hq a₁ w₁ hw hM e' h1 h2]
  simp

/-- `ρ³` is killed by every non-invertible morphism before it. -/
lemma τ_left_gen (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {w : P} (u : w ⟶ x.out)
    (hu : ¬IsIso u) : u ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = 0 := by
  obtain ⟨r1, r2, r3⟩ := D.rho_four hq a₁ w₁ hw hM
  by_cases hu0 : u = 0
  · rw [hu0]; simp
  obtain ⟨c', p, e, rfl⟩ := MildContour.exists_last_arrow u hu0 hu
  rcases arrows_eq_or_apart e D.α with ⟨h, hh⟩ | hap1
  · subst h
    rw [show e = D.α from eq_of_heq hh]
    rw [show (pathVal p ≫ D.α.1) ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = pathVal p ≫ rpow D.α.1 4 by
      simp [rpow_succ], r1, comp_zero]
  rcases arrows_eq_or_apart e D.β with ⟨h, hh⟩ | hap2
  · subst h
    rw [show e = D.β from eq_of_heq hh]
    rw [show (pathVal p ≫ D.β.1) ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 =
      pathVal p ≫ (D.β.1 ≫ D.α.1 ≫ D.α.1) ≫ D.α.1 by simp, r3]; simp
  have h1 : ¬∃ h : c' = x, HEq e D.α := fun ⟨h, hh⟩ ↦ by
    subst h; exact hap1.1 ⟨𝟙 _, by rw [show e = D.α from eq_of_heq hh]; simp⟩
  have h2 : ¬∃ h : c' = D.t, HEq e D.β := fun ⟨h, hh⟩ ↦ by
    subst h; exact hap2.1 ⟨𝟙 _, by rw [show e = D.β from eq_of_heq hh]; simp⟩
  rw [show (pathVal p ≫ e.1) ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = pathVal p ≫ (e.1 ≫ D.α.1) ≫ D.α.1 ≫ D.α.1
    by simp, D.eps_rho hq a₁ w₁ hw hMo e h1 h2]
  simp

/-- A nonzero morphism factoring through `ρ³` is `ρ³`. -/
lemma ftm_τ_gen (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {s w : P} (f : s ⟶ w) (hf : f ≠ 0)
    (h : FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) f) :
    ∃ (h1 : s = x.out) (h2 : w = x.out), f = eqToHom h1 ≫ (D.α.1 ≫ D.α.1 ≫ D.α.1) ≫
      eqToHom h2.symm := by
  obtain ⟨u, v, rfl⟩ := h
  by_cases hu : IsIso u
  · by_cases hv : IsIso v
    · obtain ⟨h1, rfl⟩ := RayQuiver.eq_id_of_isIso u
      obtain ⟨h2, rfl⟩ := RayQuiver.eq_id_of_isIso v
      exact ⟨h1, h2.symm, rfl⟩
    · exact absurd (by simp only [Category.assoc]
                       rw [D.τ_right_gen hq a₁ w₁ hw hM v hv, comp_zero]) hf
  · exact absurd (by
      rw [show u ≫ (D.α.1 ≫ D.α.1 ≫ D.α.1) ≫ v = (u ≫ D.α.1 ≫ D.α.1 ≫ D.α.1) ≫ v by simp,
        D.τ_left_gen hq a₁ w₁ hw hM hMo u hu, zero_comp]) hf

lemma nftm_src_gen (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {s w : P} (f : s ⟶ w) (hf : f ≠ 0)
    (hs : s ≠ x.out) : ¬FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) f := fun h ↦ by
  obtain ⟨h1, -, -⟩ := D.ftm_τ_gen hq a₁ w₁ hw hM hMo f hf h; exact hs h1

lemma nftm_tgt_gen (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {s w : P} (f : s ⟶ w) (hf : f ≠ 0)
    (hw' : w ≠ x.out) : ¬FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) f := fun h ↦ by
  obtain ⟨-, h2, -⟩ := D.ftm_τ_gen hq a₁ w₁ hw hM hMo f hf h; exact hw' h2

lemma nftm_endo_gen (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (f : x.out ⟶ x.out) (hf : f ≠ 0)
    (hne : f ≠ D.α.1 ≫ D.α.1 ≫ D.α.1) :
    ¬FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) f := fun h ↦ by
  obtain ⟨h1, h2, e⟩ := D.ftm_τ_gen hq a₁ w₁ hw hM hMo f hf h
  exact hne (by simpa using e)

/-- **LPF, exit at `x₁`** (`n ≥ 3`): an arrow `ε` from `x₁` to a point off `w` with
`a₁ ≫ ε ≠ 0` gives an `Ẽ₇` (the analogue of [mild] figure 3.2, second diagram). -/
theorem exit_x1 (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hn : 0 < w₁.length) {y : P} (ε : c.out ⟶ y) (hε : IsIrreducible ε)
    (hy : ¬D.OnW (RayVert.mk y)) (haε : a₁.1 ≫ ε ≠ 0) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hα := D.α.2
  have ha := a₁.2
  have hb := D.β.2
  have hτ0 := D.rho3_ne hq a₁ w₁ hw
  have hω : a₁.1 ≫ pathVal w₁ ≫ D.β.1 = D.α.1 ≫ D.α.1 := by
    rw [← D.ω_pf_w hq a₁ w₁ hw, D.ω_pf hq a₁ w₁ hw]
  set d := pathVal w₁ with hd
  set σ := d ≫ D.β.1 with hσ
  have hσw : pathVal (w₁.cons D.β) = σ := rfl
  have hdn : ¬IsIso d := not_isIso_pathVal _ hn
  have hσn : ¬IsIso σ := not_isIso_comp_left' _ hdn
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have hαa : D.α.1 ≫ a₁.1 ≠ 0 := fun h ↦ hτ0 (by
    rw [← hω, ← Category.assoc, h, zero_comp])
  have hαad : D.α.1 ≫ a₁.1 ≫ d ≠ 0 := fun h ↦ hτ0 (by
    rw [← hω, show D.α.1 ≫ a₁.1 ≫ d ≫ D.β.1 = (D.α.1 ≫ a₁.1 ≫ d) ≫ D.β.1 by simp, h,
      zero_comp])
  have hσα : σ ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by
    rw [show D.α.1 ≫ D.α.1 ≫ D.α.1 = (a₁.1 ≫ σ) ≫ D.α.1 by rw [hσ, hω]; simp,
      Category.assoc, h, comp_zero])
  have hbα : D.β.1 ≫ D.α.1 ≠ 0 := fun h ↦ hσα (by rw [hσ, Category.assoc, h, comp_zero])
  have hd0 : d ≠ 0 := fun h ↦ hσα (by rw [hσ, h]; simp)
  have hσ0 : σ ≠ 0 := fun h ↦ hσα (by rw [h, zero_comp])
  -- points
  have hcx : c ≠ x := by
    rintro rfl
    exact D.rho_a₁_apart hq a₁ w₁ hw hM ⟨rfl, heq_of_eq (D.loop_eq_rho hq a₁ w₁ hw a₁).symm⟩
  have htx : D.t ≠ x := by
    intro h
    have hap := D.C.apart hR
    let g : x.out ⟶ D.t.out := eqToHom (congrArg RayVert.out h).symm
    have hgi : IsIrreducible (g ≫ D.β.1) := isIrreducible_iso_comp g D.β.2
    obtain ⟨n, hn, hn'⟩ := D.hρ (g ≫ D.β.1) hgi.2.1
    rcases n with _ | _ | m
    · omega
    · exact hap.1 ⟨g, by change g ≫ D.β.1 = D.α.1; rw [hn']; simp [rpow_succ]⟩
    · rcases hgi.2.2 _ (rpow D.α.1 (m + 1)) D.α.1 (by rw [hn', rpow_succ]) with h' | h'
      · exact MildContour.rpow_not_isIso D.α.1 hα.2.1 (m + 1) (by omega) h'
      · exact hα.2.1 h'
  have hyx : y ≠ x.out := by rintro rfl; exact hy D.onW_x
  have hyc : y ≠ c.out := by
    rintro rfl
    exact hy ⟨Quiver.Path.nil.cons a₁, w₁.cons D.β, D.split1 hq a₁ w₁ hw⟩
  have hw0 : D.w' = (Quiver.Path.nil.cons a₁).comp w₁ := hw
  have hw'v : pathVal D.w' = a₁.1 ≫ d := by
    rw [hw0, pathVal_comp]; change (𝟙 _ ≫ a₁.1) ≫ _ = _; rw [Category.id_comp]
  have hw'pos : 0 < D.w'.length := by rw [hw0]; simp
  have Zc : ∀ g : c.out ⟶ c.out, ¬IsIso g → a₁.1 ≫ g = 0 := fun g hg ↦ by
    have := D.Z hq a₁ w₁ hw hM hE (Quiver.Path.nil.cons a₁) (w₁.cons D.β) (by simp) (by simp)
      (D.split1 hq a₁ w₁ hw) g hg
    simpa [pathVal] using this
  have Zt : ∀ g : D.t.out ⟶ D.t.out, ¬IsIso g → (a₁.1 ≫ d) ≫ g = 0 := fun g hg ↦ by
    have := D.Z hq a₁ w₁ hw hM hE D.w' (Quiver.Path.nil.cons D.β) hw'pos (by simp) rfl g hg
    rwa [hw'v] at this
  have Zdc : ∀ g : c.out ⟶ c.out, ¬IsIso g → g ≫ σ = 0 := fun g hg ↦ by
    have := D.Z_dual hq a₁ w₁ hw hMo hE (Quiver.Path.nil.cons a₁) (w₁.cons D.β) (by simp)
      (by simp) (D.split1 hq a₁ w₁ hw) g hg
    exact this
  have Zdt : ∀ g : D.t.out ⟶ D.t.out, ¬IsIso g → g ≫ D.β.1 = 0 := fun g hg ↦ by
    have := D.Z_dual hq a₁ w₁ hw hMo hE D.w' (Quiver.Path.nil.cons D.β) hw'pos (by simp) rfl g hg
    simpa [pathVal] using this
  have mfc : ∀ f : c.out ⟶ x.out, f ≠ 0 → ∃ m, f = σ ≫ rpow D.α.1 m := fun f hf ↦
    D.mor_from_interior hq a₁ w₁ hw hMo hE (Quiver.Path.nil.cons a₁) (w₁.cons D.β) (by simp)
      (by simp) (D.split1 hq a₁ w₁ hw) f hf
  have mtt : ∀ f : x.out ⟶ D.t.out, f ≠ 0 → ∃ m, f = rpow D.α.1 m ≫ (a₁.1 ≫ d) := fun f hf ↦ by
    obtain ⟨m, hm⟩ := D.mor_to_interior hq a₁ w₁ hw hM hE D.w' (Quiver.Path.nil.cons D.β) hw'pos
      (by simp) rfl f hf
    exact ⟨m, by rw [hm, hw'v]⟩
  have hαα1 : D.α.1 ≫ D.α.1 ≠ D.α.1 ≫ D.α.1 ≫ D.α.1 := fun h ↦
    sandwich_r hαα0 (𝟙 _) D.α.1 hα.2.1 (by
      conv_lhs => rw [h]
      simp)
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src_gen hq a₁ w₁ hw hM hMo f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt_gen hq a₁ w₁ hw hM hMo f hf hs
  have hcx' : c.out ≠ x.out := hcx
  have htx' : D.t.out ≠ x.out := htx
  have hωσ : a₁.1 ≫ σ = D.α.1 ≫ D.α.1 := by rw [hσ]; exact hω
  refine hM.not_lpf3 (D.α.1 ≫ D.α.1 ≫ D.α.1) (not_isIso_comp_left' _ hα.2.1) hτ0 a₁.1
    (D.α.1 ≫ a₁.1) d σ ε d (D.β.1 ≫ D.α.1)
    (nft _ ha.1 hcx') (by rw [hωσ]; exact D.nftm_endo_gen hq a₁ w₁ hw hM hMo _ hαα0 hαα1)
    (nft _ haε hyx) (nft _ hαa hcx') (nft _ (by simpa using hαad) htx') (nfs _ hd0 hcx')
    (nfs _ (by simpa [hσ] using hσα) hcx') (nfs _ hσ0 hcx') (nfs _ hε.1 hcx') (nfs _ hd0 hcx')
    (nfs _ hbα htx')
    ha.2.1 (not_isIso_comp_left' _ hα.2.1) hdn hσn hε.2.1 hdn (not_isIso_comp_left' _ hb.2.1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `a ≫ g = α ≫ a`
    rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_l ha.1 D.α.1 (𝟙 _) hα.2.1 (by simpa using hg)
    · exact hαa (by rw [← hg, Zc g hgi])
  · -- `a ≫ g = (α ≫ a) ≫ d`
    rintro ⟨g, hg⟩
    rcases IsFiniteRayCategory.factorization_comparable d g with ⟨u, v, huv⟩ | ⟨u, v, huv⟩
    · -- `g = u d v`
      subst huv
      by_cases hu : IsIso u
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
        by_cases hv : IsIso v
        · obtain ⟨hh', rfl⟩ := RayQuiver.eq_id_of_isIso v
          exact sandwich_l (show a₁.1 ≫ d ≠ 0 from fun h ↦ hαad (by rw [h, comp_zero])) D.α.1
            (𝟙 _) hα.2.1 (by simpa using hg)
        · exact hαad (by
            rw [show D.α.1 ≫ a₁.1 ≫ d = (D.α.1 ≫ a₁.1) ≫ d by simp, ← hg]
            simp only [eqToHom_refl, Category.id_comp]
            rw [← Category.assoc, Zt v hv])
      · exact hαad (by
          rw [show D.α.1 ≫ a₁.1 ≫ d = (D.α.1 ≫ a₁.1) ≫ d by simp, ← hg,
            show a₁.1 ≫ (u ≫ d) ≫ v = (a₁.1 ≫ u) ≫ d ≫ v by simp, Zc u hu, zero_comp])
    · -- `d = u g v`
      by_cases hu : IsIso u
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
        simp only [eqToHom_refl, Category.id_comp] at huv
        refine sandwich_l (show a₁.1 ≫ d ≠ 0 from fun h ↦ hαad (by rw [h, comp_zero]))
          D.α.1 v hα.2.1 ?_
        conv_lhs => rw [huv, ← Category.assoc, hg]
        simp
      · exact hαad (by rw [huv, show a₁.1 ≫ (u ≫ g) ≫ v = (a₁.1 ≫ u) ≫ g ≫ v by simp, Zc u hu,
          zero_comp, comp_zero])
  · rintro ⟨g, hg⟩
    exact sandwich_l ha.1 D.α.1 g hα.2.1 (by simp only [Category.assoc] at hg; exact hg.symm)
  · -- `(α ≫ a) ≫ g = a ≫ σ`
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hαα0 (by rw [← hωσ, ← hg, h, comp_zero])
    obtain ⟨m, rfl⟩ := mfc g hg0
    refine sandwich_r hαα0 (𝟙 _) (D.α.1 ≫ rpow D.α.1 m) (not_isIso_comp_left' _ hα.2.1) ?_
    calc D.α.1 ≫ D.α.1 = (D.α.1 ≫ a₁.1) ≫ σ ≫ rpow D.α.1 m := by rw [hg, hωσ]
      _ = D.α.1 ≫ (a₁.1 ≫ σ) ≫ rpow D.α.1 m := by simp
      _ = _ := by rw [hωσ]; simp
  · -- `(α ≫ a) ≫ g = a ≫ ε`
    rintro ⟨g, hg⟩
    rcases IsFiniteRayCategory.factorization_comparable ε g with ⟨u, v, huv⟩ | ⟨u, v, huv⟩
    · subst huv
      by_cases hu : IsIso u
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
        refine sandwich_l haε D.α.1 v hα.2.1 ?_
        simp only [eqToHom_refl, Category.id_comp, Category.assoc] at hg ⊢; exact hg.symm
      · exact haε (by rw [← hg, show (D.α.1 ≫ a₁.1) ≫ (u ≫ ε) ≫ v =
          D.α.1 ≫ (a₁.1 ≫ u) ≫ ε ≫ v by simp, Zc u hu]; simp)
    · by_cases hu : IsIso u
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
        simp only [eqToHom_refl, Category.id_comp] at huv
        rcases hε.2.2 _ g v huv with h' | h'
        · exact hyc (eq_of_isIso h').symm
        · refine sandwich_l haε D.α.1 (inv v) hα.2.1 ?_
          rw [show g = ε ≫ inv v by rw [huv]; simp] at hg
          simp only [Category.assoc] at hg ⊢; exact hg.symm
      · exact haε (by rw [huv, show a₁.1 ≫ (u ≫ g) ≫ v = (a₁.1 ≫ u) ≫ g ≫ v by simp, Zc u hu,
          zero_comp])
  · -- `σ ≫ g = ε`
    rintro ⟨g, hg⟩
    rcases hε.2.2 _ σ g hg.symm with h' | h'
    · exact hσn h'
    · exact hyx (eq_of_isIso h').symm
  · -- `ε ≫ g = σ`
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hσ0 (by rw [← hg, h, comp_zero])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    let ε' : c ⟶ (RayVert.mk y) := ⟨ε, hε⟩
    let u : Quiver.Path x x := (Quiver.Path.nil.cons a₁).comp ((Quiver.Path.nil.cons ε').comp pg)
    have hu : pathVal u = pathVal D.v := by
      change pathVal ((Quiver.Path.nil.cons a₁).comp ((Quiver.Path.nil.cons ε').comp pg)) = _
      rw [pathVal_comp, pathVal_comp, hpg, D.ω_pf hq a₁ w₁ hw, ← hω]
      change (𝟙 _ ≫ a₁.1) ≫ (𝟙 _ ≫ ε) ≫ g = _
      rw [Category.id_comp, Category.id_comp, hg]
    rcases hM.path_unique D.hval D.h0 D.hni hα.2.1 D.hωρ u hu with h' | h'
    · have h'' : u = (Quiver.Path.nil.cons D.α).comp (Quiver.Path.nil.cons D.α) := by
        rw [h']; show (D.q.cons D.α).cons D.α = _; rw [hq]; rfl
      obtain ⟨hcx2, hh⟩ := first_arrow_eq h''
      exact D.rho_a₁_apart hq a₁ w₁ hw hM ⟨hcx2.symm, hh.symm⟩
    · apply hy
      refine ⟨(Quiver.Path.nil.cons a₁).cons ε', pg, ?_⟩
      rw [← h']
      show (Quiver.Path.nil.cons a₁).comp ((Quiver.Path.nil.cons ε').comp pg) = _
      rw [← Quiver.Path.comp_assoc]; rfl
  · -- `g ≫ σ = d ≫ β α`
    rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_r hσ0 (𝟙 _) D.α.1 hα.2.1 (by simpa [hσ] using hg)
    · exact hσα (by rw [show σ ≫ D.α.1 = d ≫ D.β.1 ≫ D.α.1 by simp [hσ], ← hg, Zdc g hgi])
  · -- `g ≫ σ = β α`
    rintro ⟨g, hg⟩
    by_cases hgi : IsIso (g ≫ d)
    · obtain ⟨hh, hgd⟩ := RayQuiver.eq_id_of_isIso (g ≫ d)
      refine sandwich_r hb.1 (𝟙 _) D.α.1 hα.2.1 ?_
      rw [show g ≫ σ = (g ≫ d) ≫ D.β.1 by simp [hσ], hgd] at hg
      simpa using hg
    · exact hbα (by rw [← hg, show g ≫ σ = (g ≫ d) ≫ D.β.1 by simp [hσ], Zdt _ hgi])
  · -- `g ≫ β α = a ≫ σ`
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hαα0 (by rw [← hωσ, ← hg, h, zero_comp])
    obtain ⟨m, rfl⟩ := mtt g hg0
    refine sandwich_r hαα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 ≫ D.α.1 = (rpow D.α.1 m ≫ a₁.1 ≫ d) ≫ D.β.1 ≫ D.α.1 := by rw [hg, hωσ]
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ d ≫ D.β.1) ≫ D.α.1 := by simp
      _ = _ := by rw [hω]
  · -- `g ≫ β α = σ`
    rintro ⟨g, hg⟩
    have hag : a₁.1 ≫ g ≠ 0 := fun h ↦ hαα0 (by
      rw [← hωσ, ← hg, ← Category.assoc, h, zero_comp])
    obtain ⟨m, hm⟩ := mtt (a₁.1 ≫ g) hag
    refine sandwich_r hαα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 ≫ D.α.1 = (a₁.1 ≫ g) ≫ D.β.1 ≫ D.α.1 := by rw [← hωσ, ← hg]; simp
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ d ≫ D.β.1) ≫ D.α.1 := by rw [hm]; simp
      _ = _ := by rw [hω]


/-- A point strictly inside `w` is not `x₀`. -/
lemma interior_ne_x (hM : MildHyp k P) (hE : EndCyclic P) {q : RayVert P}
    (p : Quiver.Path x q) (s : Quiver.Path q x) (hp : 0 < p.length) (hs : 0 < s.length)
    (hps : D.w'.cons D.β = p.comp s) : q ≠ x := by
  intro h
  have hv : pathVal p ≫ pathVal s = D.α.1 ≫ D.α.1 := by
    rw [← pathVal_comp, ← hps, ← D.hval, D.ω_pf hq a₁ w₁ hw]
  have h3 := D.rho3_ne hq a₁ w₁ hw
  subst h
  have := D.Z hq a₁ w₁ hw hM hE p s hp hs hps (pathVal s) (not_isIso_pathVal _ hs)
  exact h3 (by rw [← Category.assoc, ← hv, this, zero_comp])

/-- A proper suffix of `w` ends with `β`, so it kills `a₁`. -/
lemma suffix_a₁ (hM : MildHyp k P) (hE : EndCyclic P) {q : RayVert P}
    (p : Quiver.Path x q) (s : Quiver.Path q x) (hs : 0 < s.length)
    (hps : D.w'.cons D.β = p.comp s) : pathVal s ≫ a₁.1 = 0 := by
  cases s with
  | nil => simp at hs
  | cons s₀ e =>
    simp only [Quiver.Path.comp_cons, Quiver.Path.cons.injEq] at hps
    obtain ⟨rfl, -, h3⟩ := hps
    obtain rfl := eq_of_heq h3
    change (pathVal s₀ ≫ D.β.1) ≫ a₁.1 = 0
    rw [Category.assoc, D.ba_zero_gen hq a₁ w₁ hw hM hE, comp_zero]

/-- **LPF, exit at `x_i`, `i ≥ 2`** ([mild] figure 3.2, second diagram): for an exit
`ε` at `x_i` with `λ ≫ ε ≠ 0` (`λ` the prefix of `w` to `x_i`) and `λ` of minimal
length among such exits, the shape `LPF2` is cleaving. -/
theorem exit_mid (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    {q : RayVert P} (p : Quiver.Path x q) (s : Quiver.Path q x) (hp : 2 ≤ p.length)
    (hs : 0 < s.length) (hps : D.w'.cons D.β = p.comp s) {y : RayVert P} (ε : q ⟶ y)
    (hy : ¬D.OnW y) (hpε : pathVal p ≫ ε.1 ≠ 0)
    (hmin : ∀ {q' : RayVert P} (p' : Quiver.Path x q') (s' : Quiver.Path q' x),
      D.w'.cons D.β = p'.comp s' → ∀ {y' : RayVert P} (ε' : q' ⟶ y'), ¬D.OnW y' →
      pathVal p' ≫ ε'.1 ≠ 0 → p.length ≤ p'.length) : False := by
  have hα := D.α.2
  have ha := a₁.2
  have hτ0 := D.rho3_ne hq a₁ w₁ hw
  obtain ⟨r1, r2, r3⟩ := D.rho_four hq a₁ w₁ hw hM
  -- `p = a₁ ≫ p₁`
  obtain ⟨p₁, hpe, hs₁⟩ : ∃ p₁ : Quiver.Path c q, p = (Quiver.Path.nil.cons a₁).comp p₁ ∧
      w₁.cons D.β = p₁.comp s := by
    rcases Quiver.Path.comp_eq_comp s (Quiver.Path.nil.cons a₁) (w₁.cons D.β) p
        ((D.split1 hq a₁ w₁ hw).symm.trans hps) with ⟨m, h1, h2⟩ | ⟨m, h1, h2⟩
    · exact ⟨m, h1, h2⟩
    · have := congrArg Quiver.Path.length h1
      simp at this; omega
  have hp₁ : 0 < p₁.length := by
    have := congrArg Quiver.Path.length hpe; simp at this; omega
  set cc := pathVal p₁ with hcc
  set σ := pathVal s with hσ
  have ha1v : pathVal (Quiver.Path.nil.cons a₁) = a₁.1 := by
    change 𝟙 _ ≫ a₁.1 = _; rw [Category.id_comp]
  have hlam : pathVal p = a₁.1 ≫ cc := by rw [hpe, pathVal_comp, ha1v]
  have hlσ' : a₁.1 ≫ cc ≫ σ = D.α.1 ≫ D.α.1 := by
    rw [← Category.assoc, ← hlam, ← pathVal_comp, ← hps, ← D.hval, D.ω_pf hq a₁ w₁ hw]
  have hσ1 : pathVal (w₁.cons D.β) = cc ≫ σ := by rw [hs₁, pathVal_comp]
  have hσa : σ ≫ a₁.1 = 0 := D.suffix_a₁ hq a₁ w₁ hw hM hE p s hs hps
  have hpε' : (a₁.1 ≫ cc) ≫ ε.1 ≠ 0 := by rwa [← hlam]
  -- nonzero composites
  have h3l : D.α.1 ≫ a₁.1 ≫ cc ≫ σ = D.α.1 ≫ D.α.1 ≫ D.α.1 := by rw [hlσ']
  have h3r : a₁.1 ≫ cc ≫ σ ≫ D.α.1 = D.α.1 ≫ D.α.1 ≫ D.α.1 := by
    rw [← Category.assoc cc, ← Category.assoc a₁.1, hlσ']; simp
  have hρa : D.α.1 ≫ a₁.1 ≠ 0 := fun h ↦ hτ0 (by rw [← h3l, ← Category.assoc, h, zero_comp])
  have hρac : D.α.1 ≫ a₁.1 ≫ cc ≠ 0 := fun h ↦ hτ0 (by
    rw [← h3l, show D.α.1 ≫ a₁.1 ≫ cc ≫ σ = (D.α.1 ≫ a₁.1 ≫ cc) ≫ σ by simp, h, zero_comp])
  have hac : a₁.1 ≫ cc ≠ 0 := fun h ↦ hρac (by rw [h, comp_zero])
  have hcσ : cc ≫ σ ≠ 0 := fun h ↦ hτ0 (by rw [← h3l, h, comp_zero, comp_zero])
  have hcσρ : cc ≫ σ ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [← h3r, h, comp_zero])
  have hσρ : σ ≫ D.α.1 ≠ 0 := fun h ↦ hcσρ (by rw [h, comp_zero])
  have hσ0 : σ ≠ 0 := fun h ↦ hσρ (by rw [h, zero_comp])
  have hc0 : cc ≠ 0 := fun h ↦ hcσ (by rw [h, zero_comp])
  have hα0 : D.α.1 ≠ 0 := hα.1
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have hρn : ∀ m, ¬IsIso (D.α.1 ≫ rpow D.α.1 m) := fun m ↦ not_isIso_comp_left' _ hα.2.1
  have hαα1 : D.α.1 ≫ D.α.1 ≠ D.α.1 ≫ D.α.1 ≫ D.α.1 := fun h ↦
    sandwich_r hαα0 (𝟙 _) D.α.1 hα.2.1 (by
      conv_lhs => rw [h]
      simp)
  have hα1 : D.α.1 ≠ D.α.1 ≫ D.α.1 ≫ D.α.1 := fun h ↦
    sandwich_r hα0 (𝟙 _) (D.α.1 ≫ D.α.1) (not_isIso_comp_left' _ hα.2.1) (by
      conv_lhs => rw [h]
      simp)
  -- points
  have hsplit := D.split1 hq a₁ w₁ hw
  have hqx : q ≠ x := D.interior_ne_x hq a₁ w₁ hw hM hE p s (by omega) hs hps
  have hcx : c ≠ x := D.interior_ne_x hq a₁ w₁ hw hM hE _ _ (by simp) (by simp) hsplit
  have hyx : y ≠ x := by rintro rfl; exact hy D.onW_x
  have hyq : y ≠ q := by rintro rfl; exact hy ⟨p, s, hps⟩
  have hqx' : q.out ≠ x.out := hqx
  have hcx' : c.out ≠ x.out := hcx
  have hyx' : y.out ≠ x.out := hyx
  have hyq' : q.out ≠ y.out := fun h ↦ hyq h.symm
  -- morphisms between points of `w`
  have mfq : ∀ f : q.out ⟶ x.out, f ≠ 0 → ∃ m, f = σ ≫ rpow D.α.1 m :=
    D.mor_from_interior hq a₁ w₁ hw hMo hE p s (by omega) hs hps
  have mtq : ∀ f : x.out ⟶ q.out, f ≠ 0 → ∃ m, f = rpow D.α.1 m ≫ a₁.1 ≫ cc := fun f hf ↦ by
    obtain ⟨m, hm⟩ := D.mor_to_interior hq a₁ w₁ hw hM hE p s (by omega) hs hps f hf
    exact ⟨m, by rw [hm, hlam]⟩
  have mfc : ∀ f : c.out ⟶ x.out, f ≠ 0 → ∃ m, f = (cc ≫ σ) ≫ rpow D.α.1 m := fun f hf ↦ by
    obtain ⟨m, hm⟩ := D.mor_from_interior hq a₁ w₁ hw hMo hE _ _ (by simp) (by simp) hsplit f hf
    exact ⟨m, by rw [hm, hσ1]⟩
  have mtc : ∀ f : x.out ⟶ c.out, f ≠ 0 → ∃ m, f = rpow D.α.1 m ≫ a₁.1 := fun f hf ↦ by
    obtain ⟨m, hm⟩ := D.mor_to_interior hq a₁ w₁ hw hM hE _ _ (by simp) (by simp) hsplit f hf
    exact ⟨m, by rw [hm, ha1v]⟩
  have Zq : ∀ e : q.out ⟶ q.out, ¬IsIso e → (a₁.1 ≫ cc) ≫ e = 0 := fun e he ↦ by
    rw [← hlam]; exact D.Z hq a₁ w₁ hw hM hE p s (by omega) hs hps e he
  have Zdq : ∀ e : q.out ⟶ q.out, ¬IsIso e → e ≫ σ = 0 := fun e he ↦
    D.Z_dual hq a₁ w₁ hw hMo hE p s (by omega) hs hps e he
  have Zc : ∀ e : c.out ⟶ c.out, ¬IsIso e → a₁.1 ≫ e = 0 := fun e he ↦ by
    have := D.Z hq a₁ w₁ hw hM hE _ _ (by simp) (by simp) hsplit e he
    rwa [ha1v] at this
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src_gen hq a₁ w₁ hw hM hMo f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt_gen hq a₁ w₁ hw hM hMo f hf hs
  have hlσ : (a₁.1 ≫ cc) ≫ σ = D.α.1 ≫ D.α.1 := by rw [Category.assoc, hlσ']
  refine hM.not_lpf2 (D.α.1 ≫ D.α.1 ≫ D.α.1) (not_isIso_comp_left' _ hα.2.1) hτ0
    (a₁.1 ≫ cc) σ D.α.1 D.α.1 ε.1 a₁.1 cc σ cc LPF2.not_isRepresentationFinite hlσ.symm
    (by rw [hσa, comp_zero]) (by rw [← Category.assoc σ, hσa]; simp) hσa
    (by rw [← Category.assoc, hσa, zero_comp])
    (nft _ hρa hcx') (by rw [hlσ]; exact D.nftm_endo_gen hq a₁ w₁ hw hM hMo _ hαα0 hαα1)
    (nft _ hac hqx') (nft _ (by simpa using hρac) hqx')
    (D.nftm_endo_gen hq a₁ w₁ hw hM hMo _ hα0 hα1) (nft _ hpε' hyx') (nfs _ hc0 hcx')
    (nfs _ (by simpa using hcσρ) hcx') (nfs _ hc0 hcx') (nfs _ hcσ hcx') (nfs _ hσ0 hqx')
    (nfs _ ε.2.1 hqx') (nfs _ hσρ hqx') (nfs _ hσ0 hqx') (nft _ ha.1 hcx')
    (D.nftm_endo_gen hq a₁ w₁ hw hM hMo _ hα0 hα1) (nft _ hac hqx')
    (not_isIso_comp_left' _ ha.2.1) (not_isIso_pathVal _ hs) hα.2.1 hα.2.1 ε.2.2.1 ha.2.1
    (not_isIso_pathVal _ hp₁) (not_isIso_pathVal _ hs) (not_isIso_pathVal _ hp₁)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `λ ≫ g = ρ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mfq g (fun h ↦ hα0 (by rw [← hg, h, comp_zero]))
    refine sandwich_r hα0 (𝟙 _) (D.α.1 ≫ rpow D.α.1 m) (hρn m) ?_
    calc D.α.1 = (a₁.1 ≫ cc) ≫ σ ≫ rpow D.α.1 m := hg.symm
      _ = ((a₁.1 ≫ cc) ≫ σ) ≫ rpow D.α.1 m := by simp
      _ = _ := by rw [hlσ]; simp
  · -- `λ ≫ g = ρ ≫ a₁`
    rintro ⟨g, hg⟩
    have h1 : (a₁.1 ≫ cc) ≫ (g ≫ cc) = D.α.1 ≫ a₁.1 ≫ cc := by
      rw [← Category.assoc, hg, Category.assoc]
    rw [Zq _ (not_isIso_comp_right' _ (not_isIso_pathVal _ hp₁))] at h1
    exact hρac h1.symm
  · -- `λ ≫ g = ρ ≫ a₁ ≫ cc`
    rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_l hac D.α.1 (𝟙 _) hα.2.1 (by simpa using hg)
    · exact hρac (by rw [← Category.assoc D.α.1, ← hg, Zq g hgi])
  · -- `ρ ≫ g = λ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtq g (fun h ↦ hac (by rw [← hg, h, comp_zero]))
    refine sandwich_l hac (D.α.1 ≫ rpow D.α.1 m) (𝟙 _) (hρn m) ?_
    conv_lhs => rw [← hg]
    simp
  · -- `ρ ≫ g = λ ≫ ε` (minimality of `p`)
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hpε' (by rw [← hg, h, comp_zero])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    obtain ⟨q', p', s', hps', y', ε', hy', m, g', he⟩ := D.first_exit hq a₁ w₁ hw hM hE _ pg rfl
      (by rw [hpg]; exact hg0) hy
    rw [hpg] at he
    have hne : pathVal p' ≫ ε'.1 ≠ 0 := fun h ↦ hg0 (by
      rw [he, show rpow D.α.1 m ≫ pathVal p' ≫ ε'.1 ≫ g' =
        rpow D.α.1 m ≫ (pathVal p' ≫ ε'.1) ≫ g' by simp, h]; simp)
    have hle := hmin p' s' hps' ε' hy' hne
    obtain ⟨t, ht⟩ : ∃ t : Quiver.Path q q', p' = p.comp t := by
      rcases Quiver.Path.comp_eq_comp s' p s p' (hps.symm.trans hps') with
        ⟨t, h1, -⟩ | ⟨t, h1, -⟩
      · exact ⟨t, h1⟩
      · have hl := congrArg Quiver.Path.length h1
        simp only [Quiver.Path.length_comp] at hl
        cases t with
        | nil => exact ⟨.nil, by simpa using h1.symm⟩
        | cons _ _ => simp at hl; omega
    rw [ht, pathVal_comp, hlam] at he
    rcases m with _ | m
    · set ξ := pathVal t ≫ ε'.1 ≫ g' with hξ
      have hg' : (a₁.1 ≫ cc) ≫ ε.1 = D.α.1 ≫ (a₁.1 ≫ cc) ≫ ξ := by
        rw [← hg, he]; simp [hξ, rpow]
      rcases IsFiniteRayCategory.factorization_comparable ε.1 ξ with ⟨u, v, huv⟩ | ⟨u, v, huv⟩
      · rw [huv] at hg'
        by_cases hu : IsIso u
        · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
          refine sandwich_l hpε' D.α.1 v hα.2.1 ?_
          conv_lhs => rw [hg']
          simp
        · apply hpε'
          rw [hg', show D.α.1 ≫ (a₁.1 ≫ cc) ≫ (u ≫ ε.1) ≫ v =
            D.α.1 ≫ ((a₁.1 ≫ cc) ≫ u) ≫ ε.1 ≫ v by simp, Zq u hu]; simp
      · by_cases hu : IsIso u
        · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
          simp only [eqToHom_refl, Category.id_comp] at huv
          rcases ε.2.2.2 _ ξ v huv with h' | h'
          · exact hyq' (eq_of_isIso h')
          · refine sandwich_l hpε' D.α.1 (inv v) hα.2.1 ?_
            rw [show ξ = ε.1 ≫ inv v by rw [huv]; simp] at hg'
            conv_lhs => rw [hg']
            simp
        · rcases ε.2.2.2 _ u (ξ ≫ v) (by rw [huv]; simp) with h' | h'
          · exact hu h'
          · exact hyq' (eq_of_isIso h')
    · apply hpε'
      have hz : ∀ {W : P} (k : c.out ⟶ W), D.α.1 ≫ D.α.1 ≫ a₁.1 ≫ k = 0 := fun k ↦ by
        rw [← Category.assoc, ← Category.assoc, r2, zero_comp]
      rw [← hg, he, ← Category.assoc D.α.1, ← rpow_succ', rpow_succ, rpow_succ]
      simp only [Category.assoc]
      rw [hz]; simp
  · -- `σ ≫ g = ε`
    rintro ⟨g, hg⟩
    rcases ε.2.2.2 _ σ g hg.symm with h' | h'
    · exact not_isIso_pathVal _ hs h'
    · exact hyx' (eq_of_isIso h').symm
  · -- `ε ≫ g = σ`
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hσ0 (by rw [← hg, h, comp_zero])
    obtain ⟨pg, hpg⟩ := exists_path g hg0
    let u : Quiver.Path x x :=
      (Quiver.Path.nil.cons a₁).comp (p₁.comp ((Quiver.Path.nil.cons ε).comp pg))
    have hu : pathVal u = pathVal D.v := by
      change pathVal ((Quiver.Path.nil.cons a₁).comp (p₁.comp ((Quiver.Path.nil.cons ε).comp pg)))
        = _
      rw [pathVal_comp, pathVal_comp, pathVal_comp, hpg, D.ω_pf hq a₁ w₁ hw, ← hlσ', ha1v]
      change a₁.1 ≫ cc ≫ (𝟙 _ ≫ ε.1) ≫ g = _
      rw [Category.id_comp, hg]
    rcases hM.path_unique D.hval D.h0 D.hni hα.2.1 D.hωρ u hu with h' | h'
    · have h'' : u = (Quiver.Path.nil.cons D.α).comp (Quiver.Path.nil.cons D.α) := by
        rw [h']; show (D.q.cons D.α).cons D.α = _; rw [hq]; rfl
      obtain ⟨hcx2, hh⟩ := first_arrow_eq h''
      exact D.rho_a₁_apart hq a₁ w₁ hw hM ⟨hcx2.symm, hh.symm⟩
    · apply hy
      refine ⟨p.cons ε, pg, ?_⟩
      rw [← h', hpe]
      show _ = (((Quiver.Path.nil.cons a₁).comp p₁).comp (Quiver.Path.nil.cons ε)).comp pg
      simp only [Quiver.Path.comp_assoc]
      rfl
  · -- `a₁ ≫ g = ρ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mfc g (fun h ↦ hα0 (by rw [← hg, h, comp_zero]))
    refine sandwich_r hα0 (𝟙 _) (D.α.1 ≫ rpow D.α.1 m) (hρn m) ?_
    calc D.α.1 = a₁.1 ≫ (cc ≫ σ) ≫ rpow D.α.1 m := hg.symm
      _ = (a₁.1 ≫ cc ≫ σ) ≫ rpow D.α.1 m := by simp
      _ = _ := by rw [hlσ']; simp
  · -- `ρ ≫ g = a₁`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtc g (fun h ↦ ha.1 (by rw [← hg, h, comp_zero]))
    refine sandwich_l ha.1 (D.α.1 ≫ rpow D.α.1 m) (𝟙 _) (hρn m) ?_
    conv_lhs => rw [← hg]
    simp
  · -- `ρ ≫ g = a₁ ≫ cc`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtq g (fun h ↦ hac (by rw [← hg, h, comp_zero]))
    refine sandwich_l hac (D.α.1 ≫ rpow D.α.1 m) (𝟙 _) (hρn m) ?_
    conv_lhs => rw [← hg]
    simp
  · -- `g ≫ ρ = σ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mfq g (fun h ↦ hσ0 (by rw [← hg, h, zero_comp]))
    refine sandwich_r hσ0 (𝟙 _) (rpow D.α.1 m ≫ D.α.1) (not_isIso_comp_right' _ hα.2.1) ?_
    conv_lhs => rw [← hg]
    simp
  · -- `g ≫ ρ = cc ≫ σ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mfc g (fun h ↦ hcσ (by rw [← hg, h, zero_comp]))
    refine sandwich_r hcσ (𝟙 _) (rpow D.α.1 m ≫ D.α.1) (not_isIso_comp_right' _ hα.2.1) ?_
    conv_lhs => rw [← hg]
    simp
  · -- `g ≫ σ = ρ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtq g (fun h ↦ hα0 (by rw [← hg, h, zero_comp]))
    refine sandwich_r hα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 = (rpow D.α.1 m ≫ a₁.1 ≫ cc) ≫ σ := hg.symm
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ cc ≫ σ) := by simp
      _ = _ := by rw [hlσ']
  · -- `g ≫ σ = σ ≫ ρ`
    rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_r hσ0 (𝟙 _) D.α.1 hα.2.1 (by simpa using hg)
    · exact hσρ (by rw [← hg, Zdq g hgi])
  · -- `g ≫ σ = (cc ≫ σ) ≫ ρ`
    rintro ⟨g, hg⟩
    rcases IsFiniteRayCategory.factorization_comparable cc g with ⟨u, v, huv⟩ | ⟨u, v, huv⟩
    · subst huv
      by_cases hu : IsIso u
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
        by_cases hv : IsIso v
        · obtain ⟨hh', rfl⟩ := RayQuiver.eq_id_of_isIso v
          exact sandwich_r hcσ (𝟙 _) D.α.1 hα.2.1 (by simpa using hg)
        · exact hcσρ (by
            rw [← Category.assoc, ← hg]; simp only [eqToHom_refl, Category.id_comp,
              Category.assoc]; rw [Zdq v hv, comp_zero])
      · apply hτ0
        rw [← h3r, ← Category.assoc cc, ← hg, show a₁.1 ≫ ((u ≫ cc) ≫ v) ≫ σ =
          (a₁.1 ≫ u) ≫ cc ≫ v ≫ σ by simp, Zc u hu, zero_comp]
    · by_cases hu : IsIso u
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
        simp only [eqToHom_refl, Category.id_comp] at huv
        by_cases hv : IsIso v
        · obtain ⟨hh', rfl⟩ := RayQuiver.eq_id_of_isIso v
          simp only [eqToHom_refl, Category.comp_id] at huv
          subst huv
          exact sandwich_r hcσ (𝟙 _) D.α.1 hα.2.1 (by simpa using hg)
        · exact hcσ (by rw [huv, Category.assoc, Zdq v hv, comp_zero])
      · exact hac (by rw [huv, show a₁.1 ≫ (u ≫ g) ≫ v = (a₁.1 ≫ u) ≫ g ≫ v by simp, Zc u hu,
          zero_comp])
  · -- `g ≫ σ = ρ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtq g (fun h ↦ hα0 (by rw [← hg, h, zero_comp]))
    refine sandwich_r hα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 = (rpow D.α.1 m ≫ a₁.1 ≫ cc) ≫ σ := hg.symm
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ cc ≫ σ) := by simp
      _ = _ := by rw [hlσ']
  · -- `g ≫ ρ = σ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mfq g (fun h ↦ hσ0 (by rw [← hg, h, zero_comp]))
    refine sandwich_r hσ0 (𝟙 _) (rpow D.α.1 m ≫ D.α.1) (not_isIso_comp_right' _ hα.2.1) ?_
    conv_lhs => rw [← hg]
    simp

omit hq hw in
/-- The first arrow of a path of positive length. -/
lemma path_first {V : Type*} [Quiver V] {a b : V} (p : Quiver.Path a b) (hp : 0 < p.length) :
    ∃ (c : V) (e : a ⟶ c) (r : Quiver.Path c b), p = (Quiver.Path.nil.cons e).comp r := by
  induction p with
  | nil => simp at hp
  | cons p' e' ih =>
    rcases Nat.eq_zero_or_pos p'.length with h0 | h0
    · cases p' with
      | nil => exact ⟨_, e', .nil, rfl⟩
      | cons _ _ => simp at h0
    · obtain ⟨c, e, r, rfl⟩ := ih h0
      exact ⟨c, e, r.cons e', rfl⟩

/-- `ρ²` does not factor through a point off `w` (uniqueness of `w`). -/
theorem no_detour (hM : MildHyp k P) {y : RayVert P} (hy : ¬D.OnW y) (f₁ : x.out ⟶ y.out)
    (f₂ : y.out ⟶ x.out) (h : f₁ ≫ f₂ = D.α.1 ≫ D.α.1) : False := by
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h' ↦
    D.rho3_ne hq a₁ w₁ hw (by rw [← Category.assoc, h', zero_comp])
  have h1 : f₁ ≠ 0 := fun h' ↦ hαα0 (by rw [← h, h', zero_comp])
  have h2 : f₂ ≠ 0 := fun h' ↦ hαα0 (by rw [← h, h', comp_zero])
  obtain ⟨p1, hp1⟩ := exists_path f₁ h1
  obtain ⟨p2, hp2⟩ := exists_path f₂ h2
  have hu : pathVal (p1.comp p2) = pathVal D.v := by
    rw [pathVal_comp, hp1, hp2, h, D.ω_pf hq a₁ w₁ hw]
  have hyx : y ≠ x := by rintro rfl; exact hy D.onW_x
  rcases hM.path_unique D.hval D.h0 D.hni D.α.2.2.1 D.hωρ (p1.comp p2) hu with h' | h'
  · have h'' : (Quiver.Path.nil.cons D.α).comp (Quiver.Path.nil.cons D.α) = p1.comp p2 := by
      rw [h']; show _ = (D.q.cons D.α).cons D.α; rw [hq]; rfl
    rcases Quiver.Path.comp_eq_comp p2 _ _ p1 h'' with ⟨m, -, h2'⟩ | ⟨m, h1', -⟩
    · have hl := congrArg Quiver.Path.length h2'
      simp only [Quiver.Path.length_comp, Quiver.Path.length_cons, Quiver.Path.length_nil] at hl
      rcases Nat.eq_zero_or_pos m.length with hm | hm
      · exact hyx (Quiver.Path.eq_of_length_zero m hm).symm
      · exact hyx (Quiver.Path.eq_of_length_zero p2 (by omega))
    · have hl := congrArg Quiver.Path.length h1'
      simp only [Quiver.Path.length_comp, Quiver.Path.length_cons, Quiver.Path.length_nil] at hl
      rcases Nat.eq_zero_or_pos p1.length with hm | hm
      · exact hyx (Quiver.Path.eq_of_length_zero p1 hm).symm
      · exact hyx (Quiver.Path.eq_of_length_zero m (by omega))
  · exact hy ⟨p1, p2, h'.symm⟩

/-- **LPF, exit at `x₀`** (`n ≥ 3`): an arrow `ε` out of `x₀` to a point off `w` is
impossible: [mild] figure 3.2, first diagram (`LPF1`), unless `ε ≫ ζ = ρ ≫ a₁` (`D̃₅`,
`LPF0D`) or `ε ≫ ζ = ρ ≫ a₁ ≫ a₂` (`D̃₅`, `LPF0E`). -/
theorem exit_x0 (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hn : 0 < w₁.length) {y : RayVert P} (ε : x ⟶ y) (hy : ¬D.OnW y) : False := by
  have hα := D.α.2
  have ha := a₁.2
  have hτ0 := D.rho3_ne hq a₁ w₁ hw
  obtain ⟨r1, r2, r3⟩ := D.rho_four hq a₁ w₁ hw hM
  obtain ⟨d, a₂, w₂, hw₁⟩ := path_first w₁ hn
  have ha₂ := a₂.2
  let p₂ : Quiver.Path x d := (Quiver.Path.nil.cons a₁).cons a₂
  let s₂ : Quiver.Path d x := w₂.cons D.β
  have hps₂ : D.w'.cons D.β = p₂.comp s₂ := by
    rw [hw, hw₁]
    show _ = (((Quiver.Path.nil.cons a₁).comp (Quiver.Path.nil.cons a₂)).comp w₂).cons D.β
    rw [Quiver.Path.comp_assoc]
  have hsplit := D.split1 hq a₁ w₁ hw
  set σ₂ := pathVal s₂ with hσ₂
  have hp₂v : pathVal p₂ = a₁.1 ≫ a₂.1 := by
    change (𝟙 _ ≫ a₁.1) ≫ a₂.1 = _; rw [Category.id_comp]
  have ha1v : pathVal (Quiver.Path.nil.cons a₁) = a₁.1 := by
    change 𝟙 _ ≫ a₁.1 = _; rw [Category.id_comp]
  have hσ₁ : pathVal (w₁.cons D.β) = a₂.1 ≫ σ₂ := by
    rw [hw₁]
    change pathVal ((Quiver.Path.nil.cons a₂).comp (w₂.cons D.β)) = _
    rw [pathVal_comp]; change (𝟙 _ ≫ a₂.1) ≫ _ = _; rw [Category.id_comp]
  have hω : a₁.1 ≫ a₂.1 ≫ σ₂ = D.α.1 ≫ D.α.1 := by
    rw [← hσ₁, ← ha1v, ← pathVal_comp, ← hsplit, ← D.hval, D.ω_pf hq a₁ w₁ hw]
  have hσa : σ₂ ≫ a₁.1 = 0 := D.suffix_a₁ hq a₁ w₁ hw hM hE p₂ s₂ (by simp [s₂]) hps₂
  -- nonzero composites
  have h3l : D.α.1 ≫ a₁.1 ≫ a₂.1 ≫ σ₂ = D.α.1 ≫ D.α.1 ≫ D.α.1 := by rw [hω]
  have h3r : a₁.1 ≫ a₂.1 ≫ σ₂ ≫ D.α.1 = D.α.1 ≫ D.α.1 ≫ D.α.1 := by
    rw [← Category.assoc a₂.1, ← Category.assoc a₁.1, hω]; simp
  have hρa : D.α.1 ≫ a₁.1 ≠ 0 := fun h ↦ hτ0 (by rw [← h3l, ← Category.assoc, h, zero_comp])
  have hρaa : D.α.1 ≫ a₁.1 ≫ a₂.1 ≠ 0 := fun h ↦ hτ0 (by
    rw [← h3l, show D.α.1 ≫ a₁.1 ≫ a₂.1 ≫ σ₂ = (D.α.1 ≫ a₁.1 ≫ a₂.1) ≫ σ₂ by simp, h,
      zero_comp])
  have haa : a₁.1 ≫ a₂.1 ≠ 0 := fun h ↦ hρaa (by rw [h, comp_zero])
  have haσ : a₂.1 ≫ σ₂ ≠ 0 := fun h ↦ hτ0 (by rw [← h3l, h, comp_zero, comp_zero])
  have haσρ : a₂.1 ≫ σ₂ ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [← h3r, h, comp_zero])
  have hσρ : σ₂ ≫ D.α.1 ≠ 0 := fun h ↦ haσρ (by rw [h, comp_zero])
  have hσ0 : σ₂ ≠ 0 := fun h ↦ hσρ (by rw [h, zero_comp])
  have hα0 : D.α.1 ≠ 0 := hα.1
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have hρn : ∀ m, ¬IsIso (D.α.1 ≫ rpow D.α.1 m) := fun m ↦ not_isIso_comp_left' _ hα.2.1
  have hαα1 : D.α.1 ≫ D.α.1 ≠ D.α.1 ≫ D.α.1 ≫ D.α.1 := fun h ↦
    sandwich_r hαα0 (𝟙 _) D.α.1 hα.2.1 (by
      conv_lhs => rw [h]
      simp)
  have hα1 : D.α.1 ≠ D.α.1 ≫ D.α.1 ≫ D.α.1 := fun h ↦
    sandwich_r hα0 (𝟙 _) (D.α.1 ≫ D.α.1) (not_isIso_comp_left' _ hα.2.1) (by
      conv_lhs => rw [h]
      simp)
  have hz : ∀ {W : P} (k : c.out ⟶ W), D.α.1 ≫ D.α.1 ≫ a₁.1 ≫ k = 0 := fun k ↦ by
    rw [← Category.assoc, ← Category.assoc, r2, zero_comp]
  -- points
  have hdx : d ≠ x := D.interior_ne_x hq a₁ w₁ hw hM hE p₂ s₂ (by simp [p₂]) (by simp [s₂]) hps₂
  have hcx : c ≠ x := D.interior_ne_x hq a₁ w₁ hw hM hE _ _ (by simp) (by simp) hsplit
  have hyx : y ≠ x := by rintro rfl; exact hy D.onW_x
  have hyc : y ≠ c := by rintro rfl; exact hy ⟨_, _, hsplit⟩
  have hyd : y ≠ d := by rintro rfl; exact hy ⟨p₂, s₂, hps₂⟩
  have hdx' : d.out ≠ x.out := hdx
  have hcx' : c.out ≠ x.out := hcx
  have hyx' : y.out ≠ x.out := hyx
  have hyc' : y.out ≠ c.out := hyc
  have hyd' : y.out ≠ d.out := hyd
  -- morphisms between points of `w`
  have mfd : ∀ f : d.out ⟶ x.out, f ≠ 0 → ∃ m, f = σ₂ ≫ rpow D.α.1 m :=
    D.mor_from_interior hq a₁ w₁ hw hMo hE p₂ s₂ (by simp [p₂]) (by simp [s₂]) hps₂
  have mtd : ∀ f : x.out ⟶ d.out, f ≠ 0 → ∃ m, f = rpow D.α.1 m ≫ a₁.1 ≫ a₂.1 := fun f hf ↦ by
    obtain ⟨m, hm⟩ := D.mor_to_interior hq a₁ w₁ hw hM hE p₂ s₂ (by simp [p₂]) (by simp [s₂])
      hps₂ f hf
    exact ⟨m, by rw [hm, hp₂v]⟩
  have mfc : ∀ f : c.out ⟶ x.out, f ≠ 0 → ∃ m, f = (a₂.1 ≫ σ₂) ≫ rpow D.α.1 m := fun f hf ↦ by
    obtain ⟨m, hm⟩ := D.mor_from_interior hq a₁ w₁ hw hMo hE _ _ (by simp) (by simp) hsplit f hf
    exact ⟨m, by rw [hm, hσ₁]⟩
  have mtc : ∀ f : x.out ⟶ c.out, f ≠ 0 → ∃ m, f = rpow D.α.1 m ≫ a₁.1 := fun f hf ↦ by
    obtain ⟨m, hm⟩ := D.mor_to_interior hq a₁ w₁ hw hM hE _ _ (by simp) (by simp) hsplit f hf
    exact ⟨m, by rw [hm, ha1v]⟩
  have Zd : ∀ e : d.out ⟶ d.out, ¬IsIso e → (a₁.1 ≫ a₂.1) ≫ e = 0 := fun e he ↦ by
    rw [← hp₂v]
    exact D.Z hq a₁ w₁ hw hM hE p₂ s₂ (by simp [p₂]) (by simp [s₂]) hps₂ e he
  have Zc : ∀ e : c.out ⟶ c.out, ¬IsIso e → a₁.1 ≫ e = 0 := fun e he ↦ by
    have := D.Z hq a₁ w₁ hw hM hE _ _ (by simp) (by simp) hsplit e he
    rwa [ha1v] at this
  have Zdc : ∀ e : c.out ⟶ c.out, ¬IsIso e → e ≫ a₂.1 ≫ σ₂ = 0 := fun e he ↦ by
    have := D.Z_dual hq a₁ w₁ hw hMo hE _ _ (by simp) (by simp) hsplit e he
    rwa [hσ₁] at this
  -- an endomorphism through a point off `w` is `ρ` only if it is zero after `a₁`
  have endo_y : ∀ h : y.out ⟶ x.out, ∀ {W : P} (k : c.out ⟶ W), D.α.1 ≫ a₁.1 ≫ k ≠ 0 →
      (ε.1 ≫ h) ≫ a₁.1 ≫ k = D.α.1 ≫ a₁.1 ≫ k → False := fun h W k hk he ↦ by
    rcases D.endo_cases hq a₁ w₁ hw (ε.1 ≫ h) with h1 | ⟨n, hn0, h1⟩
    · haveI : IsIso (ε.1 ≫ h) := by rw [h1]; infer_instance
      exact ε.2.2.1 (ray_isIso_factors ε.1 h).1
    · rcases n with _ | _ | n
      · omega
      · have : D.α.1 = ε.1 ≫ h := by rw [h1]; simp [rpow]
        rcases hα.2.2 _ ε.1 h this with h' | h'
        · exact ε.2.2.1 h'
        · exact hyx' (eq_of_isIso h')
      · apply hk
        rw [← he, h1, show n + 1 + 1 = n + 2 from rfl, rpow_add]
        simp only [Category.assoc]
        rw [show rpow D.α.1 2 ≫ a₁.1 ≫ k = D.α.1 ≫ D.α.1 ≫ a₁.1 ≫ k by simp [rpow], hz]
        simp
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src_gen hq a₁ w₁ hw hM hMo f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt_gen hq a₁ w₁ hw hM hMo f hf hs
  have nfe2 : ¬FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) (D.α.1 ≫ D.α.1) :=
    D.nftm_endo_gen hq a₁ w₁ hw hM hMo _ hαα0 hαα1
  have nfe1 : ¬FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) D.α.1 :=
    D.nftm_endo_gen hq a₁ w₁ hw hM hMo _ hα0 hα1
  have hτn : ¬IsIso (D.α.1 ≫ D.α.1 ≫ D.α.1) := not_isIso_comp_left' _ hα.2.1
  have hεi : ¬IsIso ε.1 := ε.2.2.1
  -- common lifting conditions
  have L_ρ_a : ¬∃ g, D.α.1 ≫ g = a₁.1 := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtc g (fun h ↦ ha.1 (by rw [← hg, h, comp_zero]))
    refine sandwich_l ha.1 (D.α.1 ≫ rpow D.α.1 m) (𝟙 _) (hρn m) ?_
    conv_lhs => rw [← hg]
    simp
  have L_ρ_aa : ¬∃ g, D.α.1 ≫ g = a₁.1 ≫ a₂.1 := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtd g (fun h ↦ haa (by rw [← hg, h, comp_zero]))
    refine sandwich_l haa (D.α.1 ≫ rpow D.α.1 m) (𝟙 _) (hρn m) ?_
    conv_lhs => rw [← hg]
    simp
  have L_a_ρ : ¬∃ g, a₁.1 ≫ g = D.α.1 := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mfc g (fun h ↦ hα0 (by rw [← hg, h, comp_zero]))
    refine sandwich_r hα0 (𝟙 _) (D.α.1 ≫ rpow D.α.1 m) (hρn m) ?_
    calc D.α.1 = a₁.1 ≫ (a₂.1 ≫ σ₂) ≫ rpow D.α.1 m := hg.symm
      _ = (a₁.1 ≫ a₂.1 ≫ σ₂) ≫ rpow D.α.1 m := by simp
      _ = _ := by rw [hω]; simp
  have L_irr : ∀ {s t : RayVert P} (f : s ⟶ t) {u : P} (f₁ : s.out ⟶ u) (f₂ : u ⟶ t.out),
      f.1 = f₁ ≫ f₂ → ¬IsIso f₁ → u ≠ t.out → False := fun f u f₁ f₂ h h1 h2 ↦ by
    rcases f.2.2.2 _ f₁ f₂ h with h' | h'
    · exact h1 h'
    · exact h2 (eq_of_isIso h')
  have L_ε_aa : ¬∃ g, ε.1 ≫ g = a₁.1 ≫ a₂.1 := fun ⟨g, hg⟩ ↦
    D.no_detour hq a₁ w₁ hw hM hy ε.1 (g ≫ σ₂) (by rw [← Category.assoc, hg, Category.assoc, hω])
  have L_ε_ρρ : ¬∃ g, ε.1 ≫ g = D.α.1 ≫ D.α.1 := fun ⟨g, hg⟩ ↦
    D.no_detour hq a₁ w₁ hw hM hy ε.1 g hg
  by_cases hDc : ∃ g : y.out ⟶ c.out, ε.1 ≫ g = D.α.1 ≫ a₁.1
  · -- `D̃₅` with `ζ : y → x₁`
    obtain ⟨ζ, hζ⟩ := hDc
    have hζaσ : ζ ≫ a₂.1 ≫ σ₂ ≠ 0 := fun h ↦ hτ0 (by
      rw [← h3l, ← Category.assoc D.α.1, ← hζ, Category.assoc, h, comp_zero])
    have hζa : ζ ≫ a₂.1 ≠ 0 := fun h ↦ hζaσ (by rw [← Category.assoc, h, zero_comp])
    have hζ0 : ζ ≠ 0 := fun h ↦ hζa (by rw [h, zero_comp])
    refine hM.not_lpf0d (D.α.1 ≫ D.α.1 ≫ D.α.1) hτn hτ0 ζ D.α.1 a₁.1 ε.1 a₂.1
      (nfs _ hζ0 hyx') (nfs _ hζa hyx') nfe1 (nft _ ha.1 hcx') (nft _ haa hdx')
      (nft _ ε.2.1 hyx') (nfs _ ha₂.1 hcx')
      (fun h ↦ hyc' (eq_of_isIso h)) hα.2.1 ha.2.1 hεi ha₂.2.1
      L_ρ_a L_ρ_aa (fun ⟨g, hg⟩ ↦ L_irr ε D.α.1 g hg.symm hα.2.1 hyx'.symm ) L_a_ρ
      (fun ⟨g, hg⟩ ↦ L_irr ε a₁.1 g hg.symm ha.2.1 (fun h ↦ hyc' h.symm))
      (fun ⟨g, hg⟩ ↦ L_irr D.α ε.1 g hg.symm hεi hyx') 
      (fun ⟨g, hg⟩ ↦ L_irr a₁ ε.1 g hg.symm hεi hyc') L_ε_aa
      (fun ⟨g, hg⟩ ↦ L_irr a₁ g ζ hg.symm (fun h ↦ hyx' (eq_of_isIso h).symm) hyc')
      ?_
    rintro ⟨g, hg⟩
    exact endo_y g (𝟙 _) (by simpa using hρa) (by simp only [Category.comp_id, Category.assoc]; rw [hg, hζ])
  by_cases hDd : ∃ g : y.out ⟶ d.out, ε.1 ≫ g = D.α.1 ≫ a₁.1 ≫ a₂.1
  · -- `D̃₅` with `ζ : y → x₂`
    obtain ⟨ζ, hζ⟩ := hDd
    have hζσ : ζ ≫ σ₂ ≠ 0 := fun h ↦ hτ0 (by
      rw [← h3l, show D.α.1 ≫ a₁.1 ≫ a₂.1 ≫ σ₂ = (D.α.1 ≫ a₁.1 ≫ a₂.1) ≫ σ₂ by simp, ← hζ,
        Category.assoc, h, comp_zero])
    have hζ0 : ζ ≠ 0 := fun h ↦ hζσ (by rw [h, zero_comp])
    have hω' : (a₁.1 ≫ a₂.1) ≫ σ₂ = D.α.1 ≫ D.α.1 := by rw [Category.assoc, hω]
    refine hM.not_lpf0e (D.α.1 ≫ D.α.1 ≫ D.α.1) hτn hτ0 ζ (D.α.1 ≫ a₁.1) (a₁.1 ≫ a₂.1) ε.1 σ₂
      (nfs _ hζ0 hyx') (nfs _ hζσ hyx') (nft _ hρa hcx') (nft _ haa hdx') (by rw [hω']; exact nfe2)
      (nft _ ε.2.1 hyx') (nfs _ hσ0 hdx')
      (fun h ↦ hyd' (eq_of_isIso h)) (not_isIso_comp_left' _ hα.2.1)
      (not_isIso_comp_left' _ ha.2.1) hεi (not_isIso_pathVal _ (by simp [s₂])) ?_ ?_
      (fun ⟨g, hg⟩ ↦ L_irr ε D.α.1 (a₁.1 ≫ g) (by rw [← hg]; simp) hα.2.1 hyx'.symm) ?_
      (fun ⟨g, hg⟩ ↦ L_irr ε (a₁.1 ≫ a₂.1) g hg.symm (not_isIso_comp_left' _ ha.2.1)
        (fun h ↦ hyd' h.symm))
      (fun ⟨g, hg⟩ ↦ hDc ⟨g, hg⟩) L_ε_aa (fun ⟨g, hg⟩ ↦ L_ε_ρρ ⟨g, by rw [hg, hω']⟩)
      (fun ⟨g, hg⟩ ↦ D.no_detour hq a₁ w₁ hw hM hy g (ζ ≫ σ₂) (by
        rw [← Category.assoc, hg, hω']))
      ?_
    · -- `ρ ≫ a₁ ≫ g = a₁ ≫ a₂`
      rintro ⟨g, hg⟩
      have hg0 : g ≫ σ₂ ≠ 0 := fun h ↦ hαα0 (by
        rw [← hω', ← hg, Category.assoc, h, comp_zero])
      obtain ⟨m, hm⟩ := mfc (g ≫ σ₂) hg0
      refine sandwich_l hαα0 D.α.1 (rpow D.α.1 m) hα.2.1 ?_
      calc D.α.1 ≫ D.α.1 = (D.α.1 ≫ a₁.1) ≫ g ≫ σ₂ := by rw [← hω', ← hg]; simp
        _ = D.α.1 ≫ (a₁.1 ≫ a₂.1 ≫ σ₂) ≫ rpow D.α.1 m := by rw [hm]; simp
        _ = _ := by rw [hω]
    · -- `ρ ≫ a₁ ≫ g = ρ ≫ ρ`
      rintro ⟨g, hg⟩
      obtain ⟨m, rfl⟩ := mfc g (fun h ↦ hαα0 (by rw [← hω', ← hg, h, comp_zero]))
      refine sandwich_l hαα0 D.α.1 (rpow D.α.1 m) hα.2.1 ?_
      calc D.α.1 ≫ D.α.1 = (D.α.1 ≫ a₁.1) ≫ (a₂.1 ≫ σ₂) ≫ rpow D.α.1 m := by rw [hg, hω']
        _ = D.α.1 ≫ (a₁.1 ≫ a₂.1 ≫ σ₂) ≫ rpow D.α.1 m := by simp
        _ = _ := by rw [hω]
    · -- `(a₁ ≫ a₂) ≫ g = ρ ≫ a₁`
      rintro ⟨g, hg⟩
      have := Zd (g ≫ a₂.1) (not_isIso_comp_right' _ ha₂.2.1)
      apply hρaa
      rw [← Category.assoc, ← hg]; simpa using this
    · -- `g ≫ a₁ ≫ a₂ = ζ`
      rintro ⟨g, hg⟩
      exact endo_y g a₂.1 hρaa (by simp only [Category.assoc]; rw [hg, hζ])
  -- `LPF1`
  have hGAB : ¬∃ g, g ≫ D.α.1 = a₂.1 ≫ σ₂ := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mfc g (fun h ↦ haσ (by rw [← hg, h, zero_comp]))
    refine sandwich_r haσ (𝟙 _) (rpow D.α.1 m ≫ D.α.1) (not_isIso_comp_right' _ hα.2.1) ?_
    conv_lhs => rw [← hg]
    simp
  refine hM.not_lpf1 (D.α.1 ≫ D.α.1 ≫ D.α.1) hτn hτ0 ε.1 a₁.1 D.α.1 (a₂.1 ≫ σ₂) D.α.1 a₁.1
    a₂.1 σ₂ a₂.1 LPF1.not_isRepresentationFinite (by rw [hω]) hσa
    (by rw [← Category.assoc, hσa, zero_comp]) (by rw [hσa, comp_zero])
    (by rw [← Category.assoc σ₂, hσa]; simp) nfe1 nfe2 (nft _ hρa hcx')
    (nft _ (by simpa using hρaa) hdx') (nft _ ha.1 hcx') (nft _ ε.2.1 hyx') nfe1
    (nft _ ha.1 hcx') (nft _ haa hdx') (nfs _ ha₂.1 hcx') (nfs _ hσ0 hdx') (nfs _ hσρ hdx')
    (nfs _ haσ hcx') (nfs _ (by simpa using haσρ) hcx') (nfs _ ha₂.1 hcx') (nfs _ haσ hcx')
    hεi ha.2.1 hα.2.1 (not_isIso_comp_left' _ ha₂.2.1) hα.2.1 ha.2.1 ha₂.2.1
    (not_isIso_pathVal _ (by simp [s₂])) ha₂.2.1
    (fun ⟨g, hg⟩ ↦ L_irr ε D.α.1 g hg.symm hα.2.1 hyx'.symm) L_ρ_a
    (fun ⟨g, hg⟩ ↦ L_irr ε a₁.1 g hg.symm ha.2.1 (fun h ↦ hyc' h.symm)) L_a_ρ ?_ ?_
    (fun ⟨g, hg⟩ ↦ L_irr a₁ ε.1 g hg.symm hεi hyc')
    (fun ⟨g, hg⟩ ↦ L_irr D.α ε.1 g hg.symm hεi hyx') L_ε_ρρ hDc
    (fun ⟨g, hg⟩ ↦ hDd ⟨g, by simpa using hg⟩) L_ρ_a L_ρ_aa L_a_ρ ?_ hGAB hGAB ?_ ?_ ?_ ?_
  · -- `a₁ ≫ g = ρ ≫ a₁`
    rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_l ha.1 D.α.1 (𝟙 _) hα.2.1 (by simpa using hg)
    · exact hρa (by rw [← hg, Zc g hgi])
  · -- `a₁ ≫ g = (ρ ≫ a₁) ≫ a₂`
    rintro ⟨g, hg⟩
    rcases IsFiniteRayCategory.factorization_comparable a₂.1 g with ⟨u, v, huv⟩ | ⟨u, v, huv⟩
    · subst huv
      by_cases hu : IsIso u
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
        by_cases hv : IsIso v
        · obtain ⟨hh', rfl⟩ := RayQuiver.eq_id_of_isIso v
          exact sandwich_l haa D.α.1 (𝟙 _) hα.2.1 (by simpa using hg)
        · apply hρaa
          have := Zd v hv
          rw [show D.α.1 ≫ a₁.1 ≫ a₂.1 = (D.α.1 ≫ a₁.1) ≫ a₂.1 by simp, ← hg]
          simp only [eqToHom_refl, Category.id_comp]
          simpa using this
      · apply hρaa
        rw [show D.α.1 ≫ a₁.1 ≫ a₂.1 = (D.α.1 ≫ a₁.1) ≫ a₂.1 by simp, ← hg,
          show a₁.1 ≫ (u ≫ a₂.1) ≫ v = (a₁.1 ≫ u) ≫ a₂.1 ≫ v by simp, Zc u hu, zero_comp]
    · by_cases hu : IsIso u
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso u
        simp only [eqToHom_refl, Category.id_comp] at huv
        refine sandwich_l haa D.α.1 v hα.2.1 ?_
        conv_lhs => rw [huv, ← Category.assoc, hg]
        simp
      · apply haa
        rw [huv, show a₁.1 ≫ (u ≫ g) ≫ v = (a₁.1 ≫ u) ≫ g ≫ v by simp, Zc u hu, zero_comp]
  · -- `g ≫ ρ = σ₂`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mfd g (fun h ↦ hσ0 (by rw [← hg, h, zero_comp]))
    refine sandwich_r hσ0 (𝟙 _) (rpow D.α.1 m ≫ D.α.1) (not_isIso_comp_right' _ hα.2.1) ?_
    conv_lhs => rw [← hg]
    simp
  · -- `g ≫ σ₂ = ρ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtd g (fun h ↦ hα0 (by rw [← hg, h, zero_comp]))
    refine sandwich_r hα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 = (rpow D.α.1 m ≫ a₁.1 ≫ a₂.1) ≫ σ₂ := hg.symm
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ a₂.1 ≫ σ₂) := by simp
      _ = _ := by rw [hω]
  · -- `g ≫ a₂ ≫ σ₂ = ρ`
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mtc g (fun h ↦ hα0 (by rw [← hg, h, zero_comp]))
    refine sandwich_r hα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 = (rpow D.α.1 m ≫ a₁.1) ≫ a₂.1 ≫ σ₂ := hg.symm
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ a₂.1 ≫ σ₂) := by simp
      _ = _ := by rw [hω]
  · -- `g ≫ a₂ ≫ σ₂ = σ₂ ≫ ρ`
    rintro ⟨g, hg⟩
    have := Zd (g ≫ a₂.1) (not_isIso_comp_right' _ ha₂.2.1)
    apply hτ0
    rw [← h3r]
    calc a₁.1 ≫ a₂.1 ≫ σ₂ ≫ D.α.1 = (a₁.1 ≫ a₂.1) ≫ (g ≫ a₂.1 ≫ σ₂) := by rw [hg]; simp
      _ = ((a₁.1 ≫ a₂.1) ≫ g ≫ a₂.1) ≫ σ₂ := by simp
      _ = 0 := by rw [this, zero_comp]
  · -- `g ≫ a₂ ≫ σ₂ = (a₂ ≫ σ₂) ≫ ρ`
    rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_r haσ (𝟙 _) D.α.1 hα.2.1 (by simpa using hg)
    · exact haσρ (by rw [← Category.assoc, ← hg, Zdc g hgi])

end LPF

end PFData

/-- **[mild] LPF**: an open penny-farthing has `n = 2`. -/
theorem lpfStmt : LPFStmt P k := by
  intro x D hq c a₁ w₁ hw hM hMo hE z μ hμ hz
  classical
  by_contra hn0
  have hn : 0 < w₁.length := Nat.pos_of_ne_zero hn0
  obtain ⟨r, hr⟩ := exists_path μ hμ
  obtain ⟨q₀, p₀, s₀, hps₀, y₀, ε₀, hy₀, m₀, g₀, he₀⟩ :=
    D.first_exit hq a₁ w₁ hw hM hE _ r rfl (by rw [hr]; exact hμ) hz
  have hex : ∃ n, ∃ (q : RayVert P) (p : Quiver.Path x q) (s : Quiver.Path q x)
      (_ : D.w'.cons D.β = p.comp s) (y : RayVert P) (ε : q ⟶ y),
      ¬D.OnW y ∧ pathVal p ≫ ε.1 ≠ 0 ∧ p.length = n :=
    ⟨_, q₀, p₀, s₀, hps₀, y₀, ε₀, hy₀, fun h ↦ hμ (by
      rw [← hr, he₀, show rpow D.α.1 m₀ ≫ pathVal p₀ ≫ ε₀.1 ≫ g₀ =
        rpow D.α.1 m₀ ≫ (pathVal p₀ ≫ ε₀.1) ≫ g₀ by simp, h]; simp), rfl⟩
  obtain ⟨q, p, s, hps, y, ε, hy, hne, hlen⟩ := Nat.find_spec hex
  have hmin : ∀ {q' : RayVert P} (p' : Quiver.Path x q') (s' : Quiver.Path q' x),
      D.w'.cons D.β = p'.comp s' → ∀ {y' : RayVert P} (ε' : q' ⟶ y'), ¬D.OnW y' →
      pathVal p' ≫ ε'.1 ≠ 0 → p.length ≤ p'.length := fun p' s' hps' y' ε' hy' hne' ↦ by
    rw [hlen]; exact Nat.find_min' hex ⟨_, p', s', hps', y', ε', hy', hne', rfl⟩
  rcases Nat.lt_or_ge p.length 2 with hp2 | hp2
  · rcases p with _ | ⟨p', e⟩
    · exact D.exit_x0 hq a₁ w₁ hw hM hMo hE hn ε hy
    · have hp' : p'.length = 0 := by simp at hp2; omega
      cases p' with
      | cons _ _ => simp at hp'
      | nil =>
        obtain ⟨hqc, he⟩ := first_arrow_eq (hps.symm.trans (D.split1 hq a₁ w₁ hw))
        subst hqc
        have hea : a₁ = e := (eq_of_heq he).symm
        subst hea
        refine D.exit_x1 hq a₁ w₁ hw hM hMo hE hn ε.1 ε.2 hy ?_
        change (𝟙 _ ≫ a₁.1) ≫ ε.1 ≠ 0 at hne
        rwa [Category.id_comp] at hne
  · rcases Nat.eq_zero_or_pos s.length with hs | hs
    · cases s with
      | cons _ _ => simp at hs
      | nil =>
        have := hmin .nil (D.w'.cons D.β) (Quiver.Path.nil_comp _).symm ε hy
          (by simpa [pathVal] using ε.2.1)
        simp only [Quiver.Path.length_nil] at this
        omega
    · exact D.exit_mid hq a₁ w₁ hw hM hMo hE p s hp2 hs hps ε hy hne hmin

end RayCat

end LargeIndecomposable
