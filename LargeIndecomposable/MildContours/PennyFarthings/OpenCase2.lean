module

public import LargeIndecomposable.MildContours.PennyFarthings.OpenAssembly
public import LargeIndecomposable.MildContours.Diamonds.Closure3
public import LargeIndecomposable.MildContours.Diamonds.Conclusion
public import LargeIndecomposable.Cleaving.Shapes.ShapePC1
public import LargeIndecomposable.Cleaving.Shapes.ShapePC2
public import LargeIndecomposable.Cleaving.Shapes.ShapePC4
public import LargeIndecomposable.Cleaving.Shapes.ShapeD6
public import LargeIndecomposable.Cleaving.Basic.Tools
public import LargeIndecomposable.Cleaving.Shapes.ShapePC6
public import LargeIndecomposable.Cleaving.Families.FamPC7
public import LargeIndecomposable.Cleaving.Families.FamPC8
public import LargeIndecomposable.Cleaving.Families.FamPC10

/-!
# Open penny-farthing, `n = 2`, no exit at `x₀` ([mild] MIPF, case 2)

`x₀ = x` with the loop `α` (`= ρ`), `x₁ = t`, `a₁ : x ⟶ t`, `β : t ⟶ x`.
* `no_entry_x`: an entry at `x₀` gives a tiny point of the reversed penny-farthing.
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

/-- A nonzero non-invertible morphism ends with an arrow. -/
lemma exists_last' {a b : P} (f : a ⟶ b) (hf0 : f ≠ 0) (hf : ¬IsIso f) :
    ∃ (c : P) (r : a ⟶ c) (e : c ⟶ b), IsIrreducible e ∧ f = r ≫ e := by
  obtain ⟨c, p, e, hp⟩ := MildContour.exists_last_arrow f hf0 hf
  exact ⟨c.out, pathVal p, e.1, e.2, hp⟩

lemma sandwich_r {a b : P} {f : a ⟶ b} (hf : f ≠ 0) (u : a ⟶ a) (v : b ⟶ b) (hv : ¬IsIso v)
    (h : f = u ≫ f ≫ v) : False :=
  hv (by rw [(IsRayCategory.eq_id_of_two_sided f hf u v h).2]; infer_instance)

lemma sandwich_l {a b : P} {f : a ⟶ b} (hf : f ≠ 0) (u : a ⟶ a) (v : b ⟶ b) (hu : ¬IsIso u)
    (h : f = u ≫ f ≫ v) : False :=
  hu (by rw [(IsRayCategory.eq_id_of_two_sided f hf u v h).1]; infer_instance)

namespace PFData

variable {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) (a₁ : x ⟶ D.t)
  (hw : D.w' = Quiver.Path.nil.cons a₁)
include hq hw

/-- **No entry at `x₀`** other than `α`, `β` (else `Pᵒᵖ` has a tiny point). -/
theorem no_entry_x (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hNTo : NoTiny Pᵒᵖ) {b : RayVert P} (ζ : b ⟶ x) (hbx : b ≠ x) (hbt : b ≠ D.t) : False := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have hw2 := D.hw2 hq a₁ hw
  refine hNTo _ _ ((D.op hq a₁ .nil hw2).tiny_x0 rfl (revArr D.β) rfl hMo hMo.op hE.op
    (revArr ζ) ?_ ?_)
  · intro h; apply hbx
    have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) h
    exact this
  · intro h; apply hbt
    have := congrArg (fun z : RayVert Pᵒᵖ ↦ (RayVert.out z).unop) h
    exact this

/-- Morphisms `x₀ ⟶ x₁` are `αᵐ a₁`. -/
lemma mor_xt (hM : MildHyp k P) (hE : EndCyclic P) (f : x.out ⟶ D.t.out) (hf : f ≠ 0) :
    ∃ m, f = rpow D.α.1 m ≫ a₁.1 := by
  obtain ⟨m, hm⟩ := D.mor_to_interior hq a₁ .nil (D.hw2 hq a₁ hw) hM hE (Quiver.Path.nil.cons a₁)
    (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) f hf
  exact ⟨m, by rw [hm]; change _ ≫ 𝟙 _ ≫ a₁.1 = _; rw [Category.id_comp]⟩

/-- **The exit at `x₁`**: with no exit at `x₀`, a nonzero morphism from `x₀` off
`{x₀, x₁}` gives an arrow `γ` out of `x₁` with `a₁ ≫ γ ≠ 0`. -/
lemma exit_t (hM : MildHyp k P) (hE : EndCyclic P)
    (hno : ∀ {y : RayVert P}, y ≠ x → y ≠ D.t → IsEmpty (x ⟶ y)) :
    ∀ (n : ℕ) {v : RayVert P} (r : Quiver.Path x v), r.length = n → pathVal r ≠ 0 → v ≠ x →
      v ≠ D.t → ∃ (y : RayVert P) (_ : y ≠ x) (_ : y ≠ D.t) (γ : D.t ⟶ y), a₁.1 ≫ γ.1 ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro v r hr _ hvx _
    cases r with
    | nil => exact (hvx rfl).elim
    | cons _ _ => simp at hr
  | succ n ih =>
    intro v r hr h0 hvx hvt
    cases r with
    | nil => simp at hr
    | cons r' e =>
      rename_i s
      have h0' : pathVal r' ≠ 0 := fun h ↦ h0 (by change pathVal r' ≫ e.1 = 0; rw [h, zero_comp])
      by_cases hsx : s = x
      · subst hsx; exact ((hno hvx hvt).false e).elim
      by_cases hst : s = D.t
      · subst hst
        refine ⟨v, hvx, hvt, e, fun h ↦ h0 ?_⟩
        obtain ⟨m, hm⟩ := D.mor_xt hq a₁ hw hM hE (pathVal r') h0'
        change pathVal r' ≫ e.1 = 0
        rw [hm, Category.assoc, h, comp_zero]
      · exact ih r' (by simpa using hr) h0' hsx hst

/-- Radical endomorphisms of `x₁` kill `a₁` on the right. -/
lemma Z_t (hM : MildHyp k P) (hE : EndCyclic P) (c : D.t.out ⟶ D.t.out) (hc : ¬IsIso c) :
    a₁.1 ≫ c = 0 := by
  have := D.Z hq a₁ .nil (D.hw2 hq a₁ hw) hM hE (Quiver.Path.nil.cons a₁)
    (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) c hc
  simpa [pathVal] using this

/-- Radical endomorphisms of `x₁` kill `β` on the left. -/
lemma Zd_t (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) (c : D.t.out ⟶ D.t.out) (hc : ¬IsIso c) :
    c ≫ D.β.1 = 0 := by
  have := D.Z_dual hq a₁ .nil (D.hw2 hq a₁ hw) hMo hE (Quiver.Path.nil.cons a₁)
    (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) c hc
  simpa [pathVal] using this

/-- Morphisms `x₁ ⟶ x₀` are `β αᵐ`. -/
lemma mor_tx (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) (f : D.t.out ⟶ x.out) (hf : f ≠ 0) :
    ∃ m, f = D.β.1 ≫ rpow D.α.1 m := by
  obtain ⟨m, hm⟩ := D.mor_from_interior hq a₁ .nil (D.hw2 hq a₁ hw) hMo hE
    (Quiver.Path.nil.cons a₁) (Quiver.Path.nil.cons D.β) (by simp) (by simp)
    (D.split2 hq a₁ hw) f hf
  exact ⟨m, by rw [hm]; change (𝟙 _ ≫ D.β.1) ≫ _ = _; rw [Category.id_comp]⟩

/-- The arrows out of `x₀` (no exit at `x₀`) are `α` and `a₁`. -/
lemma first_x (hM : MildHyp k P) (hno : ∀ {y : RayVert P}, y ≠ x → y ≠ D.t → IsEmpty (x ⟶ y))
    {w : P} (g : x.out ⟶ w) (hg : g ≠ 0) (hgi : ¬IsIso g) :
    (∃ g', g = D.α.1 ≫ g') ∨ ∃ g', g = a₁.1 ≫ g' := by
  obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' g hg hgi
  have hw2 := D.hw2 hq a₁ hw
  let e' : x ⟶ (RayVert.mk c) := ⟨e, he⟩
  by_cases hcx : (RayVert.mk c : RayVert P) = x
  · obtain rfl : c = x.out := hcx
    have := D.loop_eq_rho hq a₁ .nil hw2 e'
    exact Or.inl ⟨r, by rw [show e = D.α.1 from congrArg Subtype.val this]⟩
  by_cases hct : (RayVert.mk c : RayVert P) = D.t
  · obtain rfl : c = D.t.out := hct
    obtain ⟨-, he'⟩ := D.arrow_into_w hq a₁ .nil hw2 hM (Quiver.Path.nil.cons a₁)
      (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) e'
    exact Or.inr ⟨r, by rw [show e = a₁.1 from congrArg Subtype.val (eq_of_heq he')]⟩
  exact ((hno hcx hct).false e').elim

/-- The arrows into `x₀` (no entry at `x₀`) are `α` and `β`. -/
lemma last_x (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) (hNTo : NoTiny Pᵒᵖ)
    {w : P} (g : w ⟶ x.out) (hg : g ≠ 0) (hgi : ¬IsIso g) :
    (∃ g', g = g' ≫ D.α.1) ∨ ∃ g', g = g' ≫ D.β.1 := by
  obtain ⟨c, r, e, hr⟩ := MildContour.exists_last_arrow g hg hgi
  have hw2 := D.hw2 hq a₁ hw
  by_cases hcx : c = x
  · subst hcx
    have := D.loop_eq_rho hq a₁ .nil hw2 e
    exact Or.inl ⟨pathVal r, by rw [hr, this]⟩
  by_cases hct : c = D.t
  · subst hct
    obtain ⟨-, he'⟩ := D.arrow_from_w hq a₁ .nil hw2 hMo (Quiver.Path.nil.cons a₁)
      (Quiver.Path.nil.cons D.β) (by simp) (by simp) (D.split2 hq a₁ hw) e
    exact Or.inr ⟨pathVal r, by rw [hr, eq_of_heq he']⟩
  exact (D.no_entry_x hq a₁ hw hM hMo hE hNTo e hcx hct).elim

section Deep

variable (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) (hNTo : NoTiny Pᵒᵖ)
  (hno : ∀ {y : RayVert P}, y ≠ x → y ≠ D.t → IsEmpty (x ⟶ y))
include hM hMo hE hNTo hno

lemma rel (hM' : MildHyp k P) :
    D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = 0 ∧ D.α.1 ≫ D.α.1 ≫ a₁.1 = 0 ∧
      D.β.1 ≫ D.α.1 ≫ D.α.1 = 0 := by
  obtain ⟨h1, h2, h3⟩ := D.rho_four hq a₁ .nil (D.hw2 hq a₁ hw) hM'
  refine ⟨by simpa [rpow_succ] using h1, by simpa using h2, h3⟩

/-- `α³` is killed by every non-invertible morphism after it. -/
lemma τ_right {w : P} (v : x.out ⟶ w) (hv : ¬IsIso v) :
    D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ v = 0 := by
  obtain ⟨r1, r2, r3⟩ := D.rel hq a₁ hw hM hMo hE hNTo hno hM
  by_cases hv0 : v = 0
  · rw [hv0]; simp
  rcases D.first_x hq a₁ hw hM hno v hv0 hv with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · simp only [← Category.assoc] at r1 ⊢; rw [r1, zero_comp]
  · rw [show D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ a₁.1 ≫ g = D.α.1 ≫ (D.α.1 ≫ D.α.1 ≫ a₁.1) ≫ g by simp,
      r2]; simp

/-- `α³` is killed by every non-invertible morphism before it. -/
lemma τ_left {w : P} (u : w ⟶ x.out) (hu : ¬IsIso u) :
    u ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = 0 := by
  obtain ⟨r1, r2, r3⟩ := D.rel hq a₁ hw hM hMo hE hNTo hno hM
  by_cases hu0 : u = 0
  · rw [hu0]; simp
  rcases D.last_x hq a₁ hw hM hMo hE hNTo u hu0 hu with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · simp only [Category.assoc]; rw [r1, comp_zero]
  · rw [show (g ≫ D.β.1) ≫ D.α.1 ≫ D.α.1 ≫ D.α.1 = g ≫ (D.β.1 ≫ D.α.1 ≫ D.α.1) ≫ D.α.1 by
      simp, r3]; simp

/-- A nonzero morphism factoring through `α³` is `α³`. -/
lemma ftm_τ {s w : P} (f : s ⟶ w) (hf : f ≠ 0)
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
                       rw [D.τ_right hq a₁ hw hM hMo hE hNTo hno v hv, comp_zero]) hf
  · exact absurd (by
      rw [show u ≫ (D.α.1 ≫ D.α.1 ≫ D.α.1) ≫ v = (u ≫ D.α.1 ≫ D.α.1 ≫ D.α.1) ≫ v by simp,
        D.τ_left hq a₁ hw hM hMo hE hNTo hno u hu, zero_comp]) hf

lemma nftm_src {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) :
    ¬FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) f := fun h ↦ by
  obtain ⟨h1, -, -⟩ := D.ftm_τ hq a₁ hw hM hMo hE hNTo hno f hf h; exact hs h1

lemma nftm_tgt {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hw' : w ≠ x.out) :
    ¬FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) f := fun h ↦ by
  obtain ⟨-, h2, -⟩ := D.ftm_τ hq a₁ hw hM hMo hE hNTo hno f hf h; exact hw' h2

lemma nftm_endo (f : x.out ⟶ x.out) (hf : f ≠ 0) (hne : f ≠ D.α.1 ≫ D.α.1 ≫ D.α.1) :
    ¬FactorsThroughMorphism (D.α.1 ≫ D.α.1 ≫ D.α.1) f := fun h ↦ by
  obtain ⟨h1, h2, e⟩ := D.ftm_τ hq a₁ hw hM hMo hE hNTo hno f hf h
  exact hne (by simpa using e)

end Deep

section Exit2

variable (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) (hNTo : NoTiny Pᵒᵖ)
  (hno : ∀ {y : RayVert P}, y ≠ x → y ≠ D.t → IsEmpty (x ⟶ y))
  {c : P} (γ : D.t.out ⟶ c) (hγ : IsIrreducible γ) (hcx : c ≠ x.out) (hct : c ≠ D.t.out)
  (haγ : a₁.1 ≫ γ ≠ 0)
include hM hMo hE hNTo hno hγ hcx hct haγ

/-- Basic facts of the core. -/
lemma core :
    D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 ∧ ¬IsIso (D.α.1 ≫ D.α.1 ≫ D.α.1) ∧
      D.α.1 ≫ D.α.1 ≠ D.α.1 ≫ D.α.1 ≫ D.α.1 ∧ D.α.1 ≠ D.α.1 ≫ D.α.1 ≫ D.α.1 ∧
      D.α.1 ≫ a₁.1 ≠ 0 ∧ D.β.1 ≫ D.α.1 ≠ 0 ∧ (D.t.out ≠ x.out) := by
  have hτ0 : D.α.1 ≫ D.α.1 ≫ D.α.1 ≠ 0 := by
    have := D.hωρ
    change pathVal ((D.q.cons D.α).cons D.α) ≫ D.α.1 ≠ 0 at this
    rw [hq] at this
    simpa [pathVal] using this
  have hα := D.α.2.2.1
  have hab := D.ab_eq hq a₁ hw
  refine ⟨hτ0, not_isIso_comp_left' _ hα, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ hτ0 ?_, fun h ↦ hτ0 ?_,
    D.t_ne_x hq a₁ hw hM⟩
  · have e : D.α.1 ≫ D.α.1 = 𝟙 _ ≫ (D.α.1 ≫ D.α.1) ≫ D.α.1 := by
      conv_lhs => rw [h]
      simp
    exact hα (by rw [(IsRayCategory.eq_id_of_two_sided _ (fun h' ↦ hτ0 (by
      rw [← Category.assoc, h', zero_comp])) _ _ e).2]; infer_instance)
  · have e : D.α.1 = 𝟙 _ ≫ D.α.1 ≫ (D.α.1 ≫ D.α.1) := by rw [Category.id_comp]; exact h
    exact hα (by
      have h2 := (IsRayCategory.eq_id_of_two_sided _ (fun h' ↦ hτ0 (by rw [h', zero_comp])) _ _
        e).2
      haveI : IsIso (D.α.1 ≫ D.α.1) := by rw [h2]; infer_instance
      exact (ray_isIso_factors D.α.1 D.α.1).1)
  · rw [← hab, ← Category.assoc, h, zero_comp]
  · rw [show D.α.1 ≫ D.α.1 ≫ D.α.1 = a₁.1 ≫ D.β.1 ≫ D.α.1 by
      rw [← Category.assoc a₁.1, hab, Category.assoc], h, comp_zero]

/-- An arrow out of `x₁` to a point other than `x₀` is apart from `β` and `β α`. -/
lemma exit_back {d : P} (e : D.t.out ⟶ d) (he : IsIrreducible e) (hdx : d ≠ x.out) :
    (¬∃ g, e ≫ g = D.β.1) ∧ (¬∃ g, e ≫ g = D.β.1 ≫ D.α.1) ∧ (¬∃ g, D.β.1 ≫ g = e) ∧
      ¬∃ g, (D.β.1 ≫ D.α.1) ≫ g = e := by
  obtain ⟨hτ0, hτn, -, -, -, hbα, htx⟩ := D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hR : RightCancel P := hM.right
  have hb := D.β.2
  have n1 : ¬∃ g, e ≫ g = D.β.1 := by
    rintro ⟨g, hg⟩
    rcases hb.2.2 _ e g hg.symm with h | h
    · exact he.2.1 h
    · exact hdx (eq_of_isIso h)
  refine ⟨n1, ?_, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hbα (by rw [← hg, h, comp_zero])
    have hgi : ¬IsIso g := fun h ↦ hdx (eq_of_isIso h)
    rcases D.last_x hq a₁ hw hM hMo hE hNTo g hg0 hgi with ⟨g', rfl⟩ | ⟨g', rfl⟩
    · have e' : (e ≫ g') ≫ D.α.1 = D.β.1 ≫ D.α.1 := by rw [Category.assoc, hg]
      exact n1 ⟨g', hR _ _ _ e' (by rw [e']; exact hbα)⟩
    · have hn : ¬IsIso (e ≫ g') := fun h ↦ he.2.1 (ray_isIso_factors e g').1
      apply hbα
      rw [← hg, ← Category.assoc, D.Zd_t hq a₁ hw hMo hE _ hn]
  · rintro ⟨g, hg⟩
    rcases he.2.2 _ D.β.1 g hg.symm with h | h
    · exact hb.2.1 h
    · exact hdx (eq_of_isIso h).symm
  · rintro ⟨g, hg⟩
    rcases he.2.2 _ (D.β.1 ≫ D.α.1) g hg.symm with h | h
    · exact hb.2.1 (ray_isIso_factors D.β.1 D.α.1).1
    · exact hdx (eq_of_isIso h).symm

/-- **One exit at `x₁`** ([mild] MIPF, figure 4.5, first diagram, a `D̃₅`). -/
theorem one_exit {d : P} (γ' : D.t.out ⟶ d) (hγ' : IsIrreducible γ') (hdx : d ≠ x.out)
    (h1 : ¬∃ g, γ ≫ g = γ') (h2 : ¬∃ g, γ' ≫ g = γ) : False := by
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hα := D.α.2
  have hb := D.β.2
  have hα0 : D.α.1 ≠ 0 := hα.1
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have nf := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src hq a₁ hw hM hMo hE hNTo hno f hf hs
  have ne := fun (f : x.out ⟶ x.out) (hf : f ≠ 0) (hne : f ≠ D.α.1 ≫ D.α.1 ≫ D.α.1) ↦
    D.nftm_endo hq a₁ hw hM hMo hE hNTo hno f hf hne
  obtain ⟨g1, g2, g3, g4⟩ := D.exit_back hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ γ hγ hcx
  obtain ⟨g1', g2', g3', g4'⟩ :=
    D.exit_back hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ γ' hγ' hdx
  refine hM.not_pc1 _ hτn hτ0 D.α.1 D.α.1 D.β.1 γ γ' (ne _ hα0 hα1) (nf _ hb.1 htx)
    (nf _ hbα htx) (nf _ hγ.1 htx) (nf _ hγ'.1 htx) (ne _ hα0 hα1) (ne _ hαα0 hαα)
    hα.2.1 hα.2.1 hb.2.1 hγ.2.1 hγ'.2.1 g3 g3' g1 g2 h1 g1' g2' h2 ?_ ?_
  · rintro ⟨g, hg⟩
    rcases hb.2.2 _ g D.α.1 hg.symm with h | h
    · exact htx (eq_of_isIso h)
    · exact hα.2.1 h
  · rintro ⟨g, hg⟩
    rcases hα.2.2 _ g D.β.1 hg.symm with h | h
    · exact htx (eq_of_isIso h).symm
    · exact hb.2.1 h

/-- The arrows out of `x₁` are `β` and `γ`. -/
lemma first_t {w : P} (g : D.t.out ⟶ w) (hg : g ≠ 0) (hgi : ¬IsIso g) :
    (∃ g', g = D.β.1 ≫ g') ∨ ∃ g', g = γ ≫ g' := by
  obtain ⟨-, -, -, -, -, -, htx⟩ := D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  obtain ⟨d, e, r, he, rfl⟩ := exists_first_arrow' g hg hgi
  have hw2 := D.hw2 hq a₁ hw
  by_cases hdx : d = x.out
  · have he' : IsIrreducible (e ≫ eqToHom hdx) := isIrreducible_comp_iso he _
    obtain ⟨m, hm⟩ := D.mor_tx hq a₁ hw hMo hE _ he'.1
    rcases m with _ | m
    · refine Or.inl ⟨eqToHom hdx.symm ≫ r, ?_⟩
      have : e = D.β.1 ≫ eqToHom hdx.symm := by
        calc e = (e ≫ eqToHom hdx) ≫ eqToHom hdx.symm := by simp
          _ = _ := by rw [hm]; simp
      rw [this]; simp
    · exfalso
      rcases he'.2.2 _ D.β.1 (rpow D.α.1 (m + 1)) hm with h | h
      · exact D.β.2.2.1 h
      · exact MildContour.rpow_not_isIso D.α.1 D.α.2.2.1 (m + 1) (by omega) h
  by_cases hdt : d = D.t.out
  · exact (D.no_loop_x1 hq a₁ hw hM (⟨e ≫ eqToHom hdt, isIrreducible_comp_iso he _⟩ :
      D.t ⟶ D.t)).elim
  by_cases h1 : ∃ u, γ ≫ u = e
  · obtain ⟨u, rfl⟩ := h1
    exact Or.inr ⟨u ≫ r, by simp⟩
  by_cases h2 : ∃ u, e ≫ u = γ
  · obtain ⟨u, hu⟩ := h2
    rcases hγ.2.2 _ e u hu.symm with h | h
    · exact absurd h he.2.1
    · exact Or.inr ⟨inv u ≫ r, by rw [← hu]; simp⟩
  exact (D.one_exit hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ e he hdx h1 h2).elim

/-- **No entry at `x₁`** other than `a₁` (an `Ẽ₇` centred at `x₁`). -/
theorem no_entry_t {w : P} (δ : w ⟶ D.t.out) (hδ : IsIrreducible δ) (hwx : w ≠ x.out) : False := by
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hL : LeftCancel P := hM.left
  have hα := D.α.2
  have hb := D.β.2
  have ha := a₁.2
  have hab := D.ab_eq hq a₁ hw
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src hq a₁ hw hM hMo hE hNTo hno f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt hq a₁ hw hM hMo hE hNTo hno f hf hs
  obtain ⟨g1, g2, g3, g4⟩ := D.exit_back hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ γ hγ hcx
  have hwt : w ≠ D.t.out := fun h ↦ by
    subst h; exact D.no_loop_x1 hq a₁ hw hM (⟨δ, hδ⟩ : D.t ⟶ D.t)
  refine hM.not_pc2 _ hτn hτ0 a₁.1 (D.α.1 ≫ a₁.1) δ D.β.1 (D.β.1 ≫ D.α.1) γ γ
    (nfs _ hb.1 htx) (nfs _ hγ.1 htx) (nft _ ha.1 htx)
    (by rw [hab]; exact D.nftm_endo hq a₁ hw hM hMo hE hNTo hno _ hαα0 hαα)
    (nft _ haγ hcx) (nft _ hαa htx) (nfs _ hδ.1 hwx) (nfs _ hbα htx) (nfs _ hγ.1 htx)
    ha.2.1 (not_isIso_comp_left' _ hα.2.1) hδ.2.1 hb.2.1 (not_isIso_comp_left' _ hb.2.1)
    hγ.2.1 hγ.2.1 g3 g1 ?_ ?_ ?_ ?_ g4 g2 ?_ ?_ ?_ ?_ ?_
  · rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_l ha.1 D.α.1 (𝟙 _) hα.2.1 (by simpa using hg)
    · exact hαa (by rw [← hg, D.Z_t hq a₁ hw hM hE g hgi])
  · rintro ⟨g, hg⟩
    exact sandwich_l ha.1 D.α.1 g hα.2.1 (by simp only [Category.assoc] at hg; exact hg.symm)
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hαα0 (by rw [← hab, ← hg, h, comp_zero])
    obtain ⟨m, rfl⟩ := D.mor_tx hq a₁ hw hMo hE g hg0
    refine sandwich_r hαα0 (𝟙 _) (D.α.1 ≫ rpow D.α.1 m) (not_isIso_comp_left' _ hα.2.1) ?_
    calc D.α.1 ≫ D.α.1 = a₁.1 ≫ D.β.1 := hab.symm
      _ = (D.α.1 ≫ a₁.1) ≫ D.β.1 ≫ rpow D.α.1 m := hg.symm
      _ = D.α.1 ≫ (a₁.1 ≫ D.β.1) ≫ rpow D.α.1 m := by simp
      _ = _ := by rw [hab]; simp
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ haγ (by rw [← hg, h, comp_zero])
    have hgi : ¬IsIso g := fun h ↦ hct (eq_of_isIso h).symm
    rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ g hg0 hgi with
      ⟨g', rfl⟩ | ⟨g', rfl⟩
    · have hg'i : ¬IsIso g' := fun h ↦ hcx (eq_of_isIso h).symm
      apply haγ
      rw [← hg, show (D.α.1 ≫ a₁.1) ≫ D.β.1 ≫ g' = D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ g' by
        simp only [Category.assoc]; rw [← Category.assoc a₁.1, hab]; simp,
        D.τ_right hq a₁ hw hM hMo hE hNTo hno g' hg'i]
    · exact sandwich_l haγ D.α.1 g' hα.2.1 (by simp only [Category.assoc] at hg ⊢; exact hg.symm)
  · rintro ⟨g, hg⟩
    rcases hδ.2.2 _ g (D.α.1 ≫ a₁.1) hg.symm with h | h
    · exact hwx (eq_of_isIso h)
    · exact hα.2.1 (ray_isIso_factors D.α.1 a₁.1).1
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hαa (by rw [← hg, h, zero_comp])
    have hgi : ¬IsIso g := fun h ↦ hwx (eq_of_isIso h).symm
    rcases D.first_x hq a₁ hw hM hno g hg0 hgi with ⟨g', rfl⟩ | ⟨g', rfl⟩
    · have e := hL _ _ _ (show D.α.1 ≫ (g' ≫ δ) = D.α.1 ≫ a₁.1 by rw [← hg]; simp)
        (by rw [← Category.assoc, hg]; exact hαa)
      rcases ha.2.2 _ g' δ e.symm with h | h
      · exact hwx (eq_of_isIso h).symm
      · exact hδ.2.1 h
    · have hn : ¬IsIso (g' ≫ δ) := fun h ↦ hδ.2.1 (ray_isIso_factors g' δ).2
      apply hαa
      rw [← hg, Category.assoc, D.Z_t hq a₁ hw hM hE _ hn]
  · rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_r hb.1 (𝟙 _) D.α.1 hα.2.1 (by simpa using hg)
    · exact hbα (by rw [← hg, D.Zd_t hq a₁ hw hMo hE g hgi])
  · rintro ⟨g, hg⟩
    exact sandwich_r hb.1 g D.α.1 hα.2.1 hg.symm
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hαα0 (by rw [← hab, ← hg, h, zero_comp])
    obtain ⟨m, rfl⟩ := D.mor_xt hq a₁ hw hM hE g hg0
    refine sandwich_r hαα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 ≫ D.α.1 = a₁.1 ≫ D.β.1 := hab.symm
      _ = (rpow D.α.1 m ≫ a₁.1) ≫ D.β.1 ≫ D.α.1 := hg.symm
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ D.β.1) ≫ D.α.1 := by simp
      _ = _ := by rw [hab]

/-- The arrow conditions shared by the `Ẽ` diagrams centred at `x₁`. -/
lemma common :
    (¬∃ g, D.β.1 ≫ g = γ) ∧ (¬∃ g, γ ≫ g = D.β.1) ∧ (¬∃ g, a₁.1 ≫ g = D.α.1 ≫ a₁.1) ∧
      (¬∃ g, (D.α.1 ≫ a₁.1) ≫ g = a₁.1) ∧ (¬∃ g, (D.α.1 ≫ a₁.1) ≫ g = a₁.1 ≫ D.β.1) ∧
      (¬∃ g, (D.α.1 ≫ a₁.1) ≫ g = a₁.1 ≫ γ) ∧ (¬∃ g, (D.β.1 ≫ D.α.1) ≫ g = γ) ∧
      (¬∃ g, γ ≫ g = D.β.1 ≫ D.α.1) ∧ (¬∃ g, g ≫ D.β.1 = D.β.1 ≫ D.α.1) ∧
      (¬∃ g, g ≫ (D.β.1 ≫ D.α.1) = D.β.1) ∧ ¬∃ g, g ≫ (D.β.1 ≫ D.α.1) = a₁.1 ≫ D.β.1 := by
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hL : LeftCancel P := hM.left
  have hα := D.α.2
  have hb := D.β.2
  have ha := a₁.2
  have hab := D.ab_eq hq a₁ hw
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src hq a₁ hw hM hMo hE hNTo hno f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt hq a₁ hw hM hMo hE hNTo hno f hf hs
  obtain ⟨g1, g2, g3, g4⟩ := D.exit_back hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ γ hγ hcx
  refine ⟨g3, g1, ?_, ?_, ?_, ?_, g4, g2, ?_, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_l ha.1 D.α.1 (𝟙 _) hα.2.1 (by simpa using hg)
    · exact hαa (by rw [← hg, D.Z_t hq a₁ hw hM hE g hgi])
  · rintro ⟨g, hg⟩
    exact sandwich_l ha.1 D.α.1 g hα.2.1 (by simp only [Category.assoc] at hg; exact hg.symm)
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hαα0 (by rw [← hab, ← hg, h, comp_zero])
    obtain ⟨m, rfl⟩ := D.mor_tx hq a₁ hw hMo hE g hg0
    refine sandwich_r hαα0 (𝟙 _) (D.α.1 ≫ rpow D.α.1 m) (not_isIso_comp_left' _ hα.2.1) ?_
    calc D.α.1 ≫ D.α.1 = a₁.1 ≫ D.β.1 := hab.symm
      _ = (D.α.1 ≫ a₁.1) ≫ D.β.1 ≫ rpow D.α.1 m := hg.symm
      _ = D.α.1 ≫ (a₁.1 ≫ D.β.1) ≫ rpow D.α.1 m := by simp
      _ = _ := by rw [hab]; simp
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ haγ (by rw [← hg, h, comp_zero])
    have hgi : ¬IsIso g := fun h ↦ hct (eq_of_isIso h).symm
    rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ g hg0 hgi with
      ⟨g', rfl⟩ | ⟨g', rfl⟩
    · have hg'i : ¬IsIso g' := fun h ↦ hcx (eq_of_isIso h).symm
      apply haγ
      rw [← hg, show (D.α.1 ≫ a₁.1) ≫ D.β.1 ≫ g' = D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ g' by
        simp only [Category.assoc]; rw [← Category.assoc a₁.1, hab]; simp,
        D.τ_right hq a₁ hw hM hMo hE hNTo hno g' hg'i]
    · exact sandwich_l haγ D.α.1 g' hα.2.1 (by simp only [Category.assoc] at hg ⊢; exact hg.symm)
  · rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_r hb.1 (𝟙 _) D.α.1 hα.2.1 (by simpa using hg)
    · exact hbα (by rw [← hg, D.Zd_t hq a₁ hw hMo hE g hgi])
  · rintro ⟨g, hg⟩
    exact sandwich_r hb.1 g D.α.1 hα.2.1 hg.symm
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hαα0 (by rw [← hab, ← hg, h, zero_comp])
    obtain ⟨m, rfl⟩ := D.mor_xt hq a₁ hw hM hE g hg0
    refine sandwich_r hαα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 ≫ D.α.1 = a₁.1 ≫ D.β.1 := hab.symm
      _ = (rpow D.α.1 m ≫ a₁.1) ≫ D.β.1 ≫ D.α.1 := hg.symm
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ D.β.1) ≫ D.α.1 := by simp
      _ = _ := by rw [hab]

/-- The only arrow into `x₁` is `a₁`. -/
lemma last_t {w : P} (g : w ⟶ D.t.out) (hg : g ≠ 0) (hgi : ¬IsIso g) : ∃ g', g = g' ≫ a₁.1 := by
  obtain ⟨c', r, e, he, rfl⟩ := exists_last' g hg hgi
  have hw2 := D.hw2 hq a₁ hw
  by_cases hc'x : c' = x.out
  · have he' : IsIrreducible (eqToHom hc'x.symm ≫ e) := isIrreducible_iso_comp _ he
    obtain ⟨m, hm⟩ := D.mor_xt hq a₁ hw hM hE _ he'.1
    rcases m with _ | m
    · refine ⟨r ≫ eqToHom hc'x, ?_⟩
      have : e = eqToHom hc'x ≫ a₁.1 := by
        calc e = eqToHom hc'x ≫ (eqToHom hc'x.symm ≫ e) := by simp
          _ = _ := by rw [hm]; simp
      rw [this, Category.assoc]
    · exfalso
      rcases he'.2.2 _ (rpow D.α.1 (m + 1)) a₁.1 hm with h | h
      · exact MildContour.rpow_not_isIso D.α.1 D.α.2.2.1 (m + 1) (by omega) h
      · exact a₁.2.2.1 h
  by_cases hc't : c' = D.t.out
  · exact (D.no_loop_x1 hq a₁ hw hM (⟨eqToHom hc't.symm ≫ e, isIrreducible_iso_comp _ he⟩ :
      D.t ⟶ D.t)).elim
  exact (D.no_entry_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ e he hc'x).elim

/-- **No morphism from outside back into `{x₀, x₁}`.** -/
lemma no_back : ∀ (n : ℕ) {z : P}, z ≠ x.out → z ≠ D.t.out →
    (∀ f : z ⟶ x.out, depth f ≤ n → f = 0) ∧ ∀ f : z ⟶ D.t.out, depth f ≤ n → f = 0 := by
  intro n
  induction n with
  | zero =>
    intro z hzx hzt
    refine ⟨fun f hd ↦ ?_, fun f hd ↦ ?_⟩
    · by_contra hf
      obtain ⟨c', r, e, he, rfl⟩ := exists_last' f hf (fun h ↦ hzx (eq_of_isIso h))
      have := depth_lt_comp_right r e hf he.2.1
      omega
    · by_contra hf
      obtain ⟨c', r, e, he, rfl⟩ := exists_last' f hf (fun h ↦ hzt (eq_of_isIso h))
      have := depth_lt_comp_right r e hf he.2.1
      omega
  | succ n ih =>
    intro z hzx hzt
    have hx : ∀ f : z ⟶ x.out, depth f ≤ n + 1 → f = 0 := by
      intro f hd
      by_contra hf
      rcases D.last_x hq a₁ hw hM hMo hE hNTo f hf (fun h ↦ hzx (eq_of_isIso h)) with
        ⟨g, rfl⟩ | ⟨g, rfl⟩
      · have := depth_lt_comp_right g D.α.1 hf D.α.2.2.1
        exact hf (by rw [(ih hzx hzt).1 g (by omega), zero_comp])
      · have := depth_lt_comp_right g D.β.1 hf D.β.2.2.1
        exact hf (by rw [(ih hzx hzt).2 g (by omega), zero_comp])
    refine ⟨hx, fun f hd ↦ ?_⟩
    by_contra hf
    obtain ⟨g, rfl⟩ := D.last_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ f hf
      (fun h ↦ hzt (eq_of_isIso h))
    have := depth_lt_comp_right g a₁.1 hf a₁.2.2.1
    exact hf (by rw [(ih hzx hzt).1 g (by omega), zero_comp])

lemma no_back_x {z : P} (hzx : z ≠ x.out) (hzt : z ≠ D.t.out) (f : z ⟶ x.out) : f = 0 :=
  (D.no_back hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ _ hzx hzt).1 f le_rfl

lemma no_back_t {z : P} (hzx : z ≠ x.out) (hzt : z ≠ D.t.out) (f : z ⟶ D.t.out) : f = 0 :=
  (D.no_back hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ _ hzx hzt).2 f le_rfl

/-- `α h ≠ a₁ γ` for `h : x₀ ⟶ c`. -/
lemma L_lemma : ¬∃ h, D.α.1 ≫ h = a₁.1 ≫ γ := by
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hL : LeftCancel P := hM.left
  have hab := D.ab_eq hq a₁ hw
  rintro ⟨h, hh⟩
  have h0 : h ≠ 0 := fun h' ↦ haγ (by rw [← hh, h', comp_zero])
  have hi : ¬IsIso h := fun h' ↦ hcx (eq_of_isIso h').symm
  rcases D.first_x hq a₁ hw hM hno h h0 hi with ⟨h', rfl⟩ | ⟨h', rfl⟩
  · have e : a₁.1 ≫ (D.β.1 ≫ h') = a₁.1 ≫ γ := by
      rw [← hh, ← Category.assoc, hab]; simp
    have e' := hL _ _ _ e (by rw [e]; exact haγ)
    rcases hγ.2.2 _ D.β.1 h' e'.symm with h'' | h''
    · exact D.β.2.2.1 h''
    · exact hcx (eq_of_isIso h'').symm
  · have h'0 : h' ≠ 0 := fun h'' ↦ h0 (by rw [h'', comp_zero])
    have h'i : ¬IsIso h' := fun h'' ↦ hct (eq_of_isIso h'').symm
    rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ h' h'0 h'i with
      ⟨g, rfl⟩ | ⟨g, rfl⟩
    · have gi : ¬IsIso g := fun h'' ↦ hcx (eq_of_isIso h'').symm
      apply haγ
      rw [← hh, show D.α.1 ≫ a₁.1 ≫ D.β.1 ≫ g = D.α.1 ≫ D.α.1 ≫ D.α.1 ≫ g by
        rw [← Category.assoc a₁.1, hab]; simp, D.τ_right hq a₁ hw hM hMo hE hNTo hno g gi]
    · refine sandwich_l haγ D.α.1 g D.α.2.2.1 ?_
      simp only [Category.assoc] at hh ⊢; exact hh.symm

/-- `β h ≠ γ g` when `a₁ γ g ≠ 0`. -/
lemma K_lemma {w : P} (g : c ⟶ w) (hg : a₁.1 ≫ γ ≫ g ≠ 0) : ¬∃ h, D.β.1 ≫ h = γ ≫ g := by
  obtain ⟨r1, r2, r3⟩ := D.rel hq a₁ hw hM hMo hE hNTo hno hM
  have hab := D.ab_eq hq a₁ hw
  rintro ⟨h, hh⟩
  have e : D.α.1 ≫ D.α.1 ≫ h = a₁.1 ≫ γ ≫ g := by rw [← Category.assoc, ← hab, Category.assoc, hh]
  have hwx : w ≠ x.out := by
    rintro rfl
    exact hg (by rw [D.no_back_x hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hcx hct g,
      comp_zero, comp_zero])
  have h0 : h ≠ 0 := fun h' ↦ hg (by rw [← e, h', comp_zero, comp_zero])
  rcases D.first_x hq a₁ hw hM hno h h0 (fun h' ↦ hwx (eq_of_isIso h').symm) with
    ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩
  · apply hg
    rw [← e, D.τ_right hq a₁ hw hM hMo hE hNTo hno h₁ (fun h' ↦ hwx (eq_of_isIso h').symm)]
  · apply hg
    rw [← e, show D.α.1 ≫ D.α.1 ≫ a₁.1 ≫ h₁ = (D.α.1 ≫ D.α.1 ≫ a₁.1) ≫ h₁ by simp, r2,
      zero_comp]

/-- **Radical endomorphisms of `c` kill `a₁ γ`** (an `Ã₄` cycle). -/
theorem rad_c (ℓ : c ⟶ c) (hℓ : ¬IsIso ℓ) : a₁.1 ≫ γ ≫ ℓ = 0 := by
  by_contra h3
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  obtain ⟨r1, r2, r3⟩ := D.rel hq a₁ hw hM hMo hE hNTo hno hM
  have hL : LeftCancel P := hM.left
  have hab := D.ab_eq hq a₁ hw
  have hα := D.α.2
  have hγℓ : γ ≫ ℓ ≠ 0 := fun h ↦ h3 (by rw [h, comp_zero])
  have hℓ0 : ℓ ≠ 0 := fun h ↦ h3 (by rw [h, comp_zero, comp_zero])
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src hq a₁ hw hM hMo hE hNTo hno f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt hq a₁ hw hM hMo hE hNTo hno f hf hs
  obtain ⟨g1, g2, g3, g4⟩ := D.exit_back hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ γ hγ hcx
  have K := D.K_lemma hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ ℓ h3
  have L := D.L_lemma hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have nbx := fun (g : c ⟶ x.out) ↦ D.no_back_x hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
    hcx hct g
  refine hM.not_pc7 _ hτn hτ0 (D.α.1 ≫ D.α.1) (a₁.1 ≫ γ) (D.β.1 ≫ D.α.1) γ ℓ
    PC7.not_isRepresentationFinite (nfs _ hℓ0 hcx) (nfs _ hγ.1 htx) (nfs _ hγℓ htx)
    (nfs _ hbα htx) (nft _ haγ hcx) (D.nftm_endo hq a₁ hw hM hMo hE hNTo hno _ hαα0 hαα)
    (not_isIso_comp_left' _ hα.2.1) (not_isIso_comp_left' _ a₁.2.2.1)
    (not_isIso_comp_left' _ D.β.2.2.1) hγ.2.1 hℓ g2 g4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨g, hg⟩; exact K ⟨D.α.1 ≫ g, by rw [← hg]; simp⟩
  · rintro ⟨g, hg⟩; exact hαα0 (by rw [← hg, nbx g, comp_zero])
  · rintro ⟨g, hg⟩
    have e : a₁.1 ≫ (D.β.1 ≫ g) = a₁.1 ≫ γ := by rw [← hg, ← Category.assoc, hab]
    exact g3 ⟨g, hL _ _ _ e (by rw [e]; exact haγ)⟩
  · rintro ⟨g, hg⟩
    have g0 : g ≠ 0 := fun h ↦ haγ (by rw [← hg, h, zero_comp])
    rcases D.first_x hq a₁ hw hM hno g g0 (fun h ↦ hcx (eq_of_isIso h).symm) with
      ⟨X, rfl⟩ | ⟨h, rfl⟩
    · exact L ⟨X ≫ ℓ, by rw [← hg]; simp⟩
    · have h0 : h ≠ 0 := fun h' ↦ g0 (by rw [h', comp_zero])
      rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ h h0
        (fun h' ↦ hct (eq_of_isIso h').symm) with ⟨X, rfl⟩ | ⟨h', rfl⟩
      · refine L ⟨D.α.1 ≫ X ≫ ℓ, ?_⟩
        rw [← hg, show (a₁.1 ≫ D.β.1 ≫ X) ≫ ℓ = (a₁.1 ≫ D.β.1) ≫ X ≫ ℓ by simp, hab]; simp
      · exact sandwich_r haγ (𝟙 _) (h' ≫ ℓ) (not_isIso_comp_right' _ hℓ) (by
          simp only [Category.assoc] at hg ⊢; rw [hg]; simp)
  · rintro ⟨g, hg⟩
    have g0 : g ≠ 0 := fun h ↦ hαα0 (by rw [← hg, h, zero_comp])
    obtain ⟨m, rfl⟩ := D.mor_xt hq a₁ hw hM hE g g0
    refine sandwich_r hαα0 (rpow D.α.1 m) D.α.1 hα.2.1 ?_
    calc D.α.1 ≫ D.α.1 = (rpow D.α.1 m ≫ a₁.1) ≫ D.β.1 ≫ D.α.1 := hg.symm
      _ = rpow D.α.1 m ≫ (a₁.1 ≫ D.β.1) ≫ D.α.1 := by simp
      _ = _ := by rw [hab]
  · rintro ⟨g, hg⟩
    have g0 : g ≠ 0 := fun h ↦ hγℓ (by rw [← hg, h, zero_comp])
    obtain ⟨m, rfl⟩ := D.mor_tx hq a₁ hw hMo hE g g0
    exact K ⟨rpow D.α.1 m ≫ a₁.1 ≫ γ, by rw [← hg]; simp⟩
  · rintro ⟨g, hg⟩; exact hℓ0 (by rw [← hg, nbx g, zero_comp])
  · rintro ⟨g, hg⟩
    have g0 : g ≠ 0 := fun h ↦ hbα (by rw [← hg, h, zero_comp])
    obtain ⟨m, rfl⟩ := D.mor_tx hq a₁ hw hMo hE g g0
    apply hbα
    have hc : rpow D.α.1 m ≫ D.α.1 ≫ D.α.1 = (D.α.1 ≫ D.α.1) ≫ rpow D.α.1 m := by
      rw [← Category.assoc, ← rpow_succ, ← rpow_succ, show m + 1 + 1 = 2 + m by omega, rpow_add]
      simp [rpow_succ]
    rw [← hg, Category.assoc, hc, ← Category.assoc, ← Category.assoc, Category.assoc D.β.1, r3,
      zero_comp]

/-- **`α a₁ γ = 0`** (an `Ẽ₇` centred at `x₁`). -/
theorem αaγ_zero : D.α.1 ≫ a₁.1 ≫ γ = 0 := by
  by_contra h6
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ :=
    D.common hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hL : LeftCancel P := hM.left
  have hab := D.ab_eq hq a₁ hw
  have hα := D.α.2
  have ha := a₁.2
  have hb := D.β.2
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src hq a₁ hw hM hMo hE hNTo hno f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt hq a₁ hw hM hMo hE hNTo hno f hf hs
  have L := D.L_lemma hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  refine hM.not_pc6 _ hτn hτ0 a₁.1 (D.α.1 ≫ a₁.1) γ D.β.1 (D.β.1 ≫ D.α.1) γ γ
    (nfs _ hb.1 htx) (nfs _ hγ.1 htx) (nft _ ha.1 htx)
    (by rw [hab]; exact D.nftm_endo hq a₁ hw hM hMo hE hNTo hno _ hαα0 hαα)
    (nft _ haγ hcx) (nft _ hαa htx) (nft _ (by simpa using h6) hcx) (nfs _ hγ.1 htx)
    (nfs _ hbα htx) (nfs _ hγ.1 htx)
    ha.2.1 (not_isIso_comp_left' _ hα.2.1) hγ.2.1 hb.2.1 (not_isIso_comp_left' _ hb.2.1)
    hγ.2.1 hγ.2.1 c1 c2 c3 ?_ c4 c5 c6 c7 c8 c9 c10 c11
  rintro ⟨g, hg⟩
  have g0 : g ≠ 0 := fun h ↦ h6 (by rw [← Category.assoc, ← hg, h, comp_zero])
  rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ g g0
    (fun h ↦ hct (eq_of_isIso h).symm) with ⟨X, rfl⟩ | ⟨h, rfl⟩
  · have e : D.α.1 ≫ (D.α.1 ≫ X) = D.α.1 ≫ (a₁.1 ≫ γ) := by
      rw [← Category.assoc, ← hab, Category.assoc, hg]; simp
    exact L ⟨X, hL _ _ _ e (by rw [e]; simpa using h6)⟩
  · by_cases hi : IsIso h
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso h
      exact sandwich_l haγ D.α.1 (𝟙 _) hα.2.1 (by simpa using hg)
    · apply h6
      rw [← Category.assoc, ← hg, D.rad_c hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ h hi]

/-- **Only `γ` enters `c`** (an `Ẽ₆` centred at `x₁`). -/
theorem into_c {w : P} (ζ : w ⟶ c) (hζ : IsIrreducible ζ) (hζγ : ¬∃ u, u ≫ γ = ζ) : False := by
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ :=
    D.common hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hL : LeftCancel P := hM.left
  have hab := D.ab_eq hq a₁ hw
  have hα := D.α.2
  have ha := a₁.2
  have hb := D.β.2
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src hq a₁ hw hM hMo hE hNTo hno f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt hq a₁ hw hM hMo hE hNTo hno f hf hs
  have L := D.L_lemma hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  refine hM.not_pc4 _ hτn hτ0 a₁.1 (D.α.1 ≫ a₁.1) D.β.1 (D.β.1 ≫ D.α.1) γ ζ
    (nfs _ hb.1 htx) (nfs _ hγ.1 htx) (nft _ ha.1 htx)
    (by rw [hab]; exact D.nftm_endo hq a₁ hw hM hMo hE hNTo hno _ hαα0 hαα)
    (nft _ haγ hcx) (nft _ hαa htx) (nfs _ hbα htx) (nft _ hζ.1 hcx)
    ha.2.1 (not_isIso_comp_left' _ hα.2.1) hb.2.1 (not_isIso_comp_left' _ hb.2.1)
    hγ.2.1 hζ.2.1 c1 c2 c3 c4 c5 c6 c9 c10 c11 hζγ ?_ ?_
  · rintro ⟨g, hg⟩
    rcases hγ.2.2 _ g ζ hg.symm with h | h
    · exact hζγ ⟨inv g, by rw [← hg]; simp⟩
    · exact hζ.2.1 h
  · rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · rcases hζ.2.2 _ (inv g ≫ a₁.1) γ (by rw [Category.assoc, ← hg]; simp) with h | h
      · exact ha.2.1 (ray_isIso_factors (inv g) a₁.1).2
      · exact hγ.2.1 h
    have g0 : g ≠ 0 := fun h ↦ haγ (by rw [← hg, h, zero_comp])
    rcases D.first_x hq a₁ hw hM hno g g0 hgi with ⟨X, rfl⟩ | ⟨h, rfl⟩
    · exact L ⟨X ≫ ζ, by rw [← hg]; simp⟩
    · have e := hL _ _ _ (show a₁.1 ≫ (h ≫ ζ) = a₁.1 ≫ γ by rw [← hg]; simp)
        (by rw [← Category.assoc, hg]; exact haγ)
      rcases hγ.2.2 _ h ζ e.symm with h' | h'
      · exact hζγ ⟨inv h, by rw [← e]; simp⟩
      · exact hζ.2.1 h'

/-- `β h ≠ γ g` when `γ g ≠ 0`, given `β α a₁ γ = 0`. -/
lemma K_gen (hs : (D.β.1 ≫ D.α.1 ≫ a₁.1) ≫ γ = 0) {w : P} (g : c ⟶ w) (hg : γ ≫ g ≠ 0) :
    ¬∃ h, D.β.1 ≫ h = γ ≫ g := by
  obtain ⟨r1, r2, r3⟩ := D.rel hq a₁ hw hM hMo hE hNTo hno hM
  have hab := D.ab_eq hq a₁ hw
  have hba := D.ba_zero hq a₁ hw hM hE
  rintro ⟨h, hh⟩
  have hwx : w ≠ x.out := by
    rintro rfl
    exact hg (by rw [D.no_back_x hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hcx hct g,
      comp_zero])
  have hwt : w ≠ D.t.out := by
    rintro rfl
    exact hg (by rw [D.no_back_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hcx hct g,
      comp_zero])
  have h0 : h ≠ 0 := fun h' ↦ hg (by rw [← hh, h', comp_zero])
  have ni : ∀ (f : x.out ⟶ w), ¬IsIso f := fun f h' ↦ hwx (eq_of_isIso h').symm
  rcases D.first_x hq a₁ hw hM hno h h0 (ni h) with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩
  · have h₁0 : h₁ ≠ 0 := fun h' ↦ h0 (by rw [h', comp_zero])
    rcases D.first_x hq a₁ hw hM hno h₁ h₁0 (ni h₁) with ⟨h₂, rfl⟩ | ⟨h₂, rfl⟩
    · exact hg (by rw [← hh, show D.β.1 ≫ D.α.1 ≫ D.α.1 ≫ h₂ = (D.β.1 ≫ D.α.1 ≫ D.α.1) ≫ h₂ by
        simp, r3, zero_comp])
    · have h₂0 : h₂ ≠ 0 := fun h' ↦ h₁0 (by rw [h', comp_zero])
      rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ h₂ h₂0
        (fun h' ↦ hwt (eq_of_isIso h').symm) with ⟨X, rfl⟩ | ⟨X, rfl⟩
      · apply hg
        rw [← hh, show D.β.1 ≫ D.α.1 ≫ a₁.1 ≫ D.β.1 ≫ X =
          (D.β.1 ≫ D.α.1 ≫ D.α.1) ≫ D.α.1 ≫ X by
            rw [← Category.assoc a₁.1, hab]; simp, r3, zero_comp]
      · apply hg
        rw [← hh, show D.β.1 ≫ D.α.1 ≫ a₁.1 ≫ γ ≫ X = ((D.β.1 ≫ D.α.1 ≫ a₁.1) ≫ γ) ≫ X by
          simp, hs, zero_comp]
  · exact hg (by rw [← hh, ← Category.assoc, hba, zero_comp])

/-- **Radical endomorphisms of `c` kill `γ`** (an `Ã₄` cycle), given `β α a₁ γ = 0`. -/
theorem loop_c (hs : (D.β.1 ≫ D.α.1 ≫ a₁.1) ≫ γ = 0) (ℓ : c ⟶ c) (hℓ : ¬IsIso ℓ) :
    γ ≫ ℓ = 0 := by
  by_contra hγℓ
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ :=
    D.common hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  obtain ⟨r1, r2, r3⟩ := D.rel hq a₁ hw hM hMo hE hNTo hno hM
  have hba := D.ba_zero hq a₁ hw hM hE
  have hα := D.α.2
  have hb := D.β.2
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src hq a₁ hw hM hMo hE hNTo hno f hf hs
  refine hM.not_pc8 _ hτn hτ0 D.α.1 D.β.1 (γ ≫ ℓ) D.β.1 γ PC8.not_isRepresentationFinite
    (nfs _ hγℓ htx) (nfs _ hb.1 htx) (nfs _ hbα htx) (nfs _ hγ.1 htx) (nfs _ hb.1 htx)
    (D.nftm_endo hq a₁ hw hM hMo hE hNTo hno _ hα.1 hα1)
    hα.2.1 hb.2.1 (not_isIso_comp_left' _ hγ.2.1) hb.2.1 hγ.2.1 ?_ ?_
    (D.K_gen hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hs ℓ hγℓ) c2 c1 ?_ ?_ ?_ c9 ?_
  · rintro ⟨g, hg⟩
    rcases hb.2.2 _ (γ ≫ ℓ) g hg.symm with h | h
    · exact hγ.2.1 (ray_isIso_factors γ ℓ).1
    · exact hcx (eq_of_isIso h)
  · rintro ⟨g, hg⟩
    exact hbα (by rw [← hg, D.no_back_x hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hcx hct g,
      comp_zero])
  · rintro ⟨g, hg⟩
    exact sandwich_r hγ.1 g ℓ hℓ hg.symm
  · rintro ⟨g, hg⟩
    by_cases hgi : IsIso g
    · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact sandwich_r hγ.1 (𝟙 _) ℓ hℓ (by simpa using hg)
    have g0 : g ≠ 0 := fun h ↦ hγℓ (by rw [← hg, h, zero_comp])
    rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ g g0 hgi with
      ⟨X, rfl⟩ | ⟨X, rfl⟩
    · have X0 : X ≠ 0 := fun h ↦ g0 (by rw [h, comp_zero])
      obtain ⟨m, rfl⟩ := D.mor_xt hq a₁ hw hM hE X X0
      apply hγℓ
      rw [← hg]
      rcases m with _ | _ | m
      · simp [hba]
      · simpa [rpow_succ] using hs
      · rw [show m + 1 + 1 = 2 + m by omega, rpow_add,
          show rpow D.α.1 2 = D.α.1 ≫ D.α.1 by simp [rpow_succ]]
        simp only [← Category.assoc]
        rw [show (D.β.1 ≫ D.α.1) ≫ D.α.1 = D.β.1 ≫ D.α.1 ≫ D.α.1 by simp, r3]; simp
    · exact hγℓ (by rw [← hg, D.no_back_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hcx hct X,
        comp_zero, zero_comp])
  · rintro ⟨g, hg⟩
    rcases hα.2.2 _ g D.β.1 hg.symm with h | h
    · exact htx (eq_of_isIso h).symm
    · exact hb.2.1 h
  · rintro ⟨g, hg⟩
    rcases hb.2.2 _ g D.α.1 hg.symm with h | h
    · exact htx (eq_of_isIso h)
    · exact hα.2.1 h

/-- `β α a₁ γ = 0` (from `α a₁ γ = 0`). -/
lemma sγ_zero : (D.β.1 ≫ D.α.1 ≫ a₁.1) ≫ γ = 0 := by
  simp only [Category.assoc]
  rw [D.αaγ_zero hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ, comp_zero]

/-- **Case 2: a tiny point at `x₁`** (`s = β α a₁ ≠ 0`, `t = γ`), given that `γ` kills the
arrows out of `c`. -/
theorem tiny_case2 (hγk : ∀ {v : P} (e : c ⟶ v), IsIrreducible e → γ ≫ e = 0)
    (hs0 : D.β.1 ≫ D.α.1 ≫ a₁.1 ≠ 0) : TinyAt (D.β.1 ≫ D.α.1 ≫ a₁.1) γ := by
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  obtain ⟨r1, r2, r3⟩ := D.rel hq a₁ hw hM hMo hE hNTo hno hM
  have hab := D.ab_eq hq a₁ hw
  have hba := D.ba_zero hq a₁ hw hM hE
  have hsγ := D.sγ_zero hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hα := D.α.2
  have ha := a₁.2
  have hb := D.β.2
  set s := D.β.1 ≫ D.α.1 ≫ a₁.1 with hs
  have hsR : RightDeep s := by
    intro w ζ hζ
    by_cases hζ0 : ζ = 0
    · rw [hζ0, comp_zero]
    rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ ζ hζ0 hζ with
      ⟨X, rfl⟩ | ⟨X, rfl⟩
    · rw [hs, show (D.β.1 ≫ D.α.1 ≫ a₁.1) ≫ D.β.1 ≫ X = (D.β.1 ≫ D.α.1 ≫ D.α.1) ≫ D.α.1 ≫ X by
        simp only [Category.assoc]; rw [← Category.assoc a₁.1, hab]; simp, r3, zero_comp]
    · rw [← Category.assoc, hsγ, zero_comp]
  have hsL : LeftDeep s := by
    intro u ζ hζ
    by_cases hζ0 : ζ = 0
    · rw [hζ0, zero_comp]
    obtain ⟨ζ', rfl⟩ := D.last_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ ζ hζ0 hζ
    rw [hs, show (ζ' ≫ a₁.1) ≫ D.β.1 ≫ D.α.1 ≫ a₁.1 = ζ' ≫ D.α.1 ≫ (D.α.1 ≫ D.α.1 ≫ a₁.1) by
      simp only [Category.assoc]; rw [← Category.assoc a₁.1, hab]; simp, r2, comp_zero, comp_zero]
  have hγR : RightDeep γ := by
    intro w ζ hζ
    by_cases hζ0 : ζ = 0
    · rw [hζ0, comp_zero]
    obtain ⟨d, e, r, he, rfl⟩ := exists_first_arrow' ζ hζ0 hζ
    rw [← Category.assoc, hγk e he, zero_comp]
  refine ⟨hs0, hγ.1, hct.symm, hct.symm, hsR, hsL, hγR, fun a' c' h ↦ hγ.2.2 _ a' c' h.symm,
    ?_, ?_, ?_⟩
  · intro y μ hμ hμd
    by_cases hμi : IsIso μ
    · exfalso
      obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso μ
      subst h
      exact hb.1 (by simpa using hμd D.β.1 hb.2.1)
    rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ μ hμ hμi with
      ⟨X, rfl⟩ | ⟨X, rfl⟩
    · have X0 : X ≠ 0 := fun h ↦ hμ (by rw [h, comp_zero])
      by_cases hXi : IsIso X
      · exfalso
        obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso X
        subst h
        exact hbα (by simpa using hμd D.α.1 hα.2.1)
      rcases D.first_x hq a₁ hw hM hno X X0 hXi with ⟨X', rfl⟩ | ⟨X', rfl⟩
      · have X'0 : X' ≠ 0 := fun h ↦ X0 (by rw [h, comp_zero])
        by_cases hX'i : IsIso X'
        · exfalso
          obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso X'
          subst h
          exact hs0 (by simpa using hμd a₁.1 ha.2.1)
        rcases D.first_x hq a₁ hw hM hno X' X'0 hX'i with ⟨Y, rfl⟩ | ⟨Y, rfl⟩
        · exact (hμ (by rw [← Category.assoc, ← Category.assoc, show (D.β.1 ≫ D.α.1) ≫ D.α.1 =
            D.β.1 ≫ D.α.1 ≫ D.α.1 by simp, r3, zero_comp])).elim
        · by_cases hYi : IsIso Y
          · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso Y
            exact Or.inl ⟨h.symm, by simp [hs]⟩
          · exact (hμ (by rw [show D.β.1 ≫ D.α.1 ≫ a₁.1 ≫ Y = s ≫ Y by simp [hs],
              hsR Y hYi])).elim
      · exact (hμ (by rw [← Category.assoc, hba, zero_comp])).elim
    · by_cases hXi : IsIso X
      · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso X
        exact Or.inr ⟨h.symm, by simp⟩
      · exact (hμ (hγR X hXi)).elim
  · intro w ν hν hνd
    by_cases hνi : IsIso ν
    · exfalso
      obtain ⟨h, hh⟩ := RayQuiver.eq_id_of_isIso ν
      have := hνd (a₁.1 ≫ eqToHom h.symm) (fun h' ↦ ha.2.1 (by
        have := (ray_isIso_factors a₁.1 (eqToHom h.symm)).1; exact this))
      rw [hh] at this
      exact ha.1 (by simpa using this)
    obtain ⟨ν', rfl⟩ := D.last_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ ν hν hνi
    have ν'0 : ν' ≠ 0 := fun h ↦ hν (by rw [h, zero_comp])
    by_cases hν'i : IsIso ν'
    · exfalso
      obtain ⟨h, hh⟩ := RayQuiver.eq_id_of_isIso ν'
      have := hνd (D.α.1 ≫ eqToHom h.symm) (fun h' ↦ hα.2.1 (by
        have := (ray_isIso_factors D.α.1 (eqToHom h.symm)).1; exact this))
      rw [hh] at this
      exact hαa (by simpa using this)
    rcases D.last_x hq a₁ hw hM hMo hE hNTo ν' ν'0 hν'i with ⟨ν'', rfl⟩ | ⟨ν'', rfl⟩
    · have ν''0 : ν'' ≠ 0 := fun h ↦ ν'0 (by rw [h, zero_comp])
      by_cases hν''i : IsIso ν''
      · exfalso
        obtain ⟨h, hh⟩ := RayQuiver.eq_id_of_isIso ν''
        have := hνd (D.β.1 ≫ eqToHom h.symm) (fun h' ↦ hb.2.1 (by
          have := (ray_isIso_factors D.β.1 (eqToHom h.symm)).1; exact this))
        rw [hh] at this
        exact hs0 (by simpa using this)
      rcases D.last_x hq a₁ hw hM hMo hE hNTo ν'' ν''0 hν''i with ⟨Y, rfl⟩ | ⟨Y, rfl⟩
      · exact (hν (by simp only [Category.assoc]; rw [r2, comp_zero])).elim
      · by_cases hYi : IsIso Y
        · obtain ⟨h, hh⟩ := RayQuiver.eq_id_of_isIso Y
          subst h
          exact ⟨rfl, by rw [hh]; simp [hs]⟩
        · exact (hν (by
            rw [show ((Y ≫ D.β.1) ≫ D.α.1) ≫ a₁.1 = Y ≫ s by simp [hs], hsL Y hYi])).elim
    · exact (hν (by rw [Category.assoc, hba, comp_zero])).elim
  · intro y ν hν
    by_cases hν0 : ν = 0
    · exact ⟨0, by rw [hν0, zero_comp]⟩
    obtain ⟨d, r, e, he, rfl⟩ := exists_last' ν hν0 hν
    by_cases h1 : ∃ u, u ≫ γ = e
    · obtain ⟨u, rfl⟩ := h1
      exact ⟨r ≫ u, by simp⟩
    · exact (D.into_c hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ e he h1).elim

/-- The targets of nonzero morphisms out of `x₀` and `x₁` are `x₀`, `x₁`, `c`. -/
lemma out_core (hγk : ∀ {v : P} (e : c ⟶ v), IsIrreducible e → γ ≫ e = 0) :
    ∀ n : ℕ, (∀ {w : P} (f : x.out ⟶ w), f ≠ 0 → depth f ≤ n → w = x.out ∨ w = D.t.out ∨ w = c) ∧
      ∀ {w : P} (f : D.t.out ⟶ w), f ≠ 0 → depth f ≤ n → w = x.out ∨ w = D.t.out ∨ w = c := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun f hf hd ↦ ?_, fun f hf hd ↦ ?_⟩
    · by_cases hi : IsIso f
      · exact Or.inl (eq_of_isIso hi).symm
      obtain ⟨d, e, r, he, rfl⟩ := exists_first_arrow' f hf hi
      have := depth_lt_comp_left e r hf he.2.1
      omega
    · by_cases hi : IsIso f
      · exact Or.inr (Or.inl (eq_of_isIso hi).symm)
      obtain ⟨d, e, r, he, rfl⟩ := exists_first_arrow' f hf hi
      have := depth_lt_comp_left e r hf he.2.1
      omega
  | succ n ih =>
    have hx : ∀ {w : P} (f : x.out ⟶ w), f ≠ 0 → depth f ≤ n + 1 →
        w = x.out ∨ w = D.t.out ∨ w = c := by
      intro w f hf hd
      by_cases hi : IsIso f
      · exact Or.inl (eq_of_isIso hi).symm
      rcases D.first_x hq a₁ hw hM hno f hf hi with ⟨f', rfl⟩ | ⟨f', rfl⟩
      · have := depth_lt_comp_left _ f' hf D.α.2.2.1
        exact ih.1 f' (fun h ↦ hf (by rw [h, comp_zero])) (by omega)
      · have := depth_lt_comp_left _ f' hf a₁.2.2.1
        exact ih.2 f' (fun h ↦ hf (by rw [h, comp_zero])) (by omega)
    refine ⟨hx, fun f hf hd ↦ ?_⟩
    by_cases hi : IsIso f
    · exact Or.inr (Or.inl (eq_of_isIso hi).symm)
    rcases D.first_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ f hf hi with
      ⟨f', rfl⟩ | ⟨f', rfl⟩
    · have := depth_lt_comp_left _ f' hf D.β.2.2.1
      exact ih.1 f' (fun h ↦ hf (by rw [h, comp_zero])) (by omega)
    · by_cases hfi : IsIso f'
      · exact Or.inr (Or.inr (eq_of_isIso hfi).symm)
      have f'0 : f' ≠ 0 := fun h ↦ hf (by rw [h, comp_zero])
      obtain ⟨d, e, r, he, rfl⟩ := exists_first_arrow' f' f'0 hfi
      exact (hf (by rw [← Category.assoc, hγk e he, zero_comp])).elim

/-- **Degenerate case with an exit at `c`: `c` is a split point.** -/
theorem split_c (hγk : ∀ {v : P} (e : c ⟶ v), IsIrreducible e → γ ≫ e = 0)
    {v : P} (ζ : c ⟶ v) (hζ : IsIrreducible ζ) : SplitAt ({x.out, D.t.out} : Set P) c := by
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have mem : ∀ {i : P}, i ∈ ({x.out, D.t.out} : Set P) ↔ i = x.out ∨ i = D.t.out :=
    fun {i} ↦ by simp
  have nbx := fun {z : P} (hzx : z ≠ x.out) (hzt : z ≠ D.t.out) (f : z ⟶ x.out) ↦
    D.no_back_x hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hzx hzt f
  have nbt := fun {z : P} (hzx : z ≠ x.out) (hzt : z ≠ D.t.out) (f : z ⟶ D.t.out) ↦
    D.no_back_t hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hzx hzt f
  have oc := D.out_core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hγk
  -- nonzero morphisms into `c` come from `x₀`, `x₁` or `c`
  have inc : ∀ {w : P} (f : w ⟶ c), f ≠ 0 → w = x.out ∨ w = D.t.out ∨ w = c := by
    intro w f hf
    by_cases hi : IsIso f
    · exact Or.inr (Or.inr (eq_of_isIso hi))
    obtain ⟨d, r, e, he, rfl⟩ := exists_last' f hf hi
    by_cases h1 : ∃ u, u ≫ γ = e
    · obtain ⟨u, rfl⟩ := h1
      by_contra hw'
      push Not at hw'
      exact hf (by rw [← Category.assoc, nbt hw'.1 hw'.2.1 (r ≫ u), zero_comp])
    · exact (D.into_c hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ e he h1).elim
  have endc : ∀ f : c ⟶ c, ¬IsIso f → f = 0 := by
    intro f hf
    by_contra hf0
    obtain ⟨d, r, e, he, rfl⟩ := exists_last' f hf0 hf
    by_cases h1 : ∃ u, u ≫ γ = e
    · obtain ⟨u, rfl⟩ := h1
      exact hf0 (by rw [← Category.assoc, nbt hcx hct (r ≫ u), zero_comp])
    · exact (D.into_c hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ e he h1).elim
  refine ⟨by rw [mem]; push Not; exact ⟨hcx, hct⟩, ?_, ?_, ?_, ?_, endc, ⟨D.t.out, by simp, γ, hγ.1⟩,
    ⟨v, ?_, ?_, ζ, hζ.1⟩⟩
  · intro i hi j hj hjc f
    by_contra hf
    rw [mem] at hi hj
    push Not at hj
    rcases hi with rfl | rfl
    · rcases (oc _).1 f hf le_rfl with h | h | h
      · exact hj.1 h
      · exact hj.2 h
      · exact hjc h
    · rcases (oc _).2 f hf le_rfl with h | h | h
      · exact hj.1 h
      · exact hj.2 h
      · exact hjc h
  · intro i hi hic j hj f
    rw [mem] at hi hj
    push Not at hi
    rcases hj with rfl | rfl
    · exact nbx hi.1 hi.2 f
    · exact nbt hi.1 hi.2 f
  · intro i hi hic f
    by_contra hf
    rw [mem] at hi
    push Not at hi
    rcases inc f hf with h | h | h
    · exact hi.1 h
    · exact hi.2 h
    · exact hic h
  · intro j hj f
    rw [mem] at hj
    rcases hj with rfl | rfl
    · exact nbx hcx hct f
    · exact nbt hcx hct f
  · rw [mem]
    rintro (rfl | rfl)
    · exact hζ.1 (nbx hcx hct ζ)
    · exact hζ.1 (nbt hcx hct ζ)
  · rintro rfl
    exact hζ.1 (endc ζ hζ.2.1)

/-- **`γ` kills every arrow out of `c`** (loops: `Ã₄`; other arrows: the thin diagram
`PC10`). -/
theorem γ_kill {v : P} (ζ : c ⟶ v) (hζ : IsIrreducible ζ) : γ ≫ ζ = 0 := by
  have hs := D.sγ_zero hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  by_cases hvc : v = c
  · subst hvc; exact D.loop_c hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hs ζ hζ.2.1
  by_contra hγζ
  obtain ⟨hτ0, hτn, hαα, hα1, hαa, hbα, htx⟩ :=
    D.core hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ :=
    D.common hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have hab := D.ab_eq hq a₁ hw
  have hba := D.ba_zero hq a₁ hw hM hE
  have hα := D.α.2
  have ha := a₁.2
  have hb := D.β.2
  have hαα0 : D.α.1 ≫ D.α.1 ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have nfs := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : s ≠ x.out) ↦
    D.nftm_src hq a₁ hw hM hMo hE hNTo hno f hf hs
  have nft := fun {s w : P} (f : s ⟶ w) (hf : f ≠ 0) (hs : w ≠ x.out) ↦
    D.nftm_tgt hq a₁ hw hM hMo hE hNTo hno f hf hs
  have ne := fun (f : x.out ⟶ x.out) (hf : f ≠ 0) (hne : f ≠ D.α.1 ≫ D.α.1 ≫ D.α.1) ↦
    D.nftm_endo hq a₁ hw hM hMo hE hNTo hno f hf hne
  have L := D.L_lemma hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ
  have n1 : ¬∃ g, a₁.1 ≫ g = D.α.1 := by
    rintro ⟨g, hg⟩
    rcases hα.2.2 _ a₁.1 g hg.symm with h | h
    · exact ha.2.1 h
    · exact htx (eq_of_isIso h)
  have n2 : ¬∃ g, D.α.1 ≫ g = a₁.1 := by
    rintro ⟨g, hg⟩
    rcases ha.2.2 _ D.α.1 g hg.symm with h | h
    · exact hα.2.1 h
    · exact htx (eq_of_isIso h).symm
  have n3 : ¬∃ g, g ≫ D.β.1 = D.α.1 := by
    rintro ⟨g, hg⟩
    rcases hα.2.2 _ g D.β.1 hg.symm with h | h
    · exact htx (eq_of_isIso h).symm
    · exact hb.2.1 h
  have n4 : ¬∃ g, g ≫ D.α.1 = D.β.1 := by
    rintro ⟨g, hg⟩
    rcases hb.2.2 _ g D.α.1 hg.symm with h | h
    · exact htx (eq_of_isIso h)
    · exact hα.2.1 h
  refine hM.not_pc10 _ hτn hτ0 D.α.1 a₁.1 D.α.1 a₁.1 D.β.1 γ D.β.1 γ ζ
    PC10.not_isRepresentationFinite hab hba (nfs _ hζ.1 hcx) (nfs _ hγ.1 htx) (nfs _ hγζ htx)
    (nfs _ hb.1 htx) (nfs _ hbα htx) (nfs _ hγ.1 htx) (nfs _ hb.1 htx) (nft _ haγ hcx)
    (nft _ ha.1 htx) (nft _ hαa htx) (ne _ hα.1 hα1) (ne _ hαα0 hαα) (nft _ ha.1 htx)
    (ne _ hα.1 hα1)
    hα.2.1 ha.2.1 hα.2.1 ha.2.1 hb.2.1 hγ.2.1 hb.2.1 hγ.2.1 hζ.2.1 c2 c8 c1
    (D.K_gen hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hs ζ hγζ) c2 c1 n1 c3 n2 L n1 n2
    n3 n3 c9 n4 n4

end Exit2

end PFData

variable (P) in
/-- **The exceptional (degenerate) penny-farthing** `Q₂'`: `n = 2`, no exit at `x₀`, an
exit `γ` at `x₁` into a sink `c`, `a₁ γ ≠ 0`, `β α a₁ = 0`. -/
def PFExc : Prop :=
  ∃ (x : RayVert P) (D : PFData x x) (_ : D.q = .nil) (a₁ : x ⟶ D.t)
    (_ : D.w' = Quiver.Path.nil.cons a₁) (c : P) (γ : D.t.out ⟶ c),
    IsIrreducible γ ∧ c ≠ x.out ∧ c ≠ D.t.out ∧ a₁.1 ≫ γ ≠ 0 ∧
      D.β.1 ≫ D.α.1 ≫ a₁.1 = 0 ∧ (∀ {y : RayVert P}, y ≠ x → y ≠ D.t → IsEmpty (x ⟶ y)) ∧
      ∀ {v : P} (e : c ⟶ v), ¬IsIrreducible e

namespace PFData

/-- **[mild] MIPF, case 2, ray level**: an open penny-farthing with `n = 2` and an exit only
at `x₁` gives a tiny point, a split point, or is the exceptional `Q₂'`. -/
theorem case2_exc {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) (a₁ : x ⟶ D.t)
    (hw : D.w' = Quiver.Path.nil.cons a₁) (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ)
    (hE : EndCyclic P) (hNT : NoTiny P) (hNTo : NoTiny Pᵒᵖ) (hNS : NoSplit P)
    (hno : ∀ {y : RayVert P}, y ≠ x → y ≠ D.t → IsEmpty (x ⟶ y))
    {c : P} (γ : D.t.out ⟶ c) (hγ : IsIrreducible γ) (hcx : c ≠ x.out) (hct : c ≠ D.t.out)
    (haγ : a₁.1 ≫ γ ≠ 0) : PFExc P := by
  have hγk := fun {v : P} (e : c ⟶ v) (he : IsIrreducible e) ↦
    D.γ_kill hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ e he
  by_cases hs0 : D.β.1 ≫ D.α.1 ≫ a₁.1 = 0
  · by_cases hex : ∃ (v : P) (e : c ⟶ v), IsIrreducible e
    · obtain ⟨v, e, he⟩ := hex
      exact (hNS _ _ (D.split_c hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hγk e he)).elim
    · push Not at hex
      exact ⟨x, D, hq, a₁, hw, c, γ, hγ, hcx, hct, haγ, hs0, hno, fun e ↦ hex _ e⟩
  · exact (hNT _ _ (D.tiny_case2 hq a₁ hw hM hMo hE hNTo hno γ hγ hcx hct haγ hγk hs0)).elim

end PFData

end RayCat

end LargeIndecomposable
