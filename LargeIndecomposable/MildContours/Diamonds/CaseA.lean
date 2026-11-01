module

public import LargeIndecomposable.MildContours.Diamonds.Trichotomy
public import LargeIndecomposable.Cleaving.Shapes.ShapeSE6B
public import LargeIndecomposable.Cleaving.Shapes.ShapeSE7
public import LargeIndecomposable.Cleaving.Shapes.ShapeDM5B
public import LargeIndecomposable.Cleaving.Shapes.ShapeIn3

/-!
# [mild] diamonds, case (A): `γ = ξ ≫ ω'`

The case where `v` runs through the full cycle `ρ = ω' ≫ α` at its end is
impossible. This replaces [mild] Lemma LDI, whose proof treats only short `v`.

* `dual_db`: the dual dumb-bell `d ≫ ξ = ξ ≫ ρ^k` with `ρ` not irreducible
  (crown `Ã(ρ, g, d, ξ)` and an `Ẽ₆` for `k = 1`, an `Ẽ₆` for `k ≥ 2`).
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


section RpowNorm

variable {C' : Type*} [Category C'] {a z : C'} (e : a ⟶ a)

lemma rpow_comp_rpow (m n : ℕ) : rpow e m ≫ rpow e n = rpow e (m + n) := (rpow_add e m n).symm

lemma rpow_comp_rpow_assoc (m n : ℕ) (h : a ⟶ z) : rpow e m ≫ rpow e n ≫ h = rpow e (m + n) ≫ h := by
  rw [← Category.assoc, rpow_comp_rpow]

lemma self_comp_rpow (n : ℕ) : e ≫ rpow e n = rpow e (n + 1) := (rpow_succ' e n).symm

lemma self_comp_rpow_assoc (n : ℕ) (h : a ⟶ z) : e ≫ rpow e n ≫ h = rpow e (n + 1) ≫ h := by
  rw [← Category.assoc, self_comp_rpow]

lemma rpow_comp_self (n : ℕ) : rpow e n ≫ e = rpow e (n + 1) := rfl

lemma rpow_comp_self_assoc (n : ℕ) (h : a ⟶ z) : rpow e n ≫ e ≫ h = rpow e (n + 1) ≫ h := by
  rw [← Category.assoc, rpow_comp_self]

lemma self_comp_self : e ≫ e = rpow e 2 := by simp [rpow_succ]

lemma self_comp_self_assoc (h : a ⟶ z) : e ≫ e ≫ h = rpow e 2 ≫ h := by
  rw [← Category.assoc, self_comp_self]

end RpowNorm

/-- Normalize a composite of powers of one endomorphism. -/
macro "rnorm" : tactic => `(tactic| (
  try simp only [Category.assoc, rpow_comp_rpow, rpow_comp_rpow_assoc, self_comp_rpow,
    self_comp_rpow_assoc, rpow_comp_self, rpow_comp_self_assoc]
  try simp only [self_comp_self, self_comp_self_assoc]
  try simp only [Category.assoc, rpow_comp_rpow, rpow_comp_rpow_assoc, self_comp_rpow,
    self_comp_rpow_assoc, rpow_comp_self, rpow_comp_self_assoc]
  try (congr 1; omega)))

/-- A proper factor of a nonzero morphism does not factor through it. -/
lemma nfp {a b c d : P} {f : a ⟶ d} (hf0 : f ≠ 0) (p : a ⟶ b) (g : b ⟶ c) (q : c ⟶ d)
    (hpq : ¬IsIso p ∨ ¬IsIso q) (h : p ≫ g ≫ q = f) : ¬FactorsThroughMorphism f g := by
  rcases hpq with hp | hq
  · exact not_ftm_mid hf0 hp h
  · exact MildContour.not_ftm_mid_right hf0 hq h

lemma not_isIso_comp_left' {a b c : P} {f : a ⟶ b} (g : b ⟶ c) (hf : ¬IsIso f) :
    ¬IsIso (f ≫ g) := fun h ↦ hf (ray_isIso_factors f g).1

lemma not_isIso_comp_right' {a b c : P} (f : a ⟶ b) {g : b ⟶ c} (hg : ¬IsIso g) :
    ¬IsIso (f ≫ g) := fun h ↦ hg (ray_isIso_factors f g).2

lemma eq_of_isIso {a b : P} {f : a ⟶ b} (h : IsIso f) : a = b :=
  IsRayCategory.skeletal ⟨asIso f⟩

/-- **The dual dumb-bell with a non-irreducible loop at `y`**: an arrow `ξ : x ⟶ y` and
a loop arrow `d` at `x` with `d ≫ ξ = ξ ≫ ρ^k`, where `ρ = ω' ≫ α` generates the radical
at `y` and `ω'` is not invertible. -/
theorem dual_db (hM : MildHyp k P) {x y a : P} (ξ : x ⟶ y) (d : x ⟶ x) (ω' : y ⟶ a)
    (α : a ⟶ y) (ρ : y ⟶ y) (hρdef : ρ = ω' ≫ α) (hξ : IsIrreducible ξ) (hd : IsIrreducible d)
    (hω' : ¬IsIso ω') (hα : ¬IsIso α) (hρ : ∀ f : y ⟶ y, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow ρ n)
    (n : ℕ) (hn : 0 < n) (hdξ : d ≫ ξ = ξ ≫ rpow ρ n)
    (hτ0 : ξ ≫ rpow ρ (n + 1) ≠ 0) (hL2 : ¬∃ g, g ≫ ξ = ρ)
    (hap1 : ¬∃ g, g ≫ ξ = α) (hap2 : ¬∃ g, g ≫ α = ξ) : False := by
  have hL : LeftCancel P := hM.left
  have hR : RightCancel P := hM.right
  have hρn : ¬IsIso ρ := by rw [hρdef]; exact not_isIso_comp_right' ω' hα
  have hξn := hξ.2.1
  have hdn := hd.2.1
  -- no irreducible loop at `y`
  have hloop : ∀ f : y ⟶ y, IsIrreducible f → False := by
    intro f hf
    obtain ⟨m, hm, hfm⟩ := hρ f hf.2.1
    obtain ⟨m, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rcases hf.2.2 _ ω' (α ≫ rpow ρ m) (by rw [hfm, rpow_succ', hρdef, Category.assoc]) with h | h
    · exact hω' h
    · exact hα (ray_isIso_factors α (rpow ρ m)).1
  have hxy : x ≠ y := by
    intro h; subst h; exact hloop ξ hξ
  have hiso_xy : ∀ c : x ⟶ y, ¬IsIso c := fun c h ↦ hxy (eq_of_isIso h)
  have hiso_yx : ∀ c : y ⟶ x, ¬IsIso c := fun c h ↦ hxy (eq_of_isIso h).symm
  have hrpn : ∀ j, 0 < j → ¬IsIso (rpow ρ j) := fun j hj ↦ MildContour.rpow_not_isIso ρ hρn j hj
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = ξ ≫ rpow ρ (n + 1) := ⟨_, rfl⟩
  rw [← hτdef] at hτ0
  have hτd : τ = d ≫ ξ ≫ ρ := by rw [hτdef, rpow_succ, ← Category.assoc, ← hdξ, Category.assoc]
  have hdξ0 : d ≫ ξ ≠ 0 := fun h ↦ hτ0 (by rw [hτd, ← Category.assoc, h, zero_comp])
  have hτn : ¬IsIso τ := by rw [hτdef]; exact not_isIso_comp_left' _ hξn
  have hτv : τ = ξ ≫ ω' ≫ α ≫ rpow ρ n := by rw [hτdef, rpow_succ', hρdef]; simp
  have hXY4 : ¬FactorsThroughMorphism τ ((ξ ≫ ω') ≫ α) :=
    nfp hτ0 (𝟙 _) ((ξ ≫ ω') ≫ α) (rpow ρ n) (Or.inr (hrpn n hn)) (by rw [hτv]; simp)
  have hcommon : ∀ (dd : x ⟶ x), ¬IsIso dd → ¬FactorsThroughMorphism τ dd →
      (¬∃ g, ξ ≫ g = dd) → (¬∃ g, dd ≫ g = ξ) → (¬∃ g, dd ≫ g = ξ ≫ ω') →
      (¬∃ g, dd ≫ g = ξ ≫ (ω' ≫ α)) → False := by
    intro dd hddn hdd0 h1 h2 h3 h4
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hτv2 : τ = ξ ≫ ω' ≫ α ≫ ω' ≫ α ≫ rpow ρ j := by
      rw [hτv, hj, rpow_succ', hρdef]; simp
    have hξω' : ¬IsIso (ξ ≫ ω') := not_isIso_comp_left' _ hξn
    have hL2' : ¬∃ g, g ≫ ξ = ω' ≫ α := by rw [← hρdef]; exact hL2
    refine hM.not_se6b τ hτn hτ0 ω' α ω' α ξ dd
      (nfp hτ0 ξ ω' (α ≫ ω' ≫ α ≫ rpow ρ j) (Or.inl hξn) (by rw [hτv2]))
      (nfp hτ0 ξ (ω' ≫ α) (ω' ≫ α ≫ rpow ρ j) (Or.inl hξn) (by rw [hτv2]; simp))
      (nfp hτ0 (ξ ≫ ω') α (ω' ≫ α ≫ rpow ρ j) (Or.inl hξω') (by rw [hτv2]; simp))
      (nfp hτ0 (ξ ≫ ω') (α ≫ ω') (α ≫ rpow ρ j) (Or.inl hξω') (by rw [hτv2]; simp))
      (nfp hτ0 (ξ ≫ ω') ((α ≫ ω') ≫ α) (rpow ρ j) (Or.inl hξω') (by rw [hτv2]; simp))
      (nfp hτ0 ξ ω' (α ≫ ω' ≫ α ≫ rpow ρ j) (Or.inl hξn) (by rw [hτv2]))
      (nfp hτ0 ξ (ω' ≫ α) (ω' ≫ α ≫ rpow ρ j) (Or.inl hξn) (by rw [hτv2]; simp))
      (nfp hτ0 ξ ((ω' ≫ α) ≫ ω') (α ≫ rpow ρ j) (Or.inl hξn) (by rw [hτv2]; simp))
      (nfp hτ0 ξ (((ω' ≫ α) ≫ ω') ≫ α) (rpow ρ j) (Or.inl hξn) (by rw [hτv2]; simp))
      (nfp hτ0 (ξ ≫ ω' ≫ α ≫ ω') α (rpow ρ j) (Or.inl (not_isIso_comp_left' _ hξn))
        (by rw [hτv2]; simp))
      (nfp hτ0 (𝟙 _) ξ (ω' ≫ α ≫ rpow ρ n) (Or.inr (not_isIso_comp_left' _ hω'))
        (by rw [hτv]; simp))
      (nfp hτ0 (𝟙 _) (ξ ≫ ω') (α ≫ rpow ρ n) (Or.inr (not_isIso_comp_left' _ hα))
        (by rw [hτv]; simp))
      hXY4 hdd0 hω' hα hω' hα hξn hddn h1 h2 h3 h4 hap2 hap1 hL2'
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · -- `n ≥ 2`: the `Ẽ₆` with `d`
    obtain ⟨j, hj⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    refine hcommon d hdn (nfp hτ0 (𝟙 _) d (ξ ≫ ρ) (Or.inr (not_isIso_comp_left' _ hξn))
      (by rw [hτd]; simp)) ?_ ?_ ?_ ?_
    · rintro ⟨g, hg⟩
      rcases hd.2.2 _ ξ g hg.symm with h | h
      · exact hξn h
      · exact hiso_yx g h
    · rintro ⟨g, hg⟩
      rcases hξ.2.2 _ d g hg.symm with h | h
      · exact hdn h
      · exact hiso_xy g h
    · rintro ⟨g, hg⟩
      have e : d ≫ (g ≫ α ≫ rpow ρ (j + 1)) = d ≫ ξ := by
        rw [hdξ, hj, rpow_succ' ρ (j + 1), hρdef]
        rw [← Category.assoc, ← Category.assoc, hg]; simp
      have e2 := hL _ _ _ e (by rw [e]; exact hdξ0)
      rcases hξ.2.2 _ (g ≫ α) (rpow ρ (j + 1)) (by rw [← e2]; simp) with h | h
      · exact hα (ray_isIso_factors g α).2
      · exact hrpn (j + 1) (by omega) h
    · rintro ⟨g, hg⟩
      have e : d ≫ (g ≫ rpow ρ (j + 1)) = d ≫ ξ := by
        rw [hdξ, hj, rpow_succ' ρ (j + 1), ← Category.assoc, hg, hρdef]; simp
      have e2 := hL _ _ _ e (by rw [e]; exact hdξ0)
      rcases hξ.2.2 _ g (rpow ρ (j + 1)) e2.symm with h | h
      · exact hiso_xy g h
      · exact hrpn (j + 1) (by omega) h
  · -- `n = 1`: the crown excludes `ξ ≫ g = d ≫ d`, then the `Ẽ₆` with `d ≫ d`
    obtain rfl : n = 1 := by omega
    have hdξ1 : d ≫ ξ = ξ ≫ ρ := by rw [hdξ]; simp [rpow_succ]
    have hτdd : τ = (d ≫ d) ≫ ξ := by rw [hτd, ← hdξ1]; simp
    have hdd0 : d ≫ d ≠ 0 := fun h ↦ hτ0 (by rw [hτdd, h, zero_comp])
    have hddn : ¬IsIso (d ≫ d) := not_isIso_comp_left' _ hdn
    have hcrown : ¬∃ g, ξ ≫ g = d ≫ d := by
      rintro ⟨g, hg⟩
      have hτρ : τ = ξ ≫ ρ ≫ ρ := by rw [hτdef]; simp [rpow_succ]
      refine hM.not_crown2 τ hτn hτ0 ρ ξ d g
        (nfp hτ0 ξ ρ ρ (Or.inl hξn) (by rw [hτρ]))
        (nfp hτ0 (𝟙 _) ξ (ρ ≫ ρ) (Or.inr (not_isIso_comp_left' _ hρn)) (by rw [hτρ]; simp))
        (nfp hτ0 (𝟙 _) d (ξ ≫ ρ) (Or.inr (not_isIso_comp_left' _ hξn)) (by rw [hτd]; simp))
        ?_ hL2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rintro ⟨u, v, huv⟩
        have e : d ≫ d = (ξ ≫ u) ≫ (d ≫ d) ≫ (ξ ≫ v) := by
          conv_lhs => rw [← hg, huv, hτdd]
          simp
        obtain ⟨-, h⟩ := IsRayCategory.eq_id_of_two_sided _ hdd0 _ _ e
        haveI : IsIso (ξ ≫ v) := by rw [h]; infer_instance
        exact hξn (ray_isIso_factors ξ v).1
      · rintro ⟨c, hc⟩
        rcases hξ.2.2 _ (c ≫ ω') α (by rw [← hc, hρdef]; simp) with h | h
        · exact hω' (ray_isIso_factors c ω').2
        · exact hα h
      · rintro ⟨c, hc⟩
        rcases hd.2.2 _ c g hc.symm with h | h
        · exact hiso_xy c h
        · exact hiso_yx g h
      · rintro ⟨c, hc⟩
        have e : (ξ ≫ c) ≫ d = d ≫ d := by rw [Category.assoc, hc, hg]
        have e2 := hR _ _ _ e (by rw [e]; exact hdd0)
        rcases hd.2.2 _ ξ c e2.symm with h | h
        · exact hξn h
        · exact hiso_yx c h
      · rintro ⟨c, hc⟩
        rcases hd.2.2 _ ξ c hc.symm with h | h
        · exact hξn h
        · exact hiso_yx c h
      · rintro ⟨c, hc⟩
        rcases hξ.2.2 _ d c hc.symm with h | h
        · exact hdn h
        · exact hiso_xy c h
      · rintro ⟨c, hc⟩
        have e : d ≫ ξ = d ≫ (d ≫ c) := by rw [hdξ1, ← hc, ← Category.assoc, hg]; simp
        have e2 := hL _ _ _ e hdξ0
        rcases hξ.2.2 _ d c e2 with h | h
        · exact hdn h
        · exact hiso_xy c h
      · rintro ⟨c, hc⟩
        have e : d ≫ (ξ ≫ c) = d ≫ d := by rw [← Category.assoc, hdξ1, Category.assoc, hc, hg]
        have e2 := hL _ _ _ e (by rw [e]; exact hdd0)
        rcases hd.2.2 _ ξ c e2.symm with h | h
        · exact hξn h
        · exact hiso_yx c h
    refine hcommon (d ≫ d) hddn (nfp hτ0 (𝟙 _) (d ≫ d) ξ (Or.inr hξn) (by rw [hτdd]; simp))
      hcrown ?_ ?_ ?_
    · rintro ⟨g, hg⟩
      rcases hξ.2.2 _ d (d ≫ g) (by rw [← hg]; simp) with h | h
      · exact hdn h
      · exact hdn (ray_isIso_factors d g).1
    · rintro ⟨g, hg⟩
      have e : d ≫ (d ≫ g ≫ α) = d ≫ ξ := by
        rw [hdξ1, hρdef, ← Category.assoc, ← Category.assoc, hg]; simp
      have e2 := hL _ _ _ e (by rw [e]; exact hdξ0)
      rcases hξ.2.2 _ d (g ≫ α) e2.symm with h | h
      · exact hdn h
      · exact hα (ray_isIso_factors g α).2
    · rintro ⟨g, hg⟩
      have e : d ≫ (d ≫ g) = d ≫ ξ := by rw [hdξ1, ← Category.assoc, hg, hρdef]
      have e2 := hL _ _ _ e (by rw [e]; exact hdξ0)
      rcases hξ.2.2 _ d g e2.symm with h | h
      · exact hdn h
      · exact hiso_xy g h

lemma isIrreducible_iso_comp {a b c : P} (e : a ⟶ b) [IsIso e] {f : b ⟶ c} (hf : IsIrreducible f) :
    IsIrreducible (e ≫ f) := by
  refine ⟨fun h ↦ hf.1 (by simpa using congrArg (inv e ≫ ·) h), fun h ↦ hf.2.1 ?_, ?_⟩
  · exact (ray_isIso_factors e f).2
  · intro z g h hgh
    rcases hf.2.2 z (inv e ≫ g) h (by rw [Category.assoc, ← hgh]; simp) with h1 | h1
    · left; have : IsIso (e ≫ inv e ≫ g) := inferInstance; simpa using this
    · exact Or.inr h1

lemma isIrreducible_comp_iso {a b c : P} {f : a ⟶ b} (hf : IsIrreducible f) (e : b ⟶ c) [IsIso e] :
    IsIrreducible (f ≫ e) := by
  refine ⟨fun h ↦ hf.1 (by simpa using congrArg (· ≫ inv e) h), fun h ↦ hf.2.1 ?_, ?_⟩
  · exact (ray_isIso_factors f e).1
  · intro z g h hgh
    rcases hf.2.2 z g (h ≫ inv e) (by rw [← Category.assoc, ← hgh]; simp) with h1 | h1
    · exact Or.inl h1
    · right; have : IsIso ((h ≫ inv e) ≫ e) := inferInstance; simpa using this

/-- Arrows into the same vertex that coincide are not apart. -/
lemma not_apart_of_heq {a b y : RayVert P} (e : a ⟶ y) (f : b ⟶ y) (h : a = b) (he : HEq e f) :
    ¬ArrowsApart e f := by
  subst h
  obtain rfl := eq_of_heq he
  exact fun hap ↦ hap.1 ⟨𝟙 _, Category.id_comp _⟩

/-- A path whose value is neither invertible nor irreducible has at least two arrows. -/
lemma two_le_length {a b : RayVert P} (p : Quiver.Path a b) (hi : ¬IsIso (pathVal p))
    (hirr : ¬IsIrreducible (pathVal p)) : 2 ≤ p.length := by
  match p with
  | .nil => exact absurd isIso_pathVal_nil hi
  | .cons .nil e =>
      exact absurd (by change IsIrreducible (𝟙 _ ≫ e.1); rw [Category.id_comp]; exact e.2) hirr
  | .cons (.cons _ _) _ => simp

/-- The value of a one-arrow path is irreducible. -/
lemma irr_of_length_one {a b : RayVert P} (p : Quiver.Path a b) (h : p.length = 1) :
    IsIrreducible (pathVal p) := by
  match p, h with
  | .cons .nil e, _ => change IsIrreducible (𝟙 _ ≫ e.1); rw [Category.id_comp]; exact e.2

/-- The path `(a b)^j` around a two-arrow cycle. -/
def cycPath {y s : RayVert P} (a : y ⟶ s) (b : s ⟶ y) : ℕ → Quiver.Path y y
  | 0 => .nil
  | j + 1 => ((cycPath a b j).cons a).cons b

lemma pathVal_cycPath {y s : RayVert P} (a : y ⟶ s) (b : s ⟶ y) :
    ∀ j, pathVal (cycPath a b j) = rpow (a.1 ≫ b.1) j
  | 0 => rfl
  | j + 1 => by
      change (pathVal (cycPath a b j) ≫ a.1) ≫ b.1 = _
      rw [pathVal_cycPath a b j, rpow_succ, Category.assoc]

namespace MildContour

variable {x y : P} (C : MildContour x y)

/-- **Case (A) with `ξ` invertible** (`x = y`, `γ = ω'`): the `D̃₄` star at `y`. -/
theorem caseA_eq (hM : MildHyp k P) (hxy : x = y) (hγ : eqToHom hxy ≫ C.ρ = C.γ ≫ C.α.1) :
    False := by
  subst hxy
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hgd := C.γ_δ_apart hR hL
  simp only [eqToHom_refl, Category.id_comp] at hγ
  have hvw : C.γ ≫ C.α.1 = C.δ ≫ C.β.1 := C.hval
  have hτ1 : C.τ = C.γ ≫ C.α.1 ≫ C.γ ≫ C.α.1 := by rw [C.τ_eq_v, hγ]
  have hτ2 : C.τ = C.γ ≫ C.α.1 ≫ C.δ ≫ C.β.1 := by rw [C.τ_eq_v, hγ, hvw]
  have hτ3 : C.τ = C.δ ≫ C.β.1 ≫ C.γ ≫ C.α.1 := by rw [C.τ_eq_w, hγ]
  have hτ4 : C.τ = C.δ ≫ C.β.1 ≫ C.δ ≫ C.β.1 := by rw [C.τ_eq_w, hγ, hvw]
  have hγn := C.γ_not_isIso hR
  have hδn := C.δ_not_isIso hR
  exact hM.not_md4b C.τ C.τ_not_isIso hτ0 C.α.1 C.β.1 C.γ C.δ (C.ftm_γ hR) (C.ftm_δ hR)
    (C.ftm_α hR) (nfp hτ0 C.γ (C.α.1 ≫ C.γ) C.α.1 (Or.inl hγn) (by rw [hτ1]; simp))
    (nfp hτ0 C.γ (C.α.1 ≫ C.δ) C.β.1 (Or.inl hγn) (by rw [hτ2]; simp))
    (C.ftm_β hR) (nfp hτ0 C.δ (C.β.1 ≫ C.γ) C.α.1 (Or.inl hδn) (by rw [hτ3]; simp))
    (nfp hτ0 C.δ (C.β.1 ≫ C.δ) C.β.1 (Or.inl hδn) (by rw [hτ4]; simp))
    C.α.2.2.1 C.β.2.2.1 hγn hδn hgd.2 hgd.1 hap.2 hap.1

/-- **Case (A): `ω'` is an arrow** (otherwise a star `Ẽ₇` at `y`). -/
theorem caseA_irr (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω')
    (hρ : C.ρ = ω' ≫ C.α.1) {ξ : x ⟶ y} (hξ : ¬IsIso ξ) (hγ : ξ ≫ ω' = C.γ) :
    IsIrreducible ω' := by
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hαn := C.α.2.2.1
  have hω'0 : ω' ≠ 0 := fun h ↦ C.τ_ne_zero (by
    change C.ω ≫ C.ρ = 0; rw [hρ, h, zero_comp, comp_zero])
  by_contra hirr
  have : ∃ (z : P) (g : y ⟶ z) (ε : z ⟶ C.sv), ω' = g ≫ ε ∧ ¬IsIso g ∧ ¬IsIso ε := by
    by_contra hc
    push Not at hc
    exact hirr ⟨hω'0, hω', fun z g ε h ↦ by
      by_contra hh; push Not at hh; exact hh.2 (hc z g ε h hh.1)⟩
  obtain ⟨z, g, ε, hge, hg, hε⟩ := this
  have hτv : C.τ = ξ ≫ g ≫ ε ≫ C.α.1 ≫ g ≫ ε ≫ C.α.1 := by
    rw [C.τ_eq_v, ← hγ, hρ, hge]; simp
  have hτw : C.τ = C.δ ≫ C.β.1 ≫ g ≫ ε ≫ C.α.1 := by rw [C.τ_eq_w, hρ, hge]; simp
  have hδn := C.δ_not_isIso hR
  have nl : ∀ {s : P} (p : x ⟶ s), ¬IsIso p → ¬IsIso p := fun _ h ↦ h
  have hL2 : ∀ h : z ⟶ C.sw, h ≫ C.β.1 = ε ≫ C.α.1 → False := fun h hh ↦
    C.not_ρ_factor_both hM hρ (ω'' := g ≫ h) (by rw [hρ, hge, Category.assoc, Category.assoc, hh])
  have pξ := not_isIso_comp_left' g hξ
  have pξg := not_isIso_comp_left' ε pξ
  have pξgε := not_isIso_comp_left' C.α.1 pξg
  have pξgεα := not_isIso_comp_left' g pξgε
  have pξgεαg := not_isIso_comp_left' ε pξgεα
  refine hM.not_se7 C.τ C.τ_not_isIso hτ0 g ε C.α.1 C.β.1 g ε C.α.1
    (nfp hτ0 (ξ ≫ g ≫ ε ≫ C.α.1) g (ε ≫ C.α.1) (Or.inl (by simpa using pξgε)) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g ≫ ε ≫ C.α.1) (g ≫ ε) C.α.1 (Or.inl (by simpa using pξgε)) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g ≫ ε ≫ C.α.1) ((g ≫ ε) ≫ C.α.1) (𝟙 _) (Or.inl (by simpa using pξgε))
      (by rw [hτv]; simp))
    (C.ftm_α hR)
    (nfp hτ0 (ξ ≫ g ≫ ε) (C.α.1 ≫ g) (ε ≫ C.α.1) (Or.inl (by simpa using pξg)) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g ≫ ε) ((C.α.1 ≫ g) ≫ ε) C.α.1 (Or.inl (by simpa using pξg)) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g ≫ ε) (((C.α.1 ≫ g) ≫ ε) ≫ C.α.1) (𝟙 _) (Or.inl (by simpa using pξg))
      (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g) ε (C.α.1 ≫ g ≫ ε ≫ C.α.1) (Or.inl pξ) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g) (ε ≫ C.α.1) (g ≫ ε ≫ C.α.1) (Or.inl pξ) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g) ((ε ≫ C.α.1) ≫ g) (ε ≫ C.α.1) (Or.inl pξ) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g) (((ε ≫ C.α.1) ≫ g) ≫ ε) C.α.1 (Or.inl pξ) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g) ((((ε ≫ C.α.1) ≫ g) ≫ ε) ≫ C.α.1) (𝟙 _) (Or.inl pξ) (by rw [hτv]; simp))
    (nfp hτ0 ξ g (ε ≫ C.α.1 ≫ g ≫ ε ≫ C.α.1) (Or.inl hξ) (by rw [hτv]))
    (nfp hτ0 ξ (g ≫ ε) (C.α.1 ≫ g ≫ ε ≫ C.α.1) (Or.inl hξ) (by rw [hτv]; simp))
    (nfp hτ0 ξ ((g ≫ ε) ≫ C.α.1) (g ≫ ε ≫ C.α.1) (Or.inl hξ) (by rw [hτv]; simp))
    (nfp hτ0 ξ (((g ≫ ε) ≫ C.α.1) ≫ g) (ε ≫ C.α.1) (Or.inl hξ) (by rw [hτv]; simp))
    (nfp hτ0 ξ ((((g ≫ ε) ≫ C.α.1) ≫ g) ≫ ε) C.α.1 (Or.inl hξ) (by rw [hτv]; simp))
    (nfp hτ0 ξ (((((g ≫ ε) ≫ C.α.1) ≫ g) ≫ ε) ≫ C.α.1) (𝟙 _) (Or.inl hξ) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g ≫ ε ≫ C.α.1 ≫ g) ε C.α.1 (Or.inl (by simpa using pξgεα)) (by rw [hτv]; simp))
    (nfp hτ0 (ξ ≫ g ≫ ε ≫ C.α.1 ≫ g) (ε ≫ C.α.1) (𝟙 _) (Or.inl (by simpa using pξgεα))
      (by rw [hτv]; simp))
    (C.ftm_α hR) (C.ftm_β hR)
    (nfp hτ0 C.δ (C.β.1 ≫ g) (ε ≫ C.α.1) (Or.inl hδn) (by rw [hτw]; simp))
    (nfp hτ0 C.δ ((C.β.1 ≫ g) ≫ ε) C.α.1 (Or.inl hδn) (by rw [hτw]; simp))
    (by have := C.ftm_βρ hR; rw [hρ, hge] at this; simpa using this)
    hg hε hαn C.β.2.2.1 hg hε hαn hap.2 hap.1
    (fun ⟨h, hh⟩ ↦ hL2 h hh)
    (fun ⟨h, hh⟩ ↦ C.not_ρ_factor_both hM hρ (ω'' := h) (by rw [hh, hρ, hge]))


/-- If `γ` is not irreducible, `δ` is an arrow (the star `Ẽ₆`). -/
lemma δ_irr (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    (hγ : ¬IsIrreducible C.γ) : IsIrreducible C.δ := by
  have hR : RightCancel P := hM.right
  have hv := two_le_length C.v' (C.γ_not_isIso hR) hγ
  have hw := C.w'_pos hR
  have hw1 : C.w'.length = 1 := by
    by_contra h
    exact C.star_e6 hM hω' hρ hv (by omega)
  exact irr_of_length_one C.w' hw1

/-- An irreducible loop at `y` is impossible when `ρ = ω' ≫ α` with `ω'` not invertible. -/
lemma no_irr_loop {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1) (f : y ⟶ y)
    (hf : IsIrreducible f) : False := by
  obtain ⟨m, hm, hfm⟩ := C.hρ f hf.2.1
  obtain ⟨m, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rcases hf.2.2 _ ω' (C.α.1 ≫ rpow C.ρ m) (by rw [hfm, rpow_succ', hρ, Category.assoc]) with h | h
  · exact hω' h
  · exact C.α.2.2.1 (ray_isIso_factors C.α.1 (rpow C.ρ m)).1

/-- An arrow into `y` from `y` or an arrow `x ⟶ y` with `x = y` is impossible; in particular
an arrow `b ⟶ y` with an invertible morphism `y ⟶ b` or `b ⟶ y`. -/
lemma no_iso_to_sw {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    (g : y ⟶ C.sw) (hg : IsIso g) : False := by
  have h := eq_of_isIso hg
  have hb : IsIrreducible (g ≫ C.β.1) := isIrreducible_iso_comp g C.β.2
  exact C.no_irr_loop hω' hρ _ hb

lemma no_iso_from_sw {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    (g : C.sw ⟶ y) (hg : IsIso g) : False :=
  C.no_iso_to_sw hω' hρ (inv g) inferInstance

/-- **Case (A), `ξ` invertible, `ω = ρ^n` with `n ≥ 2`**: a `D̃₅` ([mild] figure 2.6, third
diagram, and a variant for `n ≥ 3`). -/
theorem caseA_iso_long (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω'i : IsIrreducible ω')
    (hρ : C.ρ = ω' ≫ C.α.1) (hxy : x = y) (n : ℕ) (hn : 2 ≤ n)
    (hω : C.ω = eqToHom hxy ≫ rpow C.ρ n) : False := by
  subst hxy
  simp only [eqToHom_refl, Category.id_comp] at hω
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hω' := hω'i.2.1
  have hαn := C.α.2.2.1
  have hβn := C.β.2.2.1
  have hρn := C.ρ_not_isIso
  have hrpn : ∀ j, 0 < j → ¬IsIso (rpow C.ρ j) := fun j hj ↦ rpow_not_isIso C.ρ hρn j hj
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  -- `γ = ρ^(j+1) ≫ ω'`
  have hγ : C.γ = rpow C.ρ (j + 1) ≫ ω' := by
    apply hR _ _ C.α.1
    · change C.ω = _; rw [hω, Category.assoc, ← hρ, ← rpow_succ]
    · change C.ω ≠ 0; exact C.h0
  have hγirr : ¬IsIrreducible C.γ := by
    intro h
    rcases h.2.2 _ (rpow C.ρ (j + 1)) ω' hγ with h1 | h1
    · exact hrpn (j + 1) (by omega) h1
    · exact hω' h1
  have hδ := C.δ_irr hM hω' hρ hγirr
  have hτ : C.τ = rpow C.ρ (j + 3) := by change C.ω ≫ C.ρ = _; rw [hω, ← rpow_succ]
  have hωδ : rpow C.ρ (j + 2) = C.δ ≫ C.β.1 := by rw [← hω]; exact C.ω_eq_w
  have hL2 : ∀ g, g ≫ C.β.1 = C.ρ → False := fun g hg ↦
    C.not_ρ_factor_both hM hρ (ω'' := g) hg.symm
  -- `ρ` never factors through `δ` on the left in the needed ways
  have hds : ¬∃ g, C.δ ≫ g = C.ρ := by
    rintro ⟨g, hg⟩
    have e : C.δ ≫ (g ≫ rpow C.ρ (j + 1)) = C.δ ≫ C.β.1 := by
      rw [← hωδ, ← Category.assoc, hg, ← rpow_succ']
    have e2 := hL _ _ _ e (by rw [e, ← hωδ, ← hω]; exact C.h0)
    rcases C.β.2.2.2 _ g (rpow C.ρ (j + 1)) e2.symm with h | h
    · exact C.no_iso_from_sw hω' hρ g h |>.elim
    · exact hrpn (j + 1) (by omega) h
  have hsd : ¬∃ g, C.ρ ≫ g = C.δ := by
    rintro ⟨g, hg⟩
    rcases hδ.2.2 _ ω' (C.α.1 ≫ g) (by rw [← hg, hρ, Category.assoc]) with h | h
    · exact hω' h
    · exact hαn (ray_isIso_factors C.α.1 g).1
  have hsβ : ¬∃ g, g ≫ C.ρ = C.β.1 := by
    rintro ⟨g, hg⟩
    rcases C.β.2.2.2 _ (g ≫ ω') C.α.1 (by rw [← hg, hρ, Category.assoc]) with h | h
    · exact hω' (ray_isIso_factors g ω').2
    · exact hαn h
  have hτn : ¬IsIso C.τ := C.τ_not_isIso
  have hδn := hδ.2.1
  have hρa : ω' ≫ C.α.1 = C.ρ := hρ.symm
  have hρa' : ∀ {z : P} (h : x ⟶ z), ω' ≫ C.α.1 ≫ h = C.ρ ≫ h := fun h ↦ by
    rw [← Category.assoc, hρa]
  rcases Nat.lt_or_ge 0 j with hj | hj
  · -- `n ≥ 3`: leaf `ρ`
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine hM.not_dm5b C.τ hτn hτ0 C.ρ C.δ C.ρ C.β.1 ω'
      (C.ftm_δ hR) C.ftm_ρ
      (nfp hτ0 (rpow C.ρ (i + 2)) (C.ρ ≫ ω') C.α.1
        (Or.inl (hrpn _ (by omega))) (by rw [hτ]; simp only [Category.assoc, hρa]; rnorm))
      (nfp hτ0 (rpow C.ρ (i + 3)) ω' C.α.1 (Or.inl (hrpn _ (by omega)))
        (by rw [hτ]; simp only [hρa]; rnorm))
      C.ftm_ρ
      (nfp hτ0 (𝟙 _) (C.ρ ≫ C.δ) C.β.1 (Or.inr hβn)
        (by rw [hτ, rpow_succ', hωδ]; simp))
      (nfp hτ0 (rpow C.ρ (i + 1)) (C.ρ ≫ C.ρ) C.ρ (Or.inl (hrpn _ (by omega)))
        (by rw [hτ]; rnorm))
      (nfp hτ0 (rpow C.ρ (i + 1)) ((C.ρ ≫ C.ρ) ≫ ω') C.α.1
        (Or.inl (hrpn _ (by omega))) (by rw [hτ]; simp only [Category.assoc, hρa]; rnorm))
      (C.ftm_β hR)
      (nfp hτ0 C.δ (C.β.1 ≫ ω') C.α.1 (Or.inl hδn)
        (by rw [hτ, show C.δ ≫ (C.β.1 ≫ ω') ≫ C.α.1 = (C.δ ≫ C.β.1) ≫ (ω' ≫ C.α.1) by simp,
              ← hωδ, hρa]; rnorm))
      hρn hδn hρn hβn hω' hds ?_ hsd hsβ (fun ⟨g, hg⟩ ↦ hL2 g hg) ?_
    · -- `δ ≫ g = ρ ≫ ω'`
      rintro ⟨g, hg⟩
      have e : C.δ ≫ (g ≫ C.α.1 ≫ rpow C.ρ (i + 1)) = C.δ ≫ C.β.1 := by
        rw [← hωδ, ← Category.assoc, hg]; simp only [Category.assoc, hρa']; rnorm
      have e2 := hL _ _ _ e (by rw [e, ← hωδ, ← hω]; exact C.h0)
      rcases C.β.2.2.2 _ (g ≫ C.α.1) (rpow C.ρ (i + 1)) (by rw [← e2, Category.assoc]) with h | h
      · exact hαn (ray_isIso_factors g C.α.1).2
      · exact hrpn _ (by omega) h
    · -- `g ≫ β = ρ ≫ ρ`
      rintro ⟨g, hg⟩
      have e : (rpow C.ρ (i + 1) ≫ g) ≫ C.β.1 = C.δ ≫ C.β.1 := by
        rw [← hωδ, Category.assoc, hg]; rnorm
      have e2 := hR _ _ _ e (by rw [e, ← hωδ, ← hω]; exact C.h0)
      rcases hδ.2.2 _ (rpow C.ρ (i + 1)) g e2.symm with h | h
      · exact hrpn _ (by omega) h
      · exact C.no_iso_to_sw hω' hρ g h
  · -- `n = 2`: leaf `α`
    obtain rfl : j = 0 := by omega
    refine hM.not_dm5b C.τ hτn hτ0 C.α.1 C.δ C.ρ C.β.1 ω'
      (C.ftm_δ hR) C.ftm_ρ
      (nfp hτ0 (𝟙 _) (C.ρ ≫ ω') (C.α.1 ≫ C.ρ) (Or.inr (not_isIso_comp_left' _ hαn))
        (by rw [hτ]; simp only [Category.id_comp, Category.assoc, hρa']; rnorm))
      (nfp hτ0 (rpow C.ρ 2) ω' C.α.1 (Or.inl (hrpn _ (by omega)))
        (by rw [hτ]; simp only [hρa]; rnorm))
      (C.ftm_α hR)
      (nfp hτ0 ω' (C.α.1 ≫ C.δ) C.β.1 (Or.inl hω')
        (by rw [hτ, show 0 + 3 = 1 + 2 by rfl, ← rpow_comp_rpow, hωδ]
            simp only [Category.assoc, hρa']; simp [rpow_succ]))
      (C.ftm_αρ hR)
      (nfp hτ0 ω' ((C.α.1 ≫ C.ρ) ≫ ω') C.α.1 (Or.inl hω')
        (by rw [hτ]; simp only [Category.assoc, hρa, hρa']; rnorm))
      (C.ftm_β hR)
      (nfp hτ0 C.δ (C.β.1 ≫ ω') C.α.1 (Or.inl hδn)
        (by rw [hτ, show C.δ ≫ (C.β.1 ≫ ω') ≫ C.α.1 = (C.δ ≫ C.β.1) ≫ (ω' ≫ C.α.1) by simp,
              ← hωδ, hρa]; rnorm))
      hαn hδn hρn hβn hω' hds ?_ hsd hsβ (fun ⟨g, hg⟩ ↦ hL2 g hg) ?_
    · rintro ⟨g, hg⟩
      have e : C.δ ≫ (g ≫ C.α.1) = C.δ ≫ C.β.1 := by
        rw [← hωδ, ← Category.assoc, hg]; simp only [Category.assoc, hρa]; rnorm
      have e2 := hL _ _ _ e (by rw [e, ← hωδ, ← hω]; exact C.h0)
      exact hap.2 ⟨g, e2⟩
    · rintro ⟨g, hg⟩
      have e : (ω' ≫ g) ≫ C.β.1 = C.δ ≫ C.β.1 := by
        rw [← hωδ, Category.assoc, hg, ← Category.assoc, hρa]; rnorm
      have e2 := hR _ _ _ e (by rw [e, ← hωδ, ← hω]; exact C.h0)
      rcases hδ.2.2 _ ω' g e2.symm with h | h
      · exact hω' h
      · rcases C.β.2.2.2 _ (inv g ≫ C.α.1) C.ρ (by rw [Category.assoc, ← hg]; simp) with h1 | h1
        · exact hαn (ray_isIso_factors (inv g) C.α.1).2
        · exact hρn h1


/-- **The arrow before a common final segment ending in `α` is determined** (path
uniqueness): if `g₁ ≫ e₁ ≫ σα = ω = g₂ ≫ e₂ ≫ σα`, then `e₁ = e₂`. -/
theorem last_arrow_eq (hM : MildHyp k P) {c₁ c₂ m : RayVert P} (g₁ : x ⟶ c₁.out) (e₁ : c₁ ⟶ m)
    (g₂ : x ⟶ c₂.out) (e₂ : c₂ ⟶ m) (σ : Quiver.Path m (RayVert.mk C.sv))
    (h₁ : g₁ ≫ e₁.1 ≫ pathVal (σ.cons C.α) = C.ω) (h₂ : g₂ ≫ e₂.1 ≫ pathVal (σ.cons C.α) = C.ω) :
    c₁ = c₂ ∧ HEq e₁ e₂ := by
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  have key : ∀ {c : RayVert P} (g : x ⟶ c.out) (e : c ⟶ m),
      g ≫ e.1 ≫ pathVal (σ.cons C.α) = C.ω →
      ∃ hg : g ≠ 0, (((pathOf g hg).cons e).comp σ).cons C.α = C.v'.cons C.α := by
    intro c g e h
    have hg : g ≠ 0 := fun h0 ↦ C.h0 (by change C.ω = 0; rw [← h, h0, zero_comp])
    refine ⟨hg, ?_⟩
    have hval : pathVal ((((pathOf g hg).cons e).comp σ).cons C.α) = pathVal (C.v'.cons C.α) := by
      change (pathVal (((pathOf g hg).cons e).comp σ)) ≫ C.α.1 = C.ω
      rw [pathVal_comp, ← h]
      change ((pathVal (pathOf g hg) ≫ e.1) ≫ pathVal σ) ≫ C.α.1 = g ≫ e.1 ≫ pathVal σ ≫ C.α.1
      rw [pathVal_pathOf]; simp
    rcases hM.path_unique C.hval C.h0 C.hni C.ρ_not_isIso C.hωρ _ hval with h1 | h1
    · exact h1
    · exact absurd hap (not_apart_of_heq _ _ (Quiver.Path.obj_eq_of_cons_eq_cons h1)
        (Quiver.Path.hom_heq_of_cons_eq_cons h1))
  obtain ⟨hg₁, k₁⟩ := key g₁ e₁ h₁
  obtain ⟨hg₂, k₂⟩ := key g₂ e₂ h₂
  have h12 := k₁.trans k₂.symm
  have h3 := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h12)
  have h4 := Quiver.Path.comp_inj_left.1 h3
  exact ⟨Quiver.Path.obj_eq_of_cons_eq_cons h4, Quiver.Path.hom_heq_of_cons_eq_cons h4⟩

/-- `γ = ξ ≫ ρ^(n-1) ≫ ω'` when `ω = ξ ≫ ρ^n`. -/
lemma γ_eq (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hρ : C.ρ = ω' ≫ C.α.1) (n : ℕ) {ξ : x ⟶ y}
    (hω : C.ω = ξ ≫ rpow C.ρ (n + 1)) : C.γ = ξ ≫ rpow C.ρ n ≫ ω' := by
  apply hM.right _ _ C.α.1
  · change C.ω = _; rw [hω, rpow_succ, hρ]; simp
  · change C.ω ≠ 0; exact C.h0

/-- **Case (A), `ξ = ζ ≫ β`.** -/
theorem caseA_beta (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω'i : IsIrreducible ω')
    (hρ : C.ρ = ω' ≫ C.α.1) (n : ℕ) {ξ : x ⟶ y} (hω : C.ω = ξ ≫ rpow C.ρ (n + 1))
    {ζ : x ⟶ C.sw} (hξ : ξ = ζ ≫ C.β.1) : False := by
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hω' := hω'i.2.1
  have hαn := C.α.2.2.1
  have hβn := C.β.2.2.1
  have hρn := C.ρ_not_isIso
  have hrpn : ∀ j, 0 < j → ¬IsIso (rpow C.ρ j) := fun j hj ↦ rpow_not_isIso C.ρ hρn j hj
  have hρa : ω' ≫ C.α.1 = C.ρ := hρ.symm
  have hρa' : ∀ {z : P} (h : y ⟶ z), ω' ≫ C.α.1 ≫ h = C.ρ ≫ h := fun h ↦ by
    rw [← Category.assoc, hρa]
  have hτ : C.τ = ξ ≫ rpow C.ρ (n + 2) := by change C.ω ≫ C.ρ = _; rw [hω, Category.assoc]; rfl
  have hL2 : ∀ g, g ≫ C.β.1 = C.ρ → False := fun g hg ↦
    C.not_ρ_factor_both hM hρ (ω'' := g) hg.symm
  by_cases hζ : IsIso ζ
  · -- the dual dumb-bell
    have hξirr : IsIrreducible ξ := by rw [hξ]; exact isIrreducible_iso_comp ζ C.β.2
    have hγ := C.γ_eq hM hρ n hω
    have hγirr : ¬IsIrreducible C.γ := by
      intro h
      rcases h.2.2 _ ξ (rpow C.ρ n ≫ ω') hγ with h1 | h1
      · exact hξirr.2.1 h1
      · exact hω' (ray_isIso_factors (rpow C.ρ n) ω').2
    have hδ := C.δ_irr hM hω' hρ hγirr
    refine dual_db hM ξ (C.δ ≫ inv ζ) ω' C.α.1 C.ρ hρ hξirr (isIrreducible_comp_iso hδ (inv ζ))
      hω' hαn C.hρ (n + 1) (by omega) ?_ ?_ ?_ ?_ ?_
    · calc (C.δ ≫ inv ζ) ≫ ξ = C.δ ≫ C.β.1 := by rw [hξ]; simp
        _ = C.ω := C.ω_eq_w.symm
        _ = _ := hω
    · rw [← hτ]; exact hτ0
    · rintro ⟨g, hg⟩; exact hL2 (g ≫ ζ) (by rw [Category.assoc, ← hξ, hg])
    · rintro ⟨g, hg⟩; exact hap.1 ⟨g ≫ ζ, by rw [Category.assoc, ← hξ, hg]⟩
    · rintro ⟨g, hg⟩; exact hap.2 ⟨inv ζ ≫ g, by rw [Category.assoc, hg, hξ]; simp⟩
  · -- an `Ẽ₆` star
    have hτζ : C.τ = ζ ≫ C.β.1 ≫ ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1) := by
      rw [hτ, hξ, rpow_succ', hρ]; simp
    have hτζ' : C.τ = ζ ≫ C.β.1 ≫ ω' ≫ C.α.1 ≫ ω' ≫ C.α.1 ≫ rpow C.ρ n := by
      rw [hτζ, rpow_succ', hρ]; simp
    have hζβ := not_isIso_comp_left' C.β.1 hζ
    obtain ⟨a, ha⟩ : ∃ a : (RayVert.mk y : RayVert P) ⟶ RayVert.mk C.sv, a.1 = ω' :=
      ⟨⟨ω', hω'i⟩, rfl⟩
    have hσ : C.ω = ζ ≫ C.β.1 ≫ pathVal (((cycPath a C.α n).cons a).cons C.α) := by
      change C.ω = ζ ≫ C.β.1 ≫ pathVal (cycPath a C.α (n + 1))
      rw [pathVal_cycPath, ha, hω, hξ, ← hρ]; simp
    refine hM.not_se6 C.τ C.τ_not_isIso hτ0 ω' C.α.1 ζ C.β.1 ω' C.α.1
      (nfp hτ0 (ζ ≫ C.β.1) ω' (C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inl hζβ) (by rw [hτζ]; simp))
      (by rw [hρa]; exact C.ftm_ρ) (C.ftm_α hR)
      (nfp hτ0 (ζ ≫ C.β.1 ≫ ω') (C.α.1 ≫ ω') (C.α.1 ≫ rpow C.ρ n)
        (Or.inl (by simpa using not_isIso_comp_left' ω' hζβ)) (by rw [hτζ']; simp))
      (by rw [Category.assoc, hρa]; exact C.ftm_αρ hR)
      (nfp hτ0 (ζ ≫ C.β.1) ω' (C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inl hζβ) (by rw [hτζ]; simp))
      (by rw [hρa]; exact C.ftm_ρ)
      (nfp hτ0 (ζ ≫ C.β.1) ((ω' ≫ C.α.1) ≫ ω') (C.α.1 ≫ rpow C.ρ n) (Or.inl hζβ)
        (by rw [hτζ']; simp))
      (nfp hτ0 (ζ ≫ C.β.1) (((ω' ≫ C.α.1) ≫ ω') ≫ C.α.1) (rpow C.ρ n) (Or.inl hζβ)
        (by rw [hτζ']; simp))
      (C.ftm_β hR)
      (nfp hτ0 ζ (C.β.1 ≫ ω') (C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inl hζ) (by rw [hτζ]; simp))
      (by rw [Category.assoc, hρa]; exact C.ftm_βρ hR)
      (nfp hτ0 (𝟙 _) ζ (C.β.1 ≫ ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1))
        (Or.inr (not_isIso_comp_left' _ hβn)) (by rw [hτζ]; simp))
      (nfp hτ0 (𝟙 _) (ζ ≫ C.β.1) (ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1))
        (Or.inr (not_isIso_comp_left' _ hω')) (by rw [hτζ]; simp))
      (nfp hτ0 (𝟙 _) ((ζ ≫ C.β.1) ≫ ω') (C.α.1 ≫ rpow C.ρ (n + 1))
        (Or.inr (not_isIso_comp_left' _ hαn)) (by rw [hτζ]; simp))
      (nfp hτ0 (𝟙 _) (((ζ ≫ C.β.1) ≫ ω') ≫ C.α.1) (rpow C.ρ (n + 1))
        (Or.inr (hrpn _ (by omega))) (by rw [hτζ]; simp))
      (C.ftm_α hR) hω' hαn hζ hβn hω' hαn hap.2 ?_ hap.1 (fun ⟨g, hg⟩ ↦ hL2 g (hg.trans hρa))
    rintro ⟨g, hg⟩
    have h1 : g ≫ C.α.1 ≫ pathVal (((cycPath a C.α n).cons a).cons C.α) = C.ω := by
      rw [hσ, ← Category.assoc, hg, Category.assoc]
    obtain ⟨he, hhe⟩ := C.last_arrow_eq hM g C.α ζ C.β _ h1 hσ.symm
    exact not_apart_of_heq _ _ he hhe hap


/-- A nonzero non-invertible morphism is a path value ending with an arrow. -/
lemma exists_last_arrow {a b : P} (f : a ⟶ b) (hf0 : f ≠ 0) (hf : ¬IsIso f) :
    ∃ (c : RayVert P) (p : Quiver.Path (RayVert.mk a) c) (e : c ⟶ RayVert.mk b),
      f = pathVal p ≫ e.1 := by
  obtain ⟨c, p, e, hp⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons _).1
    (Nat.pos_iff_ne_zero.1 (length_pathOf_pos f hf0 hf))
  refine ⟨c, p, e, ?_⟩
  rw [← pathVal_pathOf f hf0, hp]; rfl

/-- **Case (A), `ξ = ζ ≫ α`** ([mild] figure 2.6, first and second diagrams). -/
theorem caseA_alpha (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω'i : IsIrreducible ω')
    (hρ : C.ρ = ω' ≫ C.α.1) (n : ℕ) {ξ : x ⟶ y} (hω : C.ω = ξ ≫ rpow C.ρ (n + 1))
    (hmax : ¬∃ ξ', ξ = ξ' ≫ C.ρ) {ζ : x ⟶ C.sv} (hξ : ξ = ζ ≫ C.α.1) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hω' := hω'i.2.1
  have hαn := C.α.2.2.1
  have hβn := C.β.2.2.1
  have hρn := C.ρ_not_isIso
  have hrpn : ∀ j, 0 < j → ¬IsIso (rpow C.ρ j) := fun j hj ↦ rpow_not_isIso C.ρ hρn j hj
  have hρa : ω' ≫ C.α.1 = C.ρ := hρ.symm
  have hρa' : ∀ {z : P} (h : y ⟶ z), ω' ≫ C.α.1 ≫ h = C.ρ ≫ h := fun h ↦ by
    rw [← Category.assoc, hρa]
  have hτ : C.τ = ξ ≫ rpow C.ρ (n + 2) := by change C.ω ≫ C.ρ = _; rw [hω, Category.assoc]; rfl
  have hξn : ¬IsIso ξ := by rw [hξ]; exact not_isIso_comp_right' _ hαn
  have hL2 : ∀ g, g ≫ C.β.1 = C.ρ → False := fun g hg ↦
    C.not_ρ_factor_both hM hρ (ω'' := g) hg.symm
  have hδn := C.δ_not_isIso hR
  have hωδ : C.δ ≫ C.β.1 = ξ ≫ rpow C.ρ (n + 1) := by rw [← hω]; exact C.ω_eq_w.symm
  have hτ1 : C.τ = ξ ≫ ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1) := by
    rw [hτ, show n + 2 = 1 + (n + 1) by omega, ← rpow_comp_rpow]; simp [rpow_succ, hρ]
  have hτδ : C.τ = C.δ ≫ C.β.1 ≫ ω' ≫ C.α.1 := by
    rw [← Category.assoc, hωδ, hρa, hτ]; rnorm
  by_cases hζ : IsIso ζ
  · -- [mild] figure 2.6, first diagram
    have hγ := C.γ_eq hM hρ n hω
    have hγirr : ¬IsIrreducible C.γ := by
      intro h
      rcases h.2.2 _ ξ (rpow C.ρ n ≫ ω') hγ with h1 | h1
      · exact hξn h1
      · exact hω' (ray_isIso_factors (rpow C.ρ n) ω').2
    have hδ := C.δ_irr hM hω' hρ hγirr
    have hfs : (ω' ≫ inv ζ) ≫ ξ = C.ρ := by rw [hξ]; simp [hρ]
    refine hM.not_dm5b C.τ C.τ_not_isIso hτ0 (ω' ≫ inv ζ) C.δ ξ C.β.1 ω'
      (C.ftm_δ hR)
      (nfp hτ0 (𝟙 _) ξ (rpow C.ρ (n + 2)) (Or.inr (hrpn _ (by omega))) (by rw [hτ]; simp))
      (nfp hτ0 (𝟙 _) (ξ ≫ ω') (C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inr (not_isIso_comp_left' _ hαn))
        (by rw [hτ1]; simp))
      (nfp hτ0 ξ ω' (C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inl hξn) (by rw [hτ1]))
      (nfp hτ0 ξ (ω' ≫ inv ζ) (ζ ≫ C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inl hξn)
        (by rw [hτ1, hξ]; simp))
      (nfp hτ0 ξ ((ω' ≫ inv ζ) ≫ C.δ) C.β.1 (Or.inl hξn)
        (by rw [hτ1]; simp only [Category.assoc]; rw [hωδ, hξ]; simp))
      (by rw [hfs]; exact C.ftm_ρ)
      (nfp hτ0 ξ (((ω' ≫ inv ζ) ≫ ξ) ≫ ω') (C.α.1 ≫ rpow C.ρ n) (Or.inl hξn)
        (by rw [hfs, hτ]; simp only [Category.assoc, hρa']; rnorm))
      (C.ftm_β hR)
      (nfp hτ0 C.δ (C.β.1 ≫ ω') C.α.1 (Or.inl hδn) (by rw [hτδ]; simp))
      (not_isIso_comp_left' _ hω') hδn hξn hβn hω' ?_ ?_ ?_ ?_ ?_ ?_
    · rintro ⟨g, hg⟩
      have e : C.δ ≫ (g ≫ rpow C.ρ (n + 1)) = C.δ ≫ C.β.1 := by
        rw [hωδ, ← Category.assoc, hg]
      have e2 := hL _ _ _ e (by rw [e, hωδ, ← hω]; exact C.h0)
      rcases C.β.2.2.2 _ g (rpow C.ρ (n + 1)) e2.symm with h | h
      · exact C.no_iso_from_sw hω' hρ g h
      · exact hrpn _ (by omega) h
    · rintro ⟨g, hg⟩
      have e : C.δ ≫ (g ≫ C.α.1 ≫ rpow C.ρ n) = C.δ ≫ C.β.1 := by
        rw [hωδ, ← Category.assoc, hg]; simp only [Category.assoc, hρa']; rnorm
      have e2 := hL _ _ _ e (by rw [e, hωδ, ← hω]; exact C.h0)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; exact hap.2 ⟨g, by simpa using e2⟩
      · rcases C.β.2.2.2 _ (g ≫ C.α.1) (rpow C.ρ n) (by rw [← e2, Category.assoc]) with h | h
        · exact hαn (ray_isIso_factors g C.α.1).2
        · exact hrpn _ hn h
    · rintro ⟨g, hg⟩
      rcases hδ.2.2 _ ξ g hg.symm with h | h
      · exact hξn h
      · exact C.no_iso_to_sw hω' hρ g h
    · rintro ⟨g, hg⟩; exact hap.2 ⟨g ≫ ζ, by rw [Category.assoc, ← hξ, hg]⟩
    · rintro ⟨g, hg⟩; exact hap.1 ⟨inv ζ ≫ g, by rw [Category.assoc, hg, hξ]; simp⟩
    · rintro ⟨g, hg⟩; exact hL2 g (hg.trans hfs)
  · -- [mild] figure 2.6, second diagram (the `D̃₅` of figure 2.5 with `ζ`)
    have hζ0 : ζ ≠ 0 := fun h ↦ hξn (by
      exfalso; apply C.h0; change C.ω = 0; rw [hω, hξ, h]; simp)
    obtain ⟨c₂, p', ε₂, hp⟩ := exists_last_arrow ζ hζ0 hζ
    have hτζ : C.τ = pathVal p' ≫ ε₂.1 ≫ C.α.1 ≫ ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1) := by
      rw [hτ1, hξ, hp]; simp
    have hζn := hζ
    have pre := not_isIso_comp_left' C.α.1 hζ
    refine hM.not_dm5 C.τ C.τ_not_isIso hτ0 ε₂.1 ω' C.α.1 C.β.1 ω'
      (C.ftm_α hR)
      (nfp hτ0 ζ (C.α.1 ≫ ω') (C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inl hζ) (by rw [hτ1, hξ]; simp))
      (nfp hτ0 ξ ω' (C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inl hξn) (by rw [hτ1]))
      (nfp hτ0 (pathVal p') ε₂.1 (C.α.1 ≫ ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1))
        (Or.inr (not_isIso_comp_left' _ hαn)) (by rw [hτζ]))
      (nfp hτ0 (pathVal p') (ε₂.1 ≫ C.α.1) (ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1))
        (Or.inr (not_isIso_comp_left' _ hω')) (by rw [hτζ]; simp))
      (nfp hτ0 (pathVal p') ((ε₂.1 ≫ C.α.1) ≫ ω') (C.α.1 ≫ rpow C.ρ (n + 1))
        (Or.inr (not_isIso_comp_left' _ hαn)) (by rw [hτζ]; simp))
      (nfp hτ0 ξ ω' (C.α.1 ≫ rpow C.ρ (n + 1)) (Or.inl hξn) (by rw [hτ1]))
      (by rw [hρa]; exact C.ftm_ρ)
      (nfp hτ0 ξ ((ω' ≫ C.α.1) ≫ ω') (C.α.1 ≫ rpow C.ρ n) (Or.inl hξn)
        (by rw [hτ]; simp only [Category.assoc, hρa']; rnorm))
      (C.ftm_β hR)
      (nfp hτ0 C.δ (C.β.1 ≫ ω') C.α.1 (Or.inl hδn) (by rw [hτδ]; simp))
      ε₂.2.2.1 hω' hαn hβn hω' ?_ ?_ hap.2 hap.1 ?_ (fun ⟨g, hg⟩ ↦ hL2 g (hg.trans hρa))
    · rintro ⟨g, hg⟩
      rcases hω'i.2.2 _ g ε₂.1 hg.symm with h | h
      · exact hmax ⟨pathVal p' ≫ inv g, by rw [hξ, hp, hρ, ← hg]; simp⟩
      · exact ε₂.2.2.1 h
    · rintro ⟨g, hg⟩
      rcases ε₂.2.2.2 _ g ω' hg.symm with h | h
      · exact hmax ⟨pathVal p' ≫ g, by rw [hξ, hp, hρ, ← hg]; simp⟩
      · exact hω' h
    · rintro ⟨g, hg⟩
      exact C.caseA_beta hM hω'i hρ n hω (ζ := pathVal p' ≫ g) (by rw [hξ, hp]; simp [hg])

/-- **Case (A) with a maximal power**: `ω = ξ ≫ ρ^(n+1)` with `ξ` not a multiple of `ρ`. -/
theorem caseA_k (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω'i : IsIrreducible ω')
    (hρ : C.ρ = ω' ≫ C.α.1) (n : ℕ) {ξ : x ⟶ y} (hω : C.ω = ξ ≫ rpow C.ρ (n + 1))
    (hmax : ¬∃ ξ', ξ = ξ' ≫ C.ρ) : False := by
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  by_cases hξ : IsIso ξ
  · obtain ⟨hxy, he⟩ := RayQuiver.eq_id_of_isIso ξ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine C.caseA_eq hM hxy ?_
      rw [← he]; change _ = C.ω; rw [hω]; simp [rpow_succ]
    · exact C.caseA_iso_long hM hω'i hρ hxy (n + 1) (by omega) (by rw [← he]; exact hω)
  · have hξ0 : ξ ≠ 0 := fun h ↦ C.h0 (by change C.ω = 0; rw [hω, h, zero_comp])
    obtain ⟨c, p, ε, hp⟩ := exists_last_arrow ξ hξ0 hξ
    rcases arrows_eq_or_apart ε C.α with ⟨h, he⟩ | hεα
    · subst h
      obtain rfl := eq_of_heq he
      exact C.caseA_alpha hM hω'i hρ n hω hmax hp
    rcases arrows_eq_or_apart ε C.β with ⟨h, he⟩ | hεβ
    · subst h
      obtain rfl := eq_of_heq he
      exact C.caseA_beta hM hω'i hρ n hω hp
    -- a third arrow into `y`: the `D̃₄` star `In3`
    have hτ0 := C.τ_ne_zero
    have hω' := hω'i.2.1
    have hτ1 : C.τ = pathVal p ≫ ε.1 ≫ ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1) := by
      change C.ω ≫ C.ρ = _
      rw [hω, hp, Category.assoc, ← rpow_succ, show n + 1 + 1 = 1 + (n + 1) by omega,
        ← rpow_comp_rpow]; simp [rpow_succ, hρ]
    have hτw : C.τ = C.δ ≫ C.β.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_w, hρ]
    have hτv : C.τ = C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ]
    exact hM.not_in3 C.τ C.τ_not_isIso hτ0 C.α.1 C.β.1 ε.1 ω'
      (nfp hτ0 (C.γ ≫ C.α.1) ω' C.α.1 (Or.inr C.α.2.2.1) (by rw [hτv]; simp))
      (C.ftm_α hR)
      (nfp hτ0 C.γ (C.α.1 ≫ ω') C.α.1 (Or.inr C.α.2.2.1) (by rw [hτv]; simp))
      (C.ftm_β hR)
      (nfp hτ0 C.δ (C.β.1 ≫ ω') C.α.1 (Or.inr C.α.2.2.1) (by rw [hτw]; simp))
      (nfp hτ0 (pathVal p) ε.1 (ω' ≫ C.α.1 ≫ rpow C.ρ (n + 1))
        (Or.inr (not_isIso_comp_left' _ hω')) (by rw [hτ1]))
      (nfp hτ0 (pathVal p) (ε.1 ≫ ω') (C.α.1 ≫ rpow C.ρ (n + 1))
        (Or.inr (not_isIso_comp_left' _ C.α.2.2.1)) (by rw [hτ1]; simp))
      C.α.2.2.1 C.β.2.2.1 ε.2.2.1 hω' hap.2 hεα.1 hap.1 hεβ.1 hεα.2 hεβ.2

/-- **Case (A) of the diamond trichotomy is impossible**: `γ = ξ ≫ ω'`. -/
theorem caseA (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω')
    (hρ : C.ρ = ω' ≫ C.α.1) {ξ : x ⟶ y} (hγ : ξ ≫ ω' = C.γ) : False := by
  have hR : RightCancel P := hM.right
  by_cases hξ : IsIso ξ
  · obtain ⟨hxy, he⟩ := RayQuiver.eq_id_of_isIso ξ
    exact C.caseA_eq hM hxy (by rw [← he, hρ, ← hγ]; simp)
  have hω'i := C.caseA_irr hM hω' hρ hξ hγ
  obtain ⟨N, hN, hN0⟩ := C.hρ 0 (MildContour.zero_not_isIso y)
  have key : ∀ d m (ξ' : x ⟶ y), N - (m + 1) = d → C.ω = ξ' ≫ rpow C.ρ (m + 1) → False := by
    intro d
    induction d with
    | zero =>
        intro m ξ' hd hω
        apply C.h0
        change C.ω = 0
        rw [hω, show m + 1 = N + (m + 1 - N) by omega, ← rpow_comp_rpow, ← hN0]; simp
    | succ d ih =>
        intro m ξ' hd hω
        by_cases hmax : ∃ ξ'', ξ' = ξ'' ≫ C.ρ
        · obtain ⟨ξ'', rfl⟩ := hmax
          exact ih (m + 1) ξ'' (by omega) (by rw [hω, Category.assoc, ← rpow_succ'])
        · exact C.caseA_k hM hω'i hρ m hω hmax
  exact key _ 0 ξ rfl (by change C.γ ≫ C.α.1 = _; rw [← hγ, hρ]; simp [rpow_succ])

end MildContour

end RayCat

end LargeIndecomposable
