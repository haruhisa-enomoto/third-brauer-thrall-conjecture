module

public import LargeIndecomposable.RayCategories.Basic.RayQuiver
public import LargeIndecomposable.Modules.SplitBasic.QuiverPresentation

/-!
# The regular representation of a linearization

For a finite ray category `P`, the space `k^(P*)` with basis the nonzero
morphisms carries a right action of `P`: a morphism `g` sends `μ` to `μ ≫ g`
when this composite is defined and nonzero, and to zero otherwise
(`RayQuiver.morAct`). Composition of actions is composition of morphisms
(`morAct_comp`). This gives a representation of the path algebra of `Q_P`,
used to show that the nonzero morphisms form a basis of `k(P)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] (k : Type*) [Field k]

variable (P) in
/-- The nonzero morphisms of `P`. -/
abbrev NZ : Type := Σ (x y : P), {f : x ⟶ y // f ≠ 0}

/-- `μ ≫ g` as a basis vector, or zero. -/
def compRay (μ : NZ P) {t : P} (g : μ.2.1 ⟶ t) : NZ P →₀ k := by
  classical
  exact if h : μ.2.2.1 ≫ g = 0 then 0 else Finsupp.single ⟨μ.1, t, μ.2.2.1 ≫ g, h⟩ 1

/-- The action of `g : s ⟶ t` on a basis vector. -/
def actRay {s t : P} (g : s ⟶ t) (μ : NZ P) : NZ P →₀ k :=
  if h : μ.2.1 = s then compRay k μ (eqToHom h ≫ g) else 0

/-- The action of a morphism on `k^(P*)`. -/
def morAct {s t : P} (g : s ⟶ t) : Module.End k (NZ P →₀ k) :=
  Finsupp.linearCombination k (actRay k g)

lemma morAct_single {s t : P} (g : s ⟶ t) (μ : NZ P) :
    morAct k g (Finsupp.single μ 1) = actRay k g μ := by
  simp [morAct]

lemma actRay_mk_eq {x s t : P} (f : x ⟶ s) (hf : f ≠ 0) (g : s ⟶ t) :
    actRay k g ⟨x, s, f, hf⟩ = compRay k ⟨x, s, f, hf⟩ g := by
  simp [actRay]

lemma actRay_mk_ne {x y s t : P} (f : x ⟶ y) (hf : f ≠ 0) (g : s ⟶ t) (h : y ≠ s) :
    actRay k g ⟨x, y, f, hf⟩ = 0 := by
  simp [actRay, h]

lemma morAct_comp {s t u : P} (g : s ⟶ t) (h : t ⟶ u) :
    morAct k h ∘ₗ morAct k g = morAct k (g ≫ h) := by
  refine Finsupp.lhom_ext' fun μ ↦ LinearMap.ext_ring ?_
  obtain ⟨x, y, f, hf⟩ := μ
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, morAct_single]
  by_cases hy : y = s
  · subst hy
    rw [actRay_mk_eq, actRay_mk_eq]
    unfold compRay
    by_cases h0 : f ≫ g = 0
    · rw [dif_pos h0, dif_pos (by rw [← Category.assoc, h0, zero_comp]), map_zero]
    · rw [dif_neg h0, morAct_single, actRay_mk_eq]
      unfold compRay
      by_cases h1 : f ≫ g ≫ h = 0
      · rw [dif_pos (by rw [Category.assoc]; exact h1), dif_pos h1]
      · rw [dif_neg (by rw [Category.assoc]; exact h1), dif_neg h1]
        simp only [Category.assoc]
  · rw [actRay_mk_ne k f hf g hy, actRay_mk_ne k f hf _ hy, map_zero]

lemma morAct_comp_ne {s t t' u : P} (g : s ⟶ t) (h : t' ⟶ u) (ht : t ≠ t') :
    morAct k h ∘ₗ morAct k g = 0 := by
  refine Finsupp.lhom_ext' fun μ ↦ LinearMap.ext_ring ?_
  obtain ⟨x, y, f, hf⟩ := μ
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, morAct_single, LinearMap.zero_apply]
  by_cases hy : y = s
  · subst hy
    rw [actRay_mk_eq]
    unfold compRay
    split_ifs with h0
    · exact map_zero _
    · rw [morAct_single, actRay_mk_ne k _ _ h ht]
  · rw [actRay_mk_ne k f hf g hy, map_zero]

lemma sum_morAct_id : ∑ v : P, morAct k (𝟙 v) = 1 := by
  refine Finsupp.lhom_ext' fun μ ↦ LinearMap.ext_ring ?_
  obtain ⟨x, y, f, hf⟩ := μ
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rw [LinearMap.sum_apply, Finset.sum_eq_single y]
  · rw [morAct_single, actRay_mk_eq]
    unfold compRay
    rw [dif_neg (by rwa [Category.comp_id])]
    simp
  · intro v _ hv
    rw [morAct_single]
    exact actRay_mk_ne k f hf _ (Ne.symm hv)
  · intro h; exact absurd (Finset.mem_univ y) h

variable (P) in
/-- The representation of `kQ_P` on `k^(P*)`. -/
def regRep : (quiver P).PathAlgebra k →ₐ[k] Module.End k (NZ P →₀ k) :=
  FinQuiver.lift (quiver P) (fun v ↦ morAct k (𝟙 v)) (fun a ↦ morAct k a.2.2.1)
    (fun v w ↦ by
      split_ifs with h
      · subst h
        change morAct k (𝟙 v) ∘ₗ morAct k (𝟙 v) = _
        rw [morAct_comp, Category.comp_id]
      · exact morAct_comp_ne k (𝟙 w) (𝟙 v) (Ne.symm h))
    (sum_morAct_id k)
    (fun a ↦ by
      change morAct k a.2.2.1 ∘ₗ morAct k (𝟙 a.1) = _
      rw [morAct_comp, Category.id_comp])
    (fun a ↦ by
      change morAct k (𝟙 a.2.1) ∘ₗ morAct k a.2.2.1 = _
      rw [morAct_comp, Category.comp_id])

lemma regRep_arrow (a : (quiver P).A) :
    regRep P k (FinQuiver.arrow k (quiver P) a) = morAct k a.2.2.1 := by
  simp [regRep]

lemma regRep_vertex (v : P) :
    regRep P k (FinQuiver.vertex k (quiver P) v) = morAct k (𝟙 v) := by
  simp only [regRep]
  exact FinQuiver.lift_vertex (Q := quiver P) _ _ _ _ _ _ v

/-- A nonempty path acts by its value. -/
lemma regRep_word : ∀ (c : (quiver P).A) (l : List (quiver P).A) (x y : P)
    (h : PathFrom (D := quiver P) x (c :: l) y),
      regRep P k (FinQuiver.word k (quiver P) (c :: l)) = morAct k (pathMor (c :: l) x y h)
  | c, [], x, y, h => by
    rw [Rep.word_cons, map_mul, regRep_arrow]
    change regRep P k 1 * morAct k c.2.2.1 = _
    rw [map_one, one_mul]
    obtain ⟨h1, h2⟩ := h
    change c.2.1 = y at h2
    obtain ⟨a, b, f, hf⟩ := c
    change a = x at h1
    subst h1 h2
    change morAct k f = morAct k (eqToHom rfl ≫ f ≫ eqToHom rfl)
    simp
  | c, d :: l, x, y, h => by
    rw [Rep.word_cons, map_mul, regRep_word d l _ y h.2, regRep_arrow]
    obtain ⟨h1, h2⟩ := h
    obtain ⟨a, b, f, hf⟩ := c
    change a = x at h1
    subst h1
    change morAct k (pathMor (d :: l) b y h2) ∘ₗ morAct k f = _
    rw [morAct_comp]
    simp [pathMor]

lemma morAct_zero {s t : P} : morAct k (0 : s ⟶ t) = 0 := by
  refine Finsupp.lhom_ext' fun μ ↦ LinearMap.ext_ring ?_
  obtain ⟨x, y, f, hf⟩ := μ
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, morAct_single, LinearMap.zero_apply]
  by_cases hy : y = s
  · subst hy
    rw [actRay_mk_eq]
    unfold compRay
    rw [dif_pos comp_zero]
  · exact actRay_mk_ne k f hf _ hy

/-- The value of a nonempty closed path is not an identity. -/
lemma pathMor_ne_id (c : (quiver P).A) (l : List (quiver P).A) (x : P)
    (h : PathFrom (D := quiver P) x (c :: l) x) : pathMor (c :: l) x x h ≠ 𝟙 x := by
  intro he
  obtain ⟨a, b, f, hf⟩ := c
  obtain ⟨h1, h2⟩ := h
  change a = x at h1
  subst h1
  change eqToHom rfl ≫ f ≫ pathMor l b a h2 = 𝟙 a at he
  rw [eqToHom_refl, Category.id_comp] at he
  have hf0 : f ≠ 0 := hf.1
  have e : f = 𝟙 a ≫ f ≫ (pathMor l b a h2 ≫ f) := by
    rw [Category.id_comp, ← Category.assoc, he, Category.id_comp]
  obtain ⟨-, h3⟩ := IsRayCategory.eq_id_of_two_sided f hf0 _ _ e
  exact hf.2.1 ⟨_, he, h3⟩

variable (P) in
/-- The representation of `k(P)` on `k^(P*)`. -/
def linRep : Linearization P k →ₐ[k] Module.End k (NZ P →₀ k) :=
  RingQuot.liftAlgHom k ⟨regRep P k, by
    intro u w hr
    cases hr with
    | zero l x y h h0 =>
      rw [map_zero]
      cases l with
      | nil =>
        change x = y at h
        subst h
        exact absurd h0 (IsRayCategory.id_ne_zero x)
      | cons c l => rw [regRep_word k c l x y h, h0, morAct_zero]
    | eq l l' x y h h' he =>
      cases l with
      | nil =>
        change x = y at h
        subst h
        cases l' with
        | nil => rfl
        | cons c l' => exact absurd he.symm (pathMor_ne_id c l' x h')
      | cons c l =>
        cases l' with
        | nil =>
          change x = y at h'
          subst h'
          exact absurd he (pathMor_ne_id c l x h)
        | cons c' l' => rw [regRep_word k c l x y h, regRep_word k c' l' x y h', he]⟩

lemma linRep_linPres (z : (quiver P).PathAlgebra k) : linRep P k (linPres P k z) = regRep P k z := by
  simp [linRep, linPres]

end RayQuiver

end LargeIndecomposable
