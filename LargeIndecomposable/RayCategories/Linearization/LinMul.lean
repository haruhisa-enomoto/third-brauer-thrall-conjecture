module

public import LargeIndecomposable.RayCategories.Linearization.LinBasis

/-!
# Multiplication in the linearization

For a finite ray category `P`, the element `morElt f` of `k(P)` of a morphism
`f` (zero for `f = 0`) is multiplicative: `morElt g * morElt f = morElt (f ≫ g)`
and `morElt g * morElt f = 0` for non-composable `f`, `g`; the identities sum
to `1`. Hence a family of elements of a `k`-algebra with the same properties
extends to an algebra map `k(P) → A'` (`RayQuiver.linLift`). Modules over
`k(P)` are thus functors on `P` sending zero morphisms to zero maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] (k : Type*) [Field k]

lemma linRep_rayElt_eq (μ : NZ P) : linRep P k (rayElt k μ) = morAct k μ.2.2.1 := by
  obtain ⟨x, y, f, hf⟩ := μ
  by_cases hiso : IsIso f
  · obtain ⟨hxy, rfl⟩ := eq_id_of_isIso f
    subst hxy
    rw [rayElt, dif_pos hiso, linRep_linPres, regRep_vertex]
    rfl
  · rw [rayElt, dif_neg hiso, linRep_linPres]
    obtain ⟨h, he⟩ := (exists_path_cons f hf hiso).choose_spec.choose_spec
    rw [regRep_word k _ _ x y h]
    simp only [he]

open Classical in
/-- The element of `k(P)` of a morphism: zero for `0`. -/
def morElt {x y : P} (f : x ⟶ y) : Linearization P k :=
  if h : f = 0 then 0 else rayElt k ⟨x, y, f, h⟩

@[simp]
lemma morElt_zero {x y : P} : morElt k (0 : x ⟶ y) = 0 := by
  simp [morElt]

lemma morElt_of_ne {x y : P} (f : x ⟶ y) (h : f ≠ 0) : morElt k f = rayElt k ⟨x, y, f, h⟩ := by
  simp [morElt, h]

lemma linRep_morElt {x y : P} (f : x ⟶ y) : linRep P k (morElt k f) = morAct k f := by
  by_cases h : f = 0
  · subst h
    rw [morElt_zero, map_zero, morAct_zero]
  · rw [morElt_of_ne k f h, linRep_rayElt_eq]

/-- Evaluation of the regular representation at the sum of identities is the
coordinate map of the basis of nonzero morphisms. -/
lemma linRep_unitVec_eq (a : Linearization P k) :
    linRep P k a (unitVec P k) = (linBasis k).repr a := by
  have : (LinearMap.applyₗ (unitVec P k) ∘ₗ (linRep P k).toLinearMap :
      Linearization P k →ₗ[k] (NZ P →₀ k)) = (linBasis k).repr.toLinearMap := by
    refine (linBasis k).ext fun μ ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_coe, Module.Basis.repr_self]
    rw [linBasis_apply]
    exact linRep_rayElt k μ
  exact congrArg (fun φ : Linearization P k →ₗ[k] (NZ P →₀ k) ↦ φ a) this

lemma eq_of_linRep_unitVec {a b : Linearization P k}
    (h : linRep P k a (unitVec P k) = linRep P k b (unitVec P k)) : a = b := by
  rw [linRep_unitVec_eq, linRep_unitVec_eq] at h
  exact (linBasis k).repr.injective h

lemma morElt_mul {x y z : P} (f : x ⟶ y) (g : y ⟶ z) : morElt k g * morElt k f = morElt k (f ≫ g) := by
  apply eq_of_linRep_unitVec
  rw [map_mul, Module.End.mul_apply, linRep_morElt, linRep_morElt, linRep_morElt,
    ← LinearMap.comp_apply, morAct_comp]

lemma morElt_mul_ne {x y y' z : P} (f : x ⟶ y) (g : y' ⟶ z) (h : y ≠ y') :
    morElt k g * morElt k f = 0 := by
  apply eq_of_linRep_unitVec
  rw [map_mul, Module.End.mul_apply, linRep_morElt, linRep_morElt, ← LinearMap.comp_apply,
    morAct_comp_ne k f g h, map_zero, LinearMap.zero_apply]

lemma sum_morElt_id : ∑ x : P, morElt k (𝟙 x) = 1 := by
  apply eq_of_linRep_unitVec
  rw [map_sum, map_one]
  simp only [linRep_morElt]
  rw [sum_morAct_id]

lemma rayElt_eq_morElt (μ : NZ P) : rayElt k μ = morElt k μ.2.2.1 :=
  (morElt_of_ne k _ μ.2.2.2).symm

/-! ### Algebra maps out of `k(P)` -/

section Lift

variable {A' : Type*} [Ring A'] [Algebra k A']
  (T : ∀ {x y : P}, (x ⟶ y) → A')
  (hT0 : ∀ {x y : P}, T (0 : x ⟶ y) = 0)
  (hTc : ∀ {x y z : P} (f : x ⟶ y) (g : y ⟶ z), T g * T f = T (f ≫ g))
  (hTn : ∀ {x y y' z : P} (f : x ⟶ y) (g : y' ⟶ z), y ≠ y' → T g * T f = 0)
  (hT1 : ∑ x : P, T (𝟙 x) = 1)

/-- The linear map `k(P) → A'` with `morElt f ↦ T f`. -/
def linLiftₗ : Linearization P k →ₗ[k] A' := (linBasis k).constr k fun μ ↦ T μ.2.2.1

include hT0 in
lemma linLiftₗ_morElt {x y : P} (f : x ⟶ y) : linLiftₗ k T (morElt k f) = T f := by
  by_cases h : f = 0
  · subst h
    rw [morElt_zero, map_zero, hT0]
  · rw [morElt_of_ne k f h, ← linBasis_apply, linLiftₗ, Module.Basis.constr_basis]

include hT0 hTc hTn in
lemma linLiftₗ_mul (a b : Linearization P k) :
    linLiftₗ k T (a * b) = linLiftₗ k T a * linLiftₗ k T b := by
  let B₁ : Linearization P k →ₗ[k] Linearization P k →ₗ[k] A' :=
    (LinearMap.mul k (Linearization P k)).compr₂ (linLiftₗ k T)
  let B₂ : Linearization P k →ₗ[k] Linearization P k →ₗ[k] A' :=
    (LinearMap.mul k A').compl₁₂ (linLiftₗ k T) (linLiftₗ k T)
  have : B₁ = B₂ := by
    refine (linBasis k).ext fun μ ↦ (linBasis k).ext fun ν ↦ ?_
    simp only [B₁, B₂, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      linBasis_apply, rayElt_eq_morElt, linLiftₗ_morElt k T hT0]
    obtain ⟨x, y, f, hf⟩ := μ
    obtain ⟨x', y', g, hg⟩ := ν
    by_cases h : y' = x
    · subst h
      rw [morElt_mul, linLiftₗ_morElt k T hT0, hTc]
    · rw [morElt_mul_ne k g f h, map_zero, hTn g f h]
  exact congrArg (fun B : Linearization P k →ₗ[k] Linearization P k →ₗ[k] A' ↦ B a b) this

include hT0 hT1 in
lemma linLiftₗ_one : linLiftₗ k T 1 = 1 := by
  rw [← sum_morElt_id, map_sum]
  simp only [linLiftₗ_morElt k T hT0]
  exact hT1

/-- The algebra map `k(P) → A'` with `morElt f ↦ T f`. -/
def linLift : Linearization P k →ₐ[k] A' :=
  AlgHom.ofLinearMap (linLiftₗ k T) (linLiftₗ_one k T hT0 hT1) (linLiftₗ_mul k T hT0 hTc hTn)

lemma linLift_morElt {x y : P} (f : x ⟶ y) : linLift k T hT0 hTc hTn hT1 (morElt k f) = T f :=
  linLiftₗ_morElt k T hT0 f

end Lift

end RayQuiver

end LargeIndecomposable
