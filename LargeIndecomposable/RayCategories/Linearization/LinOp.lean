module

public import LargeIndecomposable.Cleaving.Basic.Cleaving
public import LargeIndecomposable.RayCategories.Distributive.LinearizationTable
public import LargeIndecomposable.Modules.Duality.OppositeDuality

/-!
# Linearizations of anti-isomorphic ray categories

An `AntiPair Q' Q` is a pair of contravariant, zero-preserving functors
`Q' → Q`, `Q → Q'` that are inverse up to the identity on objects. Its
linearizations are anti-isomorphic, `k(Q') ≃ₐ k(Q)ᵐᵒᵖ`, on the bases of nonzero
morphisms (`AntiPair.linEquiv`); hence `k(Q')` is representation-finite when
`k(Q)` is (`AntiPair.isRepresentationFinite`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

namespace RayQuiver

/-- Contravariant functors `Q' → Q` and `Q → Q'`, inverse to each other. -/
structure AntiPair (Q' Q : Type) [Category.{0} Q'] [HasZeroMorphisms Q'] [Category.{0} Q]
    [HasZeroMorphisms Q] where
  obj : Q' → Q
  obj' : Q → Q'
  hom : ∀ {X Y : Q'}, (X ⟶ Y) → (obj Y ⟶ obj X)
  hom' : ∀ {a b : Q}, (a ⟶ b) → (obj' b ⟶ obj' a)
  obj'_obj : ∀ X, obj' (obj X) = X
  obj_obj' : ∀ a, obj (obj' a) = a
  hom'_hom : ∀ {X Y : Q'} (f : X ⟶ Y),
    hom' (hom f) = eqToHom (obj'_obj X) ≫ f ≫ eqToHom (obj'_obj Y).symm
  hom_hom' : ∀ {a b : Q} (g : a ⟶ b),
    hom (hom' g) = eqToHom (obj_obj' a) ≫ g ≫ eqToHom (obj_obj' b).symm
  map_comp : ∀ {X Y Z : Q'} (f : X ⟶ Y) (g : Y ⟶ Z), hom (f ≫ g) = hom g ≫ hom f
  map_comp' : ∀ {a b c : Q} (f : a ⟶ b) (g : b ⟶ c), hom' (f ≫ g) = hom' g ≫ hom' f
  map_id : ∀ X : Q', hom (𝟙 X) = 𝟙 (obj X)
  map_id' : ∀ a : Q, hom' (𝟙 a) = 𝟙 (obj' a)
  map_zero : ∀ {X Y : Q'}, hom (0 : X ⟶ Y) = 0
  map_zero' : ∀ {a b : Q}, hom' (0 : a ⟶ b) = 0

namespace AntiPair

variable {Q' Q : Type} [Category.{0} Q'] [HasZeroMorphisms Q'] [IsRayCategory Q'] [Fintype Q']
  [DecidableEq Q'] [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q] [Fintype Q]
  [DecidableEq Q] (A : AntiPair Q' Q) (k : Type u) [Field k]

lemma morElt_conj {C : Type} [Category.{0} C] [HasZeroMorphisms C] [IsRayCategory C] [Fintype C]
    [DecidableEq C] {X Y X' Y' : C} (f : X ⟶ Y) (h : X' = X) (h' : Y' = Y) :
    morElt k (eqToHom h ≫ f ≫ eqToHom h'.symm) = morElt k f := by
  subst h h'; simp

/-- The linear map `morElt f ↦ morElt (hom f)`. -/
def lin : Linearization Q' k →ₗ[k] Linearization Q k :=
  (linBasis k).constr k (fun μ ↦ morElt k (A.hom μ.2.2.1))

lemma lin_morElt {X Y : Q'} (f : X ⟶ Y) : A.lin k (morElt k f) = morElt k (A.hom f) := by
  by_cases h : f = 0
  · subst h; simp [A.map_zero]
  · rw [← show linBasis k (⟨X, Y, f, h⟩ : NZ Q') = morElt k f from linBasis_eq_morElt k _]
    rw [lin, Module.Basis.constr_basis]

/-- The reversed pair. -/
def symm : AntiPair Q Q' where
  obj := A.obj'
  obj' := A.obj
  hom := A.hom'
  hom' := A.hom
  obj'_obj := A.obj_obj'
  obj_obj' := A.obj'_obj
  hom'_hom := A.hom_hom'
  hom_hom' := A.hom'_hom
  map_comp := A.map_comp'
  map_comp' := A.map_comp
  map_id := A.map_id'
  map_id' := A.map_id
  map_zero := A.map_zero'
  map_zero' := A.map_zero

lemma obj_injective : Function.Injective A.obj := fun X Y h ↦ by
  rw [← A.obj'_obj X, ← A.obj'_obj Y, h]

lemma lin_symm_lin (a : Linearization Q' k) : A.symm.lin k (A.lin k a) = a := by
  have : (A.symm.lin k).comp (A.lin k) = LinearMap.id := by
    refine (linBasis k).ext fun μ ↦ ?_
    obtain ⟨X, Y, f, hf⟩ := μ
    rw [LinearMap.comp_apply, linBasis_eq_morElt, lin_morElt]
    change A.symm.lin k (morElt k (A.hom f)) = _
    rw [lin_morElt]
    change morElt k (A.hom' (A.hom f)) = _
    rw [A.hom'_hom, morElt_conj k f (A.obj'_obj X) (A.obj'_obj Y)]; rfl
  exact LinearMap.congr_fun this a

lemma lin_mul (a b : Linearization Q' k) : A.lin k (a * b) = A.lin k b * A.lin k a := by
  let B₁ : Linearization Q' k →ₗ[k] Linearization Q' k →ₗ[k] Linearization Q k :=
    (LinearMap.mul k (Linearization Q' k)).compr₂ (A.lin k)
  let B₂ : Linearization Q' k →ₗ[k] Linearization Q' k →ₗ[k] Linearization Q k :=
    (LinearMap.mul k (Linearization Q k)).flip.compl₁₂ (A.lin k) (A.lin k)
  have hB : B₁ = B₂ := by
    refine LinearMap.ext_basis (linBasis k) (linBasis k) fun μ ν ↦ ?_
    obtain ⟨Y₁, Z, g, hg⟩ := μ
    obtain ⟨X, Y₂, f, hf⟩ := ν
    simp only [B₁, B₂, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply,
      LinearMap.mul_apply', linBasis_eq_morElt]
    change A.lin k (morElt k g * morElt k f) = A.lin k (morElt k f) * A.lin k (morElt k g)
    rw [lin_morElt, lin_morElt]
    by_cases h : Y₂ = Y₁
    · subst h
      rw [morElt_mul, lin_morElt, A.map_comp, morElt_mul]
    · rw [morElt_mul_ne k f g h, _root_.map_zero, morElt_mul_ne k (A.hom g) (A.hom f)
        (fun h' ↦ h (A.obj_injective h').symm)]
  exact LinearMap.congr_fun (LinearMap.congr_fun hB a) b

lemma lin_one : A.lin k 1 = 1 := by
  rw [← sum_morElt_id, map_sum]
  simp only [lin_morElt, A.map_id]
  rw [← sum_morElt_id]
  exact Fintype.sum_bijective A.obj ⟨A.obj_injective, fun a ↦ ⟨A.obj' a, A.obj_obj' a⟩⟩ _ _
    (fun _ ↦ rfl)

lemma lin_comp_symm : (A.lin k).comp (A.symm.lin k) = LinearMap.id :=
  LinearMap.ext fun a ↦ A.symm.lin_symm_lin k a

lemma symm_comp_lin : (A.symm.lin k).comp (A.lin k) = LinearMap.id :=
  LinearMap.ext fun a ↦ A.lin_symm_lin k a

/-- The linear equivalence `k(Q') ≃ k(Q)` on the bases. -/
def linLEquiv : Linearization Q' k ≃ₗ[k] Linearization Q k :=
  LinearEquiv.ofLinear (A.lin k) (A.symm.lin k) (A.lin_comp_symm k) (A.symm_comp_lin k)

lemma linLEquiv_apply (a : Linearization Q' k) : A.linLEquiv k a = A.lin k a := rfl

/-- **The anti-isomorphism of linearizations.** -/
def linEquiv : Linearization Q' k ≃ₐ[k] (Linearization Q k)ᵐᵒᵖ :=
  AlgEquiv.ofLinearEquiv ((A.linLEquiv k).trans (MulOpposite.opLinearEquiv k))
    (by
      show MulOpposite.op (A.linLEquiv k 1) = 1
      rw [linLEquiv_apply, lin_one]; rfl)
    (fun a b ↦ by
      show MulOpposite.op (A.linLEquiv k (a * b)) =
        MulOpposite.op (A.linLEquiv k a) * MulOpposite.op (A.linLEquiv k b)
      rw [linLEquiv_apply, linLEquiv_apply, linLEquiv_apply, lin_mul, ← MulOpposite.op_mul])

include A in
/-- `k(Q')` is representation-finite when `k(Q)` is. -/
theorem isRepresentationFinite (h : IsRepresentationFinite (Linearization Q k)) :
    IsRepresentationFinite (Linearization Q' k) :=
  isRepresentationFinite_of_ringEquiv (A.linEquiv k).symm.toRingEquiv
    (isRepresentationFinite_mop (k := k) h)

end AntiPair

end RayQuiver

end LargeIndecomposable
