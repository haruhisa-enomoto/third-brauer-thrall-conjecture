module

public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasis
public import LargeIndecomposable.RayCategories.RoiterVanishing.Roiter

/-!
# Removing an exact twist

A twisted multiplicative basis `B` of `A` over `P` gives a contour function
`c(p, q) = T(p)/T(q)`, where `T(p)` is the scalar with
`elt αₙ ⋯ elt α₁ = T(p) • elt (val p)` along a path `p = αₙ ⋯ α₁`
(`RayQuiver.MulBasis.contourFn`). If it is exact, rescaling the basis gives a
multiplicative basis, and `A ≅ k(P)` (`RayQuiver.MulBasis.nonempty_algEquiv`;
Gabriel–Roiter 13.9).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
  (B : MulBasis k P A)

/-- The scalar of a path. -/
def pathT {x : RayVert P} : ∀ {y : RayVert P}, Quiver.Path x y → kˣ
  | _, .nil => 1
  | _, .cons p e => pathT p * B.tw (pathVal p) e.1

/-- The product of the basis elements along a path. -/
def pathE {x : RayVert P} : ∀ {y : RayVert P}, Quiver.Path x y → A
  | _, .nil => B.elt (𝟙 x.out)
  | _, .cons p e => B.elt e.1 * pathE p

lemma pathE_eq {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    B.pathE p = (B.pathT p : k) • B.elt (pathVal p)
  | _, .nil => by simp [pathE, pathT, pathVal]
  | _, .cons p e => by
    rw [pathE, pathE_eq p, mul_smul_comm, B.elt_mul, smul_smul, pathT, Units.val_mul]
    rfl

lemma pathE_comp {x y : RayVert P} (p : Quiver.Path x y) : ∀ {z : RayVert P}
    (q : Quiver.Path y z), B.pathE (p.comp q) = B.pathE q * B.pathE p
  | _, .nil => by
    rw [Quiver.Path.comp_nil, pathE, B.pathE_eq p, mul_smul_comm, B.id_mul]
  | _, .cons q e => by
    rw [Quiver.Path.comp_cons, pathE, pathE, pathE_comp p q, mul_assoc]

lemma smul_elt_inj {x y : P} {f : x ⟶ y} (hf : f ≠ 0) {c d : k} (h : c • B.elt f = d • B.elt f) :
    c = d := by
  have hne : B.elt f ≠ 0 := by
    have := B.basis.ne_zero ⟨x, y, f, hf⟩
    rwa [B.basis_apply] at this
  by_contra hcd
  apply hne
  have : (c - d) • B.elt f = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hcd)

lemma pathT_comp {x y z : RayVert P} (p : Quiver.Path x y) (q : Quiver.Path y z)
    (h : pathVal (p.comp q) ≠ 0) :
    B.pathT (p.comp q) = B.pathT p * B.pathT q * B.tw (pathVal p) (pathVal q) := by
  have e := B.pathE_comp p q
  rw [B.pathE_eq, B.pathE_eq, B.pathE_eq, smul_mul_smul_comm, B.elt_mul, smul_smul,
    ← pathVal_comp] at e
  ext
  rw [B.smul_elt_inj h e]
  simp only [Units.val_mul]
  ring

/-- The contour function of a twisted multiplicative basis. -/
def contourFn : ContourFn P (Additive kˣ) where
  c p q := Additive.ofMul (B.pathT p / B.pathT q)
  trans p q r _ _ _ := by
    rw [← ofMul_mul, div_mul_div_cancel]
  left s p q hpq h0 := by
    have h0' : pathVal (s.comp q) ≠ 0 := by rwa [pathVal_comp, ← hpq, ← pathVal_comp]
    rw [B.pathT_comp s p h0, B.pathT_comp s q h0', hpq]
    rw [mul_div_mul_right_eq_div, mul_div_mul_left_eq_div]
  right p q t hpq h0 := by
    have h0' : pathVal (q.comp t) ≠ 0 := by rwa [pathVal_comp, ← hpq, ← pathVal_comp]
    rw [B.pathT_comp p t h0, B.pathT_comp q t h0', hpq]
    rw [mul_div_mul_right_eq_div, mul_div_mul_right_eq_div]

/-! ### Rescaling -/

section Gauge

variable {B} (a : ∀ {x y : RayVert P}, (x ⟶ y) → Additive kˣ)

/-- `T(p)` corrected by `a` along `p`. -/
def gaugeP {x y : RayVert P} (p : Quiver.Path x y) : Additive kˣ :=
  Additive.ofMul (B.pathT p) - pathSum a p

variable {a} (ha : B.contourFn.IsCoboundary a)

include ha in
lemma gaugeP_eq {x y : RayVert P} (p q : Quiver.Path x y) (hpq : pathVal p = pathVal q)
    (h0 : pathVal p ≠ 0) : gaugeP (B := B) a p = gaugeP (B := B) a q := by
  have h := ha p q hpq h0
  change Additive.ofMul (B.pathT p / B.pathT q) = _ at h
  rw [ofMul_div] at h
  unfold gaugeP
  rw [sub_eq_sub_iff_sub_eq_sub, h]

variable (B a) in
open Classical in
/-- The rescaling scalar of a morphism. -/
def gauge {x y : P} (f : x ⟶ y) : kˣ :=
  if hf : f ≠ 0 then Additive.toMul (gaugeP (B := B) a (RayCat.exists_path f hf).choose) else 1

include ha in
lemma gauge_eq {x y : P} (f : x ⟶ y) (hf : f ≠ 0)
    (p : Quiver.Path (RayVert.mk x) (RayVert.mk y)) (hp : pathVal p = f) :
    gauge B a f = Additive.toMul (gaugeP (B := B) a p) := by
  rw [gauge, dif_pos hf, gaugeP_eq ha _ p ((RayCat.exists_path f hf).choose_spec.trans hp.symm)
    (by rw [(RayCat.exists_path f hf).choose_spec]; exact hf)]

include ha in
lemma gauge_id (x : P) : gauge B a (𝟙 x) = 1 := by
  rw [gauge_eq ha (𝟙 x) (IsRayCategory.id_ne_zero x) Quiver.Path.nil rfl]
  simp [gaugeP, pathT, pathSum]

include ha in
lemma gauge_comp {x y z : P} (f : x ⟶ y) (g : y ⟶ z) (h : f ≫ g ≠ 0) :
    gauge B a (f ≫ g) = gauge B a f * gauge B a g * B.tw f g := by
  have hf : f ≠ 0 := fun h' ↦ h (by rw [h', zero_comp])
  have hg : g ≠ 0 := fun h' ↦ h (by rw [h', comp_zero])
  obtain ⟨p, hp⟩ := RayCat.exists_path f hf
  obtain ⟨q, hq⟩ := RayCat.exists_path g hg
  have hpq : pathVal (p.comp q) = f ≫ g := by rw [pathVal_comp, hp, hq]
  rw [gauge_eq ha f hf p hp, gauge_eq ha g hg q hq, gauge_eq ha _ h (p.comp q) hpq]
  have hT := B.pathT_comp p q (by rwa [hpq])
  simp only [gaugeP, pathSum_comp, toMul_sub, toMul_add, toMul_ofMul, hT, hp, hq]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

variable (B a) in
/-- The rescaled basis elements. -/
def untw {x y : P} (f : x ⟶ y) : A := (gauge B a f : k) • B.elt f

include ha in
lemma untw_mul {x y z : P} (f : x ⟶ y) (g : y ⟶ z) :
    untw B a g * untw B a f = untw B a (f ≫ g) := by
  unfold untw
  rw [smul_mul_smul_comm, B.elt_mul, smul_smul]
  by_cases h : f ≫ g = 0
  · rw [h, B.elt_zero, smul_zero, smul_zero]
  · rw [gauge_comp ha f g h]
    congr 1
    simp only [Units.val_mul]
    ring

variable (B) in
include ha in
/-- **Exact twists are trivial**: `A ≅ k(P)`. -/
theorem nonempty_algEquiv : Nonempty (Linearization P k ≃ₐ[k] A) := by
  let φ : Linearization P k →ₐ[k] A := linLift k (fun f ↦ untw B a f)
    (by intro x y; simp [untw, B.elt_zero])
    (fun f g ↦ untw_mul ha f g)
    (by intro x y y' z f g h; simp only [untw]; rw [smul_mul_smul_comm, B.elt_mul_ne f g h, smul_zero])
    (by simp only [untw, gauge_id ha, Units.val_one, one_smul]; exact B.sum_id)
  let w : NZ P → kˣ := fun μ ↦ gauge B a μ.2.2.1
  let e := (linBasis (P := P) k).equiv (B.basis.unitsSMul w) (Equiv.refl _)
  have hφ : φ.toLinearMap = e.toLinearMap := by
    refine (linBasis (P := P) k).ext fun μ ↦ ?_
    rw [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Module.Basis.unitsSMul_apply, linBasis_apply, rayElt_eq_morElt]
    change linLift k _ _ _ _ _ (morElt k μ.2.2.1) = _
    rw [linLift_morElt, B.basis_apply]
    rfl
  refine ⟨AlgEquiv.ofBijective φ ?_⟩
  have : (φ : Linearization P k → A) = e := by
    funext x
    exact LinearMap.congr_fun hφ x
  rw [this]
  exact e.bijective

end Gauge

end MulBasis

end RayQuiver

end LargeIndecomposable
