module

public import LargeIndecomposable.KroneckerModules.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Quotients of projective modules by submodules of the socle

Setting 3.2 and Construction 3.3 of the manuscript: for a basic algebra `Λ`
with idempotents `e_x, e_y` and linearly independent `s, t ∈ e_x J e_y`
annihilated on both sides by `J = rad Λ`, and a Kronecker module
`T = (V, W; a, b)`,

`F₁(T) = (Λe_y ⊗ W) / {s ⊗ a(v) + t ⊗ b(v) : v ∈ V}`.

The functor is defined here on all Kronecker modules, of any dimension.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct

universe u

variable {k : Type u} [Field k]

/-- Setting 3.2. The idempotents `e_x, e_y` are taken from a complete set of
primitive orthogonal idempotents of the basic algebra `Λ`; this file only
uses that `s, t ∈ e_x J e_y` and `Js = Jt = sJ = tJ = 0`, so the remaining
conditions are recorded as hypotheses where needed. -/
structure QuotientData (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] where
  /-- The idempotent `e_x`. -/
  ex : Λ
  /-- The idempotent `e_y`. -/
  ey : Λ
  /-- The element `s ∈ e_x J e_y`. -/
  s : Λ
  /-- The element `t ∈ e_x J e_y`. -/
  t : Λ
  ex_idem : IsIdempotentElem ex
  ey_idem : IsIdempotentElem ey
  s_mem : s ∈ Ring.jacobson Λ ∧ ex * s * ey = s
  t_mem : t ∈ Ring.jacobson Λ ∧ ex * t * ey = t
  linearIndependent : LinearIndependent k ![s, t]
  J_mul_s : ∀ j ∈ Ring.jacobson Λ, j * s = 0
  J_mul_t : ∀ j ∈ Ring.jacobson Λ, j * t = 0
  s_mul_J : ∀ j ∈ Ring.jacobson Λ, s * j = 0
  t_mul_J : ∀ j ∈ Ring.jacobson Λ, t * j = 0

namespace QuotientData

variable {Λ : Type u} [Ring Λ] [Algebra k Λ] (Q : QuotientData k Λ)

/-- The projective module `Λ e_y`. -/
abbrev P : Submodule Λ Λ := Submodule.span Λ {Q.ey}

lemma mem_P_of_mul_ey (r : Λ) (h : r * Q.ey = r) : r ∈ Q.P := by
  rw [← h]
  exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)

lemma s_mem_P : Q.s ∈ Q.P := Q.mem_P_of_mul_ey _ (by
  nth_rewrite 1 [← Q.s_mem.2]
  rw [mul_assoc (Q.ex * Q.s), Q.ey_idem.eq, Q.s_mem.2])

lemma t_mem_P : Q.t ∈ Q.P := Q.mem_P_of_mul_ey _ (by
  nth_rewrite 1 [← Q.t_mem.2]
  rw [mul_assoc (Q.ex * Q.t), Q.ey_idem.eq, Q.t_mem.2])

/-- The element `s` of `Λ e_y`. -/
def sP : Q.P := ⟨Q.s, Q.s_mem_P⟩

/-- The element `t` of `Λ e_y`. -/
def tP : Q.P := ⟨Q.t, Q.t_mem_P⟩

/-- The `k`-linear map `V → Λ e_y ⊗ W`, `v ↦ s ⊗ a(v) + t ⊗ b(v)`. -/
def relMap (X : Kron k) : X.V →ₗ[k] Q.P ⊗[k] X.W :=
  (TensorProduct.mk k Q.P X.W Q.sP).comp X.a.hom +
    (TensorProduct.mk k Q.P X.W Q.tP).comp X.b.hom

/-- The relation submodule `{s ⊗ a(v) + t ⊗ b(v)}` (the `Λ`-span; it equals
the `k`-span, see `relSub_eq_range`). -/
def relSub (X : Kron k) : Submodule Λ (Q.P ⊗[k] X.W) :=
  Submodule.span Λ (Set.range (Q.relMap X))

/-- Construction 3.3 on objects: `F₁(T) = (Λe_y ⊗ W)/{s ⊗ a(v) + t ⊗ b(v)}`. -/
abbrev obj (X : Kron k) : ModuleCat.{u} Λ := ModuleCat.of Λ (Q.P ⊗[k] X.W ⧸ Q.relSub X)

/-- `1 ⊗ h` as a `Λ`-linear map. -/
def tensorMap {W W' : ModuleCat.{u} k} (h : W ⟶ W') : Q.P ⊗[k] W →ₗ[Λ] Q.P ⊗[k] W' :=
  TensorProduct.AlgebraTensorModule.lTensor Λ Q.P h.hom

lemma tensorMap_tmul {W W' : ModuleCat.{u} k} (h : W ⟶ W') (p : Q.P) (w : W) :
    Q.tensorMap h (p ⊗ₜ w) = p ⊗ₜ h.hom w := rfl

lemma relSub_le_comap {X Y : Kron k} (f : X ⟶ Y) :
    Q.relSub X ≤ (Q.relSub Y).comap (Q.tensorMap (f.app one)) := by
  rw [relSub, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine Submodule.subset_span ⟨(f.app zero).hom v, ?_⟩
  simp [relMap, tensorMap_tmul]

/-- Construction 3.3: the functor `F₁`, defined on all Kronecker modules. -/
def functor : Kron k ⥤ ModuleCat.{u} Λ where
  obj := Q.obj
  map {X Y} f := ModuleCat.ofHom (Submodule.mapQ _ _ (Q.tensorMap (f.app one))
    (Q.relSub_le_comap f))
  map_id X := by
    ext p w
    rfl
  map_comp f g := by
    ext p w
    rfl

end QuotientData

end LargeIndecomposable
