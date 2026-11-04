module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Finsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# At most `2^κ` modules of dimension `κ`

Let `A` be a finite-dimensional algebra over a field `k`, and `κ ≥ |k|` an
infinite cardinal. Pairwise non-isomorphic `A`-modules of dimension `κ` form a
family of cardinality at most `2^κ` (`card_le_two_pow_of_pairwise_not_iso`), as in
the proof of Corollary 5.7: a vector space `Y` of dimension `κ` has `κ`
elements, so there are at most `κ^κ = 2^κ` linear endomorphisms of `Y`, and an
`A`-module structure on `Y` is determined by the action of a finite basis of
`A`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open Cardinal

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- A `k`-linear bijection between `A`-modules that commutes with the action of a
`k`-basis of `A` is `A`-linear. -/
lemma map_smul_of_basis {M N : Type u} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι k A) (φ : M →ₗ[k] N)
    (h : ∀ l (m : M), φ (b l • m) = b l • φ m) (a : A) (m : M) : φ (a • m) = a • φ m := by
  rw [← b.sum_repr a]
  simp only [Finset.sum_smul, map_sum, smul_assoc, map_smul, h]

/-- At most `2^κ` pairwise non-isomorphic `A`-modules of dimension `κ ≥ |k|`. -/
theorem card_le_two_pow_of_pairwise_not_iso (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hk : #k ≤ κ)
    {ι : Type u} (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    (hni : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) (hdim : ∀ i, Module.rank k (M i) = κ) :
    #ι ≤ 2 ^ κ := by
  classical
  let X := κ.ord.ToType
  have hX : #X = κ := mk_ord_toType κ
  haveI : Infinite X := Cardinal.infinite_iff.2 (hX ▸ hκ)
  let Y := X →₀ k
  have hYr : Module.rank k Y = κ := by rw [rank_finsupp_self, lift_id, hX]
  have hY : #Y ≤ κ := by
    rw [mk_finsupp_lift_of_infinite, lift_id, lift_id, hX]
    exact max_le le_rfl hk
  have he : ∀ i, Nonempty (M i ≃ₗ[k] Y) := fun i ↦
    LinearEquiv.nonempty_equiv_iff_rank_eq.2 (by rw [hdim i, hYr])
  let e : ∀ i, M i ≃ₗ[k] Y := fun i ↦ (he i).some
  let b := Module.finBasis k A
  let code : ι → Fin (Module.finrank k A) → Y → Y := fun i l y ↦ e i (b l • (e i).symm y)
  have hcode : Function.Injective code := by
    intro i j hij
    refine hni i j ⟨?_⟩
    let φ : M i ≃ₗ[k] M j := (e i).trans (e j).symm
    have hφ : ∀ l (m : M i), φ (b l • m) = b l • φ m := fun l m ↦ by
      have := congrFun (congrFun hij l) (e i m)
      simp only [code, LinearEquiv.symm_apply_apply] at this
      change (e j).symm (e i (b l • m)) = b l • (e j).symm (e i m)
      rw [this, LinearEquiv.symm_apply_apply]
    exact
      { toFun := φ
        invFun := φ.symm
        map_add' := φ.map_add
        map_smul' := map_smul_of_basis b φ.toLinearMap hφ
        left_inv := φ.left_inv
        right_inv := φ.right_inv }
  have hP : #(Fin (Module.finrank k A) × Y) ≤ κ := by
    rw [mk_prod, mk_fin, lift_natCast, lift_uzero]
    exact (mul_le_mul' (natCast_lt_aleph0.le.trans hκ) hY).trans (mul_eq_self hκ).le
  calc #ι ≤ #(Fin (Module.finrank k A) × Y → Y) :=
        mk_le_of_injective (f := fun i p ↦ code i p.1 p.2) fun i j h ↦ hcode
          (funext fun l ↦ funext fun y ↦ congrFun h (l, y))
    _ = #Y ^ #(Fin (Module.finrank k A) × Y) := (power_def _ _).symm
    _ ≤ κ ^ κ := (power_le_power_right hY).trans (power_le_power_left
        (aleph0_pos.trans_le hκ).ne' hP)
    _ = 2 ^ κ := power_self_eq hκ
