module

public import LargeIndecomposable.KroneckerBricks.TransportPool
public import LargeIndecomposable.KroneckerBricks.Iterate
public import LargeIndecomposable.KroneckerBricks.Injective

/-!
# Kronecker bricks of singular dimension

Let `κ > |k|` be singular, `μ = cf κ`, `λ = (max μ |k|)⁺ < κ`. Take a pool of
`λ` orthogonal bricks (`Bricks.transportPool`), cofinal regular cardinals
`κ_i > λ` (`i < μ`) with `∑ κ_i = κ`, and transport the rigid structure of
`κ_i` along the sub-seed `{i} × ℕ` of the pool. The transports `H_i` are
pairwise orthogonal bricks of dimension `κ_i`; glued over a new anchor they give
a brick of dimension `κ` (`Bricks.exists_brick_singular`). With the regular case
this proves `KroneckerBricksLarge` (`Bricks.kroneckerBricksLarge`), the
remaining part of Göbel–Simson, Corollary 1.3.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct
open _root_.Cardinal

universe u

variable {k : Type u} [Field k]

namespace Bricks

/-- The initial ordinal of a regular uncountable cardinal is a regular well-order. -/
lemma regular_order (κ : Cardinal.{u}) (hreg : κ.IsRegular) (hκ : ℵ₀ < κ) :
    ∃ (_ : IsRegularCardinalOrder κ.ord.ToType) (_ : Nonempty κ.ord.ToType)
      (_ : NoMaxOrder κ.ord.ToType), ℵ₀ < Order.cof κ.ord.ToType ∧ #κ.ord.ToType = κ := by
  have hcof : Order.cof κ.ord.ToType = κ := by
    rw [Ordinal.cof_toType]
    exact hreg.cof_eq
  have hα : ℵ₀ < Order.cof κ.ord.ToType := by rw [hcof]; exact hκ
  have hmk : #κ.ord.ToType = κ := by rw [mk_toType, card_ord]
  have : Nonempty κ.ord.ToType := by
    apply mk_ne_zero_iff.1
    rw [hmk]
    exact (aleph0_pos.trans hκ).ne'
  exact ⟨⟨by rw [Ordinal.type_toType, hcof]⟩, this,
    (noTopOrder_iff_noMaxOrder _).1 ((Order.one_lt_cof_iff).1 (one_lt_aleph0.trans hα)), hα, hmk⟩

lemma mk_dec_eq {α : Type u} [LinearOrder α] [Infinite α] : #(Rigid.Dec α) = #α :=
  le_antisymm Rigid.Dec.mk_le (mk_le_of_injective (Rigid.Dec.sing_injective (α := α)))

/-- Rigid `R_ω`-structures of every regular uncountable dimension. -/
lemma exists_rigid_structure [Infinite k] (κ : Cardinal.{u}) (hreg : κ.IsRegular) (hκ : ℵ₀ < κ) :
    ∃ (G : ModuleCat.{u} k) (Gs : Nu → Submodule k G), Gs ⟨0⟩ = ⊤ ∧ IsRigidR Gs ∧
      Module.rank k G = κ := by
  obtain ⟨_, _, _, hα, hmk⟩ := regular_order κ hreg hκ
  haveI := Rigid.infinite_of hα
  refine ⟨ModuleCat.of k ((Rigid.Dec κ.ord.ToType →₀ k) × (Rigid.Dec κ.ord.ToType →₀ k)),
    Rigid.subs k (Rigid.regSys hα), rfl,
    Rigid.isRigidR_of_isRigidSys (Rigid.isRigidSys_regSys k hα), ?_⟩
  change Module.rank k ((Rigid.Dec κ.ord.ToType →₀ k) × (Rigid.Dec κ.ord.ToType →₀ k)) = κ
  rw [rank_prod', rank_finsupp_self', mk_dec_eq,
    add_eq_self (Cardinal.infinite_iff.1 inferInstance), hmk]

variable [Infinite k]

lemma dim_T_le (Λ : Set k) : (T Λ).dim ≤ #k :=
  (add_le_add (rank_T_V_le Λ) (rank_T_W_le Λ)).trans
    (add_eq_self (Cardinal.infinite_iff.1 inferInstance)).le

/-- Pools of every regular size `λ > |k|`, orthogonal to the outer anchor
`T_{Λ_{Y₁}}` and with a non-split class onto their anchor. -/
lemma exists_pool (lam : Cardinal.{u}) (hreg : lam.IsRegular) (hk : #k < lam) :
    ∃ (J : Type u) (_ : DecidableEq J) (σ : Anchored k J), #J = lam ∧ σ.C.dim ≤ lam ∧
      (∀ j, (σ.B j).dim ≤ lam) ∧ Kron.ABInj σ.C ∧ (∀ j, Kron.ABInj (σ.B j)) ∧
      Orth (T (LamX (nE (k := k) 1))) σ.C ∧
      (∀ j, Orth (T (LamX (nE (k := k) 1))) (σ.B j)) ∧
      ∃ α0 β0 : σ.C.V →ₗ[k] (T (LamX (nE (k := k) 1))).W,
        ¬Splits (T (LamX (nE (k := k) 1))) σ.C α0 β0 := by
  classical
  have hk0 : ℵ₀ ≤ #k := Cardinal.infinite_iff.1 inferInstance
  obtain ⟨_, _, _, hα, hmk⟩ := regular_order lam hreg (hk0.trans_lt hk)
  haveI := Rigid.infinite_of hα
  refine ⟨Rigid.Dec lam.ord.ToType, inferInstance, transportPool hα, by rw [mk_dec_eq, hmk],
    (dim_T_le _).trans hk.le, fun j ↦ ((dim_poolB hα (hmk.symm ▸ hk.le : #k ≤ #lam.ord.ToType) j).trans hmk).le,
    abInj_T _, fun j ↦ (poolSeed k).abInj_transport _ (abInj_T _) fun _ ↦ abInj_T _,
    orth_T (diff_infinite (nE_ne (by omega))) (diff_infinite (nE_ne (by omega))),
    fun j ↦ (poolSeed k).orth_transport _ (orth_poolSeed (by omega)).1
      (orth_poolSeed (by omega)).2, 0,
    betaExt (LamX (nE 0)) (LamX (nE 1)) (diff_infinite (nE_ne (k := k) (by omega : 0 ≠ 1))).nonempty.some,
    not_splits (diff_infinite (nE_ne (by omega))) (diff_infinite (nE_ne (k := k)
      (by omega : 0 ≠ 1))).nonempty.some_mem⟩

/-- Kronecker bricks of every singular dimension `κ > |k|`. -/
theorem exists_brick_singular (κ : Cardinal.{u}) (hk : #k < κ) (hreg : ¬κ.IsRegular) :
    ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T := by
  classical
  have hk0 : ℵ₀ ≤ #k := Cardinal.infinite_iff.1 inferInstance
  have hκ0 : ℵ₀ ≤ κ := hk0.trans hk.le
  have hμκ : κ.ord.cof < κ :=
    lt_of_le_of_ne (Ordinal.cof_ord_le κ) fun h ↦ hreg ⟨hκ0, h.ge⟩
  have hν0 : ℵ₀ ≤ max κ.ord.cof #k := le_max_of_le_right hk0
  set lam := Order.succ (max κ.ord.cof #k) with hlam
  have hlreg : lam.IsRegular := isRegular_succ hν0
  have hlk : #k < lam := (le_max_right _ _).trans_lt (Order.lt_succ _)
  have hlκ : lam < κ := lt_of_le_of_ne (Order.succ_le_of_lt (max_lt hμκ hk))
    fun h ↦ hreg (h ▸ hlreg)
  obtain ⟨J, _, σ, hJ, hCd, hBd, -, -, hoC, hoB, α0, β0, hns0⟩ := exists_pool lam hlreg hlk
  obtain ⟨ι, f, hf, hι⟩ := Ordinal.exists_lsub_cof κ.ord
  have hιNu : #(ι × Nu) ≤ #J := by
    rw [mk_prod, lift_id, lift_id, hι, hJ]
    have : #Nu = ℵ₀ := by simp
    rw [this]
    refine (mul_le_max_of_aleph0_le_right le_rfl).trans ?_
    refine (max_le (le_max_left _ _) (hk0.trans (le_max_right _ _))).trans (Order.le_succ _)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hιNu
  let σ' := σ.comap e
  -- cofinal regular cardinals
  let κi : ι → Cardinal.{u} := fun i ↦ Order.succ (max (f i).card lam)
  have hκi_reg : ∀ i, (κi i).IsRegular := fun i ↦
    isRegular_succ (le_max_of_le_right hlreg.aleph0_le)
  have hκi_lam : ∀ i, lam < κi i := fun i ↦ (le_max_right _ _).trans_lt (Order.lt_succ _)
  have hκi_le : ∀ i, κi i ≤ κ := fun i ↦
    Order.succ_le_of_lt (max_lt (lt_ord.1 (hf ▸ Ordinal.lt_lsub f i)) hlκ)
  have hsum : Cardinal.sum κi = κ := by
    refine le_antisymm ?_ ?_
    · refine (sum_le_sum _ (fun _ ↦ κ) hκi_le).trans ?_
      rw [sum_const', hι]
      exact (mul_le_mul_left (Ordinal.cof_ord_le κ) κ).trans (mul_eq_self hκ0).le
    · by_contra h
      rw [not_le] at h
      obtain ⟨i, hi⟩ := Ordinal.lt_lsub_iff.1 (hf.symm ▸ ord_lt_ord.2 h)
      exact (((ord_le.1 hi).trans_lt ((le_max_left _ _).trans_lt (Order.lt_succ _))).trans_le
        (le_sum κi i)).false
  -- the rigid structures
  choose G Gs h0 hrig hrank using fun i ↦
    exists_rigid_structure (k := k) (κi i) (hκi_reg i) (hlreg.aleph0_le.trans_lt (hκi_lam i))
  let Gsi : ∀ i, ι × Nu → Submodule k (G i) := fun i p ↦ if p.1 = i then Gs i p.2 else ⊥
  have hGsi0 : ∀ i, Gsi i (i, ⟨0⟩) = ⊤ := fun i ↦ by simp [Gsi, h0]
  have hrigi : ∀ i, IsRigidR (Gsi i) := fun i ψ hψ ↦ hrig i ψ fun n x hx ↦ by
    have := hψ (i, n) x (by simpa [Gsi] using hx)
    simpa [Gsi] using this
  have hnt : ∀ i, Nontrivial (G i) := fun i ↦ rank_pos_iff_nontrivial.1
    (by rw [hrank]; exact aleph0_pos.trans_le (hlreg.aleph0_le.trans (hκi_lam i).le))
  let H : ι → Kron k := fun i ↦ σ'.transport (Gsi i)
  have hHb : ∀ i, IsBrickKron (H i) := fun i ↦
    σ'.isBrick_transport (Gsi i) (hGsi0 i) (hrigi i)
  have hSV : Module.rank k (σ'.SV Set.univ) ≤ lam :=
    σ'.rank_SV_le hlreg.aleph0_le (hιNu.trans hJ.le) ((rank_V_le_dim _).trans hCd)
      fun j ↦ (rank_V_le_dim _).trans (hBd (e j))
  have hSW : Module.rank k (σ'.SW Set.univ) ≤ lam :=
    σ'.rank_SW_le hlreg.aleph0_le (hιNu.trans hJ.le) ((rank_W_le_dim _).trans hCd)
      fun j ↦ (rank_W_le_dim _).trans (hBd (e j))
  have hHd : ∀ i, (H i).dim = κi i := fun i ↦ by
    rw [σ'.dim_transport (Gsi i) (hGsi0 i) (by rw [hrank]; exact (hlreg.aleph0_le.trans
      (hκi_lam i).le)) (by rw [hrank]; exact hSV.trans (hκi_lam i).le)
      (by rw [hrank]; exact hSW.trans (hκi_lam i).le), hrank]
  have hHH : ∀ i i', i ≠ i' → ∀ g : H i ⟶ H i', g = 0 := fun i i' hii' ↦
    σ'.transport_hom_eq_zero (Gsi i) (Gsi i') (hGsi0 i) fun Ψ hΨ ↦ LinearMap.ext fun g ↦ by
      have := hΨ (i, ⟨0⟩) g (by rw [hGsi0]; trivial)
      simpa [Gsi, hii'] using this
  have hHo : ∀ i, Orth (T (LamX (nE (k := k) 1))) (H i) := fun i ↦
    σ'.orth_transport (Gsi i) hoC fun j ↦ hoB (e j)
  have hcls : ∀ i, ∃ αc βc : (H i).V →ₗ[k] (T (LamX (nE (k := k) 1))).W,
      ¬Splits (T (LamX (nE 1))) (H i) αc βc := fun i ↦ by
    obtain ⟨g0, hg0⟩ := exists_ne (0 : G i)
    exact σ'.exists_not_splits_transport (Gsi i) hns0 (j0 := (i, ⟨0⟩))
      (by rw [hGsi0]; trivial) hg0
  choose αc βc hαβ using hcls
  refine ⟨extFamily (T (LamX (nE 1))) H αc βc, ?_, isBrick_extFamily (isBrick _ (lamX_nonempty _))
    hHb (fun i ↦ (hHo i).1) (fun i ↦ (hHo i).2) hHH hαβ⟩
  rw [dim_extFamily]
  simp only [hHd]
  rw [hsum]
  exact add_eq_right hκ0 ((dim_T_le _).trans hk.le)

/-- Göbel–Simson, Corollary 1.3, beyond `|k|`: Kronecker bricks of every dimension
`κ > |k|`. -/
theorem exists_brick_large (κ : Cardinal.{u}) (hk : #k < κ) :
    ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T := by
  by_cases hreg : κ.IsRegular
  · exact exists_brick_regular κ hreg hk
  · exact exists_brick_singular κ hk hreg

end Bricks

/-- The large case of Göbel–Simson, Corollary 1.3 (formerly a hypothesis). -/
theorem kroneckerBricksLarge : KroneckerBricksLarge.{u} := fun _ _ _ κ hk ↦
  Bricks.exists_brick_large κ hk

end LargeIndecomposable
