module

public import LargeIndecomposable.KroneckerBricks.Seed
public import LargeIndecomposable.KroneckerBricks.RigidRegular

/-!
# Kronecker bricks of regular dimension

The dimension of a transport `H` of a structure on `G` is `dim G` when the
anchored family is small (`Bricks.Anchored.dim_transport`). Transporting the
rigid map system of a regular uncountable cardinal `κ > |k|` along the
countable `T_Λ` seed gives a Kronecker brick of dimension `κ`
(`Bricks.exists_brick_regular`).
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

namespace Anchored

variable {J : Type u} [DecidableEq J] (σ : Anchored k J)
variable {G : Type u} [AddCommGroup G] [Module k G] (Gs : J → Submodule k G)

lemma rank_le_tV {j0 : J} (h0 : Gs j0 = ⊤) : Module.rank k G ≤ Module.rank k (σ.tV Gs) := by
  let f : G →ₗ[k] σ.tV Gs :=
    ((TensorProduct.mk k G (σ.SV Set.univ)).flip (σ.iV j0 (σ.c0, 0))).codRestrict (σ.tV Gs)
      fun g ↦ σ.genV_mem Gs (h0 ▸ Submodule.mem_top : g ∈ Gs j0) _
  refine f.rank_le_of_injective fun g g' h ↦ ?_
  have := congrArg Subtype.val h
  change g ⊗ₜ σ.iV j0 (σ.c0, 0) = g' ⊗ₜ σ.iV j0 (σ.c0, 0) at this
  rw [iV_anchor] at this
  exact tmul_left_inj σ.anchor_ne_zero this

theorem dim_transport {j0 : J} (h0 : Gs j0 = ⊤) (hG : ℵ₀ ≤ Module.rank k G)
    (hV : Module.rank k (σ.SV Set.univ) ≤ Module.rank k G)
    (hW : Module.rank k (σ.SW Set.univ) ≤ Module.rank k G) :
    (σ.transport Gs).dim = Module.rank k G := by
  have h1 : Module.rank k (σ.tV Gs) ≤ Module.rank k G := (Submodule.rank_le _).trans (by
    rw [rank_tensorProduct']
    exact (mul_le_mul_right hV _).trans (mul_eq_self hG).le)
  have h2 : Module.rank k (σ.tW Gs) ≤ Module.rank k G := (Submodule.rank_le _).trans (by
    rw [rank_tensorProduct']
    exact (mul_le_mul_right hW _).trans (mul_eq_self hG).le)
  change Module.rank k (σ.tV Gs) + Module.rank k (σ.tW Gs) = _
  exact le_antisymm ((add_le_add h1 h2).trans (add_eq_self hG).le)
    ((σ.rank_le_tV Gs h0).trans le_self_add)

lemma rank_sum_le {M : J → Type u} [∀ j, AddCommGroup (M j)] [∀ j, Module k (M j)]
    {D : Cardinal.{u}} (hD : ℵ₀ ≤ D) (hJ : #J ≤ D) (hM : ∀ j, Module.rank k (M j) ≤ D)
    (S : Set J) : Module.rank k (Π₀ j : S, M j) ≤ D := by
  change Module.rank k (DirectSum S fun j ↦ M j) ≤ D
  rw [rank_directSum]
  refine (sum_le_sum _ (fun _ : S ↦ D) fun j ↦ hM j).trans ?_
  rw [sum_const']
  exact (mul_le_mul_left ((mk_set_le S).trans hJ) D).trans (mul_eq_self hD).le

lemma rank_SV_le {D : Cardinal.{u}} (hD : ℵ₀ ≤ D) (hJ : #J ≤ D)
    (hC : Module.rank k σ.C.V ≤ D) (hB : ∀ j, Module.rank k (σ.B j).V ≤ D) :
    Module.rank k (σ.SV Set.univ) ≤ D := by
  rw [rank_prod']
  exact (add_le_add hC (rank_sum_le hD hJ hB _)).trans (add_eq_self hD).le

lemma rank_SW_le {D : Cardinal.{u}} (hD : ℵ₀ ≤ D) (hJ : #J ≤ D)
    (hC : Module.rank k σ.C.W ≤ D) (hB : ∀ j, Module.rank k (σ.B j).W ≤ D) :
    Module.rank k (σ.SW Set.univ) ≤ D := by
  rw [rank_prod']
  exact (add_le_add hC (rank_sum_le hD hJ hB _)).trans (add_eq_self hD).le

end Anchored

variable [Infinite k]

omit [Infinite k] in
lemma rank_T_V_le (Λ : Set k) : Module.rank k (T Λ).V ≤ #k := by
  change Module.rank k (Λ →₀ k) ≤ _
  rw [rank_finsupp_self']
  exact mk_set_le Λ

lemma rank_T_W_le (Λ : Set k) : Module.rank k (T Λ).W ≤ #k := by
  change Module.rank k (k × (Λ →₀ k)) ≤ _
  rw [rank_prod', rank_finsupp_self', Module.rank_self]
  have hk : ℵ₀ ≤ #k := Cardinal.infinite_iff.1 inferInstance
  exact (add_le_add (one_le_aleph0.trans hk) (mk_set_le Λ)).trans (add_eq_self hk).le

lemma omegaSeed_SV_le : Module.rank k ((omegaSeed k).SV Set.univ) ≤ #k :=
  have hk : ℵ₀ ≤ #k := Cardinal.infinite_iff.1 inferInstance
  (omegaSeed k).rank_SV_le hk (by simp) (rank_T_V_le _) fun _ ↦ rank_T_V_le _

lemma omegaSeed_SW_le : Module.rank k ((omegaSeed k).SW Set.univ) ≤ #k :=
  have hk : ℵ₀ ≤ #k := Cardinal.infinite_iff.1 inferInstance
  (omegaSeed k).rank_SW_le hk (by simp) (rank_T_W_le _) fun _ ↦ rank_T_W_le _

/-- Kronecker bricks of dimension `#α` for a well-order `α` of regular uncountable type
with `|k| ≤ #α`. -/
theorem exists_brick_of_order (α : Type u) [LinearOrder α] [WellFoundedLT α] [Nonempty α]
    [NoMaxOrder α] [IsRegularCardinalOrder α] (hα : ℵ₀ < Order.cof α) (hk : #k ≤ #α) :
    ∃ T : Kron k, T.dim = #α ∧ IsBrickKron T := by
  classical
  haveI := Rigid.infinite_of hα
  have hα0 : ℵ₀ ≤ #α := Cardinal.infinite_iff.1 inferInstance
  have hX : #(Rigid.Dec α) = #α :=
    le_antisymm Rigid.Dec.mk_le (mk_le_of_injective (Rigid.Dec.sing_injective (α := α)))
  have hrank : Module.rank k ((Rigid.Dec α →₀ k) × (Rigid.Dec α →₀ k)) = #α := by
    rw [rank_prod', rank_finsupp_self', hX, add_eq_self hα0]
  have : Nontrivial ((Rigid.Dec α →₀ k) × (Rigid.Dec α →₀ k)) :=
    nontrivial_of_ne (Finsupp.single (Rigid.Dec.sing (Classical.arbitrary α)) 1, 0) 0
      fun h ↦ Finsupp.single_ne_zero.2 one_ne_zero (congrArg Prod.fst h)
  refine ⟨(omegaSeed k).transport (Rigid.subs k (Rigid.regSys hα)), ?_, ?_⟩
  · rw [(omegaSeed k).dim_transport _ (j0 := ⟨0⟩) (Rigid.subs_zero _) (hrank ▸ hα0)
      (hrank ▸ omegaSeed_SV_le.trans hk) (hrank ▸ omegaSeed_SW_le.trans hk), hrank]
  · exact (omegaSeed k).isBrick_transport _ (j0 := ⟨0⟩) (Rigid.subs_zero _)
      (Rigid.isRigidR_of_isRigidSys (Rigid.isRigidSys_regSys k hα))

/-- Kronecker bricks of every regular dimension `κ > |k|`. -/
theorem exists_brick_regular (κ : Cardinal.{u}) (hreg : κ.IsRegular) (hk : #k < κ) :
    ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T := by
  have hk0 : ℵ₀ ≤ #k := Cardinal.infinite_iff.1 inferInstance
  have hcof : Order.cof κ.ord.ToType = κ := by
    rw [Ordinal.cof_toType]
    exact hreg.cof_eq
  have hα : ℵ₀ < Order.cof κ.ord.ToType := by
    rw [hcof]
    exact hk0.trans_lt hk
  have : IsRegularCardinalOrder κ.ord.ToType := ⟨by rw [Ordinal.type_toType, hcof]⟩
  have hmk : #κ.ord.ToType = κ := by rw [mk_toType, card_ord]
  have : Nonempty κ.ord.ToType := by
    apply mk_ne_zero_iff.1
    rw [hmk]
    exact (aleph0_pos.trans_le hreg.aleph0_le).ne'
  have : NoMaxOrder κ.ord.ToType :=
    (noTopOrder_iff_noMaxOrder _).1 ((Order.one_lt_cof_iff).1 (one_lt_aleph0.trans hα))
  obtain ⟨T, hT, hb⟩ := exists_brick_of_order (k := k) κ.ord.ToType hα (hmk.symm ▸ hk.le)
  exact ⟨T, hT.trans hmk, hb⟩

end Bricks

end LargeIndecomposable
