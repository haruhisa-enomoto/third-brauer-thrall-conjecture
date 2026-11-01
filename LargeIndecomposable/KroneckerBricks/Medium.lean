module

public import LargeIndecomposable.KroneckerBricks.ExtensionFamily
public import LargeIndecomposable.KroneckerBricks.NonSplit
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Kronecker bricks of dimension up to `2^|k|`

Identify the infinite field `k` with `((k × Bool) × ℕ) ⊕ ℕ`. For `X ⊆ k` the set
`Λ_X` of the points `((a, [a ∈ X]), n)` gives pairwise Hom-orthogonal bricks
`T_{Λ_X}` (`Λ_X \ Λ_Y` is infinite for `X ≠ Y`), all orthogonal to `T_{Λ₀}`
for the `ℕ` part `Λ₀`. Gluing `ν ≤ 2^|k|` of them over `T_{Λ₀}` along the
explicit non-split extensions gives a brick of dimension `max(|k|, ν)`
(`exists_brick_of_le_two_pow`). So Göbel–Simson's Corollary 1.3 is proved for
`κ ≤ 2^|k|`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair _root_.Cardinal
open scoped Cardinal

universe u

variable {k : Type u} [Field k]

namespace Bricks

variable [Infinite k]

omit [Field k] in
lemma mk_code : Cardinal.mk (((k × Bool) × ℕ) ⊕ ℕ) = Cardinal.mk k := by
  have h1 : Cardinal.aleph0 ≤ Cardinal.mk k := Cardinal.infinite_iff.1 inferInstance
  simp only [mk_sum, mk_prod, mk_fintype, Fintype.card_bool, mk_nat, lift_aleph0, lift_uzero,
    lift_ofNat, Nat.cast_ofNat]
  have h2 : (2 : Cardinal) ≤ Cardinal.mk k := Cardinal.ofNat_lt_aleph0.le.trans h1
  rw [Cardinal.mul_eq_left h1 h2 (by norm_num),
    Cardinal.mul_eq_left h1 h1 aleph0_ne_zero, Cardinal.add_eq_left h1 h1]

variable (k) in
/-- An identification `k ≃ ((k × Bool) × ℕ) ⊕ ℕ`. -/
def code : k ≃ (((k × Bool) × ℕ) ⊕ ℕ) := (Cardinal.eq.1 mk_code.symm).some

open Classical in
/-- The set `Λ_X`. -/
def LamX (X : Set k) : Set k := {t | ∃ (a : k) (n : ℕ), code k t = Sum.inl ((a, decide (a ∈ X)), n)}

/-- The set `Λ₀`. -/
def Lam0 : Set k := {t | ∃ n : ℕ, code k t = Sum.inr n}

open Classical in
/-- The point `((a, [a ∈ X]), n)` of `Λ_X`. -/
def ptX (X : Set k) (a : k) (n : ℕ) : k := (code k).symm (Sum.inl ((a, decide (a ∈ X)), n))

lemma ptX_mem (X : Set k) (a : k) (n : ℕ) : ptX X a n ∈ LamX X :=
  ⟨a, n, by simp [ptX]⟩

lemma ptX_injective (X : Set k) (a : k) : Function.Injective (ptX X a) := by
  intro n m h
  have := congrArg (code k) h
  simp [ptX] at this
  exact this

lemma ptX_not_mem_of (X Y : Set k) (a : k) (h : ¬(a ∈ X ↔ a ∈ Y)) (n : ℕ) : ptX X a n ∉ LamX Y := by
  rintro ⟨a', n', h'⟩
  simp only [ptX, Equiv.apply_symm_apply, Sum.inl.injEq, Prod.mk.injEq] at h'
  obtain ⟨⟨rfl, hd⟩, -⟩ := h'
  apply h
  classical
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp_all

lemma ptX_not_mem_lam0 (X : Set k) (a : k) (n : ℕ) : ptX X a n ∉ Lam0 := by
  rintro ⟨m, hm⟩
  simp [ptX] at hm

lemma diff_infinite {X Y : Set k} (h : X ≠ Y) : (LamX X \ LamX Y).Infinite := by
  obtain ⟨a, ha⟩ : ∃ a, ¬(a ∈ X ↔ a ∈ Y) := by
    by_contra hc
    push Not at hc
    exact h (Set.ext hc)
  exact Set.infinite_of_injective_forall_mem (ptX_injective X a)
    fun n ↦ ⟨ptX_mem X a n, ptX_not_mem_of X Y a ha n⟩

lemma diff_lam0_infinite (X : Set k) : (LamX X \ Lam0).Infinite := by
  obtain ⟨a⟩ := (inferInstance : Nonempty k)
  exact Set.infinite_of_injective_forall_mem (ptX_injective X a)
    fun n ↦ ⟨ptX_mem X a n, ptX_not_mem_lam0 X a n⟩

/-- The point `n` of `Λ₀`. -/
def pt0 (n : ℕ) : k := (code k).symm (Sum.inr n)

lemma lam0_diff_infinite (X : Set k) : (Lam0 \ LamX X).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := pt0) (fun n m h ↦ ?_) fun n ↦ ⟨⟨n, by simp [pt0]⟩, ?_⟩
  · have := congrArg (code k) h
    simpa [pt0] using this
  · rintro ⟨a, m, h⟩
    simp [pt0] at h

lemma mk_lamX (X : Set k) : Cardinal.mk (LamX X) = Cardinal.mk k := by
  have hinj : Function.Injective (fun p : k × ℕ ↦ ptX X p.1 p.2) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ h
    have := congrArg (code k) h
    simp only [ptX, Equiv.apply_symm_apply, Sum.inl.injEq, Prod.mk.injEq] at this
    obtain ⟨⟨rfl, -⟩, rfl⟩ := this
    rfl
  have hrange : Set.range (fun p : k × ℕ ↦ ptX X p.1 p.2) = LamX X := by
    ext t
    constructor
    · rintro ⟨⟨a, n⟩, rfl⟩; exact ptX_mem X a n
    · rintro ⟨a, n, h⟩
      exact ⟨(a, n), by simp only [ptX, ← h, Equiv.symm_apply_apply]⟩
  rw [← hrange, Cardinal.mk_range_eq _ hinj, mk_prod, mk_nat, lift_uzero, lift_aleph0,
    Cardinal.mul_eq_left (Cardinal.infinite_iff.1 inferInstance)
      (Cardinal.infinite_iff.1 inferInstance) aleph0_ne_zero]

lemma lam0_nonempty : (Lam0 : Set k).Nonempty := ⟨pt0 0, 0, by simp [pt0]⟩

/-- Göbel–Simson bricks for dimensions between `|k|` and `2^|k|`. -/
theorem exists_brick_of_le_two_pow (κ : Cardinal.{u}) (h1 : Cardinal.mk k ≤ κ)
    (h2 : κ ≤ 2 ^ Cardinal.mk k) : ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T := by
  classical
  have hk : Cardinal.aleph0 ≤ Cardinal.mk k := Cardinal.infinite_iff.1 inferInstance
  have hκ : Cardinal.aleph0 ≤ κ := hk.trans h1
  obtain ⟨S, hS⟩ := Cardinal.le_mk_iff_exists_subset.1 (show κ ≤ Cardinal.mk (Set.univ : Set (Set k))
    by rwa [Cardinal.mk_univ, Cardinal.mk_set])
  let B : S → Kron k := fun i ↦ T (LamX i.1)
  let l : S → k := fun i ↦ (diff_lam0_infinite i.1).nonempty.some
  have hl : ∀ i : S, l i ∈ LamX i.1 \ Lam0 := fun i ↦ (diff_lam0_infinite i.1).nonempty.some_mem
  let β : ∀ i : S, (B i).V →ₗ[k] (T Lam0).W := fun i ↦ betaExt (LamX i.1) Lam0 (l i)
  refine ⟨extFamily (T Lam0) B (fun _ ↦ 0) β, ?_, isBrick_extFamily (isBrick _ lam0_nonempty)
    (fun i ↦ isBrick _ ((diff_lam0_infinite i.1).nonempty.mono Set.sdiff_subset))
    (fun i ↦ hom_eq_zero (lam0_diff_infinite i.1)) (fun i ↦ hom_eq_zero (diff_lam0_infinite i.1))
    (fun i j hij ↦ hom_eq_zero (diff_infinite fun h ↦ hij (Subtype.ext h)))
    (fun i ↦ not_splits (diff_lam0_infinite i.1) (hl i))⟩
  have hS' : Cardinal.mk S = κ := hS.2
  have hκ0 : κ ≠ 0 := (Cardinal.aleph0_pos.trans_le hκ).ne'
  have hrV : ∀ i : S, Module.rank k ((B i).V) = Cardinal.mk k := fun i ↦ by
    change Module.rank k (LamX i.1 →₀ k) = _
    rw [rank_finsupp_self, Cardinal.lift_id, mk_lamX]
  have hrW : ∀ i : S, Module.rank k ((B i).W) = Cardinal.mk k := fun i ↦ by
    change Module.rank k (k × (LamX i.1 →₀ k)) = _
    rw [rank_prod', Module.rank_self, rank_finsupp_self, Cardinal.lift_id, mk_lamX,
      Cardinal.add_eq_right hk (Cardinal.one_le_aleph0.trans hk)]
  have hsumV : Module.rank k (SumV B) = κ := by
    change Module.rank k (DirectSum S fun i ↦ ((B i).V : Type u)) = κ
    rw [rank_directSum, show (fun i : S ↦ Module.rank k ((B i).V)) = fun _ ↦ Cardinal.mk k from
      funext hrV, Cardinal.sum_const', hS', Cardinal.mul_eq_left hκ h1 (Cardinal.mk_ne_zero k)]
  have hsumW : Module.rank k (SumW B) = κ := by
    change Module.rank k (DirectSum S fun i ↦ ((B i).W : Type u)) = κ
    rw [rank_directSum, show (fun i : S ↦ Module.rank k ((B i).W)) = fun _ ↦ Cardinal.mk k from
      funext hrW, Cardinal.sum_const', hS', Cardinal.mul_eq_left hκ h1 (Cardinal.mk_ne_zero k)]
  have h0 : Cardinal.mk (Lam0 : Set k) ≤ κ := (Cardinal.mk_set_le _).trans h1
  change Module.rank k ((Lam0 →₀ k) × SumV B) + Module.rank k ((k × (Lam0 →₀ k)) × SumW B) = κ
  rw [rank_prod', rank_prod', rank_prod', hsumV, hsumW, Module.rank_self, rank_finsupp_self,
    Cardinal.lift_id, Cardinal.add_eq_right hκ h0,
    Cardinal.add_eq_right hκ ((add_le_add (Cardinal.one_le_aleph0.trans hκ) h0).trans
      (Cardinal.add_eq_self hκ).le), Cardinal.add_eq_self hκ]

end Bricks

/-- The part of Göbel–Simson Corollary 1.3 still needed: Kronecker bricks of
every dimension `κ > 2^|k|`. -/
def KroneckerBricksHuge : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (κ : Cardinal.{u}), 2 ^ Cardinal.mk k < κ →
    ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T

/-- The large case of Göbel–Simson Corollary 1.3 from its huge case. -/
theorem kroneckerBricksLarge_of_huge (H : KroneckerBricksHuge.{u}) : KroneckerBricksLarge.{u} := by
  intro k _ _ κ hκ
  rcases le_or_gt κ (2 ^ Cardinal.mk k) with h | h
  · exact Bricks.exists_brick_of_le_two_pow κ hκ.le h
  · exact H k κ h

end LargeIndecomposable
