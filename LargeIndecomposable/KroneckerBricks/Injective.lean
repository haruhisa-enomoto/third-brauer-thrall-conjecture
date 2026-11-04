module

public import LargeIndecomposable.KroneckerBricks.Transport
public import LargeIndecomposable.KroneckerBricks.Small
public import Mathlib.RingTheory.Flat.Basic

/-!
# Injective arrow maps

A Kronecker module `(V, W; a, b)` has *injective arrows* if `a` and `b` are both
injective (`Kron.ABInj`), as required of the rigid families in Theorem 5.6. The
bricks `T_Λ` have injective arrows (`Bricks.abInj_T`); gluing along a family and
transport preserve the property (`Bricks.abInj_extFamily`,
`Bricks.Anchored.abInj_transport`), because the arrow maps are block triangular
with injective diagonal blocks, and tensoring over a field preserves injectivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

/-- Both arrow maps of a Kronecker module are injective. -/
def Kron.ABInj (X : Kron k) : Prop := Function.Injective X.a.hom ∧ Function.Injective X.b.hom

namespace Bricks

lemma diagMap_apply (Λ : Set k) (c : Λ →₀ k) (l : Λ) : diagMap Λ c l = (l : k) * c l := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.coe_add, Pi.add_apply, hf, hg, mul_add]
  | single m t =>
    rw [diagMap_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]

/-- The bricks `T_Λ` have injective arrows. -/
lemma abInj_T (Λ : Set k) : Kron.ABInj (T Λ) := by
  classical
  refine ⟨fun x y h ↦ congrArg Prod.snd h, ?_⟩
  change Function.Injective ((sumMap Λ).prod (diagMap Λ))
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have h1 : sumMap Λ c = 0 := congrArg Prod.fst hc
  have h2 : diagMap Λ c = 0 := congrArg Prod.snd hc
  have hsupp : ∀ l : Λ, (l : k) ≠ 0 → c l = 0 := fun l hl ↦ by
    have := diagMap_apply Λ c l
    rw [h2, Finsupp.coe_zero, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hl
  by_cases h0 : (0 : k) ∈ Λ
  · have hc : c = Finsupp.single ⟨0, h0⟩ (c ⟨0, h0⟩) := by
      ext l
      by_cases hl : l = ⟨0, h0⟩
      · subst hl; simp
      · rw [Finsupp.single_apply, ite_cond_eq_false _ _ (eq_false (Ne.symm hl))]
        exact hsupp l fun h ↦ hl (Subtype.ext h)
    rw [hc, sumMap_single] at h1
    rw [hc, h1, Finsupp.single_zero]
  · ext l
    exact hsupp l fun h ↦ h0 (h ▸ l.2)

section ExtFamily

variable {ι : Type u} [DecidableEq ι] {C : Kron k} {B : ι → Kron k}

lemma famMap_injective {aC : C.V →ₗ[k] C.W} {g : ∀ i, (B i).V →ₗ[k] (B i).W}
    (γ : ∀ i, (B i).V →ₗ[k] C.W) (hC : Function.Injective aC) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (famMap C B aC g γ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨v, x⟩ h
  have hx : x = 0 := DFinsupp.ext fun i ↦ by
    have := congrArg (fun p ↦ p.2 i) h
    rw [famMap_snd] at this
    exact hg i (this.trans (map_zero _).symm)
  subst hx
  have := congrArg Prod.fst h
  rw [famMap_fst] at this
  simp only [map_zero, add_zero] at this
  rw [hC (this.trans (map_zero aC).symm)]
  rfl

/-- Gluing modules with injective arrows gives a module with injective arrows. -/
lemma abInj_extFamily (α β : ∀ i, (B i).V →ₗ[k] C.W) (hC : Kron.ABInj C) (hB : ∀ i, Kron.ABInj (B i)) :
    Kron.ABInj (extFamily C B α β) :=
  ⟨famMap_injective α hC.1 fun i ↦ (hB i).1, famMap_injective β hC.2 fun i ↦ (hB i).2⟩

lemma abInj_subExt (α β : ∀ i, (B i).V →ₗ[k] C.W) (hC : Kron.ABInj C) (hB : ∀ i, Kron.ABInj (B i))
    (S : Set ι) : Kron.ABInj (subExt C B α β S) :=
  abInj_extFamily _ _ hC fun i ↦ hB i

end ExtFamily

namespace Anchored

variable {J : Type u} [DecidableEq J] (σ : Anchored k J)

/-- Transport preserves injective arrows. -/
lemma abInj_transport {G : Type u} [AddCommGroup G] [Module k G] (Gs : J → Submodule k G)
    (hC : Kron.ABInj σ.C) (hB : ∀ j, Kron.ABInj (σ.B j)) : Kron.ABInj (σ.transport Gs) := by
  have h := abInj_subExt σ.α σ.β hC hB Set.univ
  refine ⟨fun x y hxy ↦ Subtype.ext ?_, fun x y hxy ↦ Subtype.ext ?_⟩
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := G) (σ.aS Set.univ) h.1
      (congrArg Subtype.val hxy)
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := G) (σ.bS Set.univ) h.2
      (congrArg Subtype.val hxy)

end Anchored

end Bricks

end LargeIndecomposable
