module

public import Mathlib

/-!
# Gradings by a group

A `G`-grading of a `k`-vector space `V` with finite support is a family of projections
`proj g` (orthogonal, summing to the identity over a finite set `supp`).
`GrAlg G k A` grades a `k`-algebra multiplicatively; `GrMod` grades an `A`-module
compatibly (`A_g · M_h ⊆ M_{gh}`).

A `k`-linear map is homogeneous of degree `h` when it maps `V_g` into `W_{gh}`. Every
`A`-linear map between graded modules is the finite sum of its homogeneous components
(`sum_comp`), and the components are `A`-linear (`comp`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Graded

open Module

variable {G : Type*} [Group G] [DecidableEq G] {k : Type*} [Field k]

/-- A finite grading of a `k`-vector space. -/
structure Grading (G : Type*) [Group G] (k V : Type*) [Field k] [AddCommGroup V]
    [Module k V] where
  proj : G → V →ₗ[k] V
  supp : Finset G
  orth : ∀ g h, g ≠ h → ∀ v, proj g (proj h v) = 0
  out : ∀ g ∉ supp, ∀ v, proj g v = 0
  sum_eq : ∀ v, ∑ g ∈ supp, proj g v = v

namespace Grading

variable {V : Type*} [AddCommGroup V] [Module k V] (γ : Grading G k V)

/-- Homogeneous elements of degree `g`. -/
def Mem (g : G) (v : V) : Prop := γ.proj g v = v

lemma proj_proj (g : G) (v : V) : γ.proj g (γ.proj g v) = γ.proj g v := by
  conv_rhs => rw [← γ.sum_eq v]
  rw [map_sum]
  by_cases hg : g ∈ γ.supp
  · rw [Finset.sum_eq_single g]
    · intro h _ hh; exact γ.orth g h (Ne.symm hh) v
    · intro h; exact absurd hg h
  · simp [γ.out g hg]

lemma mem_proj (g : G) (v : V) : γ.Mem g (γ.proj g v) := γ.proj_proj g v

lemma proj_of_mem {g h : G} {v : V} (hv : γ.Mem h v) (hgh : g ≠ h) : γ.proj g v = 0 := by
  rw [← hv]; exact γ.orth g h hgh v

lemma mem_zero (g : G) : γ.Mem g 0 := by simp [Mem]

lemma mem_add {g : G} {v w : V} (hv : γ.Mem g v) (hw : γ.Mem g w) : γ.Mem g (v + w) := by
  simp only [Mem, map_add] at *; rw [hv, hw]

lemma mem_smul {g : G} (c : k) {v : V} (hv : γ.Mem g v) : γ.Mem g (c • v) := by
  simp only [Mem, map_smul] at *; rw [hv]

lemma mem_sum {g : G} {ι : Type*} (s : Finset ι) (f : ι → V) (hf : ∀ i ∈ s, γ.Mem g (f i)) :
    γ.Mem g (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using γ.mem_zero g
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact γ.mem_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- The sum of the projections over any finite superset of the support. -/
lemma sum_eq_of_subset {T : Finset G} (hT : γ.supp ⊆ T) (v : V) :
    ∑ g ∈ T, γ.proj g v = v := by
  rw [← Finset.sum_subset hT fun g _ hg ↦ γ.out g hg v]
  exact γ.sum_eq v

/-- Two vectors with the same projections are equal. -/
lemma ext_proj {v w : V} (h : ∀ g, γ.proj g v = γ.proj g w) : v = w := by
  rw [← γ.sum_eq v, ← γ.sum_eq w]
  exact Finset.sum_congr rfl fun g _ ↦ h g

end Grading

/-- A `k`-algebra graded by `G`. -/
structure GrAlg (G : Type*) [Group G] (k A : Type*) [Field k] [Ring A] [Algebra k A] extends
    Grading G k A where
  one_mem : toGrading.Mem 1 1
  mul_mem : ∀ g h a b, toGrading.Mem g a → toGrading.Mem h b → toGrading.Mem (g * h) (a * b)

variable {A : Type*} [Ring A] [Algebra k A]

/-- A graded module over a graded algebra. -/
structure GrMod (Γ : GrAlg G k A) (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] extends Grading G k M where
  smul_mem : ∀ g h (a : A) (m : M), Γ.Mem g a → toGrading.Mem h m →
    toGrading.Mem (g * h) (a • m)

namespace GrMod

variable {Γ : GrAlg G k A}
variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable (μ : GrMod Γ M)

/-- Homogeneous scalars move the projections. -/
lemma proj_smul {x : G} {a : A} (ha : Γ.Mem x a) (g : G) (m : M) :
    μ.proj (x * g) (a • m) = a • μ.proj g m := by
  conv_lhs => rw [← μ.sum_eq m]
  rw [Finset.smul_sum, map_sum]
  by_cases hg : g ∈ μ.supp
  · rw [Finset.sum_eq_single g]
    · exact μ.smul_mem x g a _ ha (μ.mem_proj g m)
    · intro h _ hh
      exact μ.proj_of_mem (μ.smul_mem x h a _ ha (μ.mem_proj h m))
        (fun e ↦ hh (mul_left_cancel e).symm)
    · intro h; exact absurd hg h
  · rw [μ.out g hg, smul_zero]
    refine Finset.sum_eq_zero fun h hh ↦ ?_
    exact μ.proj_of_mem (μ.smul_mem x h a _ ha (μ.mem_proj h m))
      (fun e ↦ hg (mul_left_cancel e ▸ hh))

/-- The projections of a scalar multiple. -/
lemma proj_smul' (a : A) (g : G) (m : M) :
    μ.proj g (a • m) = ∑ x ∈ Γ.supp, Γ.proj x a • μ.proj (x⁻¹ * g) m := by
  conv_lhs => rw [← Γ.sum_eq a, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [show g = x * (x⁻¹ * g) by group, μ.proj_smul (Γ.mem_proj x a), mul_inv_cancel_left]

end GrMod

end LargeIndecomposable.Graded
