module

public import LargeIndecomposable.Foundations.Gradings.Basic

/-!
# Homogeneous maps and components

`IsHomog μ ν h f`: `f` maps degree `g` into degree `g h`. `comp μ ν h f` is the degree-`h`
component of an `A`-linear map; it is `A`-linear (`comp`), homogeneous of degree `h`
(`isHomog_comp`), and `f` is the sum of its components (`sum_comp`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Graded

open Module

variable {G : Type*} [Group G] [DecidableEq G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] {Γ : GrAlg G k A}
variable {M N L : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [AddCommGroup L] [Module A L] [Module k L] [IsScalarTower k A L]
variable (μ : GrMod Γ M) (ν : GrMod Γ N) (ρ : GrMod Γ L)

/-- Homogeneous of degree `h`. -/
def IsHomog (h : G) (f : M →ₗ[A] N) : Prop :=
  ∀ g m, μ.Mem g m → ν.Mem (g * h) (f m)

variable {μ ν ρ}

lemma IsHomog.comp {h h' : G} {f : M →ₗ[A] N} {f' : N →ₗ[A] L} (hf : IsHomog μ ν h f)
    (hf' : IsHomog ν ρ h' f') : IsHomog μ ρ (h * h') (f' ∘ₗ f) := fun g m hm ↦ by
  rw [← mul_assoc]; exact hf' _ _ (hf g m hm)

lemma isHomog_id : IsHomog μ μ 1 LinearMap.id := fun g m hm ↦ by simpa using hm

/-- A homogeneous map moves projections. -/
lemma IsHomog.proj_apply {h : G} {f : M →ₗ[A] N} (hf : IsHomog μ ν h f) (x : G) (m : M) :
    ν.proj (x * h) (f m) = f (μ.proj x m) := by
  conv_lhs => rw [← μ.sum_eq m, map_sum, map_sum]
  by_cases hx : x ∈ μ.supp
  · rw [Finset.sum_eq_single x]
    · exact hf x _ (μ.mem_proj x m)
    · intro g _ hg
      exact ν.proj_of_mem (hf g _ (μ.mem_proj g m)) (fun e ↦ hg (mul_right_cancel e).symm)
    · intro h'; exact absurd hx h'
  · rw [μ.out x hx, map_zero]
    refine Finset.sum_eq_zero fun g hg ↦ ν.proj_of_mem (hf g _ (μ.mem_proj g m)) ?_
    intro e; exact hx (mul_right_cancel e ▸ hg)

variable (μ ν)

/-- The degree-`h` component, as a `k`-linear map. -/
def compK (h : G) (f : M →ₗ[A] N) : M →ₗ[k] N where
  toFun m := ∑ g ∈ μ.supp, ν.proj (g * h) (f (μ.proj g m))
  map_add' m m' := by simp [Finset.sum_add_distrib]
  map_smul' c m := by
    simp only [map_smul, LinearMap.map_smul_of_tower, Finset.smul_sum, RingHom.id_apply]

lemma compK_eq_of_subset (h : G) (f : M →ₗ[A] N) {T : Finset G} (hT : μ.supp ⊆ T) (m : M) :
    compK μ ν h f m = ∑ g ∈ T, ν.proj (g * h) (f (μ.proj g m)) := by
  refine Finset.sum_subset hT fun g _ hg ↦ ?_
  rw [μ.out g hg, map_zero, map_zero]

lemma compK_smul_homog (h : G) (f : M →ₗ[A] N) {x : G} {a : A} (ha : Γ.Mem x a) (m : M) :
    compK μ ν h f (a • m) = a • compK μ ν h f m := by
  classical
  set T := μ.supp ∪ μ.supp.image (fun g ↦ x * g) with hT
  rw [compK_eq_of_subset μ ν h f (Finset.subset_union_left) (a • m)]
  have step : ∀ g, ν.proj (g * h) (f (μ.proj g (a • m))) =
      a • ν.proj (x⁻¹ * g * h) (f (μ.proj (x⁻¹ * g) m)) := by
    intro g
    have e1 : μ.proj g (a • m) = a • μ.proj (x⁻¹ * g) m := by
      rw [← μ.proj_smul ha, mul_inv_cancel_left]
    rw [e1, map_smul, show g * h = x * (x⁻¹ * g * h) by group, ν.proj_smul ha]
  simp_rw [step]
  rw [← Finset.smul_sum]
  congr 1
  rw [← Finset.sum_image (f := fun g' ↦ ν.proj (g' * h) (f (μ.proj g' m)))
    (s := T) (g := fun g ↦ x⁻¹ * g) (fun _ _ _ _ e ↦ mul_left_cancel e)]
  refine (compK_eq_of_subset μ ν h f ?_ m).symm
  intro g hg
  refine Finset.mem_image.2 ⟨x * g, ?_, by group⟩
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg)

/-- **The degree-`h` component** of an `A`-linear map. -/
def comp (h : G) (f : M →ₗ[A] N) : M →ₗ[A] N where
  toFun := compK μ ν h f
  map_add' := map_add _
  map_smul' a m := by
    rw [RingHom.id_apply]
    conv_lhs => rw [← Γ.sum_eq a, Finset.sum_smul, map_sum]
    conv_rhs => rw [← Γ.sum_eq a, Finset.sum_smul]
    exact Finset.sum_congr rfl fun x _ ↦ compK_smul_homog μ ν h f (Γ.mem_proj x a) m

lemma comp_apply (h : G) (f : M →ₗ[A] N) (m : M) :
    comp μ ν h f m = ∑ g ∈ μ.supp, ν.proj (g * h) (f (μ.proj g m)) := rfl

lemma isHomog_comp (h : G) (f : M →ₗ[A] N) : IsHomog μ ν h (comp μ ν h f) := by
  intro g m hm
  rw [comp_apply]
  by_cases hg : g ∈ μ.supp
  · rw [Finset.sum_eq_single g]
    · rw [hm]; exact ν.mem_proj _ _
    · intro g' _ hg'; rw [μ.proj_of_mem hm hg', map_zero, map_zero]
    · intro h'; exact absurd hg h'
  · have : m = 0 := by rw [← hm, μ.out g hg]
    subst this; simpa using ν.mem_zero (g * h)

/-- The degrees that can occur. -/
def degs : Finset G := (μ.supp ×ˢ ν.supp).image fun p ↦ p.1⁻¹ * p.2

/-- **A map is the sum of its components.** -/
lemma sum_comp (f : M →ₗ[A] N) : ∑ h ∈ degs μ ν, comp μ ν h f = f := by
  classical
  ext m
  rw [LinearMap.sum_apply]
  simp only [comp_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [← μ.sum_eq m, map_sum]
  refine Finset.sum_congr rfl fun g hg ↦ ?_
  conv_rhs => rw [← ν.sum_eq (f (μ.proj g m))]
  rw [← Finset.sum_image (f := fun g'' ↦ ν.proj g'' (f (μ.proj g m)))
    (g := fun h ↦ g * h) (fun _ _ _ _ e ↦ mul_left_cancel e)]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro g'' hg''
    refine Finset.mem_image.2 ⟨g⁻¹ * g'', ?_, by group⟩
    exact Finset.mem_image.2 ⟨(g, g''), Finset.mem_product.2 ⟨hg, hg''⟩, rfl⟩
  · intro g'' _ hg''; exact ν.out g'' hg'' _

/-- The component of a homogeneous map. -/
lemma comp_of_isHomog {h h' : G} {f : M →ₗ[A] N} (hf : IsHomog μ ν h' f) :
    comp μ ν h f = if h = h' then f else 0 := by
  ext m
  rw [comp_apply]
  split_ifs with hh
  · subst hh
    simp_rw [hf.proj_apply, μ.proj_proj]
    rw [← map_sum, μ.sum_eq]
  · refine Finset.sum_eq_zero fun g _ ↦ ν.proj_of_mem (hf g _ (μ.mem_proj g m)) ?_
    intro e; exact hh (mul_left_cancel e)

/-- Degree-one maps on the left commute with taking components. -/
lemma comp_comp_left {h : G} {u : N →ₗ[A] L} (hu : IsHomog ν ρ 1 u) (f : M →ₗ[A] N) :
    comp μ ρ h (u ∘ₗ f) = u ∘ₗ comp μ ν h f := by
  ext m
  simp only [comp_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  have := hu.proj_apply (g * h) (f (μ.proj g m))
  rwa [mul_one] at this

end LargeIndecomposable.Graded
