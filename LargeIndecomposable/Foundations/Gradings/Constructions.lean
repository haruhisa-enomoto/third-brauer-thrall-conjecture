module

public import LargeIndecomposable.Foundations.Gradings.Sub
public import LargeIndecomposable.Modules.Homological.Presentation

/-!
# Gradings of products, of `DA`, and of kernels

* `GrMod.prod`, `GrMod.pi`: products of graded modules.
* `GrAlg.proj_mul_left`, `proj_mul_right`: homogeneous factors move projections.
* `grDA Γ d`: `DA = Hom_k(A, k)` graded with shift `d`: degree `g` means supported on
  `A_{d g⁻¹}`.
* `isGrSub_ker'`: the kernel of a homogeneous map is graded.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Graded

open Module AR

variable {G : Type*} [Group G] [DecidableEq G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] {Γ : GrAlg G k A}

section Prod

variable {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- The product grading. -/
def GrMod.prod (μ : GrMod Γ M) (ν : GrMod Γ N) : GrMod Γ (M × N) where
  proj g := LinearMap.prodMap (μ.proj g) (ν.proj g)
  supp := μ.supp ∪ ν.supp
  orth g h hgh x := by simp [μ.orth g h hgh, ν.orth g h hgh]
  out g hg x := by
    simp only [Finset.mem_union, not_or] at hg
    simp [μ.out g hg.1, ν.out g hg.2]
  sum_eq x := by
    ext
    · simp only [LinearMap.prodMap_apply, Prod.fst_sum]
      exact μ.sum_eq_of_subset Finset.subset_union_left x.1
    · simp only [LinearMap.prodMap_apply, Prod.snd_sum]
      exact ν.sum_eq_of_subset Finset.subset_union_right x.2
  smul_mem g h a x ha hx := by
    have h1 : μ.Mem h x.1 := congrArg Prod.fst hx
    have h2 : ν.Mem h x.2 := congrArg Prod.snd hx
    exact Prod.ext (μ.smul_mem g h a _ ha h1) (ν.smul_mem g h a _ ha h2)

/-- The product grading on a finite family. -/
def GrMod.pi {n : ℕ} {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
    [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)] (μ : ∀ i, GrMod Γ (V i)) :
    GrMod Γ (∀ i, V i) where
  proj g := LinearMap.pi fun i ↦ (μ i).proj g ∘ₗ LinearMap.proj i
  supp := Finset.univ.biUnion fun i ↦ (μ i).supp
  orth g h hgh x := by funext i; simp [(μ i).orth g h hgh]
  out g hg x := by
    funext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hg
    simp [(μ i).out g (hg i)]
  sum_eq x := by
    funext i
    simp only [Finset.sum_apply, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_proj, Function.eval]
    exact (μ i).sum_eq_of_subset (Finset.subset_biUnion_of_mem (fun i ↦ (μ i).supp)
      (Finset.mem_univ i)) (x i)
  smul_mem g h a x ha hx := by
    funext i
    have : (μ i).Mem h (x i) := congrFun hx i
    exact (μ i).smul_mem g h a _ ha this

end Prod

namespace GrAlg

/-- A homogeneous left factor moves the projections. -/
lemma proj_mul_left {x : G} {a : A} (ha : Γ.Mem x a) (g : G) (b : A) :
    Γ.proj (x * g) (a * b) = a * Γ.proj g b := by
  conv_lhs => rw [← Γ.sum_eq b, Finset.mul_sum, map_sum]
  by_cases hg : g ∈ Γ.supp
  · rw [Finset.sum_eq_single g]
    · exact Γ.mul_mem x g a _ ha (Γ.mem_proj g b)
    · intro h _ hh
      exact Γ.proj_of_mem (Γ.mul_mem x h a _ ha (Γ.mem_proj h b))
        (fun e ↦ hh (mul_left_cancel e).symm)
    · intro h; exact absurd hg h
  · rw [Γ.out g hg, mul_zero]
    refine Finset.sum_eq_zero fun h hh ↦ ?_
    exact Γ.proj_of_mem (Γ.mul_mem x h a _ ha (Γ.mem_proj h b))
      (fun e ↦ hg (mul_left_cancel e ▸ hh))

/-- A homogeneous right factor moves the projections. -/
lemma proj_mul_right {x : G} {a : A} (ha : Γ.Mem x a) (g : G) (b : A) :
    Γ.proj (g * x) (b * a) = Γ.proj g b * a := by
  conv_lhs => rw [← Γ.sum_eq b, Finset.sum_mul, map_sum]
  by_cases hg : g ∈ Γ.supp
  · rw [Finset.sum_eq_single g]
    · exact Γ.mul_mem g x _ a (Γ.mem_proj g b) ha
    · intro h _ hh
      exact Γ.proj_of_mem (Γ.mul_mem h x _ a (Γ.mem_proj h b) ha)
        (fun e ↦ hh (mul_right_cancel e).symm)
    · intro h; exact absurd hg h
  · rw [Γ.out g hg, zero_mul]
    refine Finset.sum_eq_zero fun h hh ↦ ?_
    exact Γ.proj_of_mem (Γ.mul_mem h x _ a (Γ.mem_proj h b) ha)
      (fun e ↦ hg (mul_right_cancel e ▸ hh))

end GrAlg

/-- Precomposition of an element of `DA` with a `k`-linear map. -/
def DAprecomp (l : DA k A) (T : A →ₗ[k] A) : DA k A := DA.mk ((show A →ₗ[k] k from l) ∘ₗ T)

@[simp] lemma DAprecomp_ev (l : DA k A) (T : A →ₗ[k] A) (b : A) :
    (DAprecomp l T).ev b = l.ev (T b) := rfl

/-- **`DA` graded with shift `d`**: degree `g` = supported on `A_{d g⁻¹}`. -/
def grDA (Γ : GrAlg G k A) (d : G) : GrMod Γ (DA k A) where
  proj g :=
    { toFun l := DAprecomp l (Γ.proj (d * g⁻¹))
      map_add' l m := DA.ext fun b ↦ by simp
      map_smul' c l := DA.ext fun b ↦ by simp }
  supp := Γ.supp.image fun x ↦ x⁻¹ * d
  orth g h hgh l := DA.ext fun b ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, DAprecomp_ev, DA.ev_zero]
    rw [Γ.orth _ _ (fun e ↦ hgh (by simpa using e.symm)), DA.ev_zeroB]
  out g hg l := DA.ext fun b ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, DAprecomp_ev, DA.ev_zero]
    rw [Γ.out (d * g⁻¹) (fun h ↦ hg (Finset.mem_image.2 ⟨_, h, by group⟩)), DA.ev_zeroB]
  sum_eq l := DA.ext fun b ↦ by
    rw [DA.ev_finset_sum]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, DAprecomp_ev]
    rw [Finset.sum_image (f := fun g ↦ l.ev (Γ.proj (d * g⁻¹) b))
      (fun x _ y _ e ↦ by simpa using e)]
    simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [← DA.ev_sum, Γ.sum_eq b]
  smul_mem x h a l ha hl := DA.ext fun b ↦ by
    have hl' : ∀ c, l.ev (Γ.proj (d * h⁻¹) c) = l.ev c := fun c ↦ by
      have := congrArg (fun m : DA k A ↦ m.ev c) hl
      simpa using this
    simp only [LinearMap.coe_mk, AddHom.coe_mk, DAprecomp_ev, DA.ev_smulA]
    rw [← hl' (b * a), show d * h⁻¹ = d * (x * h)⁻¹ * x by group,
      GrAlg.proj_mul_right ha]

lemma grDA_mem (d g : G) (l : DA k A) :
    (grDA Γ d).Mem g l ↔ ∀ b, l.ev (Γ.proj (d * g⁻¹) b) = l.ev b := by
  constructor
  · intro h b
    have := congrArg (fun m : DA k A ↦ m.ev b) h
    simpa [grDA] using this
  · intro h
    exact DA.ext fun b ↦ by simpa [grDA] using h b

section Ker

variable {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

lemma isGrSub_ker' {μ : GrMod Γ M} {ν : GrMod Γ N} {h : G} {f : M →ₗ[A] N}
    (hf : IsHomog μ ν h f) : IsGrSub μ (LinearMap.ker f) := by
  intro m hm g
  rw [LinearMap.mem_ker, ← hf.proj_apply g m, LinearMap.mem_ker.1 hm, map_zero]

end Ker

end LargeIndecomposable.Graded
