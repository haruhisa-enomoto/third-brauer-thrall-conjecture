module

public import LargeIndecomposable.Coverings.GradedModules.GabrielCovering
public import LargeIndecomposable.RayCategories.Distributive.LinearizationTable
public import LargeIndecomposable.Coverings.UniversalCover.Cover

/-!
# The grading of `k(P)` by the fundamental group

Choose for each object `y` of a finite ray category `P` a morphism `ℓ y : x₀ ⟶ y` of the
fundamental groupoid. A nonzero morphism `f : y ⟶ z` gets the degree
`ℓ y ≫ [f] ≫ (ℓ z)⁻¹ ∈ Π(P, x₀)` (`rayDeg`); degrees multiply along composites
(`rayDeg_comp`). Grading the ray basis by degree makes `k(P)` a `Π(P, x₀)`-graded
algebra (`rayGrAlg`). Graded `k(P)`-modules are the push-downs of finite-support modules
over the universal cover.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Graded RayQuiver Cover

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}
variable (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y)

/-- The degree of a nonzero morphism. -/
def rayDeg (μ : NZ P) : Pi1 x₀ := asIso (ℓ μ.1 ≫ cls μ.2.2.1 μ.2.2.2 ≫ inv (ℓ μ.2.1))

lemma rayDeg_comp {y z w : P} (f : y ⟶ z) (g : z ⟶ w) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f ≫ g ≠ 0) :
    rayDeg ℓ ⟨y, w, f ≫ g, hfg⟩ = rayDeg ℓ ⟨z, w, g, hg⟩ * rayDeg ℓ ⟨y, z, f, hf⟩ := by
  apply Iso.ext
  change ℓ y ≫ cls (f ≫ g) hfg ≫ inv (ℓ w) =
    (ℓ y ≫ cls f hf ≫ inv (ℓ z)) ≫ (ℓ z ≫ cls g hg ≫ inv (ℓ w))
  rw [cls_comp f g hfg]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

lemma rayDeg_id (x : P) : rayDeg ℓ (idNZ x) = 1 := by
  apply Iso.ext
  change ℓ x ≫ cls (𝟙 x) (IsRayCategory.id_ne_zero x) ≫ inv (ℓ x) = 𝟙 _
  rw [cls_id, Category.id_comp, IsIso.hom_inv_id]

variable (k : Type u) [Field k]

open Classical in
/-- The grading of the ray basis. -/
def rayGrading : Grading (Pi1 x₀) k (Linearization P k) where
  proj g := (linBasisR k P).constr k fun μ ↦ if rayDeg ℓ μ = g then linBasisR k P μ else 0
  supp := Finset.univ.image (rayDeg ℓ)
  orth g h hgh v := by
    rw [← LinearMap.comp_apply]
    suffices H : ((linBasisR k P).constr k fun μ ↦ if rayDeg ℓ μ = g then linBasisR k P μ else 0) ∘ₗ
        ((linBasisR k P).constr k fun μ ↦ if rayDeg ℓ μ = h then linBasisR k P μ else 0) = 0 by
      rw [H]; rfl
    refine (linBasisR k P).ext fun μ ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Module.Basis.constr_basis,
      LinearMap.zero_apply]
    split_ifs with h1
    · rw [Module.Basis.constr_basis, if_neg (h1 ▸ Ne.symm hgh)]
    · simp
  out g hg v := by
    have H : ((linBasisR k P).constr k fun μ ↦ if rayDeg ℓ μ = g then linBasisR k P μ else 0) =
        0 := (linBasisR k P).ext fun μ ↦ by
      rw [Module.Basis.constr_basis, if_neg (fun (h : rayDeg ℓ μ = g) ↦ hg (h ▸
        Finset.mem_image_of_mem _ (Finset.mem_univ μ))), LinearMap.zero_apply]
    rw [H]; rfl
  sum_eq v := by
    have H : ∑ g ∈ Finset.univ.image (rayDeg ℓ),
        ((linBasisR k P).constr k fun μ ↦ if rayDeg ℓ μ = g then linBasisR k P μ else 0) =
        LinearMap.id := (linBasisR k P).ext fun μ ↦ by
      rw [LinearMap.sum_apply, LinearMap.id_apply]
      simp only [Module.Basis.constr_basis]
      rw [Finset.sum_eq_single (rayDeg ℓ μ)]
      · simp
      · intro g _ hg; simp [Ne.symm hg]
      · intro h; exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ μ)) h
    rw [← LinearMap.sum_apply, H]; rfl

lemma rayGrading_mem_basis (μ : NZ P) : (rayGrading ℓ k).Mem (rayDeg ℓ μ) (linBasisR k P μ) := by
  classical
  show (linBasisR k P).constr k _ (linBasisR k P μ) = _
  rw [Module.Basis.constr_basis]
  simp

/-- Homogeneous elements are combinations of basis elements of their degree. -/
lemma rayGrading_mem_iff (g : Pi1 x₀) (a : Linearization P k) :
    (rayGrading ℓ k).Mem g a ↔
      a ∈ Submodule.span k (linBasisR k P '' {μ | rayDeg ℓ μ = g}) := by
  classical
  constructor
  · intro h
    rw [← h]
    show (linBasisR k P).constr k _ a ∈ _
    rw [Module.Basis.constr_apply]
    refine Submodule.finsuppSum_mem _ _ _ _ fun μ _ ↦ ?_
    split_ifs with hμ
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, rfl⟩)
    · simp
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨μ, hμ, rfl⟩ := hx
      have := rayGrading_mem_basis ℓ k μ
      rwa [hμ] at this
    | zero => exact (rayGrading ℓ k).mem_zero g
    | add x y _ _ hx hy => exact (rayGrading ℓ k).mem_add hx hy
    | smul c x _ hx => exact (rayGrading ℓ k).mem_smul c hx

/-- **The graded algebra `k(P)`.** -/
def rayGrAlg : GrAlg (Pi1 x₀) k (Linearization P k) where
  toGrading := rayGrading ℓ k
  one_mem := by
    rw [rayGrading_mem_iff, ← sum_morElt_id k]
    refine Submodule.sum_mem _ fun x _ ↦ Submodule.subset_span ⟨idNZ x, rayDeg_id ℓ x, ?_⟩
    rw [linBasisR_apply]; rfl
  mul_mem g h a b ha hb := by
    rw [rayGrading_mem_iff] at ha hb ⊢
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ν, hν, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨μ, hμ, rfl⟩ := hy
        obtain ⟨a', b', f, hf⟩ := μ
        obtain ⟨c', d', f', hf'⟩ := ν
        rw [linBasisR_apply, linBasisR_apply]
        by_cases hdb : c' = b'
        · subst hdb
          rw [morElt_mul]
          by_cases h0 : f ≫ f' = 0
          · rw [h0, morElt_zero]; exact Submodule.zero_mem _
          · refine Submodule.subset_span ⟨⟨a', d', f ≫ f', h0⟩, ?_, ?_⟩
            · simp only [Set.mem_setOf_eq] at hμ hν ⊢
              rw [rayDeg_comp ℓ f f' hf hf' h0, hν, hμ]
            · rw [linBasisR_apply]
        · rw [morElt_mul_ne k f f' (Ne.symm hdb)]; exact Submodule.zero_mem _
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

end LargeIndecomposable.RayCat
