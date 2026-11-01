module

public import LargeIndecomposable.Foundations.Gradings.Constructions

/-!
# Graded free presentations

`grShift Γ d`: `A` as a graded left module with shift `d` (degree `g` = `A_{g d⁻¹}`).
`GrPres μ`: a free presentation with homogeneous generators `zⱼ` of degree `dⱼ` and
relation rows homogeneous of degree `eᵢ` (`Fᵢⱼ ∈ A_{eᵢ dⱼ⁻¹}`). Every finite-dimensional
graded module over a finite-dimensional graded algebra has one (`GrPres.exists`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Graded

open Module AR

variable {G : Type*} [Group G] [DecidableEq G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] {Γ : GrAlg G k A}

/-- `A` graded with shift `d`. -/
def grShift (Γ : GrAlg G k A) (d : G) : GrMod Γ A where
  proj g := Γ.proj (g * d⁻¹)
  supp := Γ.supp.image fun x ↦ x * d
  orth g h hgh b := Γ.orth _ _ (fun e ↦ hgh (mul_right_cancel e)) b
  out g hg b := Γ.out _ (fun h ↦ hg (Finset.mem_image.2 ⟨_, h, by group⟩)) b
  sum_eq b := by
    rw [Finset.sum_image (fun x _ y _ e ↦ mul_right_cancel e)]
    simp only [mul_inv_cancel_right]
    exact Γ.sum_eq b
  smul_mem x h a b ha hb := by
    change Γ.Mem (x * h * d⁻¹) (a * b)
    rw [mul_assoc]
    exact Γ.mul_mem x _ a b ha hb

/-- **A homogeneous spanning family** of a finite-dimensional graded space. -/
theorem exists_homog_span {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (γ : Grading G k V) :
    ∃ (n : ℕ) (z : Fin n → V) (d : Fin n → G), (∀ j, γ.Mem (d j) (z j)) ∧
      ∀ x, ∃ c : Fin n → k, ∑ j, c j • z j = x := by
  classical
  let W : γ.supp → Submodule k V := fun g ↦ LinearMap.range (γ.proj g)
  let b : ∀ g : γ.supp, Basis (Fin (finrank k (W g))) k (W g) := fun g ↦ Module.finBasis k _
  let ι := Σ g : γ.supp, Fin (finrank k (W g))
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j ↦ (b (e.symm j).1 (e.symm j).2 : V),
    fun j ↦ ((e.symm j).1 : G), fun j ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨y, hy⟩ := (b (e.symm j).1 (e.symm j).2).2
    show γ.proj _ _ = _
    dsimp only
    rw [← hy, γ.proj_proj]
  · let c : ι → k := fun p ↦ (b p.1).repr ⟨γ.proj p.1 x, LinearMap.mem_range_self _ _⟩ p.2
    refine ⟨fun j ↦ c (e.symm j), ?_⟩
    dsimp only
    rw [e.symm.sum_comp (fun p ↦ c p • (b p.1 p.2 : V)), Fintype.sum_sigma]
    conv_rhs => rw [← γ.sum_eq x]
    rw [← Finset.sum_coe_sort γ.supp]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    have h1 := (b g).sum_repr ⟨γ.proj g x, LinearMap.mem_range_self _ _⟩
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2

variable {Z : Type*} [AddCommGroup Z] [Module A Z] [Module k Z] [IsScalarTower k A Z]

/-- A graded free presentation. -/
structure GrPres (μ : GrMod Γ Z) extends FreePres A Z where
  d : Fin n₀ → G
  hz : ∀ j, μ.Mem (d j) (z j)
  e : Fin n₁ → G
  hF : ∀ i j, Γ.Mem (e i * (d j)⁻¹) (F i j)

/-- The free graded module `⊕ⱼ A(dⱼ)`. -/
def grFree {n : ℕ} (Γ : GrAlg G k A) (d : Fin n → G) : GrMod Γ (Fin n → A) :=
  GrMod.pi fun j ↦ grShift Γ (d j)

lemma grFree_mem {n : ℕ} (d : Fin n → G) (g : G) (p : Fin n → A) :
    (grFree Γ d).Mem g p ↔ ∀ j, Γ.Mem (g * (d j)⁻¹) (p j) := by
  constructor
  · intro h j; exact congrFun h j
  · intro h; funext j; exact h j

/-- **Every finite-dimensional graded module has a graded free presentation.** -/
theorem GrPres.exists [FiniteDimensional k A] [FiniteDimensional k Z] (μ : GrMod Γ Z) :
    Nonempty (GrPres μ) := by
  classical
  obtain ⟨n₀, z, d, hz, hspan⟩ := exists_homog_span μ.toGrading
  let g₀ : (Fin n₀ → A) →ₗ[A] Z :=
    { toFun p := ∑ j, p j • z j
      map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' a p := by simp [mul_smul, Finset.smul_sum] }
  have hg₀ : IsHomog (grFree Γ d) μ 1 g₀ := by
    intro g p hp
    rw [mul_one]
    show μ.Mem g (∑ j, p j • z j)
    refine μ.mem_sum _ _ fun j _ ↦ ?_
    have := μ.smul_mem _ _ (p j) (z j) ((grFree_mem d g p).1 hp j) (hz j)
    rwa [inv_mul_cancel_right] at this
  have hK : IsGrSub (grFree Γ d) (LinearMap.ker g₀) := isGrSub_ker' hg₀
  let κ := (grFree Γ d).sub hK
  haveI : FiniteDimensional k (LinearMap.ker g₀) :=
    inferInstanceAs (FiniteDimensional k ((LinearMap.ker g₀).restrictScalars k))
  obtain ⟨n₁, F', e, hF', hspanK⟩ := exists_homog_span κ.toGrading
  refine ⟨GrPres.mk (FreePres.mk n₀ n₁ z (fun i ↦ (F' i : Fin n₀ → A)) (fun i ↦ (F' i).2)
    (fun x ↦ ?_) (fun p hp ↦ ?_)) d hz e (fun i j ↦ ?_)⟩
  · obtain ⟨c, hc⟩ := hspan x
    exact ⟨fun j ↦ algebraMap k A (c j), by simpa [algebraMap_smul] using hc⟩
  · obtain ⟨c, hc⟩ := hspanK ⟨p, hp⟩
    refine ⟨fun i ↦ algebraMap k A (c i), fun j ↦ ?_⟩
    have := congrArg (fun q : LinearMap.ker g₀ ↦ (q : Fin n₀ → A) j) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ ↦ Algebra.smul_def _ _
  · have h1 : κ.Mem (e i) (F' i) := hF' i
    have h2 : (grFree Γ d).Mem (e i) (F' i : Fin n₀ → A) := congrArg Subtype.val h1
    exact (grFree_mem d (e i) _).1 h2 j

end LargeIndecomposable.Graded
