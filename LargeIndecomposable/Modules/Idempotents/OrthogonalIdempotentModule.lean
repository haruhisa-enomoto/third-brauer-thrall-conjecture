module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Idempotents

@[expose] public section

/-!
# Module decompositions from orthogonal idempotents

A complete orthogonal family in an algebra splits every module into the
internal direct sum of the images of the corresponding idempotent actions.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {M : Type w}
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

/-- The `k`-linear projector given by the action of one algebra element. -/
def algebraElementAction (a : A) : M →ₗ[k] M :=
  (Algebra.lsmul k k M) a

@[simp]
theorem algebraElementAction_apply (a : A) (m : M) :
    algebraElementAction (k := k) (M := M) a m = a • m := rfl

/-- The module piece selected by one member of an idempotent family. -/
def idempotentModuleComponent (e : ι → A) (i : ι) : Submodule k M :=
  LinearMap.range (algebraElementAction (k := k) (M := M) (e i))

/-- A complete orthogonal idempotent family splits every module internally. -/
theorem idempotentModuleComponent_isInternal
    (e : ι → A) (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal
      (idempotentModuleComponent (k := k) (M := M) e) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hv0 i hi
    have hproject : e i • (∑ j ∈ s, v j) = v i := by
      rw [Finset.smul_sum]
      rw [Finset.sum_eq_single i]
      · obtain ⟨m, hm⟩ := hv i hi
        change algebraElementAction (k := k) (M := M) (e i) m = v i at hm
        rw [← hm, algebraElementAction_apply, ← mul_smul,
          he.toOrthogonalIdempotents.idem i |>.eq]
      · intro j hj hji
        obtain ⟨m, hm⟩ := hv j hj
        change algebraElementAction (k := k) (M := M) (e j) m = v j at hm
        rw [← hm, algebraElementAction_apply, ← mul_smul,
          he.toOrthogonalIdempotents.ortho (Ne.symm hji), zero_smul]
      · exact fun h ↦ False.elim (h hi)
    rw [hv0, smul_zero] at hproject
    exact hproject.symm
  · apply top_unique
    intro m hm
    have hsum : ∑ i : ι, e i • m = m := by
      rw [← Finset.sum_smul, he.complete, one_smul]
    rw [← hsum]
    apply Submodule.sum_mem
    intro i hi
    apply (le_iSup (idempotentModuleComponent (k := k) (M := M) e) i)
    exact ⟨m, rfl⟩

/-- The canonical decomposition of a module selected by a complete
orthogonal idempotent family. -/
@[reducible] noncomputable def idempotentModuleDecomposition
    (e : ι → A) (he : CompleteOrthogonalIdempotents e) :
    DirectSum.Decomposition
      (idempotentModuleComponent (k := k) (M := M) e) :=
  (idempotentModuleComponent_isInternal (k := k) (M := M) e he).chooseDecomposition

/-- The projector selected by an idempotent, restricted to a vector subspace
which is stable under that idempotent. -/
def idempotentSubmoduleProjection
    (N : Submodule k M) (e : ι → A)
    (hstable : ∀ i ⦃m : M⦄, m ∈ N → e i • m ∈ N) (i : ι) :
    N →ₗ[k] N :=
  (algebraElementAction (k := k) (M := M) (e i)).restrict
    (hstable i)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem idempotentSubmoduleProjection_coe
    (N : Submodule k M) (e : ι → A)
    (hstable : ∀ i ⦃m : M⦄, m ∈ N → e i • m ∈ N)
    (i : ι) (m : N) :
    ((idempotentSubmoduleProjection N e hstable i m : N) : M) =
      e i • (m : M) := rfl

/-- The piece of an invariant vector subspace selected by one idempotent. -/
def idempotentSubmoduleComponent
    (N : Submodule k M) (e : ι → A)
    (hstable : ∀ i ⦃m : M⦄, m ∈ N → e i • m ∈ N) (i : ι) :
    Submodule k N :=
  LinearMap.range (idempotentSubmoduleProjection N e hstable i)

/-- A complete orthogonal family internally splits every vector subspace
which is stable under the family. -/
theorem idempotentSubmoduleComponent_isInternal
    (N : Submodule k M) (e : ι → A)
    (hstable : ∀ i ⦃m : M⦄, m ∈ N → e i • m ∈ N)
    (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal (idempotentSubmoduleComponent N e hstable) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hv0 i hi
    have hproject :
        idempotentSubmoduleProjection N e hstable i (∑ j ∈ s, v j) = v i := by
      rw [map_sum]
      rw [Finset.sum_eq_single i]
      · obtain ⟨m, hm⟩ := hv i hi
        change idempotentSubmoduleProjection N e hstable i m = v i at hm
        rw [← hm]
        apply Subtype.ext
        change e i • (e i • (m : M)) = e i • (m : M)
        rw [← mul_smul, he.toOrthogonalIdempotents.idem i |>.eq]
      · intro j hj hji
        obtain ⟨m, hm⟩ := hv j hj
        change idempotentSubmoduleProjection N e hstable j m = v j at hm
        rw [← hm]
        apply Subtype.ext
        change e i • (e j • (m : M)) = 0
        rw [← mul_smul,
          he.toOrthogonalIdempotents.ortho (Ne.symm hji), zero_smul]
      · exact fun h ↦ False.elim (h hi)
    rw [hv0, map_zero] at hproject
    exact hproject.symm
  · apply top_unique
    intro m hm
    have hsum :
        ∑ i : ι, idempotentSubmoduleProjection N e hstable i m = m := by
      apply Subtype.ext
      change N.subtype (∑ i : ι,
        idempotentSubmoduleProjection N e hstable i m) = N.subtype m
      rw [map_sum]
      change ∑ i : ι, e i • (m : M) = (m : M)
      rw [← Finset.sum_smul, he.complete, one_smul]
    rw [← hsum]
    apply Submodule.sum_mem
    intro i hi
    apply (le_iSup (idempotentSubmoduleComponent N e hstable) i)
    exact ⟨m, rfl⟩

/-- The canonical vertex decomposition of an invariant vector subspace. -/
@[reducible] noncomputable def idempotentSubmoduleDecomposition
    (N : Submodule k M) (e : ι → A)
    (hstable : ∀ i ⦃m : M⦄, m ∈ N → e i • m ∈ N)
    (he : CompleteOrthogonalIdempotents e) :
    DirectSum.Decomposition (idempotentSubmoduleComponent N e hstable) :=
  (idempotentSubmoduleComponent_isInternal N e hstable he).chooseDecomposition

section Pi

variable {β : Type x}

/-- Selecting an idempotent component commutes with an arbitrary dependent
product of invariant subspaces. -/
def idempotentPiSubmoduleComponentLinearEquiv
    (N : β → Submodule k M) (e : ι → A)
    (hstable : ∀ i b ⦃m : M⦄, m ∈ N b → e i • m ∈ N b)
    (i : ι) :
    idempotentSubmoduleComponent
        (Submodule.pi Set.univ N) e
        (fun i _ hf ↦ by
          rw [Submodule.mem_pi] at hf ⊢
          intro b hb
          exact hstable i b (hf b hb)) i ≃ₗ[k]
      (∀ b : β, idempotentSubmoduleComponent (N b) e
        (fun i _ hm ↦ hstable i b hm) i) where
  toFun f b := by
    let fb : N b := ⟨f.1.1 b, by
      exact f.1.2 b (Set.mem_univ b)⟩
    refine ⟨fb, ?_⟩
    obtain ⟨g, hg⟩ := f.2
    let gb : N b := ⟨g.1 b, by
      exact g.2 b (Set.mem_univ b)⟩
    refine ⟨gb, ?_⟩
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val hg) b
  invFun f := by
    let g : Submodule.pi Set.univ N :=
      ⟨fun b ↦ ((f b).1 : N b), by
        rw [Submodule.mem_pi]
        intro b hb
        exact ((f b).1 : N b).2⟩
    let witness : Submodule.pi Set.univ N :=
      ⟨fun b ↦ ((Classical.choose (f b).2 : N b) : M), by
        rw [Submodule.mem_pi]
        intro b hb
        exact (Classical.choose (f b).2 : N b).2⟩
    refine ⟨g, ⟨witness, ?_⟩⟩
    apply Subtype.ext
    funext b
    exact congrArg Subtype.val (Classical.choose_spec (f b).2)
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext b
    rfl
  right_inv f := by
    funext b
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_add' f g := by
    funext b
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c f := by
    funext b
    apply Subtype.ext
    apply Subtype.ext
    rfl

end Pi

end LargeIndecomposable

