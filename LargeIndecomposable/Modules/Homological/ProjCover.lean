module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerProj

/-!
# Covering a module by indecomposable projectives

For a list of vectors `mᵢ ∈ eᵢ M`, the sum `⊕ A eᵢ` maps to `M` by `a ↦ a mᵢ` on the `i`-th
summand (`sumMap`). The sum is Euler-projective (`eulerProj_sumProj`), and taking bases of all
`eᵢ M` gives a surjection (`exists_cover`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

variable (k A) in
/-- The zero object. -/
abbrev FDMod.zero : FDMod k A where
  carrier := PUnit

/-- The sum of the indecomposable projectives of a list of vertices. -/
def sumProj : List D.ι → FDMod k A
  | [] => FDMod.zero k A
  | i :: l => FDMod.prod (projE (k := k) (D.idem i)) (sumProj l)

lemma eulerProj_zero : EulerProj D (FDMod.zero k A) := by
  intro W
  have h1 : dimZ D (FDMod.zero k A) = 0 := by
    funext j
    simp only [dimZ, dimv, Pi.zero_apply, Nat.cast_eq_zero]
    exact Submodule.finrank_eq_zero.2 (Subsingleton.elim _ _)
  have h2 : finrank k ((FDMod.zero k A) →ₗ[A] W) = 0 := by
    haveI : Subsingleton ((FDMod.zero k A) →ₗ[A] W) :=
      ⟨fun f g ↦ LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    exact Module.finrank_zero_of_subsingleton
  rw [h1, h2]
  simp [euler]

/-- **Sums of indecomposable projectives are Euler-projective.** -/
theorem eulerProj_sumProj (hT : ∀ x, x ∈ D.T) : ∀ l : List D.ι, EulerProj D (sumProj D l)
  | [] => eulerProj_zero D
  | i :: l => (eulerProj_projE D hT i).prod D (eulerProj_sumProj hT l)

/-- The map `⊕ A eᵢ → M` of a list of vectors `mᵢ ∈ eᵢ M`. -/
def sumMap (M : FDMod k A) : ∀ L : List (Σ i : D.ι, eSub M (D.e i)),
    sumProj D (L.map Sigma.fst) →ₗ[A] M
  | [] => 0
  | ⟨i, m⟩ :: L => LinearMap.coprod ((homProjEquiv (D.idem i) M).symm m) (sumMap M L)

lemma mem_range_sumMap (M : FDMod k A) : ∀ (L : List (Σ i : D.ι, eSub M (D.e i))) (x),
    x ∈ L → ((x.2 : eSub M (D.e x.1)) : M) ∈ LinearMap.range (sumMap D M L)
  | [], _, h => absurd h List.not_mem_nil
  | ⟨i, m⟩ :: L, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · refine ⟨(⟨D.e i, e_mem (D.idem i)⟩, 0), ?_⟩
      change (homProjEquiv (D.idem i) M).symm m ⟨D.e i, e_mem (D.idem i)⟩ + sumMap D M L 0 = m
      rw [map_zero, add_zero, homProjEquiv_symm_apply]
      exact m.2
    · obtain ⟨y, hy⟩ := mem_range_sumMap M L x h
      refine ⟨(0, y), ?_⟩
      change (homProjEquiv (D.idem i) M).symm m 0 + sumMap D M L y = _
      rw [map_zero, zero_add, hy]

/-- **Every module is a quotient of a sum of indecomposable projectives.** -/
theorem exists_cover (M : FDMod k A) :
    ∃ L : List (Σ i : D.ι, eSub M (D.e i)), Function.Surjective (sumMap D M L) := by
  classical
  let L : List (Σ i : D.ι, eSub M (D.e i)) :=
    (Finset.univ.toList).flatMap fun i ↦
      (List.ofFn (Module.finBasis k (eSub M (D.e i)))).map fun b ↦ ⟨i, b⟩
  refine ⟨L, ?_⟩
  rw [← LinearMap.range_eq_top]
  -- the range is an `A`-submodule containing every `eᵢ M`
  have hsub : ∀ i, ∀ m : eSub M (D.e i), (m : M) ∈ LinearMap.range (sumMap D M L) := by
    intro i m
    have hspan : (m : eSub M (D.e i)) ∈ Submodule.span k
        (Set.range (Module.finBasis k (eSub M (D.e i)))) := by
      rw [(Module.finBasis k (eSub M (D.e i))).span_eq]
      trivial
    induction hspan using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨t, rfl⟩ := hb
      refine mem_range_sumMap D M L ⟨i, _⟩ ?_
      refine List.mem_flatMap.2 ⟨i, Finset.mem_toList.2 (Finset.mem_univ i), ?_⟩
      exact List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨t, rfl⟩, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have := Submodule.smul_mem _ (algebraMap k A c) ha
      rwa [algebraMap_smul] at this
  rw [eq_top_iff]
  intro m _
  have hm : m = ∑ i, D.e i • m := by rw [← Finset.sum_smul, D.sum, one_smul]
  rw [hm]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  exact hsub i ⟨D.e i • m, by
    change D.e i • D.e i • m = D.e i • m
    rw [← mul_smul, (D.idem i).eq]⟩

end LargeIndecomposable.AR
