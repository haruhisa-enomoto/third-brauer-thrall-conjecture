module

public import LargeIndecomposable.DirectedAlgebras.Directing.RigidMin

/-!
# Extensions of predecessors by a directing module split

If `M` is directing and `U` is an indecomposable predecessor of `M` (a path `U → ⋯ → M` of
nonzero non-isomorphisms between indecomposables), then every short exact sequence
`0 → M → E → U → 0` splits (`Directing.extVanish_pred`; ASS IX.1.4, first step). Otherwise some
summand `Eⱼ` of `E` gives a path `M → Eⱼ → U`, and with `U → ⋯ → M` a cycle through `M`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **Extensions of a predecessor by a directing module split.** -/
theorem Directing.extVanish_pred [FiniteDimensional k A] {M U : FDMod k A} (hM : Directing M)
    (hU : IsInd U) (hUM : Reach₁ U M) : ExtVanish U M := by
  classical
  intro E i p hi hp hex
  obtain ⟨d⟩ := FDMod.exists_decomp E
  let ij : ∀ j, M →ₗ[A] d.obj j := fun j ↦ FDMod.lin (d.proj j) ∘ₗ i
  let pj : ∀ j, d.obj j →ₗ[A] U := fun j ↦ p ∘ₗ FDMod.lin (d.inc j)
  have hsum : ∀ x : E, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
    have := LinearMap.congr_fun d.sum_id x
    simpa using this
  by_contra hns
  have hpj : ∀ j, ¬Function.Bijective (pj j) := by
    intro j hb
    apply hns
    let e := LinearEquiv.ofBijective (pj j) hb
    refine ⟨FDMod.lin (d.inc j) ∘ₗ e.symm.toLinearMap, ?_⟩
    ext x
    exact e.apply_symm_apply x
  have hij : ∀ j, ¬Function.Bijective (ij j) := by
    intro j hb
    apply hns
    let e := LinearEquiv.ofBijective (ij j) hb
    let r : E →ₗ[A] M := e.symm.toLinearMap ∘ₗ FDMod.lin (d.proj j)
    have hr : r ∘ₗ i = LinearMap.id := by
      ext x; exact e.symm_apply_apply x
    exact split_of_endo' i p hp hex (LinearMap.id - i ∘ₗ r) (fun x ↦ by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp,
          Function.comp_apply, map_sub]
        rw [mem_ker_of_range hex, sub_zero]) (fun m ↦ by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp,
          Function.comp_apply]
        rw [show r (i m) = m from LinearMap.congr_fun hr m, sub_self])
  by_cases hboth : ∃ j, ij j ≠ 0 ∧ pj j ≠ 0
  · obtain ⟨j, h1, h2⟩ := hboth
    have hInd : IsInd (d.obj j) := ⟨d.indec j, d.nt j⟩
    exact hM.2 (Reach₁.trans (Reach₁.trans
      (Reach₁.step hM.1 hInd (show M ⟶ d.obj j from ij j) h1 (hij j))
      (Reach₁.step hInd hU (show d.obj j ⟶ U from pj j) h2 (hpj j))) hUM)
  · push Not at hboth
    apply hns
    let e₂ : E →ₗ[A] E := ∑ j ∈ Finset.univ.filter (fun j ↦ ij j = 0),
      FDMod.lin (d.inc j) ∘ₗ FDMod.lin (d.proj j)
    have hpe : ∀ x, p (e₂ x) = p x := by
      intro x
      conv_rhs => rw [← hsum x]
      rw [map_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ ij j = 0)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j ↦ ¬ij j = 0) (fun j hj ↦ by
        have := hboth j (Finset.mem_filter.1 hj).2
        exact LinearMap.congr_fun this _), add_zero]
      simp only [e₂, LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, map_sum]
    have hei : ∀ m, e₂ (i m) = 0 := by
      intro m
      rw [LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun j hj ↦ by
        have := LinearMap.congr_fun (Finset.mem_filter.1 hj).2 m
        simp only [LinearMap.coe_comp, Function.comp_apply]
        change FDMod.lin (d.inc j) (ij j m) = 0
        rw [this, LinearMap.zero_apply, map_zero]
    exact split_of_endo' i p hp hex e₂ hpe hei

end LargeIndecomposable.AR
