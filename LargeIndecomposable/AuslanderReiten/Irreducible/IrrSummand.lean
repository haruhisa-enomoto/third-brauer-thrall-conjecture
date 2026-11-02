module

public import LargeIndecomposable.AuslanderReiten.Lengths.Lemma24

/-!
# Summands of minimal right almost split maps are irreducible

For a right minimal right almost split `g : E → Z` into a nonzero indecomposable and a
decomposition of `E`, each component `E_i → Z` is irreducible (`isIrr_summand`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **Components of minimal right almost split maps are irreducible.** -/
theorem isIrr_summand {E Z : FDMod k A} {g : E ⟶ Z} (hg : IsRightAS g)
    (hmin : ∀ φ : E ⟶ E, φ ≫ g = g → Function.Bijective (FDMod.lin φ)) (hZ : IndNT Z)
    (d : Decomp E) (i : d.ι) : IsIrr (d.inc i ≫ g) := by
  classical
  have hsum : ∀ x : E, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
    simpa using LinearMap.congr_fun d.sum_id x
  have hretr : ∀ u, FDMod.lin (d.proj i) (FDMod.lin (d.inc i) u) = u := fun u ↦
    LinearMap.congr_fun (d.retr i) u
  have horth : ∀ j, j ≠ i → ∀ u, FDMod.lin (d.proj i) (FDMod.lin (d.inc j) u) = 0 := fun j hj u ↦
    LinearMap.congr_fun (d.orth j i hj) u
  have hretr' : ∀ j u, FDMod.lin (d.proj j) (FDMod.lin (d.inc j) u) = u := fun j u ↦
    LinearMap.congr_fun (d.retr j) u
  have horth' : ∀ j l, j ≠ l → ∀ u, FDMod.lin (d.proj l) (FDMod.lin (d.inc j) u) = 0 :=
    fun j l h u ↦ LinearMap.congr_fun (d.orth j l h) u
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨s, hs⟩ ↦ hg.1 ⟨s ≫ d.inc i, by rw [Category.assoc, hs]⟩,
    fun W a b hab ↦ ?_⟩
  · -- a split mono `E_i → Z` between indecomposables is an isomorphism
    have hrb := bijective_of_split hZ.1 (d.nt i) r (d.inc i ≫ g) (LinearMap.ext fun u ↦
      LinearMap.congr_fun ((FDMod.comp_eq_id_iff _ _).1 (hr)) u)
    apply hg.1
    refine ⟨r ≫ d.inc i, (FDMod.hom_ext (LinearMap.ext fun z ↦ ?_))⟩
    apply hrb.1
    exact LinearMap.congr_fun (congrArg FDMod.lin (hr)) (FDMod.lin r z)
  · by_cases hb : SplitEpi b
    · exact Or.inr hb
    left
    obtain ⟨c, hc⟩ := hg.2 W b hb
    have hca : ∀ u, FDMod.lin g (FDMod.lin c (FDMod.lin a u)) = FDMod.lin g (FDMod.lin (d.inc i) u) :=
      fun u ↦ by
        have h1 : FDMod.lin g (FDMod.lin c (FDMod.lin a u)) = FDMod.lin b (FDMod.lin a u) :=
          LinearMap.congr_fun (congrArg FDMod.lin hc) _
        rw [h1]; exact LinearMap.congr_fun (congrArg FDMod.lin (hab)) u
    let φ : E →ₗ[A] E := FDMod.lin c ∘ₗ FDMod.lin a ∘ₗ FDMod.lin (d.proj i) +
      ∑ j ∈ Finset.univ.erase i, FDMod.lin (d.inc j) ∘ₗ FDMod.lin (d.proj j)
    have hφ : (show E ⟶ E from (FDMod.ofLin (φ))) ≫ g = g := by
      apply FDMod.hom_ext; apply LinearMap.ext; intro x
      change FDMod.lin g (φ x) = FDMod.lin g x
      conv_rhs => rw [← hsum x, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [φ, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.sum_apply, map_add, map_sum, hca]
    have hφb := hmin _ hφ
    have hφinc : ∀ j, j ≠ i → ∀ u, φ (FDMod.lin (d.inc j) u) = FDMod.lin (d.inc j) u := by
      intro j hj u
      simp only [φ, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.sum_apply, horth j hj, map_zero, zero_add]
      rw [Finset.sum_eq_single j]
      · rw [hretr' j u]
      · intro l _ hl
        rw [horth' j l (Ne.symm hl) u, map_zero]
      · intro h; exact absurd (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) h
    have hφi : ∀ u, φ (FDMod.lin (d.inc i) u) = FDMod.lin c (FDMod.lin a u) := by
      intro u
      simp only [φ, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.sum_apply, hretr]
      rw [Finset.sum_eq_zero, add_zero]
      intro l hl
      rw [horth' i l (Finset.ne_of_mem_erase hl).symm u, map_zero]
    let τ : d.obj i →ₗ[A] d.obj i := FDMod.lin (d.proj i) ∘ₗ FDMod.lin c ∘ₗ FDMod.lin a
    have hτinj : Function.Injective τ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      let w : E := ∑ j ∈ Finset.univ.erase i,
        FDMod.lin (d.inc j) (FDMod.lin (d.proj j) (FDMod.lin c (FDMod.lin a u)))
      have hw : FDMod.lin c (FDMod.lin a u) = w := by
        conv_lhs => rw [← hsum (FDMod.lin c (FDMod.lin a u)),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        rw [show FDMod.lin (d.proj i) (FDMod.lin c (FDMod.lin a u)) = 0 from hu, map_zero,
          zero_add]
      have hφw : φ w = w := by
        simp only [w, map_sum]
        exact Finset.sum_congr rfl fun j hj ↦ hφinc j (Finset.ne_of_mem_erase hj) _
      have h1 : φ (FDMod.lin (d.inc i) u) = φ w := by rw [hφi, hφw, hw]
      have h2 := congrArg (FDMod.lin (d.proj i)) (hφb.1 h1)
      rw [hretr] at h2
      rw [h2]
      simp only [w, map_sum]
      exact Finset.sum_eq_zero fun j hj ↦ horth j (Finset.ne_of_mem_erase hj) _
    haveI : FiniteDimensional k (d.obj i) := inferInstance
    have hτb : Function.Bijective τ :=
      ⟨hτinj, (LinearMap.injective_iff_surjective (f := τ.restrictScalars k)).1 hτinj⟩
    let eτ := LinearEquiv.ofBijective τ hτb
    refine ⟨(FDMod.ofLin (show W →ₗ[A] d.obj i from eτ.symm.toLinearMap ∘ₗ FDMod.lin (d.proj i) ∘ₗ FDMod.lin c)),
      (FDMod.hom_ext (LinearMap.ext fun u ↦ ?_))⟩
    change eτ.symm (FDMod.lin (d.proj i) (FDMod.lin c (FDMod.lin a u))) = u
    rw [LinearEquiv.symm_apply_eq]
    rfl

end LargeIndecomposable.AR
