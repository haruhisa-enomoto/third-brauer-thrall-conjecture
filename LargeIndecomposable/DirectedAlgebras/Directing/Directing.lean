module

public import LargeIndecomposable.Modules.KrullSchmidt.Fitting

/-!
# Directing modules

`Reach₁ X Y`: a path `X → ⋯ → Y` of nonzero non-bijective maps between nonzero
indecomposables, of length at least one. `M` is directing when it is a nonzero
indecomposable with no such cycle `M → ⋯ → M`.

* `Directing.endo`: every endomorphism of a directing module is zero or bijective.
* `Directing.split`: every short exact sequence `0 → M → E → M → 0` splits
  (`Ext¹(M, M) = 0`; Ringel, *Tame algebras*, 2.4).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Nonzero indecomposable objects. -/
def IsInd (X : FDMod k A) : Prop := IsIndecMod A X ∧ Nontrivial X

/-- Paths of nonzero non-bijective maps between nonzero indecomposables. -/
inductive Reach₁ : FDMod k A → FDMod k A → Prop
  | step {X Y : FDMod k A} (hX : IsInd X) (hY : IsInd Y) (f : X ⟶ Y)
      (hf : FDMod.lin f ≠ 0) (hnb : ¬Function.Bijective (FDMod.lin f)) : Reach₁ X Y
  | trans {X Y Z : FDMod k A} : Reach₁ X Y → Reach₁ Y Z → Reach₁ X Z

/-- A directing module. -/
def Directing (M : FDMod k A) : Prop := IsInd M ∧ ¬Reach₁ M M

/-- **Endomorphisms of a directing module are zero or bijective.** -/
lemma Directing.endo {M : FDMod k A} (hM : Directing M) (e : M ⟶ M) :
    FDMod.lin e = 0 ∨ Function.Bijective (FDMod.lin e) := by
  by_contra h
  push Not at h
  exact hM.2 (Reach₁.step hM.1 hM.1 e h.1 h.2)

/-- A surjection splits if some endomorphism of its source fixes it and kills the kernel. -/
lemma split_of_endo {E M : Type*} [AddCommGroup E] [Module A E] [AddCommGroup M] [Module A M]
    (i : M →ₗ[A] E) (p : E →ₗ[A] M) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p) (e : E →ₗ[A] E) (he1 : ∀ x, p (e x) = p x)
    (he2 : ∀ m, e (i m) = 0) : ∃ s : M →ₗ[A] E, p ∘ₗ s = LinearMap.id := by
  have hker : LinearMap.ker p ≤ LinearMap.ker e := by
    intro x hx
    rw [← hex] at hx
    obtain ⟨m, rfl⟩ := hx
    exact he2 m
  let q := LinearMap.quotKerEquivOfSurjective p hp
  refine ⟨((LinearMap.ker p).liftQ e hker) ∘ₗ q.symm.toLinearMap, ?_⟩
  ext m
  obtain ⟨x, rfl⟩ := hp m
  have hq : q.symm (p x) = Submodule.Quotient.mk x := q.symm_apply_eq.2 rfl
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hq,
    Submodule.liftQ_apply, LinearMap.id_coe, id_eq]
  exact he1 x

/-- **A directing module has no self-extensions.** -/
theorem Directing.split [FiniteDimensional k A] {M E : FDMod k A} (hM : Directing M)
    (i : M ⟶ E) (p : E ⟶ M) (hi : Function.Injective (FDMod.lin i))
    (hp : Function.Surjective (FDMod.lin p))
    (hex : LinearMap.range (FDMod.lin i) = LinearMap.ker (FDMod.lin p)) :
    ∃ s : M ⟶ E, FDMod.lin p ∘ₗ FDMod.lin s = LinearMap.id := by
  classical
  obtain ⟨d⟩ := FDMod.exists_decomp E
  -- components of `i` and `p`
  let ij : ∀ j, M →ₗ[A] d.obj j := fun j ↦ FDMod.lin (d.proj j) ∘ₗ FDMod.lin i
  let pj : ∀ j, d.obj j →ₗ[A] M := fun j ↦ FDMod.lin p ∘ₗ FDMod.lin (d.inc j)
  have hsum : ∀ x : E, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
    have := LinearMap.congr_fun d.sum_id x
    simpa using this
  by_contra hns
  -- no `pⱼ` is a split epimorphism
  have hpj : ∀ j, ¬Function.Bijective (pj j) := by
    intro j hb
    apply hns
    let e := LinearEquiv.ofBijective (pj j) hb
    refine ⟨(FDMod.ofLin (show M →ₗ[A] E from FDMod.lin (d.inc j) ∘ₗ e.symm.toLinearMap)), ?_⟩
    ext x
    exact e.apply_symm_apply x
  -- no `iⱼ` is a split monomorphism
  have hij : ∀ j, ¬Function.Bijective (ij j) := by
    intro j hb
    apply hns
    let e := LinearEquiv.ofBijective (ij j) hb
    -- the retraction `r = e⁻¹ ∘ projⱼ` of `i` splits the sequence
    let r : E →ₗ[A] M := e.symm.toLinearMap ∘ₗ FDMod.lin (d.proj j)
    have hr : r ∘ₗ FDMod.lin i = LinearMap.id := by
      ext x; exact e.symm_apply_apply x
    obtain ⟨s', hs'⟩ := split_of_endo (FDMod.lin i) (FDMod.lin p) hp hex
      (LinearMap.id - FDMod.lin i ∘ₗ r) (fun x ↦ by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp,
          Function.comp_apply, map_sub]
        have : FDMod.lin p (FDMod.lin i (r x)) = 0 :=
          LinearMap.mem_ker.1 (hex ▸ LinearMap.mem_range_self (FDMod.lin i) (r x))
        rw [this, sub_zero]) (fun m ↦ by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp,
          Function.comp_apply]
        rw [show r (FDMod.lin i m) = m from LinearMap.congr_fun hr m, sub_self])
    exact ⟨(FDMod.ofLin s'), hs'⟩
  -- some summand receives `i` nonzero and maps nonzero by `p`
  by_cases hboth : ∃ j, ij j ≠ 0 ∧ pj j ≠ 0
  · obtain ⟨j, h1, h2⟩ := hboth
    have hInd : IsInd (d.obj j) := ⟨d.indec j, d.nt j⟩
    exact hM.2 (Reach₁.trans
      (Reach₁.step hM.1 hInd (show M ⟶ d.obj j from (FDMod.ofLin (ij j))) h1 (hij j))
      (Reach₁.step hInd hM.1 (show d.obj j ⟶ M from (FDMod.ofLin (pj j))) h2 (hpj j)))
  · push Not at hboth
    -- the summands receiving `i` are killed by `p`, so `p` is injective on the others
    apply hns
    let e₂ : E →ₗ[A] E := ∑ j ∈ Finset.univ.filter (fun j ↦ ij j = 0),
      FDMod.lin (d.inc j) ∘ₗ FDMod.lin (d.proj j)
    have hpe : ∀ x, FDMod.lin p (e₂ x) = FDMod.lin p x := by
      intro x
      conv_rhs => rw [← hsum x]
      rw [map_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ ij j = 0)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j ↦ ¬ij j = 0) (fun j hj ↦ by
        have := hboth j (Finset.mem_filter.1 hj).2
        exact LinearMap.congr_fun this _), add_zero]
      simp only [e₂, LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, map_sum]
    have hei : ∀ m, e₂ (FDMod.lin i m) = 0 := by
      intro m
      rw [LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun j hj ↦ by
        have := LinearMap.congr_fun (Finset.mem_filter.1 hj).2 m
        simp only [LinearMap.coe_comp, Function.comp_apply]
        change FDMod.lin (d.inc j) (ij j m) = 0
        rw [this, LinearMap.zero_apply, map_zero]
    obtain ⟨s', hs'⟩ := split_of_endo (FDMod.lin i) (FDMod.lin p) hp hex e₂ (fun x ↦ (hpe x))
      hei
    exact ⟨(FDMod.ofLin s'), hs'⟩

end LargeIndecomposable.AR
