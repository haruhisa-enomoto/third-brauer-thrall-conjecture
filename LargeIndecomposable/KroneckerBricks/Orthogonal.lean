module

public import LargeIndecomposable.KroneckerBricks.Small
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Orthogonality of the bricks `T_Λ`

`Hom(T_Λ, T_Λ') = 0` when `Λ \ Λ'` is infinite (`Bricks.hom_eq_zero`). A
morphism `(g, h)` is determined by `γ = h(1, 0) ∈ k^(Λ')`: for `μ ∈ Λ \ Λ'` the
coordinates of `g(e_μ)` are `γ_λ / (λ - μ)`, and the first component of `b`
gives `∑_λ γ_λ / (λ - μ) = h(1, 0)₁` for all these `μ`. A rational function with
simple poles that is constant at infinitely many points vanishes, so `γ = 0`
and then `(g, h) = 0`. In terms of `P¹`, `Hom(O(D), O(D')) = H⁰(O(D' - D)) = 0`
when `D` has infinitely many points outside `D'`.

Ingredient of the Göbel–Simson construction (the rigid ω-families of their
Proposition 3.5 are of this kind).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair Polynomial

universe u

variable {k : Type u} [Field k]

namespace Bricks

/-- A rational function `∑_{λ ∈ S} γ_λ / (λ - t)` that equals a constant `α` at
infinitely many points outside `S` vanishes, together with `α`. -/
lemma rational_vanish (S : Finset k) (γ : k → k) (α : k) (M : Set k) (hM : M.Infinite)
    (hMS : ∀ μ ∈ M, μ ∉ S) (h : ∀ μ ∈ M, ∑ l ∈ S, γ l / (l - μ) = α) : ∀ l ∈ S, γ l = 0 := by
  classical
  let P : k[X] := ∑ l ∈ S, C (γ l) * ∏ l' ∈ S.erase l, (C l' - X) - C α * ∏ l ∈ S, (C l - X)
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P (hM.mono fun μ hμ ↦ ?_)
    have hne : ∀ l ∈ S, l - μ ≠ 0 := fun l hl ↦ sub_ne_zero.2 fun e ↦ hMS μ hμ (e ▸ hl)
    show P.eval μ = 0
    simp only [P, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [← h μ hμ, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [← Finset.mul_prod_erase S (fun l ↦ l - μ) hl]
    field_simp [hne l hl]
    ring
  intro l₀ hl₀
  have h0 := congrArg (Polynomial.eval l₀) hP
  simp only [P, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_X, eval_zero] at h0
  rw [Finset.prod_eq_zero (f := fun x ↦ x - l₀) hl₀ (sub_self l₀), mul_zero, sub_zero,
    Finset.sum_eq_single l₀] at h0
  · have hprod : ∏ l' ∈ S.erase l₀, (l' - l₀) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun l' hl' ↦ sub_ne_zero.2 (Finset.ne_of_mem_erase hl')
    exact (mul_eq_zero.1 h0).resolve_right hprod
  · intro l hl hne
    rw [Finset.prod_eq_zero (f := fun x ↦ x - l₀) (Finset.mem_erase.2 ⟨Ne.symm hne, hl₀⟩)
      (sub_self l₀), mul_zero]
  · intro h; exact absurd hl₀ h

/-- The bricks `T_Λ` and `T_Λ'` are orthogonal when `Λ \ Λ'` is infinite. -/
theorem hom_eq_zero {Λ Λ' : Set k} (hinf : (Λ \ Λ').Infinite) (f : T Λ ⟶ T Λ') : f = 0 := by
  classical
  set g : (Λ →₀ k) →ₗ[k] (Λ' →₀ k) := (f.app zero).hom
  set h : k × (Λ →₀ k) →ₗ[k] k × (Λ' →₀ k) := (f.app one).hom
  have ha : ∀ c, h (0, c) = (0, g c) := fun c ↦
    congrArg (fun φ ↦ φ.hom c) (Kron.a_comp f)
  have hb : ∀ c, h (sumMap Λ c, diagMap Λ c) = (sumMap Λ' (g c), diagMap Λ' (g c)) := fun c ↦
    congrArg (fun φ ↦ φ.hom c) (Kron.b_comp f)
  set α := (h (1, 0)).1
  set γ := (h (1, 0)).2
  have key : ∀ (μ : Λ), α = sumMap Λ' (g (Finsupp.single μ 1)) ∧
      γ + (μ : k) • g (Finsupp.single μ 1) = diagMap Λ' (g (Finsupp.single μ 1)) := by
    intro μ
    have e := hb (Finsupp.single μ 1)
    rw [sumMap_single, diagMap_single, mul_one,
      show ((1 : k), Finsupp.single μ (μ : k)) = (1, 0) + (0, (μ : k) • Finsupp.single μ 1) by
        simp [Finsupp.smul_single], map_add, ha, map_smul] at e
    refine ⟨?_, by simpa using congrArg Prod.snd e⟩
    have := congrArg Prod.fst e
    simpa [α] using this
  have hcoord : ∀ (μ : Λ) (l : Λ'), γ l = ((l : k) - μ) * g (Finsupp.single μ 1) l := by
    intro μ l
    have := congrArg (fun c ↦ c l) (key μ).2
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    have hd : diagMap Λ' (g (Finsupp.single μ 1)) l = (l : k) * g (Finsupp.single μ 1) l := by
      conv_lhs => rw [← Finsupp.sum_single (g (Finsupp.single μ 1))]
      rw [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
      simp only [diagMap_single]
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · intro hl; simp [Finsupp.notMem_support_iff.1 hl]
    rw [hd] at this
    linear_combination this
  -- the rational function argument gives `γ = 0`
  let Γ : k → k := fun t ↦ if ht : t ∈ Λ' then γ ⟨t, ht⟩ else 0
  let S : Finset k := γ.support.map ⟨Subtype.val, Subtype.val_injective⟩
  have hsum : ∀ μ ∈ Λ \ Λ', ∑ l ∈ S, Γ l / (l - μ) = α := by
    rintro μ ⟨hμ, hμ'⟩
    have hx : ∀ l : Λ', g (Finsupp.single ⟨μ, hμ⟩ 1) l = γ l / ((l : k) - μ) := by
      intro l
      have hne : (l : k) - μ ≠ 0 := sub_ne_zero.2 fun e ↦ hμ' (e ▸ l.2)
      rw [hcoord ⟨μ, hμ⟩ l]
      field_simp
    rw [(key ⟨μ, hμ⟩).1, sumMap, Finsupp.linearCombination_apply]
    simp only [smul_eq_mul, mul_one]
    rw [Finsupp.sum_of_support_subset (s := γ.support)]
    · simp only [S, Finset.sum_map, Function.Embedding.coeFn_mk, Γ, Subtype.coe_prop,
        dite_true, hx]
    · intro l hl
      rw [Finsupp.mem_support_iff] at hl ⊢
      intro h0
      apply hl
      rw [hx, h0, zero_div]
    · intro _ _; rfl
  have hΓ := rational_vanish S Γ α (Λ \ Λ') hinf
    (fun μ hμ hS ↦ by
      obtain ⟨l, _, rfl⟩ := Finset.mem_map.1 hS
      exact hμ.2 l.2) hsum
  have hγ : γ = 0 := by
    ext l
    by_contra hl
    have hmem : (l : k) ∈ S := Finset.mem_map.2 ⟨l, Finsupp.mem_support_iff.2 hl, rfl⟩
    have := hΓ l hmem
    simp only [Γ, Subtype.coe_prop, dite_true] at this
    exact hl this
  -- hence `α = 0` and `g = 0`
  obtain ⟨μ₀, hμ₀⟩ := hinf.nonempty
  have hα0 : α = 0 := by
    have := hsum μ₀ hμ₀
    simp only [S, hγ, Finsupp.support_zero, Finset.map_empty, Finset.sum_empty] at this
    exact this.symm
  have hg0 : ∀ μ : Λ, g (Finsupp.single μ 1) = 0 := by
    intro μ
    have hoff : ∀ l : Λ', (l : k) ≠ μ → g (Finsupp.single μ 1) l = 0 := by
      intro l hl
      have := hcoord μ l
      rw [hγ, Finsupp.coe_zero, Pi.zero_apply] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (sub_ne_zero.2 hl)
    ext l
    by_cases hl : (l : k) = μ
    · have hx : g (Finsupp.single μ 1) = Finsupp.single l (g (Finsupp.single μ 1) l) := by
        ext l'
        by_cases hl' : l' = l
        · subst hl'; simp
        · rw [Finsupp.single_eq_of_ne hl']
          exact hoff l' fun e ↦ hl' (Subtype.ext (e.trans hl.symm))
      have h1 := (key μ).1
      rw [hx, sumMap_single, hα0] at h1
      rw [Finsupp.coe_zero, Pi.zero_apply]
      exact h1.symm
    · exact hoff l hl
  have hg : g = 0 := Finsupp.lhom_ext' fun μ ↦ LinearMap.ext_ring (by simpa using hg0 μ)
  have h10 : h (1, 0) = 0 := Prod.ext hα0 hγ
  refine Kron.hom_ext ?_ ?_
  · exact ModuleCat.hom_ext (hg.trans rfl)
  · refine ModuleCat.hom_ext (LinearMap.ext fun ⟨t, c⟩ ↦ ?_)
    change h (t, c) = 0
    rw [show (t, c) = t • ((1 : k), (0 : Λ →₀ k)) + (0, c) by simp, map_add, map_smul, ha, h10,
      hg]
    simp

end Bricks

end LargeIndecomposable
