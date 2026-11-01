module

public import LargeIndecomposable.KroneckerBricks.Extension
public import LargeIndecomposable.KroneckerBricks.Orthogonal

/-!
# A non-split extension of `T_Λ` by `T_Λ'`

Fix `λ₀ ∈ Λ \ Λ'` with `Λ \ Λ'` infinite. The extension of `T_Λ` by `T_Λ'` with
`α = 0` and `β(e_μ) = ((μ − λ₀)⁻¹, 0)` (and `β(e_{λ₀}) = 0`) does not split
(`Bricks.not_splits`): a splitting would make the rational function
`∑ z_λ / (λ − μ) + 1 / (λ₀ − μ)` constant at infinitely many `μ`, against
`Bricks.rational_vanish`. With `Bricks.isBrick_ext` and `Bricks.hom_eq_zero`
the extension module is a brick.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

namespace Bricks

variable (Λ Λ' : Set k) (l₀ : k)

open Classical in
/-- The extension class `β(e_μ) = ((μ − λ₀)⁻¹, 0)`. -/
def betaExt : (Λ →₀ k) →ₗ[k] (k × (Λ' →₀ k)) :=
  Finsupp.linearCombination k fun μ : Λ ↦ ((if (μ : k) = l₀ then 0 else ((μ : k) - l₀)⁻¹), 0)

open Classical in
lemma betaExt_single (μ : Λ) :
    betaExt Λ Λ' l₀ (Finsupp.single μ 1) = ((if (μ : k) = l₀ then 0 else ((μ : k) - l₀)⁻¹), 0) := by
  simp [betaExt]

variable {Λ Λ' l₀}

/-- The extension does not split. -/
theorem not_splits (hinf : (Λ \ Λ').Infinite) (hl₀ : l₀ ∈ Λ \ Λ') :
    ¬Splits (T Λ') (T Λ) 0 (betaExt Λ Λ' l₀) := by
  classical
  rintro ⟨φ₀, ψ₀, hα, hβ⟩
  let φ : (Λ →₀ k) →ₗ[k] (Λ' →₀ k) := φ₀
  let ψ : (k × (Λ →₀ k)) →ₗ[k] (k × (Λ' →₀ k)) := ψ₀
  -- `ψ (0, c) = (0, φ c)`
  have hψ0 : ∀ c : Λ →₀ k, ψ (0, c) = (0, φ c) := by
    intro c
    have := LinearMap.congr_fun hα c
    change (0 : k × (Λ' →₀ k)) = ((0 : k), φ c) - ψ (0, c) at this
    exact (sub_eq_zero.1 this.symm).symm
  have hβμ : ∀ μ : Λ, betaExt Λ Λ' l₀ (Finsupp.single μ 1) =
      (sumMap Λ' (φ (Finsupp.single μ 1)), diagMap Λ' (φ (Finsupp.single μ 1))) -
        ψ (1, Finsupp.single μ (μ : k)) := by
    intro μ
    have := LinearMap.congr_fun hβ (Finsupp.single μ 1)
    change _ = (sumMap Λ' (φ _), diagMap Λ' (φ _)) - ψ (sumMap Λ _, diagMap Λ _) at this
    rwa [sumMap_single, diagMap_single, mul_one] at this
  set t := (ψ (1, 0)).1
  set z := (ψ (1, 0)).2
  have hψμ : ∀ μ : Λ, ψ (1, Finsupp.single μ (μ : k)) = (t, z + (μ : k) • φ (Finsupp.single μ 1)) := by
    intro μ
    rw [show ((1 : k), Finsupp.single μ (μ : k)) = (1, 0) + (μ : k) • ((0 : k), Finsupp.single μ 1) by
      ext <;> simp [Finsupp.smul_single], map_add, map_smul, hψ0]
    ext <;> simp [t, z]
  -- for `μ ∈ Λ \ Λ'`, `μ ≠ λ₀`, the coordinates of `φ(e_μ)` are `z_λ / (λ − μ)`
  let Γ : k → k := fun s ↦ if hs : s ∈ Λ' then z ⟨s, hs⟩ else 0
  let S : Finset k := insert l₀ (z.support.map ⟨Subtype.val, Subtype.val_injective⟩)
  let γ : k → k := fun s ↦ if s = l₀ then 1 else Γ s
  have hl₀S : l₀ ∉ z.support.map ⟨Subtype.val, Subtype.val_injective⟩ := by
    intro h
    obtain ⟨l, -, hl⟩ := Finset.mem_map.1 h
    exact hl₀.2 (hl ▸ l.2)
  let M : Set k := (Λ \ Λ') \ {l₀}
  have hM : M.Infinite := hinf.sdiff (Set.finite_singleton l₀)
  have hsum : ∀ μ ∈ M, ∑ l ∈ S, γ l / (l - μ) = t := by
    rintro μ ⟨⟨hμ, hμ'⟩, hμ0⟩
    have hμ0' : μ ≠ l₀ := hμ0
    have e := hβμ ⟨μ, hμ⟩
    rw [betaExt_single, hψμ] at e
    simp only [if_neg hμ0'] at e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [Prod.fst_sub, Prod.snd_sub] at e1 e2
    set x := φ (Finsupp.single ⟨μ, hμ⟩ 1)
    have hx : ∀ l : Λ', x l = z l / ((l : k) - μ) := by
      intro l
      have hne : (l : k) - μ ≠ 0 := sub_ne_zero.2 fun h ↦ hμ' (h ▸ l.2)
      have := congrArg (fun c : Λ' →₀ k ↦ c l) e2
      have hd : diagMap Λ' x l = (l : k) * x l := by
        conv_lhs => rw [← Finsupp.sum_single x]
        rw [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
        simp only [diagMap_single]
        rw [Finset.sum_eq_single l]
        · simp
        · intro b _ hb; simp [hb]
        · intro hl; simp [Finsupp.notMem_support_iff.1 hl]
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_add,
        Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hd] at this
      rw [eq_div_iff hne]
      linear_combination (-1 : k) * this
    have hsx : sumMap Λ' x = ∑ l ∈ z.support.map ⟨Subtype.val, Subtype.val_injective⟩,
        Γ l / (l - μ) := by
      rw [sumMap, Finsupp.linearCombination_apply]
      simp only [smul_eq_mul, mul_one]
      rw [Finsupp.sum_of_support_subset (s := z.support)]
      · simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Γ, Subtype.coe_prop, dite_true, hx]
      · intro l hl
        rw [Finsupp.mem_support_iff] at hl ⊢
        intro h0
        apply hl
        rw [hx, h0, zero_div]
      · intro _ _; rfl
    rw [Finset.sum_insert hl₀S]
    simp only [γ, if_pos rfl]
    rw [show ∑ l ∈ z.support.map ⟨Subtype.val, Subtype.val_injective⟩,
        (if l = l₀ then 1 else Γ l) / (l - μ) =
          ∑ l ∈ z.support.map ⟨Subtype.val, Subtype.val_injective⟩, Γ l / (l - μ) from
      Finset.sum_congr rfl fun l hl ↦ by
        rw [if_neg (show l ≠ l₀ from fun h ↦ hl₀S (by rw [← h]; exact hl))], ← hsx]
    have hne : l₀ - μ ≠ 0 := sub_ne_zero.2 (Ne.symm hμ0')
    have hne' : μ - l₀ ≠ 0 := sub_ne_zero.2 hμ0'
    rw [eq_sub_iff_add_eq] at e1
    rw [← e1]
    field_simp
    ring
  have := rational_vanish S γ t M hM (fun μ hμ hS ↦ by
    rcases Finset.mem_insert.1 hS with h | h
    · exact hμ.2 h
    · obtain ⟨l, -, hl⟩ := Finset.mem_map.1 h
      exact hμ.1.2 (hl ▸ l.2)) hsum l₀ (Finset.mem_insert_self _ _)
  simp [γ] at this

/-- The extension module of `T_Λ` by `T_Λ'` is a brick when `Λ \ Λ'` and `Λ' \ Λ`
are infinite. -/
theorem isBrick_extT (h₁ : (Λ \ Λ').Infinite) (h₂ : (Λ' \ Λ).Infinite) (hl₀ : l₀ ∈ Λ \ Λ') :
    IsBrickKron (ext (T Λ') (T Λ) 0 (betaExt Λ Λ' l₀)) :=
  isBrick_ext (isBrick Λ' (h₂.nonempty.mono Set.sdiff_subset)) (isBrick Λ (h₁.nonempty.mono
    Set.sdiff_subset)) (hom_eq_zero h₂) (hom_eq_zero h₁) (not_splits h₁ hl₀)

end Bricks

end LargeIndecomposable
